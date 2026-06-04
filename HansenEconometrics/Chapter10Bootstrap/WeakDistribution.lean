import HansenEconometrics.Chapter10Bootstrap.Distribution
import HansenEconometrics.Chapter10Bootstrap.WLLN

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Elementwise Function

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

section BootstrapWeakDistribution

/-- Conditional bootstrap expectation of a bounded continuous test function.

This is the bounded-continuous-test-function analogue of the conditional CDF
used in `TendstoInBootstrapDistribution`.  It is a convenient weak-convergence
backend for mapping theorems, while the finite-dimensional CDF API remains the
chapter-facing form of Hansen Definition 10.2. -/
noncomputable def bootstrapBoundedContinuousIntegral
    [TopologicalSpace E]
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → E)
    (f : BoundedContinuousFunction E ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ ωs, f (Zstar n ω ωs) ∂Pstar n ω

/-- Conditional bootstrap probability of an event under the transformed
bootstrap statistic.

This real-valued wrapper is the event-probability face used after
bounded-continuous weak convergence has supplied a Portmanteau-style
lower/upper sandwich. -/
noncomputable def bootstrapEventProbability
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → E)
    (A : Set E) (n : ℕ) (ω : Ω) : ℝ :=
  ((Pstar n ω) {ωs | Zstar n ω ωs ∈ A}).toReal

/-- Bootstrap convergence in distribution in bounded-continuous-test-function
form.

For every bounded continuous real test function, the conditional bootstrap
expectation converges in ordinary probability to the corresponding expectation
under the limiting law. -/
def TendstoInBootstrapWeakDistribution
    [TopologicalSpace E]
    (μ : Measure Ω) (Pstar : ℕ → Ω → Measure Ωs)
    (Zstar : ℕ → Ω → Ωs → E)
    (ν : Measure Ωlim) (Z : Ωlim → E) : Prop :=
  ∀ f : BoundedContinuousFunction E ℝ,
    TendstoInMeasure μ
      (fun n ω => bootstrapBoundedContinuousIntegral Pstar Zstar f n ω)
      atTop (fun _ => ∫ ωlim, f (Z ωlim) ∂ν)

/-- Projection from the bounded-continuous-test-function bootstrap convergence
definition. -/
theorem TendstoInBootstrapWeakDistribution.tendsto_integral
    [TopologicalSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (f : BoundedContinuousFunction E ℝ) :
    TendstoInMeasure μ
      (fun n ω => bootstrapBoundedContinuousIntegral Pstar Zstar f n ω)
      atTop (fun _ => ∫ ωlim, f (Z ωlim) ∂ν) :=
  hZ f

/-- Bootstrap weak convergence from pathwise conditional weak convergence.

If every bounded continuous conditional bootstrap integral converges to the
limit integral for almost every original sample path, then it also converges in
outer probability. This is the bridge used by sample-path conditional CLTs. -/
theorem TendstoInBootstrapWeakDistribution.of_ae_tendsto_integrals
    [TopologicalSpace E] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E}
    (hmeas : ∀ f : BoundedContinuousFunction E ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω => bootstrapBoundedContinuousIntegral Pstar Zstar f n ω) μ)
    (hae : ∀ f : BoundedContinuousFunction E ℝ,
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n => bootstrapBoundedContinuousIntegral Pstar Zstar f n ω)
          atTop (nhds (∫ ωlim, f (Z ωlim) ∂ν))) :
    TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z := by
  intro f
  exact tendstoInMeasure_of_tendsto_ae (hmeas f) (hae f)

/-- Bootstrap weak convergence from pathwise conditional weak convergence in
Mathlib's `TendstoInDistribution` form.

This removes one layer of bounded-continuous integral bookkeeping: a conditional
CLT stated as weak convergence of the conditional bootstrap laws supplies the
integral convergence premises of
`TendstoInBootstrapWeakDistribution.of_ae_tendsto_integrals`. -/
theorem TendstoInBootstrapWeakDistribution.of_ae_tendstoInDistribution
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs} [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E} [IsProbabilityMeasure ν]
    (hmeas : ∀ f : BoundedContinuousFunction E ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω => bootstrapBoundedContinuousIntegral Pstar Zstar f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωs) => Zstar n ω ωs)
        atTop Z (fun n => Pstar n ω) ν) :
    TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z := by
  refine TendstoInBootstrapWeakDistribution.of_ae_tendsto_integrals
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    hmeas ?_
  intro f
  filter_upwards [hae] with ω hdist
  simpa [bootstrapBoundedContinuousIntegral] using
    (TendstoInDistribution.integral_boundedContinuous_tendsto_indexed
      (Ω := fun _ : ℕ => Ωs) (μ := fun n => Pstar n ω)
      (X := fun n (ωs : Ωs) => Zstar n ω ωs) (Z := Z) hdist f)

/-- Bootstrap weak convergence after an a.e.-continuous mapping, from pathwise
conditional weak convergence in Mathlib's `TendstoInDistribution` form.

This is the pathwise-distribution version of Hansen Theorem 10.5: for almost
every original sample path, Mathlib's a.e.-continuous CMT maps the conditional
weak convergence of `Zstar` to the conditional weak convergence of `g ∘ Zstar`;
the existing pathwise-to-bootstrap bridge then turns those conditional weak
limits into bootstrap weak convergence in probability. -/
theorem TendstoInBootstrapWeakDistribution.of_ae_tendstoInDistribution_ae_continuous_comp
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E]
    [TopologicalSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [BorelSpace F] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs} [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → E}
    {g : E → F} (hg : Measurable g) {D : Set E}
    (hD : (ν.map Z) D = 0)
    (hcont : ∀ x, x ∉ D → ContinuousAt g x)
    (hmeas : ∀ f : BoundedContinuousFunction F ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          bootstrapBoundedContinuousIntegral Pstar
            (fun n ω ωs => g (Zstar n ω ωs)) f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωs) => Zstar n ω ωs)
        atTop Z (fun n => Pstar n ω) ν) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  refine TendstoInBootstrapWeakDistribution.of_ae_tendstoInDistribution
    (μ := μ) (Pstar := Pstar)
    (Zstar := fun n ω ωs => g (Zstar n ω ωs))
    (ν := ν) (Z := fun ωlim => g (Z ωlim)) hmeas ?_
  filter_upwards [hae] with ω hdist
  exact
    tendstoInDistribution_ae_continuous_comp
      (P := fun n => Pstar n ω) (ν := ν)
      (X := fun n (ωs : Ωs) => Zstar n ω ωs) (Z := Z)
      (g := g) hdist hg hD hcont

/-- Measurability of finite-uniform bootstrap bounded-continuous integrals.

When the bootstrap law is the uniform law on a finite resampling space, the
conditional integral is a finite average over resampling paths.  Thus
a.e.-measurability of each pathwise statistic in the original sample is enough
to discharge the measurability side condition in pathwise conditional weak
convergence constructors. -/
theorem bootstrapBoundedContinuousIntegral_uniformOn_univ_aestronglyMeasurable
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ωs] [Finite Ωs] [MeasurableSingletonClass Ωs]
    {μ : Measure Ω} {Zstar : ℕ → Ω → Ωs → E}
    (hZ : ∀ n ωs, AEMeasurable (fun ω => Zstar n ω ωs) μ)
    (f : BoundedContinuousFunction E ℝ) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω => bootstrapBoundedContinuousIntegral
        (fun _ _ => ProbabilityTheory.uniformOn (Set.univ : Set Ωs))
        Zstar f n ω) μ := by
  classical
  letI : Fintype Ωs := Fintype.ofFinite Ωs
  have hsum : AEStronglyMeasurable
      (fun ω => ∑ ωs : Ωs, f (Zstar n ω ωs)) μ := by
    refine Finset.aestronglyMeasurable_fun_sum Finset.univ (fun ωs _ => ?_)
    exact (f.continuous.measurable.comp_aemeasurable (hZ n ωs)).aestronglyMeasurable
  refine (hsum.const_smul (((Fintype.card Ωs : ℝ≥0∞)⁻¹).toReal)).congr ?_
  exact ae_of_all μ fun ω => by
    symm
    simpa [bootstrapBoundedContinuousIntegral] using
      (integral_uniformOn_univ_eq_card_inv_smul_sum
        (ι := Ωs) (E := ℝ) (fun ωs => f (Zstar n ω ωs)))

/-- Bootstrap weak convergence is invariant under pointwise equality of the
bootstrap statistic. -/
theorem TendstoInBootstrapWeakDistribution.congr_bootstrap
    [TopologicalSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z) :
    TendstoInBootstrapWeakDistribution μ Pstar Zstar' ν Z := by
  intro f
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl (hZ.tendsto_integral f)
  refine ae_of_all μ fun ω => ?_
  simp [bootstrapBoundedContinuousIntegral, hstar]

/-- Bootstrap weak convergence is invariant under pointwise equality of the
limiting statistic. -/
theorem TendstoInBootstrapWeakDistribution.congr_limit
    [TopologicalSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {Z Z' : Ωlim → E}
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z) :
    TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z' := by
  intro f
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ (hZ.tendsto_integral f)
  refine ae_of_all μ fun _ => ?_
  simp [hlim]

/-- Pointwise congruence for bootstrap weak convergence. -/
theorem TendstoInBootstrapWeakDistribution.congr
    [TopologicalSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → E}
    {Z Z' : Ωlim → E}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z) :
    TendstoInBootstrapWeakDistribution μ Pstar Zstar' ν Z' :=
  (hZ.congr_bootstrap hstar).congr_limit hlim

/-- Bootstrap weak convergence is invariant under replacing the auxiliary
limit space and limit map by another pair with the same law. -/
theorem TendstoInBootstrapWeakDistribution.congr_limit_law
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Ωlim' : Type*} [MeasurableSpace Ωlim']
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E} {Y : Ωlim' → E}
    {law : Measure E} {νlim : Measure Ωlim'}
    (hZlaw : HasLaw Z law ν)
    (hYlaw : HasLaw Y law νlim)
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z) :
    TendstoInBootstrapWeakDistribution μ Pstar Zstar νlim Y := by
  intro f
  have htarget :
      ∫ ωlim, f (Z ωlim) ∂ν = ∫ ωlim, f (Y ωlim) ∂νlim := by
    calc
      ∫ ωlim, f (Z ωlim) ∂ν = ∫ x, f x ∂(ν.map Z) := by
        exact
          (integral_map hZlaw.aemeasurable
            f.continuous.aestronglyMeasurable).symm
      _ = ∫ x, f x ∂law := by rw [hZlaw.map_eq]
      _ = ∫ x, f x ∂(νlim.map Y) := by rw [← hYlaw.map_eq]
      _ = ∫ ωlim, f (Y ωlim) ∂νlim := by
        exact integral_map hYlaw.aemeasurable f.continuous.aestronglyMeasurable
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ (hZ.tendsto_integral f)
  exact ae_of_all μ fun _ => htarget

/-- Transfer bootstrap weak convergence across an `oₚ(1)` difference in every
bounded-continuous test-function integral.

This is the reusable linearization bridge behind nonlinear bootstrap Delta
method wrappers: once the linearized statistic has a bootstrap weak limit, it
is enough to show that applying any bounded continuous test function and
taking the conditional bootstrap expectation differs from the nonlinear
statistic by `oₚ(1)`. -/
theorem TendstoInBootstrapWeakDistribution.of_integral_difference_zero
    [TopologicalSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hdiff :
      ∀ f : BoundedContinuousFunction E ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegral Pstar Zstar' f n ω -
              bootstrapBoundedContinuousIntegral Pstar Zstar f n ω)
          atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistribution μ Pstar Zstar' ν Z := by
  intro f
  have hlin := hZ.tendsto_integral f
  have hlin0 := TendstoInMeasure.sub_limit_zero_real hlin
  have hsum := TendstoInMeasure.add_zero_real (hdiff f) hlin0
  have htarget0 :
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapBoundedContinuousIntegral Pstar Zstar' f n ω -
            ∫ ωlim, f (Z ωlim) ∂ν)
        atTop (fun _ => 0) := by
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hsum
    exact ae_of_all μ fun ω => by ring
  exact TendstoInMeasure.of_sub_limit_zero_real htarget0

/-- Deterministic integral bound for uniformly close bootstrap statistics.

If two statistics are within `δ` except on a bad event, then the conditional
integrals of a bounded continuous test function differ by at most the
uniform-continuity tolerance plus `2 ‖f‖` times the bad-event probability. -/
theorem abs_integral_boundedContinuous_comp_sub_le_of_dist_event
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E]
    {P : Measure Ωs} [IsProbabilityMeasure P] {Z Z' : Ωs → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (f : BoundedContinuousFunction E ℝ)
    {η δ : ℝ} (hη : 0 ≤ η)
    (hsmall : ∀ ωs, dist (Z' ωs) (Z ωs) < δ →
      |f (Z' ωs) - f (Z ωs)| ≤ η) :
    |(∫ ωs, f (Z' ωs) ∂P) - (∫ ωs, f (Z ωs) ∂P)| ≤
      η + (2 * ‖f‖) * P.real {ωs | δ ≤ dist (Z' ωs) (Z ωs)} := by
  classical
  let bad : Set Ωs := {ωs | δ ≤ dist (Z' ωs) (Z ωs)}
  let C : ℝ := 2 * ‖f‖
  have hbad : MeasurableSet bad := by
    dsimp [bad]
    exact measurableSet_le measurable_const (hZ'.dist hZ)
  have hZ_int : Integrable (fun ωs => f (Z ωs)) P := by
    refine Integrable.of_bound
      ((f.continuous.measurable.comp hZ).aestronglyMeasurable) ‖f‖ ?_
    exact ae_of_all P fun ωs => f.norm_coe_le_norm (Z ωs)
  have hZ'_int : Integrable (fun ωs => f (Z' ωs)) P := by
    refine Integrable.of_bound
      ((f.continuous.measurable.comp hZ').aestronglyMeasurable) ‖f‖ ?_
    exact ae_of_all P fun ωs => f.norm_coe_le_norm (Z' ωs)
  have hdiff_int : Integrable (fun ωs => f (Z' ωs) - f (Z ωs)) P :=
    hZ'_int.sub hZ_int
  have hbad_ind_int :
      Integrable (fun ωs => if ωs ∈ bad then (1 : ℝ) else 0) P := by
    simpa [bad] using
      ((integrable_indicator_iff hbad).mpr
        (integrable_const (1 : ℝ)).integrableOn)
  have hbound_int :
      Integrable (fun ωs => η + C * (if ωs ∈ bad then (1 : ℝ) else 0)) P :=
    (integrable_const η).add (hbad_ind_int.const_mul C)
  have hpoint :
      (fun ωs => |f (Z' ωs) - f (Z ωs)|) ≤
        fun ωs => η + C * (if ωs ∈ bad then (1 : ℝ) else 0) := by
    intro ωs
    by_cases hω : ωs ∈ bad
    · have hfx : |f (Z' ωs)| ≤ ‖f‖ := by
        simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (Z' ωs)
      have hfy : |f (Z ωs)| ≤ ‖f‖ := by
        simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (Z ωs)
      have hdiff_le : |f (Z' ωs) - f (Z ωs)| ≤ C := by
        dsimp [C]
        calc
          |f (Z' ωs) - f (Z ωs)| = |f (Z' ωs) + -f (Z ωs)| := by ring_nf
          _ ≤ |f (Z' ωs)| + |-f (Z ωs)| := abs_add_le _ _
          _ = |f (Z' ωs)| + |f (Z ωs)| := by rw [abs_neg]
          _ ≤ ‖f‖ + ‖f‖ := add_le_add hfx hfy
          _ = 2 * ‖f‖ := by ring
      have hC_nonneg : 0 ≤ C := by
        dsimp [C]
        positivity
      simp [hω]
      linarith
    · have hdist_lt : dist (Z' ωs) (Z ωs) < δ := by
        exact not_le.mp hω
      have hsmall' : |f (Z' ωs) - f (Z ωs)| ≤ η :=
        hsmall ωs hdist_lt
      simp [hω, hsmall']
  have habs_bound :
      ∫ ωs, |f (Z' ωs) - f (Z ωs)| ∂P ≤
        ∫ ωs, η + C * (if ωs ∈ bad then (1 : ℝ) else 0) ∂P :=
    integral_mono hdiff_int.norm hbound_int hpoint
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
    |(∫ ωs, f (Z' ωs) ∂P) - (∫ ωs, f (Z ωs) ∂P)|
        = |∫ ωs, f (Z' ωs) - f (Z ωs) ∂P| := by
          rw [integral_sub hZ'_int hZ_int]
    _ ≤ ∫ ωs, |f (Z' ωs) - f (Z ωs)| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ωs, η + C * (if ωs ∈ bad then (1 : ℝ) else 0) ∂P := habs_bound
    _ = η + C * P.real bad := by
      rw [integral_add (integrable_const η) (hbad_ind_int.const_mul C)]
      rw [integral_const, integral_const_mul, hbad_integral]
      simp [C]

/-- Deterministic integral bound for locally uniformly close bootstrap
statistics with compact-tail errors.

This is the noncompact companion to
`abs_integral_boundedContinuous_comp_sub_le_of_dist_event`: the bounded
continuous test function only needs uniform continuity on a compact set `K`,
and the price of leaving that set is paid by the two compact-tail
probabilities. -/
theorem abs_integral_boundedContinuous_comp_sub_le_of_dist_event_compact_tails
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] [T2Space E]
    {P : Measure Ωs} [IsProbabilityMeasure P] {Z Z' : Ωs → E}
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (f : BoundedContinuousFunction E ℝ) {K : Set E}
    (hK : IsCompact K) {η δ : ℝ} (hη : 0 ≤ η)
    (hsmall : ∀ x, x ∈ K → ∀ y, y ∈ K →
      dist y x < δ → |f y - f x| ≤ η) :
    |(∫ ωs, f (Z' ωs) ∂P) - (∫ ωs, f (Z ωs) ∂P)| ≤
      η + (2 * ‖f‖) *
        P.real
          ({ωs | δ ≤ dist (Z' ωs) (Z ωs)} ∪
            {ωs | Z ωs ∉ K} ∪ {ωs | Z' ωs ∉ K}) := by
  classical
  let bad : Set Ωs :=
    {ωs | δ ≤ dist (Z' ωs) (Z ωs)} ∪
      {ωs | Z ωs ∉ K} ∪ {ωs | Z' ωs ∉ K}
  let C : ℝ := 2 * ‖f‖
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hclose_meas : MeasurableSet {ωs | δ ≤ dist (Z' ωs) (Z ωs)} := by
    exact measurableSet_le measurable_const (hZ'.dist hZ)
  have htail_meas : MeasurableSet {ωs | Z ωs ∉ K} := by
    simpa only [Set.mem_setOf_eq, Set.mem_compl_iff] using
      hKmeas.compl.preimage hZ
  have htail'_meas : MeasurableSet {ωs | Z' ωs ∉ K} := by
    simpa only [Set.mem_setOf_eq, Set.mem_compl_iff] using
      hKmeas.compl.preimage hZ'
  have hbad : MeasurableSet bad :=
    (hclose_meas.union htail_meas).union htail'_meas
  have hZ_int : Integrable (fun ωs => f (Z ωs)) P := by
    refine Integrable.of_bound
      ((f.continuous.measurable.comp hZ).aestronglyMeasurable) ‖f‖ ?_
    exact ae_of_all P fun ωs => f.norm_coe_le_norm (Z ωs)
  have hZ'_int : Integrable (fun ωs => f (Z' ωs)) P := by
    refine Integrable.of_bound
      ((f.continuous.measurable.comp hZ').aestronglyMeasurable) ‖f‖ ?_
    exact ae_of_all P fun ωs => f.norm_coe_le_norm (Z' ωs)
  have hdiff_int : Integrable (fun ωs => f (Z' ωs) - f (Z ωs)) P :=
    hZ'_int.sub hZ_int
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
      Integrable (fun ωs => η + C * (if ωs ∈ bad then (1 : ℝ) else 0)) P :=
    (integrable_const η).add (hbad_ind_int.const_mul C)
  have hpoint :
      (fun ωs => |f (Z' ωs) - f (Z ωs)|) ≤
        fun ωs => η + C * (if ωs ∈ bad then (1 : ℝ) else 0) := by
    intro ωs
    by_cases hω : ωs ∈ bad
    · have hfx : |f (Z' ωs)| ≤ ‖f‖ := by
        simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (Z' ωs)
      have hfy : |f (Z ωs)| ≤ ‖f‖ := by
        simpa [Real.norm_eq_abs] using f.norm_coe_le_norm (Z ωs)
      have hdiff_le : |f (Z' ωs) - f (Z ωs)| ≤ C := by
        dsimp [C]
        calc
          |f (Z' ωs) - f (Z ωs)| = |f (Z' ωs) + -f (Z ωs)| := by ring_nf
          _ ≤ |f (Z' ωs)| + |-f (Z ωs)| := abs_add_le _ _
          _ = |f (Z' ωs)| + |f (Z ωs)| := by rw [abs_neg]
          _ ≤ ‖f‖ + ‖f‖ := add_le_add hfx hfy
          _ = 2 * ‖f‖ := by ring
      have hC_nonneg : 0 ≤ C := by
        dsimp [C]
        positivity
      simp [hω]
      linarith
    · have hnot_close : ¬ δ ≤ dist (Z' ωs) (Z ωs) := by
        intro hclose
        exact hω (Or.inl (Or.inl hclose))
      have hZ_mem : Z ωs ∈ K := by
        by_contra hnot
        exact hω (Or.inl (Or.inr hnot))
      have hZ'_mem : Z' ωs ∈ K := by
        by_contra hnot
        exact hω (Or.inr hnot)
      have hdist_lt : dist (Z' ωs) (Z ωs) < δ := not_le.mp hnot_close
      have hsmall' : |f (Z' ωs) - f (Z ωs)| ≤ η :=
        hsmall (Z ωs) hZ_mem (Z' ωs) hZ'_mem hdist_lt
      simp [hω, hsmall']
  have habs_bound :
      ∫ ωs, |f (Z' ωs) - f (Z ωs)| ∂P ≤
        ∫ ωs, η + C * (if ωs ∈ bad then (1 : ℝ) else 0) ∂P :=
    integral_mono hdiff_int.norm hbound_int hpoint
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
    |(∫ ωs, f (Z' ωs) ∂P) - (∫ ωs, f (Z ωs) ∂P)|
        = |∫ ωs, f (Z' ωs) - f (Z ωs) ∂P| := by
          rw [integral_sub hZ'_int hZ_int]
    _ ≤ ∫ ωs, |f (Z' ωs) - f (Z ωs)| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ωs, η + C * (if ωs ∈ bad then (1 : ℝ) else 0) ∂P := habs_bound
    _ = η + C * P.real bad := by
      calc
        ∫ ωs, η + C * (if ωs ∈ bad then (1 : ℝ) else 0) ∂P
            = ∫ _ωs, η ∂P +
                ∫ ωs, C * (if ωs ∈ bad then (1 : ℝ) else 0) ∂P := by
              rw [integral_add (integrable_const η) (hbad_ind_int.const_mul C)]
        _ = η + C * P.real bad := by
              rw [integral_const, integral_const_mul, hbad_integral]
              simp [C]

/-- Compact-codomain nonlinear transfer for bootstrap weak convergence.

If `Zstar'` is conditionally close to `Zstar` in bootstrap probability and the
codomain is compact, then every bounded continuous test-function integral for
`Zstar'` differs from the corresponding integral for `Zstar` by `oₚ(1)`.
Thus any weak bootstrap limit for `Zstar` transfers to `Zstar'`. -/
theorem TendstoInBootstrapWeakDistribution.of_bootstrap_dist_tendsto_zero_compact
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] [CompactSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistribution μ Pstar Zstar' ν Z := by
  refine hZ.of_integral_difference_zero ?_
  intro f
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε / 2) hε2
  let C : ℝ := 2 * ‖f‖
  have hCclose :
      TendstoInMeasure μ
        (fun n ω =>
          C * (Pstar n ω).real
            {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real C (hclose δ hδ_pos)
  rw [tendstoInMeasure_iff_dist] at hCclose
  have htail := hCclose (ε / 2) hε2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  let pbad : ℝ :=
    (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)}
  have hpbad_nonneg : 0 ≤ pbad := measureReal_nonneg
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hdist_integral :
      |bootstrapBoundedContinuousIntegral Pstar Zstar' f n ω -
          bootstrapBoundedContinuousIntegral Pstar Zstar f n ω| ≤
        ε / 2 + C * pbad := by
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    dsimp [bootstrapBoundedContinuousIntegral, pbad, C]
    refine abs_integral_boundedContinuous_comp_sub_le_of_dist_event
      (P := Pstar n ω) (Z := Zstar n ω) (Z' := Zstar' n ω)
      (hZstar n ω) (hZstar' n ω) f (le_of_lt hε2) ?_
    intro ωs hxy
    have hxy' := hδ hxy
    exact le_of_lt (by simpa [Real.dist_eq] using hxy')
  have habs_ge :
      ε ≤ |bootstrapBoundedContinuousIntegral Pstar Zstar' f n ω -
          bootstrapBoundedContinuousIntegral Pstar Zstar f n ω| := by
    simpa [Real.dist_eq] using hω
  have hpbad_ge : ε / 2 ≤ C * pbad := by
    linarith
  have hCprod_nonneg : 0 ≤ C * pbad := mul_nonneg hC_nonneg hpbad_nonneg
  rw [Real.dist_eq]
  simpa [abs_of_nonneg hCprod_nonneg, C, pbad] using hpbad_ge

/-- Noncompact nonlinear transfer for bootstrap weak convergence from
bootstrap-probability closeness and asymptotic compact-tail control.

This is the global finite-dimensional linearization bridge used when the
statistics do not live in a fixed compact range.  The caller supplies a compact
set whose conditional tails are `oₚ(1)` for both the linearized and nonlinear
statistics; on that compact set, bounded continuous test functions are uniformly
continuous. -/
theorem TendstoInBootstrapWeakDistribution.of_bootstrap_dist_tendsto_zero_tight
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] [T2Space E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set E, IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Zstar n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Zstar' n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistribution μ Pstar Zstar' ν Z := by
  refine hZ.of_integral_difference_zero ?_
  intro f
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨K, hK, hTailZ, hTailZ'⟩ := hTail (ε / 4) hε4
  have hf_uc : UniformContinuousOn (fun x => f x) K :=
    hK.uniformContinuousOn_of_continuous f.continuous.continuousOn
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    Metric.uniformContinuousOn_iff.mp hf_uc (ε / 4) hε4
  let C : ℝ := 2 * ‖f‖
  let closeProb : ℕ → Ω → ℝ := fun n ω =>
    (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)}
  let tailProb : ℕ → Ω → ℝ := fun n ω =>
    (Pstar n ω).real {ωs | Zstar n ω ωs ∉ K}
  let tailProb' : ℕ → Ω → ℝ := fun n ω =>
    (Pstar n ω).real {ωs | Zstar' n ω ωs ∉ K}
  have hcloseC :
      TendstoInMeasure μ (fun n ω => C * closeProb n ω) atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real C (hclose δ hδ_pos)
  have htailC :
      TendstoInMeasure μ (fun n ω => C * tailProb n ω) atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real C hTailZ
  have htailC' :
      TendstoInMeasure μ (fun n ω => C * tailProb' n ω) atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real C hTailZ'
  have hsumC :
      TendstoInMeasure μ
        (fun n ω => C * closeProb n ω + C * tailProb n ω + C * tailProb' n ω)
        atTop (fun _ => 0) :=
    TendstoInMeasure.add_zero_real
      (TendstoInMeasure.add_zero_real hcloseC htailC) htailC'
  rw [tendstoInMeasure_iff_dist] at hsumC
  have htail := hsumC (ε / 4) hε4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  let A : Set Ωs := {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)}
  let B : Set Ωs := {ωs | Zstar n ω ωs ∉ K}
  let D : Set Ωs := {ωs | Zstar' n ω ωs ∉ K}
  let pclose : ℝ := closeProb n ω
  let ptail : ℝ := tailProb n ω
  let ptail' : ℝ := tailProb' n ω
  have hpclose_nonneg : 0 ≤ pclose := measureReal_nonneg
  have hptail_nonneg : 0 ≤ ptail := measureReal_nonneg
  have hptail'_nonneg : 0 ≤ ptail' := measureReal_nonneg
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
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
    have hAB :
        (Pstar n ω).real (A ∪ B) ≤ pclose + ptail := by
      have hμ :
          (Pstar n ω) (A ∪ B) ≤ (Pstar n ω) A + (Pstar n ω) B :=
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
    have hrewrite : A ∪ B ∪ D = (A ∪ B) ∪ D := by
      rfl
    rw [hrewrite]
    linarith
  have hdist_integral :
      |bootstrapBoundedContinuousIntegral Pstar Zstar' f n ω -
          bootstrapBoundedContinuousIntegral Pstar Zstar f n ω| ≤
        ε / 4 + C * (pclose + ptail + ptail') := by
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    dsimp [bootstrapBoundedContinuousIntegral, pclose, ptail, ptail',
      closeProb, tailProb, tailProb', A, B, D]
    have hbound :=
      abs_integral_boundedContinuous_comp_sub_le_of_dist_event_compact_tails
        (P := Pstar n ω) (Z := Zstar n ω) (Z' := Zstar' n ω)
        (hZstar n ω) (hZstar' n ω) f hK (le_of_lt hε4)
        (fun x hx y hy hxy =>
          le_of_lt (by simpa [Real.dist_eq] using hδ y hy x hx hxy))
    have hbound' :
        |∫ ωs, f (Zstar' n ω ωs) ∂Pstar n ω -
            ∫ ωs, f (Zstar n ω ωs) ∂Pstar n ω| ≤
          ε / 4 + (2 * ‖f‖) * (Pstar n ω).real (A ∪ B ∪ D) := by
      simpa [A, B, D] using hbound
    have hmul_bad :
        (2 * ‖f‖) * (Pstar n ω).real (A ∪ B ∪ D) ≤
          (2 * ‖f‖) * (pclose + ptail + ptail') :=
      mul_le_mul_of_nonneg_left hbad_real_le (by positivity)
    exact hbound'.trans (by
      dsimp [C]
      linarith)
  have habs_ge :
      ε ≤ |bootstrapBoundedContinuousIntegral Pstar Zstar' f n ω -
          bootstrapBoundedContinuousIntegral Pstar Zstar f n ω| := by
    simpa [Real.dist_eq] using hω
  have hCsum_ge :
      ε / 4 ≤ C * pclose + C * ptail + C * ptail' := by
    have hCsum_eq :
        C * (pclose + ptail + ptail') = C * pclose + C * ptail + C * ptail' := by
      ring
    linarith
  have hCsum_nonneg : 0 ≤ C * pclose + C * ptail + C * ptail' := by
    positivity
  rw [Real.dist_eq]
  simpa [abs_of_nonneg hCsum_nonneg, pclose, ptail, ptail', closeProb,
    tailProb, tailProb'] using hCsum_ge

/-- Compact-range nonlinear transfer for bootstrap weak convergence.

This version only requires both bootstrap statistics to take values in a fixed
compact set. It is the useful form for bounded or trimmed finite-dimensional
statistics, where the ambient codomain need not itself be compact. -/
theorem TendstoInBootstrapWeakDistribution.of_bootstrap_dist_tendsto_zero_compact_range
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E} {K : Set E}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZstar_mem : ∀ n ω ωs, Zstar n ω ωs ∈ K)
    (hZstar'_mem : ∀ n ω ωs, Zstar' n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistribution μ Pstar Zstar' ν Z := by
  refine hZ.of_integral_difference_zero ?_
  intro f
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hf_uc : UniformContinuousOn (fun x => f x) K :=
    hK.uniformContinuousOn_of_continuous f.continuous.continuousOn
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    Metric.uniformContinuousOn_iff.mp hf_uc (ε / 2) hε2
  let C : ℝ := 2 * ‖f‖
  have hCclose :
      TendstoInMeasure μ
        (fun n ω =>
          C * (Pstar n ω).real
            {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real C (hclose δ hδ_pos)
  rw [tendstoInMeasure_iff_dist] at hCclose
  have htail := hCclose (ε / 2) hε2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  let pbad : ℝ :=
    (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)}
  have hpbad_nonneg : 0 ≤ pbad := measureReal_nonneg
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hdist_integral :
      |bootstrapBoundedContinuousIntegral Pstar Zstar' f n ω -
          bootstrapBoundedContinuousIntegral Pstar Zstar f n ω| ≤
        ε / 2 + C * pbad := by
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    dsimp [bootstrapBoundedContinuousIntegral, pbad, C]
    refine abs_integral_boundedContinuous_comp_sub_le_of_dist_event
      (P := Pstar n ω) (Z := Zstar n ω) (Z' := Zstar' n ω)
      (hZstar n ω) (hZstar' n ω) f (le_of_lt hε2) ?_
    intro ωs hxy
    have hxy' :=
      hδ (Zstar' n ω ωs) (hZstar'_mem n ω ωs)
        (Zstar n ω ωs) (hZstar_mem n ω ωs) hxy
    exact le_of_lt (by simpa [Real.dist_eq] using hxy')
  have habs_ge :
      ε ≤ |bootstrapBoundedContinuousIntegral Pstar Zstar' f n ω -
          bootstrapBoundedContinuousIntegral Pstar Zstar f n ω| := by
    simpa [Real.dist_eq] using hω
  have hpbad_ge : ε / 2 ≤ C * pbad := by
    linarith
  have hCprod_nonneg : 0 ≤ C * pbad := mul_nonneg hC_nonneg hpbad_nonneg
  rw [Real.dist_eq]
  simpa [abs_of_nonneg hCprod_nonneg, C, pbad] using hpbad_ge

namespace TendstoInBootstrapWeakDistribution

/-- A pointwise distance envelope with vanishing conditional bootstrap tails
implies conditional bootstrap-probability closeness. -/
theorem bootstrap_dist_tendsto_zero_of_dist_bound
    [PseudoMetricSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → E}
    {R : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (Zstar' n ω ωs) (Zstar n ω ωs) ≤ R n ω ωs) :
    ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0) := by
  intro δ hδ
  refine tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω =>
      (Pstar n ω).real
        {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
    (g := fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
    ?_ ?_ (hR_tail δ hδ)
  · intro n ω
    exact ENNReal.toReal_nonneg
  · intro n ω
    refine ENNReal.toReal_mono ?_ (measure_mono ?_)
    · letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      exact measure_ne_top (Pstar n ω) {ωs | δ ≤ R n ω ωs}
    · intro ωs hωs
      exact hωs.trans (hR_bound n ω ωs)

/-- Compact-range nonlinear transfer from a pointwise distance bound.

This is the remainder-bound form used by smooth bootstrap Delta-method
arguments: if a remainder envelope has vanishing conditional bootstrap tails,
then the compact-range closeness premise follows. -/
theorem of_bootstrap_dist_tendsto_zero_compact_range_of_dist_bound
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E} {K : Set E} {R : ℕ → Ω → Ωs → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZstar_mem : ∀ n ω ωs, Zstar n ω ωs ∈ K)
    (hZstar'_mem : ∀ n ω ωs, Zstar' n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (Zstar' n ω ωs) (Zstar n ω ωs) ≤ R n ω ωs) :
    TendstoInBootstrapWeakDistribution μ Pstar Zstar' ν Z :=
  hZ.of_bootstrap_dist_tendsto_zero_compact_range
    hK hPstar hZstar hZstar' hZstar_mem hZstar'_mem
    (bootstrap_dist_tendsto_zero_of_dist_bound hPstar hR_tail hR_bound)

end TendstoInBootstrapWeakDistribution

variable {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]

/-- Indexed conditional bootstrap expectation of a bounded continuous test
function, for sample-size-dependent bootstrap spaces. -/
noncomputable def bootstrapBoundedContinuousIntegralIndexed
    [TopologicalSpace E]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → E)
    (f : BoundedContinuousFunction E ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ ωs, f (Zstar n ω ωs) ∂Pstar n ω

/-- Indexed conditional bootstrap probability of a transformed event. -/
noncomputable def bootstrapEventProbabilityIndexed
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → E)
    (A : Set E) (n : ℕ) (ω : Ω) : ℝ :=
  ((Pstar n ω) {ωs | Zstar n ω ωs ∈ A}).toReal

/-- Indexed bootstrap convergence in distribution in
bounded-continuous-test-function form.

This is the sample-size-dependent counterpart of
`TendstoInBootstrapWeakDistribution`, used when the ordinary nonparametric
bootstrap resampling space varies with `n`. -/
def TendstoInBootstrapWeakDistributionIndexed
    [TopologicalSpace E]
    (μ : Measure Ω) (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → E)
    (ν : Measure Ωlim) (Z : Ωlim → E) : Prop :=
  ∀ f : BoundedContinuousFunction E ℝ,
    TendstoInMeasure μ
      (fun n ω => bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
      atTop (fun _ => ∫ ωlim, f (Z ωlim) ∂ν)

/-- Projection from indexed bounded-continuous-test-function bootstrap
convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.tendsto_integral
    [TopologicalSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (f : BoundedContinuousFunction E ℝ) :
    TendstoInMeasure μ
      (fun n ω => bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
      atTop (fun _ => ∫ ωlim, f (Z ωlim) ∂ν) :=
  hZ f

/-- Indexed bootstrap weak convergence from pathwise conditional weak
convergence.

This is the sample-size-dependent counterpart of
`TendstoInBootstrapWeakDistribution.of_ae_tendsto_integrals`, used for ordinary
nonparametric-bootstrap spaces such as `Fin (n+1) -> Fin (n+1)`. -/
theorem TendstoInBootstrapWeakDistributionIndexed.of_ae_tendsto_integrals
    [TopologicalSpace E] [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E}
    (hmeas : ∀ f : BoundedContinuousFunction E ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω => bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω) μ)
    (hae : ∀ f : BoundedContinuousFunction E ℝ,
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n => bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
          atTop (nhds (∫ ωlim, f (Z ωlim) ∂ν))) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z := by
  intro f
  exact tendstoInMeasure_of_tendsto_ae (hmeas f) (hae f)

/-- Indexed bootstrap weak convergence from pathwise conditional weak
convergence in Mathlib's `TendstoInDistribution` form.

This is the sample-size-dependent counterpart of
`TendstoInBootstrapWeakDistribution.of_ae_tendstoInDistribution`, used when the
ordinary nonparametric-bootstrap resampling space varies with `n`. -/
theorem TendstoInBootstrapWeakDistributionIndexed.of_ae_tendstoInDistribution
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E} [IsProbabilityMeasure ν]
    (hmeas : ∀ f : BoundedContinuousFunction E ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω => bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωboot n) => Zstar n ω ωs)
        atTop Z (fun n => Pstar n ω) ν) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z := by
  refine TendstoInBootstrapWeakDistributionIndexed.of_ae_tendsto_integrals
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    hmeas ?_
  intro f
  filter_upwards [hae] with ω hdist
  simpa [bootstrapBoundedContinuousIntegralIndexed] using
    (TendstoInDistribution.integral_boundedContinuous_tendsto_indexed
      (Ω := Ωboot) (μ := fun n => Pstar n ω)
      (X := fun n (ωs : Ωboot n) => Zstar n ω ωs) (Z := Z) hdist f)

/-- Indexed bootstrap weak convergence after an a.e.-continuous mapping, from
pathwise conditional weak convergence in Mathlib's `TendstoInDistribution`
form. -/
theorem TendstoInBootstrapWeakDistributionIndexed.of_ae_tendstoInDistribution_ae_continuous_comp
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E]
    [TopologicalSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [BorelSpace F] [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → E}
    {g : E → F} (hg : Measurable g) {D : Set E}
    (hD : (ν.map Z) D = 0)
    (hcont : ∀ x, x ∉ D → ContinuousAt g x)
    (hmeas : ∀ f : BoundedContinuousFunction F ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          bootstrapBoundedContinuousIntegralIndexed Pstar
            (fun n ω ωs => g (Zstar n ω ωs)) f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωboot n) => Zstar n ω ωs)
        atTop Z (fun n => Pstar n ω) ν) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  refine TendstoInBootstrapWeakDistributionIndexed.of_ae_tendstoInDistribution
    (μ := μ) (Pstar := Pstar)
    (Zstar := fun n ω ωs => g (Zstar n ω ωs))
    (ν := ν) (Z := fun ωlim => g (Z ωlim)) hmeas ?_
  filter_upwards [hae] with ω hdist
  exact
    tendstoInDistribution_ae_continuous_comp_indexed
      (P := fun n => Pstar n ω) (ν := ν)
      (X := fun n (ωs : Ωboot n) => Zstar n ω ωs) (Z := Z)
      (g := g) hdist hg hD hcont

/-- Measurability of indexed finite-uniform bootstrap bounded-continuous
integrals.

This is the sample-size-indexed counterpart of
`bootstrapBoundedContinuousIntegral_uniformOn_univ_aestronglyMeasurable`, used
for ordinary bootstrap spaces such as `Fin (n+1) -> Fin (n+1)`. -/
theorem bootstrapBoundedContinuousIntegralIndexed_uniformOn_univ_aestronglyMeasurable
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [∀ n, Finite (Ωboot n)] [∀ n, MeasurableSingletonClass (Ωboot n)]
    {μ : Measure Ω} {Zstar : ∀ n, Ω → Ωboot n → E}
    (hZ : ∀ n ωs, AEMeasurable (fun ω => Zstar n ω ωs) μ)
    (f : BoundedContinuousFunction E ℝ) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω => bootstrapBoundedContinuousIntegralIndexed
        (Ωboot := Ωboot)
        (fun n _ =>
          (ProbabilityTheory.uniformOn (Set.univ : Set (Ωboot n)) :
            Measure (Ωboot n)))
        Zstar f n ω) μ := by
  classical
  letI : Fintype (Ωboot n) := Fintype.ofFinite (Ωboot n)
  have hsum : AEStronglyMeasurable
      (fun ω => ∑ ωs : Ωboot n, f (Zstar n ω ωs)) μ := by
    refine Finset.aestronglyMeasurable_fun_sum Finset.univ (fun ωs _ => ?_)
    exact (f.continuous.measurable.comp_aemeasurable (hZ n ωs)).aestronglyMeasurable
  refine (hsum.const_smul (((Fintype.card (Ωboot n) : ℝ≥0∞)⁻¹).toReal)).congr ?_
  exact ae_of_all μ fun ω => by
    symm
    simpa [bootstrapBoundedContinuousIntegralIndexed] using
      (integral_uniformOn_univ_eq_card_inv_smul_sum
        (ι := Ωboot n) (E := ℝ) (fun ωs => f (Zstar n ω ωs)))

/-- A.e.-measurability of the normalized ordinary empirical-bootstrap sample
mean along a fixed finite resampling path.

This is the pathwise measurability input needed by the indexed finite-uniform
bounded-continuous integral helper for Hansen Theorem 10.4. -/
theorem normalized_finSucc_resampleMean_sub_empiricalMean_aemeasurable
    {μ : Measure Ω} {Y : ℕ → Ω → k → ℝ} [Fintype k]
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (n : ℕ) (ωs : Fin (n + 1) → Fin (n + 1)) :
    AEMeasurable
      (fun ω a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a)) μ := by
  classical
  refine aemeasurable_pi_lambda _ ?_
  intro a
  have hboot_sum : AEMeasurable
      (fun ω => ∑ t : Fin (n + 1), Y (ωs t).val ω a) μ := by
    exact Finset.aemeasurable_fun_sum Finset.univ
      (fun t _ => hY (ωs t).val a)
  have hboot : AEMeasurable
      (fun ω =>
        empiricalBootstrapResampleMean
          (fun i : Fin (n + 1) => Y i.val ω)
          (fun ωs t => ωs t) ωs a) μ := by
    simpa [empiricalBootstrapResampleMean] using
      hboot_sum.const_smul ((Fintype.card (Fin (n + 1)) : ℝ)⁻¹)
  have hmean_sum : AEMeasurable
      (fun ω => ∑ i : Fin (n + 1), Y i.val ω a) μ := by
    exact Finset.aemeasurable_fun_sum Finset.univ
      (fun i _ => hY i.val a)
  have hmean : AEMeasurable
      (fun ω => empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a) μ := by
    simpa [empiricalMean] using
      hmean_sum.const_smul (((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal)
  exact (hboot.sub hmean).const_mul (Real.sqrt (n + 1 : ℝ))

/-- Measurability in the finite resampling path of the normalized ordinary
empirical-bootstrap sample mean.

This discharges the bootstrap-statistic measurability side condition in
Hansen Theorem 10.4 wrappers for the concrete `Fin (n+1) -> Fin (n+1)`
ordinary-bootstrap statistic. -/
theorem normalized_finSucc_resampleMean_sub_empiricalMean_measurable
    {Y : ℕ → Ω → k → ℝ} [Fintype k]
    (n : ℕ) (ω : Ω) :
    Measurable
      (fun ωs : Fin (n + 1) → Fin (n + 1) => fun a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a)) :=
  measurable_of_finite _

/-- Bounded-continuous conditional integrals of the normalized ordinary
empirical-bootstrap sample mean are a.e.-strongly measurable in the original
sample.

This discharges the measurability side condition in
`TendstoInBootstrapWeakDistributionIndexed.of_ae_tendsto_integrals` for the
ordinary `Fin (n+1) -> Fin (n+1)` bootstrap statistic used in Hansen Theorem
10.4. -/
theorem
    bootstrapBoundedContinuousIntegralIndexed_normalized_finSucc_resampleMean_aestronglyMeasurable
    {μ : Measure Ω} {Y : ℕ → Ω → k → ℝ} [Fintype k]
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (f : BoundedContinuousFunction (k → ℝ) ℝ) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω => bootstrapBoundedContinuousIntegralIndexed
        (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
        f n ω) μ := by
  refine bootstrapBoundedContinuousIntegralIndexed_uniformOn_univ_aestronglyMeasurable
    (Ωboot := fun n => Fin (n + 1) → Fin (n + 1)) ?_ f n
  intro n ωs
  exact normalized_finSucc_resampleMean_sub_empiricalMean_aemeasurable hY n ωs

/-- Indexed bootstrap weak convergence is invariant under pointwise equality of
the bootstrap statistic. -/
theorem TendstoInBootstrapWeakDistributionIndexed.congr_bootstrap
    [TopologicalSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' ν Z := by
  intro f
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl (hZ.tendsto_integral f)
  refine ae_of_all μ fun ω => ?_
  simp [bootstrapBoundedContinuousIntegralIndexed, hstar]

/-- Indexed bootstrap weak convergence is invariant under pointwise equality of
the limiting statistic. -/
theorem TendstoInBootstrapWeakDistributionIndexed.congr_limit
    [TopologicalSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z Z' : Ωlim → E}
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z' := by
  intro f
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ (hZ.tendsto_integral f)
  refine ae_of_all μ fun _ => ?_
  simp [hlim]

/-- Pointwise congruence for indexed bootstrap weak convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.congr
    [TopologicalSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {Z Z' : Ωlim → E}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' ν Z' :=
  (hZ.congr_bootstrap hstar).congr_limit hlim

/-- Indexed bootstrap weak convergence is invariant under replacing the
auxiliary limit space and limit map by another pair with the same law. -/
theorem TendstoInBootstrapWeakDistributionIndexed.congr_limit_law
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Ωlim' : Type*} [MeasurableSpace Ωlim']
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E} {Y : Ωlim' → E}
    {law : Measure E} {νlim : Measure Ωlim'}
    (hZlaw : HasLaw Z law ν)
    (hYlaw : HasLaw Y law νlim)
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar νlim Y := by
  intro f
  have htarget :
      ∫ ωlim, f (Z ωlim) ∂ν = ∫ ωlim, f (Y ωlim) ∂νlim := by
    calc
      ∫ ωlim, f (Z ωlim) ∂ν = ∫ x, f x ∂(ν.map Z) := by
        exact
          (integral_map hZlaw.aemeasurable
            f.continuous.aestronglyMeasurable).symm
      _ = ∫ x, f x ∂law := by rw [hZlaw.map_eq]
      _ = ∫ x, f x ∂(νlim.map Y) := by rw [← hYlaw.map_eq]
      _ = ∫ ωlim, f (Y ωlim) ∂νlim := by
        exact integral_map hYlaw.aemeasurable f.continuous.aestronglyMeasurable
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ (hZ.tendsto_integral f)
  exact ae_of_all μ fun _ => htarget

/-- Transfer indexed bootstrap weak convergence across an `oₚ(1)` difference in
every bounded-continuous test-function integral. -/
theorem TendstoInBootstrapWeakDistributionIndexed.of_integral_difference_zero
    [TopologicalSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hdiff :
      ∀ f : BoundedContinuousFunction E ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
          atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' ν Z := by
  intro f
  have hlin := hZ.tendsto_integral f
  have hlin0 := TendstoInMeasure.sub_limit_zero_real hlin
  have hsum := TendstoInMeasure.add_zero_real (hdiff f) hlin0
  have htarget0 :
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
            ∫ ωlim, f (Z ωlim) ∂ν)
        atTop (fun _ => 0) := by
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hsum
    exact ae_of_all μ fun ω => by ring
  exact TendstoInMeasure.of_sub_limit_zero_real htarget0

/-- Indexed compact-codomain nonlinear transfer for bootstrap weak convergence.

This is the sample-size-dependent counterpart of
`TendstoInBootstrapWeakDistribution.of_bootstrap_dist_tendsto_zero_compact`. -/
theorem TendstoInBootstrapWeakDistributionIndexed.of_bootstrap_dist_tendsto_zero_compact
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] [CompactSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' ν Z := by
  refine hZ.of_integral_difference_zero ?_
  intro f
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε / 2) hε2
  let C : ℝ := 2 * ‖f‖
  have hCclose :
      TendstoInMeasure μ
        (fun n ω =>
          C * (Pstar n ω).real
            {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real C (hclose δ hδ_pos)
  rw [tendstoInMeasure_iff_dist] at hCclose
  have htail := hCclose (ε / 2) hε2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  let pbad : ℝ :=
    (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)}
  have hpbad_nonneg : 0 ≤ pbad := measureReal_nonneg
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hdist_integral :
      |bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
          bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω| ≤
        ε / 2 + C * pbad := by
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    dsimp [bootstrapBoundedContinuousIntegralIndexed, pbad, C]
    refine abs_integral_boundedContinuous_comp_sub_le_of_dist_event
      (P := Pstar n ω) (Z := Zstar n ω) (Z' := Zstar' n ω)
      (hZstar n ω) (hZstar' n ω) f (le_of_lt hε2) ?_
    intro ωs hxy
    have hxy' := hδ hxy
    exact le_of_lt (by simpa [Real.dist_eq] using hxy')
  have habs_ge :
      ε ≤ |bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
          bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω| := by
    simpa [Real.dist_eq] using hω
  have hpbad_ge : ε / 2 ≤ C * pbad := by
    linarith
  have hCprod_nonneg : 0 ≤ C * pbad := mul_nonneg hC_nonneg hpbad_nonneg
  rw [Real.dist_eq]
  simpa [abs_of_nonneg hCprod_nonneg, C, pbad] using hpbad_ge

/-- Indexed noncompact nonlinear transfer for bootstrap weak convergence from
bootstrap-probability closeness and asymptotic compact-tail control.

This is the sample-size-dependent counterpart of
`TendstoInBootstrapWeakDistribution.of_bootstrap_dist_tendsto_zero_tight`. -/
theorem TendstoInBootstrapWeakDistributionIndexed.of_bootstrap_dist_tendsto_zero_tight
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] [T2Space E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set E, IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Zstar n ω ωs ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | Zstar' n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' ν Z := by
  refine hZ.of_integral_difference_zero ?_
  intro f
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨K, hK, hTailZ, hTailZ'⟩ := hTail (ε / 4) hε4
  have hf_uc : UniformContinuousOn (fun x => f x) K :=
    hK.uniformContinuousOn_of_continuous f.continuous.continuousOn
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    Metric.uniformContinuousOn_iff.mp hf_uc (ε / 4) hε4
  let C : ℝ := 2 * ‖f‖
  let closeProb : ℕ → Ω → ℝ := fun n ω =>
    (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)}
  let tailProb : ℕ → Ω → ℝ := fun n ω =>
    (Pstar n ω).real {ωs | Zstar n ω ωs ∉ K}
  let tailProb' : ℕ → Ω → ℝ := fun n ω =>
    (Pstar n ω).real {ωs | Zstar' n ω ωs ∉ K}
  have hcloseC :
      TendstoInMeasure μ (fun n ω => C * closeProb n ω) atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real C (hclose δ hδ_pos)
  have htailC :
      TendstoInMeasure μ (fun n ω => C * tailProb n ω) atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real C hTailZ
  have htailC' :
      TendstoInMeasure μ (fun n ω => C * tailProb' n ω) atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real C hTailZ'
  have hsumC :
      TendstoInMeasure μ
        (fun n ω => C * closeProb n ω + C * tailProb n ω + C * tailProb' n ω)
        atTop (fun _ => 0) :=
    TendstoInMeasure.add_zero_real
      (TendstoInMeasure.add_zero_real hcloseC htailC) htailC'
  rw [tendstoInMeasure_iff_dist] at hsumC
  have htail := hsumC (ε / 4) hε4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  let A : Set (Ωboot n) := {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)}
  let B : Set (Ωboot n) := {ωs | Zstar n ω ωs ∉ K}
  let D : Set (Ωboot n) := {ωs | Zstar' n ω ωs ∉ K}
  let pclose : ℝ := closeProb n ω
  let ptail : ℝ := tailProb n ω
  let ptail' : ℝ := tailProb' n ω
  have hpclose_nonneg : 0 ≤ pclose := measureReal_nonneg
  have hptail_nonneg : 0 ≤ ptail := measureReal_nonneg
  have hptail'_nonneg : 0 ≤ ptail' := measureReal_nonneg
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
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
    have hAB :
        (Pstar n ω).real (A ∪ B) ≤ pclose + ptail := by
      have hμ :
          (Pstar n ω) (A ∪ B) ≤ (Pstar n ω) A + (Pstar n ω) B :=
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
    have hrewrite : A ∪ B ∪ D = (A ∪ B) ∪ D := by
      rfl
    rw [hrewrite]
    linarith
  have hdist_integral :
      |bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
          bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω| ≤
        ε / 4 + C * (pclose + ptail + ptail') := by
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    dsimp [bootstrapBoundedContinuousIntegralIndexed, pclose, ptail, ptail',
      closeProb, tailProb, tailProb', A, B, D]
    have hbound :=
      abs_integral_boundedContinuous_comp_sub_le_of_dist_event_compact_tails
        (P := Pstar n ω) (Z := Zstar n ω) (Z' := Zstar' n ω)
        (hZstar n ω) (hZstar' n ω) f hK (le_of_lt hε4)
        (fun x hx y hy hxy =>
          le_of_lt (by simpa [Real.dist_eq] using hδ y hy x hx hxy))
    have hbound' :
        |∫ ωs, f (Zstar' n ω ωs) ∂Pstar n ω -
            ∫ ωs, f (Zstar n ω ωs) ∂Pstar n ω| ≤
          ε / 4 + (2 * ‖f‖) * (Pstar n ω).real (A ∪ B ∪ D) := by
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
  have hCsum_ge :
      ε / 4 ≤ C * pclose + C * ptail + C * ptail' := by
    have hCsum_eq :
        C * (pclose + ptail + ptail') = C * pclose + C * ptail + C * ptail' := by
      ring
    linarith
  have hCsum_nonneg : 0 ≤ C * pclose + C * ptail + C * ptail' := by
    nlinarith [hC_nonneg, hpclose_nonneg, hptail_nonneg, hptail'_nonneg]
  rw [Real.dist_eq]
  simpa [abs_of_nonneg hCsum_nonneg, pclose, ptail, ptail',
    closeProb, tailProb, tailProb'] using hCsum_ge

/-- Indexed compact-range nonlinear transfer for bootstrap weak convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.of_bootstrap_dist_tendsto_zero_compact_range
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E} {K : Set E}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZstar_mem : ∀ n ω ωs, Zstar n ω ωs ∈ K)
    (hZstar'_mem : ∀ n ω ωs, Zstar' n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' ν Z := by
  refine hZ.of_integral_difference_zero ?_
  intro f
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hf_uc : UniformContinuousOn (fun x => f x) K :=
    hK.uniformContinuousOn_of_continuous f.continuous.continuousOn
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    Metric.uniformContinuousOn_iff.mp hf_uc (ε / 2) hε2
  let C : ℝ := 2 * ‖f‖
  have hCclose :
      TendstoInMeasure μ
        (fun n ω =>
          C * (Pstar n ω).real
            {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real C (hclose δ hδ_pos)
  rw [tendstoInMeasure_iff_dist] at hCclose
  have htail := hCclose (ε / 2) hε2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  let pbad : ℝ :=
    (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)}
  have hpbad_nonneg : 0 ≤ pbad := measureReal_nonneg
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hdist_integral :
      |bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
          bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω| ≤
        ε / 2 + C * pbad := by
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    dsimp [bootstrapBoundedContinuousIntegralIndexed, pbad, C]
    refine abs_integral_boundedContinuous_comp_sub_le_of_dist_event
      (P := Pstar n ω) (Z := Zstar n ω) (Z' := Zstar' n ω)
      (hZstar n ω) (hZstar' n ω) f (le_of_lt hε2) ?_
    intro ωs hxy
    have hxy' :=
      hδ (Zstar' n ω ωs) (hZstar'_mem n ω ωs)
        (Zstar n ω ωs) (hZstar_mem n ω ωs) hxy
    exact le_of_lt (by simpa [Real.dist_eq] using hxy')
  have habs_ge :
      ε ≤ |bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
          bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω| := by
    simpa [Real.dist_eq] using hω
  have hpbad_ge : ε / 2 ≤ C * pbad := by
    linarith
  have hCprod_nonneg : 0 ≤ C * pbad := mul_nonneg hC_nonneg hpbad_nonneg
  rw [Real.dist_eq]
  simpa [abs_of_nonneg hCprod_nonneg, C, pbad] using hpbad_ge

namespace TendstoInBootstrapWeakDistributionIndexed

/-- Indexed pointwise distance envelopes imply conditional bootstrap-probability
closeness. -/
theorem bootstrap_dist_tendsto_zero_of_dist_bound
    [PseudoMetricSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (Zstar' n ω ωs) (Zstar n ω ωs) ≤ R n ω ωs) :
    ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0) := by
  intro δ hδ
  refine tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω =>
      (Pstar n ω).real
        {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
    (g := fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
    ?_ ?_ (hR_tail δ hδ)
  · intro n ω
    exact ENNReal.toReal_nonneg
  · intro n ω
    refine ENNReal.toReal_mono ?_ (measure_mono ?_)
    · letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      exact measure_ne_top (Pstar n ω) {ωs | δ ≤ R n ω ωs}
    · intro ωs hωs
      exact hωs.trans (hR_bound n ω ωs)

/-- Indexed compact-range nonlinear transfer from a pointwise distance bound.

This is the sample-size-dependent counterpart of
`TendstoInBootstrapWeakDistribution.of_bootstrap_dist_tendsto_zero_compact_range_of_dist_bound`. -/
theorem of_bootstrap_dist_tendsto_zero_compact_range_of_dist_bound
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E} {K : Set E} {R : ∀ n, Ω → Ωboot n → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZstar_mem : ∀ n ω ωs, Zstar n ω ωs ∈ K)
    (hZstar'_mem : ∀ n ω ωs, Zstar' n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (Zstar' n ω ωs) (Zstar n ω ωs) ≤ R n ω ωs) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' ν Z :=
  hZ.of_bootstrap_dist_tendsto_zero_compact_range
    hK hPstar hZstar hZstar' hZstar_mem hZstar'_mem
    (bootstrap_dist_tendsto_zero_of_dist_bound hPstar hR_tail hR_bound)

end TendstoInBootstrapWeakDistributionIndexed

private theorem tendstoInMeasure_of_squeeze_approx_real
    {X : ℕ → Ω → ℝ} {c : ℝ}
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ L U : ℕ → Ω → ℝ, ∃ l u : ℝ,
          l ≤ c ∧ c ≤ u ∧ u - l ≤ ε ∧
            (∀ n ω, L n ω ≤ X n ω) ∧
            (∀ n ω, X n ω ≤ U n ω) ∧
            TendstoInMeasure μ L atTop (fun _ => l) ∧
            TendstoInMeasure μ U atTop (fun _ => u)) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨L, U, l, u, hlc, hcu, hgap, hLX, hXU, hL, hU⟩ :=
    happrox (ε / 3) hε3
  rw [tendstoInMeasure_iff_dist] at hL hU
  have hLtail := hL (ε / 3) hε3
  have hUtail := hU (ε / 3) hε3
  have hsum :
      Tendsto
        (fun n =>
          μ {ω | ε / 3 ≤ dist (L n ω) l} +
            μ {ω | ε / 3 ≤ dist (U n ω) u})
        atTop (𝓝 0) := by
    simpa using hLtail.add hUtail
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le _) ?_
  intro n
  calc
    μ {ω | ε ≤ dist (X n ω) c}
        ≤ μ ({ω | ε / 3 ≤ dist (L n ω) l} ∪
            {ω | ε / 3 ≤ dist (U n ω) u}) := by
          refine measure_mono ?_
          intro ω hω
          simp only [Set.mem_union, Set.mem_setOf_eq]
          by_cases hLbig : ε / 3 ≤ dist (L n ω) l
          · exact Or.inl hLbig
          · right
            by_contra hUnot
            have hLsmall : dist (L n ω) l < ε / 3 := not_le.mp hLbig
            have hUsmall : dist (U n ω) u < ε / 3 := not_le.mp hUnot
            have hLabs : |L n ω - l| < ε / 3 := by
              simpa [Real.dist_eq] using hLsmall
            have hUabs : |U n ω - u| < ε / 3 := by
              simpa [Real.dist_eq] using hUsmall
            have hLgt : l - ε / 3 < L n ω := by
              linarith [(abs_lt.mp hLabs).1]
            have hUlt : U n ω < u + ε / 3 := by
              linarith [(abs_lt.mp hUabs).2]
            have hx_lower : c - ε < X n ω := by
              have hcl : c - l ≤ ε / 3 := by linarith
              linarith [hLgt, hLX n ω]
            have hx_upper : X n ω < c + ε := by
              have huc : u - c ≤ ε / 3 := by linarith
              linarith [hUlt, hXU n ω]
            have hdist_lt : dist (X n ω) c < ε := by
              rw [Real.dist_eq]
              exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
            exact (not_le_of_gt hdist_lt) hω
    _ ≤ μ {ω | ε / 3 ≤ dist (L n ω) l} +
        μ {ω | ε / 3 ≤ dist (U n ω) u} :=
          measure_union_le _ _

/-- Bootstrap weak convergence gives event-probability convergence whenever
the event indicator can be squeezed by bounded continuous test functions.

This is the reusable Portmanteau-style bridge for Hansen Theorem 10.5's
event-probability face.  The topological/null-frontier argument that constructs
the lower and upper bounded continuous functions is kept as an explicit premise,
so the theorem works for any event class where that approximation is available. -/
theorem TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_boundedContinuous_sandwich
    [TopologicalSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E} {A : Set E} {c : ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ lower upper : BoundedContinuousFunction E ℝ,
        (∫ ωlim, lower (Z ωlim) ∂ν) ≤ c ∧
          c ≤ (∫ ωlim, upper (Z ωlim) ∂ν) ∧
          (∫ ωlim, upper (Z ωlim) ∂ν) -
              (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
          (∀ n ω,
            bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤
              bootstrapEventProbability Pstar Zstar A n ω) ∧
          (∀ n ω,
            bootstrapEventProbability Pstar Zstar A n ω ≤
              bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω)) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar Zstar A)
      atTop (fun _ => c) := by
  refine tendstoInMeasure_of_squeeze_approx_real (μ := μ) ?_
  intro ε hε
  obtain ⟨lower, upper, hlc, hcu, hgap, hlower, hupper⟩ := happrox ε hε
  refine ⟨bootstrapBoundedContinuousIntegral Pstar Zstar lower,
    bootstrapBoundedContinuousIntegral Pstar Zstar upper,
    ∫ ωlim, lower (Z ωlim) ∂ν,
    ∫ ωlim, upper (Z ωlim) ∂ν, hlc, hcu, hgap, hlower, hupper, ?_, ?_⟩
  · exact hZ.tendsto_integral lower
  · exact hZ.tendsto_integral upper

/-- Indexed bootstrap weak convergence gives event-probability convergence
whenever the event indicator can be squeezed by bounded continuous test
functions. -/
theorem TendstoInBootstrapWeakDistributionIndexed.event_probability_tendsto_of_sandwich
    [TopologicalSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E} {A : Set E} {c : ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ lower upper : BoundedContinuousFunction E ℝ,
        (∫ ωlim, lower (Z ωlim) ∂ν) ≤ c ∧
          c ≤ (∫ ωlim, upper (Z ωlim) ∂ν) ∧
          (∫ ωlim, upper (Z ωlim) ∂ν) -
              (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
          (∀ n ω,
            bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤
              bootstrapEventProbabilityIndexed Pstar Zstar A n ω) ∧
          (∀ n ω,
            bootstrapEventProbabilityIndexed Pstar Zstar A n ω ≤
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω)) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar Zstar A)
      atTop (fun _ => c) := by
  refine tendstoInMeasure_of_squeeze_approx_real (μ := μ) ?_
  intro ε hε
  obtain ⟨lower, upper, hlc, hcu, hgap, hlower, hupper⟩ := happrox ε hε
  refine ⟨bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower,
    bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper,
    ∫ ωlim, lower (Z ωlim) ∂ν,
    ∫ ωlim, upper (Z ωlim) ∂ν, hlc, hcu, hgap, hlower, hupper, ?_, ?_⟩
  · exact hZ.tendsto_integral lower
  · exact hZ.tendsto_integral upper

/-- Bootstrap weak convergence transfers any real conditional functional that
can be squeezed by bounded continuous test-function integrals.

This is the general bounded-continuous sandwich step behind the
Portmanteau/event-probability bridge and the a.e.-continuous mapping route:
once the target conditional functional lies between lower and upper bounded
continuous test integrals whose limit-law integrals have arbitrarily small
gap, convergence in probability follows. -/
theorem TendstoInBootstrapWeakDistribution.integral_tendsto_of_boundedContinuous_sandwich
    [TopologicalSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E} {X : ℕ → Ω → ℝ} {c : ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ lower upper : BoundedContinuousFunction E ℝ,
        (∫ ωlim, lower (Z ωlim) ∂ν) ≤ c ∧
          c ≤ (∫ ωlim, upper (Z ωlim) ∂ν) ∧
          (∫ ωlim, upper (Z ωlim) ∂ν) -
              (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
          (∀ n ω,
            bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤ X n ω) ∧
          (∀ n ω,
            X n ω ≤
              bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω)) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  refine tendstoInMeasure_of_squeeze_approx_real (μ := μ) ?_
  intro ε hε
  obtain ⟨lower, upper, hlc, hcu, hgap, hlower, hupper⟩ := happrox ε hε
  refine ⟨bootstrapBoundedContinuousIntegral Pstar Zstar lower,
    bootstrapBoundedContinuousIntegral Pstar Zstar upper,
    ∫ ωlim, lower (Z ωlim) ∂ν,
    ∫ ωlim, upper (Z ωlim) ∂ν, hlc, hcu, hgap, hlower, hupper, ?_, ?_⟩
  · exact hZ.tendsto_integral lower
  · exact hZ.tendsto_integral upper

/-- Indexed bootstrap weak convergence transfers real conditional functionals
that are squeezed by bounded continuous test-function integrals. -/
theorem TendstoInBootstrapWeakDistributionIndexed.integral_tendsto_of_sandwich
    [TopologicalSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E} {X : ℕ → Ω → ℝ} {c : ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ lower upper : BoundedContinuousFunction E ℝ,
        (∫ ωlim, lower (Z ωlim) ∂ν) ≤ c ∧
          c ≤ (∫ ωlim, upper (Z ωlim) ∂ν) ∧
          (∫ ωlim, upper (Z ωlim) ∂ν) -
              (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
          (∀ n ω,
            bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤ X n ω) ∧
          (∀ n ω,
            X n ω ≤
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω)) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  refine tendstoInMeasure_of_squeeze_approx_real (μ := μ) ?_
  intro ε hε
  obtain ⟨lower, upper, hlc, hcu, hgap, hlower, hupper⟩ := happrox ε hε
  refine ⟨bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower,
    bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper,
    ∫ ωlim, lower (Z ωlim) ∂ν,
    ∫ ωlim, upper (Z ωlim) ∂ν, hlc, hcu, hgap, hlower, hupper, ?_, ?_⟩
  · exact hZ.tendsto_integral lower
  · exact hZ.tendsto_integral upper

/-- Bootstrap weak convergence mapped through a possibly discontinuous
transformation, assuming bounded-continuous sandwich approximations for every
bounded continuous test function after transformation.

This is the reusable approximation-facing form of Hansen Theorem 10.5.  The
separate topological step for an a.e.-continuous `g` is to construct the
sandwich premise for each transformed test function. -/
theorem TendstoInBootstrapWeakDistribution.map_of_boundedContinuous_sandwich
    [TopologicalSpace E] [TopologicalSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E} {g : E → F}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction F ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  intro f
  exact hZ.integral_tendsto_of_boundedContinuous_sandwich
    (X := fun n ω =>
      bootstrapBoundedContinuousIntegral Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) f n ω)
    (c := ∫ ωlim, f (g (Z ωlim)) ∂ν)
    (happrox f)

/-- Indexed version of
`TendstoInBootstrapWeakDistribution.map_of_boundedContinuous_sandwich`. -/
theorem TendstoInBootstrapWeakDistributionIndexed.map_of_boundedContinuous_sandwich
    [TopologicalSpace E] [TopologicalSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E} {g : E → F}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction F ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  intro f
  exact hZ.integral_tendsto_of_sandwich
    (X := fun n ω =>
      bootstrapBoundedContinuousIntegralIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) f n ω)
    (c := ∫ ωlim, f (g (Z ωlim)) ∂ν)
    (happrox f)

private noncomputable def nnrealBoundedContinuousFunctionToReal
    [TopologicalSpace E] (f : BoundedContinuousFunction E NNReal) :
    BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.comp ((↑) : NNReal → ℝ)
    NNReal.isometry_coe.lipschitz f

private theorem nnrealBoundedContinuousFunctionToReal_apply
    [TopologicalSpace E] (f : BoundedContinuousFunction E NNReal) (x : E) :
    nnrealBoundedContinuousFunctionToReal f x = (f x : ℝ) :=
  rfl

/-- Bounded-continuous lower/upper sandwiches for events with null frontier.

For a probability law on a pseudo-emetric space, if the event boundary carries
zero mass, then for every tolerance there are bounded continuous functions
below and above the event indicator whose integrals differ by at most that
tolerance.  This is the topological approximation input needed by the
bootstrap event-probability Portmanteau bridge. -/
theorem boundedContinuous_event_sandwich_of_null_frontier
    [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {law : Measure E} [IsProbabilityMeasure law] {A : Set E}
    {ε : ℝ} (hε : 0 < ε) (hfrontier : law (frontier A) = 0) :
    ∃ lower upper : BoundedContinuousFunction E ℝ,
      (∀ x, x ∈ A → lower x ≤ 1) ∧
        (∀ x, x ∉ A → lower x ≤ 0) ∧
        (∀ x, x ∈ A → 1 ≤ upper x) ∧
        (∀ x, 0 ≤ upper x) ∧
        (∫ x, lower x ∂law) ≤ law.real A ∧
        law.real A ≤ (∫ x, upper x ∂law) ∧
        (∫ x, upper x ∂law) - (∫ x, lower x ∂law) ≤ ε := by
  classical
  let δs : ℕ → ℝ := fun n => (1 : ℝ) / (n + 1)
  have hδs_pos : ∀ n, 0 < δs n := fun n => by positivity
  have hδs_lim : Tendsto δs atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let upperSeq : ℕ → BoundedContinuousFunction E ℝ := fun n =>
    nnrealBoundedContinuousFunctionToReal (thickenedIndicator (hδs_pos n) (closure A))
  let complSeq : ℕ → BoundedContinuousFunction E ℝ := fun n =>
    nnrealBoundedContinuousFunctionToReal (thickenedIndicator (hδs_pos n) (interior A)ᶜ)
  have hupper_tendsto :
      Tendsto (fun n => ∫ x, upperSeq n x ∂law)
        atTop (𝓝 (law.real (closure A))) := by
    change Tendsto
      (fun n => ∫ x, (thickenedIndicator (hδs_pos n) (closure A) x : ℝ) ∂law)
        atTop (𝓝 (law.real (closure A)))
    exact tendsto_integral_thickenedIndicator_of_isClosed law isClosed_closure
      (δs_pos := hδs_pos) hδs_lim
  have hcompl_tendsto :
      Tendsto (fun n => ∫ x, complSeq n x ∂law)
        atTop (𝓝 (law.real ((interior A)ᶜ))) := by
    change Tendsto
      (fun n => ∫ x, (thickenedIndicator (hδs_pos n) (interior A)ᶜ x : ℝ) ∂law)
        atTop (𝓝 (law.real ((interior A)ᶜ)))
    exact tendsto_integral_thickenedIndicator_of_isClosed law
      isOpen_interior.isClosed_compl
      (δs_pos := hδs_pos) hδs_lim
  have hε4 : 0 < ε / 4 := by positivity
  have hupper_room : law.real (closure A) < law.real (closure A) + ε / 4 := by
    linarith
  have hcompl_room : law.real ((interior A)ᶜ) < law.real ((interior A)ᶜ) + ε / 4 := by
    linarith
  obtain ⟨Nu, hNu⟩ :=
    eventually_atTop.mp (hupper_tendsto.eventually_lt_const hupper_room)
  obtain ⟨Nl, hNl⟩ :=
    eventually_atTop.mp (hcompl_tendsto.eventually_lt_const hcompl_room)
  let upper : BoundedContinuousFunction E ℝ := upperSeq Nu
  let lower : BoundedContinuousFunction E ℝ :=
    BoundedContinuousFunction.const E (1 : ℝ) - complSeq Nl
  have hupper_lt :
      ∫ x, upper x ∂law < law.real (closure A) + ε / 4 := by
    exact hNu Nu le_rfl
  have hcompl_lt :
      ∫ x, complSeq Nl x ∂law < law.real ((interior A)ᶜ) + ε / 4 := by
    exact hNl Nl le_rfl
  have hclosure_real : law.real (closure A) = law.real A := by
    simp [Measure.real_def, measure_closure_of_null_frontier hfrontier]
  have hinterior_real : law.real (interior A) = law.real A := by
    simp [Measure.real_def, measure_interior_of_null_frontier hfrontier]
  have hclosure_interior : law.real (closure A) = law.real (interior A) := by
    rw [hclosure_real, hinterior_real]
  have hcompl_real : law.real ((interior A)ᶜ) = 1 - law.real (interior A) := by
    rw [measureReal_compl isOpen_interior.measurableSet]
    simp
  have hlower_eq :
      ∫ x, lower x ∂law = 1 - ∫ x, complSeq Nl x ∂law := by
    calc
      ∫ x, lower x ∂law =
          law.real Set.univ • (1 : ℝ) - ∫ x, complSeq Nl x ∂law := by
            simpa [lower] using
              (BoundedContinuousFunction.integral_const_sub
                (μ := law) (complSeq Nl) (1 : ℝ))
      _ = 1 - ∫ x, complSeq Nl x ∂law := by simp
  have hlower_gt :
      law.real (interior A) - ε / 4 < ∫ x, lower x ∂law := by
    rw [hlower_eq]
    rw [hcompl_real] at hcompl_lt
    linarith
  refine ⟨lower, upper, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hnonneg : 0 ≤ complSeq Nl x := by
      simp [complSeq, nnrealBoundedContinuousFunctionToReal_apply]
    change 1 - complSeq Nl x ≤ (1 : ℝ)
    linarith
  · intro x hx
    have hxcomp : x ∈ (interior A)ᶜ := by
      exact fun hxi => hx (interior_subset hxi)
    have hone :
        thickenedIndicator (hδs_pos Nl) (interior A)ᶜ x = (1 : NNReal) :=
      thickenedIndicator_one_of_mem_closure (hδs_pos Nl) (interior A)ᶜ
        (subset_closure hxcomp)
    have hcompl_one : complSeq Nl x = (1 : ℝ) := by
      simp [complSeq, nnrealBoundedContinuousFunctionToReal_apply, hone]
    change 1 - complSeq Nl x ≤ (0 : ℝ)
    linarith
  · intro x hx
    have hxcl : x ∈ closure A := subset_closure hx
    have hone :
        thickenedIndicator (hδs_pos Nu) (closure A) x = (1 : NNReal) :=
      thickenedIndicator_one_of_mem_closure (hδs_pos Nu) (closure A)
        (by simpa [closure_closure] using hxcl)
    have hupper_one : upper x = (1 : ℝ) := by
      simp [upper, upperSeq, nnrealBoundedContinuousFunctionToReal_apply, hone]
    linarith
  · intro x
    simp [upper, upperSeq, nnrealBoundedContinuousFunctionToReal_apply]
  · have hlower_le_interior_indicator :
        (fun x => lower x) ≤ fun x => if x ∈ interior A then (1 : ℝ) else 0 := by
      intro x
      by_cases hx : x ∈ interior A
      · have hnonneg : 0 ≤ complSeq Nl x := by
          simp [complSeq, nnrealBoundedContinuousFunctionToReal_apply]
        simp [lower, hx, hnonneg]
      · have hxcomp : x ∈ (interior A)ᶜ := by
          exact hx
        have hone :
            thickenedIndicator (hδs_pos Nl) (interior A)ᶜ x = (1 : NNReal) :=
          thickenedIndicator_one_of_mem_closure (hδs_pos Nl) (interior A)ᶜ
            (subset_closure hxcomp)
        simp [lower, complSeq, nnrealBoundedContinuousFunctionToReal_apply, hx, hone]
    calc
      ∫ x, lower x ∂law
          ≤ ∫ x, (if x ∈ interior A then (1 : ℝ) else 0) ∂law := by
            refine integral_mono (lower.integrable law)
              ((integrable_indicator_iff isOpen_interior.measurableSet).mpr
                (integrable_const (1 : ℝ)).integrableOn) ?_
            exact hlower_le_interior_indicator
      _ = law.real (interior A) := by
            rw [← integral_indicator_one isOpen_interior.measurableSet]
            rfl
      _ = law.real A := hinterior_real
  · have hclosure_indicator_le_upper :
        (fun x => if x ∈ closure A then (1 : ℝ) else 0) ≤ fun x => upper x := by
      intro x
      by_cases hx : x ∈ closure A
      · have hone :
            thickenedIndicator (hδs_pos Nu) (closure A) x = (1 : NNReal) :=
          thickenedIndicator_one_of_mem_closure (hδs_pos Nu) (closure A)
            (by simpa [closure_closure] using hx)
        simp [upper, upperSeq, nnrealBoundedContinuousFunctionToReal_apply, hx, hone]
      · have hnonneg : 0 ≤ upper x := by
          simp [upper, upperSeq, nnrealBoundedContinuousFunctionToReal_apply]
        simp [hx, hnonneg]
    calc
      law.real A = law.real (closure A) := hclosure_real.symm
      _ = ∫ x, (if x ∈ closure A then (1 : ℝ) else 0) ∂law := by
            rw [← integral_indicator_one isClosed_closure.measurableSet]
            rfl
      _ ≤ ∫ x, upper x ∂law := by
            refine integral_mono
              ((integrable_indicator_iff isClosed_closure.measurableSet).mpr
                (integrable_const (1 : ℝ)).integrableOn)
              (upper.integrable law) ?_
            exact hclosure_indicator_le_upper
  · have hgap_lt :
        (∫ x, upper x ∂law) - (∫ x, lower x ∂law) < ε := by
      have hupper_lt' : ∫ x, upper x ∂law <
          law.real (interior A) + ε / 4 := by
        simpa [hclosure_interior] using hupper_lt
      linarith
    exact le_of_lt hgap_lt

private theorem integrable_boundedContinuous_comp_measurable
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {P : Measure Ωs} [IsFiniteMeasure P] {Z : Ωs → E}
    (hZ : Measurable Z) (f : BoundedContinuousFunction E ℝ) :
    Integrable (fun ωs => f (Z ωs)) P := by
  refine Integrable.of_bound
    ((f.continuous.measurable.comp hZ).aestronglyMeasurable) ‖f‖ ?_
  exact ae_of_all P fun ωs => f.norm_coe_le_norm (Z ωs)

/-- Pointwise bounded-continuous event sandwiches integrate to probability
sandwiches after composing with a measurable statistic.

This is the measure-theoretic bridge from an event-indicator approximation
`lower <= 1_A <= upper` to the integral inequalities used by the bootstrap
Portmanteau wrapper. -/
theorem boundedContinuous_event_integral_sandwich
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {P : Measure Ωs} [IsFiniteMeasure P] {Z : Ωs → E} {A : Set E}
    (hZ : Measurable Z) (hA : MeasurableSet A)
    {lower upper : BoundedContinuousFunction E ℝ}
    (hl_mem : ∀ x, x ∈ A → lower x ≤ 1)
    (hl_notMem : ∀ x, x ∉ A → lower x ≤ 0)
    (hu_mem : ∀ x, x ∈ A → 1 ≤ upper x)
    (hu_nonneg : ∀ x, 0 ≤ upper x) :
    (∫ ωs, lower (Z ωs) ∂P) ≤ P.real {ωs | Z ωs ∈ A} ∧
      P.real {ωs | Z ωs ∈ A} ≤ (∫ ωs, upper (Z ωs) ∂P) := by
  classical
  let S : Set Ωs := {ωs | Z ωs ∈ A}
  have hS : MeasurableSet S := hA.preimage hZ
  have hlower_int : Integrable (fun ωs => lower (Z ωs)) P :=
    integrable_boundedContinuous_comp_measurable (P := P) hZ lower
  have hupper_int : Integrable (fun ωs => upper (Z ωs)) P :=
    integrable_boundedContinuous_comp_measurable (P := P) hZ upper
  have hindicator_int : Integrable (fun ωs => if ωs ∈ S then (1 : ℝ) else 0) P := by
    simpa [S] using
      ((integrable_indicator_iff hS).mpr
        (integrable_const (1 : ℝ)).integrableOn)
  constructor
  · have hlower_le_indicator :
        (fun ωs => lower (Z ωs)) ≤
          fun ωs => if ωs ∈ S then (1 : ℝ) else 0 := by
      intro ωs
      by_cases hωs : Z ωs ∈ A
      · simpa [S, hωs] using hl_mem (Z ωs) hωs
      · simpa [S, hωs] using hl_notMem (Z ωs) hωs
    calc
      ∫ ωs, lower (Z ωs) ∂P
          ≤ ∫ ωs, (if ωs ∈ S then (1 : ℝ) else 0) ∂P :=
            integral_mono hlower_int hindicator_int hlower_le_indicator
      _ = P.real S := by
            rw [← integral_indicator_one hS]
            rfl
      _ = P.real {ωs | Z ωs ∈ A} := rfl
  · have hindicator_le_upper :
        (fun ωs => if ωs ∈ S then (1 : ℝ) else 0) ≤
          fun ωs => upper (Z ωs) := by
      intro ωs
      by_cases hωs : Z ωs ∈ A
      · simpa [S, hωs] using hu_mem (Z ωs) hωs
      · simpa [S, hωs] using hu_nonneg (Z ωs)
    calc
      P.real {ωs | Z ωs ∈ A} = P.real S := rfl
      _ = ∫ ωs, (if ωs ∈ S then (1 : ℝ) else 0) ∂P := by
            rw [← integral_indicator_one hS]
            rfl
      _ ≤ ∫ ωs, upper (Z ωs) ∂P :=
            integral_mono hindicator_int hupper_int hindicator_le_upper

/-- Conditional-bootstrap event probability sandwich from pointwise
bounded-continuous lower and upper functions.

This packages `boundedContinuous_event_integral_sandwich` in the `n, ω`
conditional-bootstrap notation required by
`TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_boundedContinuous_sandwich`. -/
theorem bootstrapEventProbability_sandwich_of_boundedContinuous_event_sandwich
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → E} {A : Set E}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hA : MeasurableSet A)
    {lower upper : BoundedContinuousFunction E ℝ}
    (hl_mem : ∀ x, x ∈ A → lower x ≤ 1)
    (hl_notMem : ∀ x, x ∉ A → lower x ≤ 0)
    (hu_mem : ∀ x, x ∈ A → 1 ≤ upper x)
    (hu_nonneg : ∀ x, 0 ≤ upper x) :
    (∀ n ω,
      bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤
        bootstrapEventProbability Pstar Zstar A n ω) ∧
      (∀ n ω,
        bootstrapEventProbability Pstar Zstar A n ω ≤
          bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω) := by
  constructor
  · intro n ω
    letI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    simpa [bootstrapBoundedContinuousIntegral, bootstrapEventProbability,
      Measure.real_def] using
      (boundedContinuous_event_integral_sandwich
        (P := Pstar n ω) (Z := Zstar n ω) (A := A)
        (hZstar n ω) hA hl_mem hl_notMem hu_mem hu_nonneg).1
  · intro n ω
    letI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    simpa [bootstrapBoundedContinuousIntegral, bootstrapEventProbability,
      Measure.real_def] using
        (boundedContinuous_event_integral_sandwich
          (P := Pstar n ω) (Z := Zstar n ω) (A := A)
          (hZstar n ω) hA hl_mem hl_notMem hu_mem hu_nonneg).2

/-- Indexed conditional-bootstrap event probability sandwich from pointwise
bounded-continuous lower and upper functions. -/
theorem bootstrapEventProbabilityIndexed_sandwich_of_boundedContinuous_event_sandwich
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E} {A : Set E}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hA : MeasurableSet A)
    {lower upper : BoundedContinuousFunction E ℝ}
    (hl_mem : ∀ x, x ∈ A → lower x ≤ 1)
    (hl_notMem : ∀ x, x ∉ A → lower x ≤ 0)
    (hu_mem : ∀ x, x ∈ A → 1 ≤ upper x)
    (hu_nonneg : ∀ x, 0 ≤ upper x) :
    (∀ n ω,
      bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤
        bootstrapEventProbabilityIndexed Pstar Zstar A n ω) ∧
      (∀ n ω,
        bootstrapEventProbabilityIndexed Pstar Zstar A n ω ≤
          bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω) := by
  constructor
  · intro n ω
    letI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    simpa [bootstrapBoundedContinuousIntegralIndexed,
      bootstrapEventProbabilityIndexed, Measure.real_def] using
      (boundedContinuous_event_integral_sandwich
        (P := Pstar n ω) (Z := Zstar n ω) (A := A)
        (hZstar n ω) hA hl_mem hl_notMem hu_mem hu_nonneg).1
  · intro n ω
    letI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    simpa [bootstrapBoundedContinuousIntegralIndexed,
      bootstrapEventProbabilityIndexed, Measure.real_def] using
      (boundedContinuous_event_integral_sandwich
        (P := Pstar n ω) (Z := Zstar n ω) (A := A)
        (hZstar n ω) hA hl_mem hl_notMem hu_mem hu_nonneg).2

/-- Bootstrap weak convergence gives event-probability convergence for events
whose limit-law frontier has zero mass.

This combines the bounded-continuous-test-function bootstrap convergence
definition, the null-frontier event-sandwich constructor, and the conditional
bootstrap integral sandwich. -/
theorem TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_null_frontier
    [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → E} {A : Set E}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZ : AEMeasurable Z ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map Z) (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar Zstar A)
      atTop (fun _ => (ν.map Z).real A) := by
  letI : IsProbabilityMeasure (ν.map Z) := Measure.isProbabilityMeasure_map hZ
  refine hweak.event_probability_tendsto_of_boundedContinuous_sandwich ?_
  intro ε hε
  obtain ⟨lower, upper, hl_mem, hl_notMem, hu_mem, hu_nonneg,
      hlower_law, hupper_law, hgap_law⟩ :=
    boundedContinuous_event_sandwich_of_null_frontier
      (law := ν.map Z) (A := A) hε hfrontier
  have hlower_map :
      ∫ x, lower x ∂(ν.map Z) = ∫ ωlim, lower (Z ωlim) ∂ν :=
    integral_map hZ lower.continuous.measurable.aestronglyMeasurable
  have hupper_map :
      ∫ x, upper x ∂(ν.map Z) = ∫ ωlim, upper (Z ωlim) ∂ν :=
    integral_map hZ upper.continuous.measurable.aestronglyMeasurable
  obtain ⟨hlower_boot, hupper_boot⟩ :=
    bootstrapEventProbability_sandwich_of_boundedContinuous_event_sandwich
      (Pstar := Pstar) (Zstar := Zstar) (A := A)
      hPstar hZstar hA hl_mem hl_notMem hu_mem hu_nonneg
  refine ⟨lower, upper, ?_, ?_, ?_, hlower_boot, hupper_boot⟩
  · simpa [hlower_map] using hlower_law
  · simpa [hupper_map] using hupper_law
  · simpa [hlower_map, hupper_map] using hgap_law

/-- Indexed bootstrap weak convergence gives event-probability convergence for
events whose limit-law frontier has zero mass. -/
theorem TendstoInBootstrapWeakDistributionIndexed.event_probability_tendsto_of_null_frontier
    [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → E} {A : Set E}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZ : AEMeasurable Z ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map Z) (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar Zstar A)
      atTop (fun _ => (ν.map Z).real A) := by
  letI : IsProbabilityMeasure (ν.map Z) := Measure.isProbabilityMeasure_map hZ
  refine hweak.event_probability_tendsto_of_sandwich ?_
  intro ε hε
  obtain ⟨lower, upper, hl_mem, hl_notMem, hu_mem, hu_nonneg,
      hlower_law, hupper_law, hgap_law⟩ :=
    boundedContinuous_event_sandwich_of_null_frontier
      (law := ν.map Z) (A := A) hε hfrontier
  have hlower_map :
      ∫ x, lower x ∂(ν.map Z) = ∫ ωlim, lower (Z ωlim) ∂ν :=
    integral_map hZ lower.continuous.measurable.aestronglyMeasurable
  have hupper_map :
      ∫ x, upper x ∂(ν.map Z) = ∫ ωlim, upper (Z ωlim) ∂ν :=
    integral_map hZ upper.continuous.measurable.aestronglyMeasurable
  obtain ⟨hlower_boot, hupper_boot⟩ :=
    bootstrapEventProbabilityIndexed_sandwich_of_boundedContinuous_event_sandwich
      (Pstar := Pstar) (Zstar := Zstar) (A := A)
      hPstar hZstar hA hl_mem hl_notMem hu_mem hu_nonneg
  refine ⟨lower, upper, ?_, ?_, ?_, hlower_boot, hupper_boot⟩
  · simpa [hlower_map] using hlower_law
  · simpa [hupper_map] using hupper_law
  · simpa [hlower_map, hupper_map] using hgap_law

/-- Bootstrap weak convergence plus a bounded-continuous integral
linearization gives event-probability convergence for null-frontier events.

This is the event-probability face of the nonlinear Delta-method transfer:
one first proves a weak limit for the linearized statistic, then checks that
the nonlinear statistic has the same conditional bounded-continuous integrals
up to `oₚ(1)`. -/
theorem TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_integral_diff
    [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar Zstar' : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → E} {A : Set E}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hdiff :
      ∀ f : BoundedContinuousFunction E ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegral Pstar Zstar' f n ω -
              bootstrapBoundedContinuousIntegral Pstar Zstar f n ω)
          atTop (fun _ => 0))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZ : AEMeasurable Z ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map Z) (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar Zstar' A)
      atTop (fun _ => (ν.map Z).real A) := by
  exact (hweak.of_integral_difference_zero hdiff).event_probability_tendsto_of_null_frontier
    hPstar hZstar' hZ hA hfrontier

/-- Indexed bootstrap weak convergence plus a bounded-continuous integral
linearization gives event-probability convergence for null-frontier events. -/
theorem TendstoInBootstrapWeakDistributionIndexed.event_probability_tendsto_of_integral_diff
    [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → E} {A : Set E}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hdiff :
      ∀ f : BoundedContinuousFunction E ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
          atTop (fun _ => 0))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZ : AEMeasurable Z ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map Z) (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar Zstar' A)
      atTop (fun _ => (ν.map Z).real A) := by
  exact (hweak.of_integral_difference_zero hdiff).event_probability_tendsto_of_null_frontier
    hPstar hZstar' hZ hA hfrontier

/-- Compact-range bootstrap-probability closeness gives event-probability
convergence for null-frontier events. -/
theorem TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_compact_range_closeness
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar Zstar' : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → E} {A K : Set E}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZstar_mem : ∀ n ω ωs, Zstar n ω ωs ∈ K)
    (hZstar'_mem : ∀ n ω ωs, Zstar' n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0))
    (hZ : AEMeasurable Z ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map Z) (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar Zstar' A)
      atTop (fun _ => (ν.map Z).real A) := by
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    (hweak.of_bootstrap_dist_tendsto_zero_compact_range hK hPstar hZstar hZstar'
      hZstar_mem hZstar'_mem hclose).event_probability_tendsto_of_null_frontier
      hPfinite hZstar' hZ hA hfrontier

/-- Indexed compact-range bootstrap-probability closeness gives
event-probability convergence for null-frontier events. -/
theorem
    TendstoInBootstrapWeakDistributionIndexed.event_probability_tendsto_of_compact_range_closeness
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → E} {A K : Set E}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZstar_mem : ∀ n ω ωs, Zstar n ω ωs ∈ K)
    (hZstar'_mem : ∀ n ω ωs, Zstar' n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0))
    (hZ : AEMeasurable Z ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map Z) (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar Zstar' A)
      atTop (fun _ => (ν.map Z).real A) := by
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    (hweak.of_bootstrap_dist_tendsto_zero_compact_range hK hPstar hZstar hZstar'
      hZstar_mem hZstar'_mem hclose).event_probability_tendsto_of_null_frontier
      hPfinite hZstar' hZ hA hfrontier

/-- Coordinate lower orthants are closed in product space. -/
theorem isClosed_coordinateLE (x : k → ℝ) :
    IsClosed {z : k → ℝ | coordinateLE z x} := by
  rw [show {z : k → ℝ | coordinateLE z x} =
      ⋂ i : k, {z : k → ℝ | z i ≤ x i} by
    ext z
    simp [coordinateLE]]
  exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const

/-- Coordinate lower orthants are measurable. -/
theorem measurableSet_coordinateLE
    [MeasurableSpace (k → ℝ)] [OpensMeasurableSpace (k → ℝ)] (x : k → ℝ) :
    MeasurableSet {z : k → ℝ | coordinateLE z x} :=
  (isClosed_coordinateLE x).measurableSet

/-- The frontier of a finite-dimensional coordinate lower orthant is contained
in the finite union of its coordinate hyperplanes. -/
theorem frontier_coordinateLE_subset_iUnion_coord_eq [Finite k] (x : k → ℝ) :
    frontier {z : k → ℝ | coordinateLE z x} ⊆
      ⋃ i : k, {z : k → ℝ | z i = x i} := by
  intro z hz
  have hz_lower : z ∈ {z : k → ℝ | coordinateLE z x} :=
    (isClosed_coordinateLE x).frontier_subset hz
  by_contra hnot
  have hstrict : ∀ i : k, z i < x i := by
    intro i
    have hne : z i ≠ x i := by
      intro hi
      exact hnot (Set.mem_iUnion.mpr ⟨i, by simp [hi]⟩)
    exact lt_of_le_of_ne (hz_lower i) hne
  have hopen :
      IsOpen {z : k → ℝ | ∀ i : k, z i < x i} := by
    rw [show {z : k → ℝ | ∀ i : k, z i < x i} =
        ⋂ i : k, {z : k → ℝ | z i < x i} by
      ext y
      simp]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (continuous_apply i) continuous_const
  have hsubset :
      {z : k → ℝ | ∀ i : k, z i < x i} ⊆
        {z : k → ℝ | coordinateLE z x} := by
    intro y hy i
    exact (hy i).le
  have hz_interior : z ∈ interior {z : k → ℝ | coordinateLE z x} :=
    interior_maximal hsubset hopen hstrict
  exact ((mem_frontier_iff_notMem_interior hz_lower).mp hz) hz_interior

/-- A coordinate lower-orthant frontier is null when every coordinate
hyperplane at the cutoff is null. -/
theorem measure_frontier_coordinateLE_eq_zero_of_coord_singletons [Finite k]
    {law : Measure (k → ℝ)} (x : k → ℝ)
    (hcoord : ∀ i : k, law {z : k → ℝ | z i = x i} = 0) :
    law (frontier {z : k → ℝ | coordinateLE z x}) = 0 := by
  refine measure_mono_null (frontier_coordinateLE_subset_iUnion_coord_eq x) ?_
  exact measure_iUnion_null hcoord

/-- Mapped lower-orthant frontiers are null when each transformed coordinate
has zero mass at the cutoff. -/
theorem map_measure_frontier_coordinateLE_eq_zero_of_coord_singletons [Finite k]
    {ν : Measure Ωlim} {Z : Ωlim → k → ℝ} (hZ : AEMeasurable Z ν)
    (x : k → ℝ) (hcoord : ∀ i : k, ν {ωlim | Z ωlim i = x i} = 0) :
    (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0 := by
  refine measure_frontier_coordinateLE_eq_zero_of_coord_singletons x ?_
  intro i
  have hhyperplane :
      MeasurableSet {z : k → ℝ | z i = x i} :=
    (isClosed_eq (continuous_apply i) continuous_const).measurableSet
  rw [Measure.map_apply_of_aemeasurable hZ hhyperplane]
  simpa using hcoord i

/-- Positive definite multivariate Gaussian laws assign zero mass to coordinate
lower-orthant frontiers.

This discharges the null-frontier premise in the Gaussian finite-dimensional
faces of Hansen Theorems 10.4, 10.6, and 10.7 when the covariance matrix is
positive definite. -/
theorem multivariateGaussian_coordinateLE_frontier_null_of_posDef
    [Fintype k] [DecidableEq k] {S : Matrix k k ℝ}
    (hS : S.PosDef) (x : k → ℝ) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
      (frontier {z : k → ℝ | coordinateLE z x}) = 0 := by
  have hcoord_aemeas :
      AEMeasurable (fun z : EuclideanSpace ℝ k => (z : k → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S) :=
    (PiLp.continuous_ofLp 2 (fun _ : k => ℝ)).aemeasurable
  refine map_measure_frontier_coordinateLE_eq_zero_of_coord_singletons
    (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) S)
    (Z := fun z : EuclideanSpace ℝ k => (z : k → ℝ))
    hcoord_aemeas x ?_
  intro i
  have hvar_pos : 0 < S i i := hS.diag_pos
  have hvar_ne : (S i i).toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hvar_pos)
  haveI : NoAtoms (gaussianReal 0 (S i i).toNNReal) :=
    noAtoms_gaussianReal hvar_ne
  have hLaw :
      HasLaw (fun z : EuclideanSpace ℝ k => z.ofLp i)
        (gaussianReal 0 (S i i).toNNReal)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S) := by
    simpa using
      (multivariateGaussian_eval_hasLaw
        (μ := (0 : EuclideanSpace ℝ k)) (S := S) hS.posSemidef (i := i))
  have hpre :=
    HasLaw.preimage_eq (μ := multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      hLaw (measurableSet_singleton (x i))
  calc
    (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
        {z : EuclideanSpace ℝ k | (z : k → ℝ) i = x i}
        =
          (gaussianReal 0 (S i i).toNNReal) {x i} := by
            simpa using hpre
    _ = 0 := measure_singleton (x i)

/-- Weak bootstrap convergence gives conditional-CDF convergence at a
lower-orthant null-frontier point.

This is the bridge from the bounded-continuous-test-function API back to
Hansen Definition 10.2's coordinate-CDF surface. -/
theorem TendstoInBootstrapWeakDistribution.bootstrapVectorCDF_tendsto_of_null_frontier
    [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZ : AEMeasurable Z ν) {x : k → ℝ}
    (hfrontier : (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInMeasure μ (fun n ω => bootstrapVectorCDF Pstar Zstar x n ω)
      atTop (fun _ => vectorCDF ν Z x) := by
  letI : Fintype k := Fintype.ofFinite k
  let A : Set (k → ℝ) := {z | coordinateLE z x}
  have hA : MeasurableSet A := measurableSet_coordinateLE x
  have hevent :
      TendstoInMeasure μ (bootstrapEventProbability Pstar Zstar A)
        atTop (fun _ => (ν.map Z).real A) :=
    hweak.event_probability_tendsto_of_null_frontier hPstar hZstar hZ hA hfrontier
  simpa [bootstrapVectorCDF, bootstrapEventProbability, vectorCDF, A, Measure.real_def,
    Measure.map_apply_of_aemeasurable hZ hA] using hevent

/-- Indexed weak bootstrap convergence gives conditional-CDF convergence at a
lower-orthant null-frontier point. -/
theorem TendstoInBootstrapWeakDistributionIndexed.bootstrapVectorCDF_tendsto_of_null_frontier
    [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZ : AEMeasurable Z ν) {x : k → ℝ}
    (hfrontier : (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInMeasure μ (fun n ω => bootstrapVectorCDFIndexed Pstar Zstar x n ω)
      atTop (fun _ => vectorCDF ν Z x) := by
  letI : Fintype k := Fintype.ofFinite k
  let A : Set (k → ℝ) := {z | coordinateLE z x}
  have hA : MeasurableSet A := measurableSet_coordinateLE x
  have hevent :
      TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar Zstar A)
        atTop (fun _ => (ν.map Z).real A) :=
    hweak.event_probability_tendsto_of_null_frontier hPstar hZstar hZ hA hfrontier
  simpa [bootstrapVectorCDFIndexed, bootstrapEventProbabilityIndexed, vectorCDF, A,
    Measure.real_def, Measure.map_apply_of_aemeasurable hZ hA] using hevent

/-- Bootstrap weak convergence plus a bounded-continuous integral
linearization gives Hansen coordinate-CDF convergence at lower-orthant
null-frontier points. -/
theorem TendstoInBootstrapWeakDistribution.bootstrapVectorCDF_tendsto_of_integral_diff
    [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hdiff :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegral Pstar Zstar' f n ω -
              bootstrapBoundedContinuousIntegral Pstar Zstar f n ω)
          atTop (fun _ => 0))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZ : AEMeasurable Z ν) {x : k → ℝ}
    (hfrontier : (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInMeasure μ (fun n ω => bootstrapVectorCDF Pstar Zstar' x n ω)
      atTop (fun _ => vectorCDF ν Z x) := by
  exact (hweak.of_integral_difference_zero hdiff).bootstrapVectorCDF_tendsto_of_null_frontier
    hPstar hZstar' hZ hfrontier

/-- Indexed bootstrap weak convergence plus a bounded-continuous integral
linearization gives Hansen coordinate-CDF convergence at lower-orthant
null-frontier points. -/
theorem TendstoInBootstrapWeakDistributionIndexed.bootstrapVectorCDF_tendsto_of_integral_diff
    [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hdiff :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
          atTop (fun _ => 0))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZ : AEMeasurable Z ν) {x : k → ℝ}
    (hfrontier : (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInMeasure μ (fun n ω => bootstrapVectorCDFIndexed Pstar Zstar' x n ω)
      atTop (fun _ => vectorCDF ν Z x) := by
  exact (hweak.of_integral_difference_zero hdiff).bootstrapVectorCDF_tendsto_of_null_frontier
    hPstar hZstar' hZ hfrontier

/-- Compact-range bootstrap-probability closeness gives Hansen coordinate-CDF
convergence at lower-orthant null-frontier points. -/
theorem
    TendstoInBootstrapWeakDistribution.bootstrapVectorCDF_tendsto_of_compact_range_closeness
    [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    {K : Set (k → ℝ)}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZstar_mem : ∀ n ω ωs, Zstar n ω ωs ∈ K)
    (hZstar'_mem : ∀ n ω ωs, Zstar' n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0))
    (hZ : AEMeasurable Z ν) {x : k → ℝ}
    (hfrontier : (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInMeasure μ (fun n ω => bootstrapVectorCDF Pstar Zstar' x n ω)
      atTop (fun _ => vectorCDF ν Z x) := by
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    (hweak.of_bootstrap_dist_tendsto_zero_compact_range hK hPstar hZstar hZstar'
      hZstar_mem hZstar'_mem hclose).bootstrapVectorCDF_tendsto_of_null_frontier
      hPfinite hZstar' hZ hfrontier

/-- Indexed compact-range bootstrap-probability closeness gives Hansen
coordinate-CDF convergence at lower-orthant null-frontier points. -/
theorem
    TendstoInBootstrapWeakDistributionIndexed.bootstrapVectorCDF_tendsto_of_compact_range_closeness
    [Fintype k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    {K : Set (k → ℝ)}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZstar_mem : ∀ n ω ωs, Zstar n ω ωs ∈ K)
    (hZstar'_mem : ∀ n ω ωs, Zstar' n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0))
    (hZ : AEMeasurable Z ν) {x : k → ℝ}
    (hfrontier : (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInMeasure μ (fun n ω => bootstrapVectorCDFIndexed Pstar Zstar' x n ω)
      atTop (fun _ => vectorCDF ν Z x) := by
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    (hweak.of_bootstrap_dist_tendsto_zero_compact_range hK hPstar hZstar hZstar'
      hZstar_mem hZstar'_mem hclose).bootstrapVectorCDF_tendsto_of_null_frontier
      hPfinite hZstar' hZ hfrontier

/-- Weak bootstrap convergence implies Hansen's coordinate-CDF bootstrap
distribution convergence when every relevant lower orthant has null frontier
under the limiting law.

The null-frontier premise is stated only at continuity points of the limiting
CDF, matching Hansen Definition 10.2. -/
theorem TendstoInBootstrapDistribution.of_weakDistribution_null_frontiers
    [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZ : AEMeasurable Z ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y => vectorCDF ν Z y) x →
        (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar Zstar ν Z := by
  letI : Fintype k := Fintype.ofFinite k
  intro x hx
  exact hweak.bootstrapVectorCDF_tendsto_of_null_frontier
    hPstar hZstar hZ (hfrontier x hx)

/-- Indexed weak bootstrap convergence implies indexed Hansen coordinate-CDF
bootstrap distribution convergence when every relevant lower orthant has null
frontier under the limiting law. -/
theorem TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers
    [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZ : AEMeasurable Z ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y => vectorCDF ν Z y) x →
        (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar ν Z := by
  letI : Fintype k := Fintype.ofFinite k
  intro x hx
  exact hweak.bootstrapVectorCDF_tendsto_of_null_frontier
    hPstar hZstar hZ (hfrontier x hx)

/-- Compact-range bootstrap-probability closeness transfers a weak bootstrap
limit into Hansen Definition 10.2's coordinate-CDF API. -/
theorem TendstoInBootstrapDistribution.of_weakDistribution_compact_range_closeness
    [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    {K : Set (k → ℝ)}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZstar_mem : ∀ n ω ωs, Zstar n ω ωs ∈ K)
    (hZstar'_mem : ∀ n ω ωs, Zstar' n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0))
    (hZ : AEMeasurable Z ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y => vectorCDF ν Z y) x →
        (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar Zstar' ν Z := by
  intro x hx
  exact hweak.bootstrapVectorCDF_tendsto_of_compact_range_closeness
    hK hPstar hZstar hZstar' hZstar_mem hZstar'_mem hclose hZ (hfrontier x hx)

/-- Indexed compact-range bootstrap-probability closeness transfers a weak
bootstrap limit into Hansen Definition 10.2's coordinate-CDF API. -/
theorem TendstoInBootstrapDistributionIndexed.of_weakDistribution_compact_range_closeness
    [Fintype k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    {K : Set (k → ℝ)}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZstar_mem : ∀ n ω ωs, Zstar n ω ωs ∈ K)
    (hZstar'_mem : ∀ n ω ωs, Zstar' n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real {ωs | δ ≤ dist (Zstar' n ω ωs) (Zstar n ω ωs)})
        atTop (fun _ => 0))
    (hZ : AEMeasurable Z ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y => vectorCDF ν Z y) x →
        (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar' ν Z := by
  intro x hx
  exact hweak.bootstrapVectorCDF_tendsto_of_compact_range_closeness
    hK hPstar hZstar hZstar' hZstar_mem hZstar'_mem hclose hZ (hfrontier x hx)

/-- Hansen Theorem 10.4, Gaussian bootstrap CLT from weak bootstrap
convergence.

If a normalized bootstrap statistic converges weakly, in the
bounded-continuous-test-function bootstrap sense, to `N(0, S)`, then the
coordinate-CDF version of Hansen Definition 10.2 follows at all continuity
points whose lower-orthant frontiers are null under that Gaussian law. -/
theorem chapter10_bootstrap_clt_gaussian_of_weakDistribution
    [Fintype k] [DecidableEq k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {S : Matrix k k ℝ}
    (hweak :
      TendstoInBootstrapWeakDistribution μ Pstar Zstar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  have hZlim :
      AEMeasurable (fun z : EuclideanSpace ℝ k => (z : k → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S) :=
    (PiLp.continuous_ofLp 2 (fun _ : k => ℝ)).aemeasurable
  exact
    TendstoInBootstrapDistribution.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (Z := fun z : EuclideanSpace ℝ k => (z : k → ℝ))
      hweak hPstar hZstar hZlim hfrontier

/-- Hansen Theorem 10.4 Gaussian bootstrap CLT from weak bootstrap convergence
with positive definite covariance.

This is the theorem-facing finite-dimensional route: positive definiteness of
`Σ` makes every Gaussian lower-orthant frontier null, so a bounded-continuous
bootstrap weak limit to `N(0,Σ)` directly yields Hansen Definition 10.2. -/
theorem chapter10_bootstrap_clt_gaussian_of_weakDistribution_posDef
    [Fintype k] [DecidableEq k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hweak :
      TendstoInBootstrapWeakDistribution μ Pstar Zstar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω)) :
    TendstoInBootstrapDistribution μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_bootstrap_clt_gaussian_of_weakDistribution
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (S := S)
    hweak hPstar hZstar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Hansen Theorem 10.4 Gaussian bootstrap CLT from pathwise conditional
bounded-continuous integral convergence.

This bridge converts sample-path conditional weak convergence, supplied as
bounded-continuous test-function integral convergence for almost every original
sample path, into Hansen Definition 10.2. -/
theorem chapter10_bootstrap_clt_gaussian_of_ae_tendsto_integrals
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {S : Matrix k k ℝ}
    (hmeas : ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω => bootstrapBoundedContinuousIntegral Pstar Zstar f n ω) μ)
    (hae : ∀ f : BoundedContinuousFunction (k → ℝ) ℝ,
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n => bootstrapBoundedContinuousIntegral Pstar Zstar f n ω)
          atTop
          (nhds (∫ z : EuclideanSpace ℝ k,
            f (z : k → ℝ) ∂(multivariateGaussian (0 : EuclideanSpace ℝ k) S))))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  have hweak :
      TendstoInBootstrapWeakDistribution μ Pstar Zstar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
    TendstoInBootstrapWeakDistribution.of_ae_tendsto_integrals
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (Z := fun z : EuclideanSpace ℝ k => (z : k → ℝ))
      hmeas hae
  exact chapter10_bootstrap_clt_gaussian_of_weakDistribution
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (S := S)
    hweak hPstar hZstar hfrontier

/-- Positive-definite Hansen Theorem 10.4 Gaussian bootstrap CLT from pathwise
conditional bounded-continuous integral convergence. -/
theorem chapter10_bootstrap_clt_gaussian_of_ae_tendsto_integrals_posDef
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hmeas : ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω => bootstrapBoundedContinuousIntegral Pstar Zstar f n ω) μ)
    (hae : ∀ f : BoundedContinuousFunction (k → ℝ) ℝ,
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n => bootstrapBoundedContinuousIntegral Pstar Zstar f n ω)
          atTop
          (nhds (∫ z : EuclideanSpace ℝ k,
            f (z : k → ℝ) ∂(multivariateGaussian (0 : EuclideanSpace ℝ k) S))))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω)) :
    TendstoInBootstrapDistribution μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_bootstrap_clt_gaussian_of_ae_tendsto_integrals
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (S := S)
    hmeas hae hPstar hZstar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Hansen Theorem 10.4 Gaussian bootstrap CLT from pathwise conditional weak
convergence in Mathlib's distributional form.

This theorem-facing wrapper lets a conditional CLT stated as
`TendstoInDistribution` feed directly into Hansen Definition 10.2; the
bounded-continuous integral route is derived internally. -/
theorem chapter10_bootstrap_clt_gaussian_of_ae_tendstoInDistribution
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {S : Matrix k k ℝ}
    (hmeas : ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω => bootstrapBoundedContinuousIntegral Pstar Zstar f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωs) => Zstar n ω ωs)
        atTop
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ))
        (fun n => Pstar n ω)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  have hweak :
      TendstoInBootstrapWeakDistribution μ Pstar Zstar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
    TendstoInBootstrapWeakDistribution.of_ae_tendstoInDistribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (Z := fun z : EuclideanSpace ℝ k => (z : k → ℝ))
      hmeas hae
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := inferInstance
    infer_instance
  exact chapter10_bootstrap_clt_gaussian_of_weakDistribution
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (S := S)
    hweak hPfinite hZstar hfrontier

/-- Positive-definite Hansen Theorem 10.4 Gaussian bootstrap CLT from pathwise
conditional weak convergence in Mathlib's distributional form. -/
theorem chapter10_bootstrap_clt_gaussian_of_ae_tendstoInDistribution_posDef
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hmeas : ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω => bootstrapBoundedContinuousIntegral Pstar Zstar f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωs) => Zstar n ω ωs)
        atTop
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ))
        (fun n => Pstar n ω)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S))
    (hZstar : ∀ n ω, Measurable (Zstar n ω)) :
    TendstoInBootstrapDistribution μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_bootstrap_clt_gaussian_of_ae_tendstoInDistribution
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (S := S)
    hmeas hae hZstar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Indexed-space Hansen Theorem 10.4 Gaussian bootstrap CLT from weak
bootstrap convergence. -/
theorem chapter10_indexed_bootstrap_clt_gaussian_of_weakDistribution
    [Fintype k] [DecidableEq k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {S : Matrix k k ℝ}
    (hweak :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  have hZlim :
      AEMeasurable (fun z : EuclideanSpace ℝ k => (z : k → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S) :=
    (PiLp.continuous_ofLp 2 (fun _ : k => ℝ)).aemeasurable
  exact
    TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (Z := fun z : EuclideanSpace ℝ k => (z : k → ℝ))
      hweak hPstar hZstar hZlim hfrontier

/-- Indexed-space Hansen Theorem 10.4 Gaussian bootstrap CLT from weak bootstrap
convergence with positive definite covariance. -/
theorem chapter10_indexed_bootstrap_clt_gaussian_of_weakDistribution_posDef
    [Fintype k] [DecidableEq k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hweak :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω)) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_of_weakDistribution
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (S := S)
    hweak hPstar hZstar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Indexed-space Hansen Theorem 10.4 Gaussian bootstrap CLT from pathwise
conditional bounded-continuous integral convergence. -/
theorem chapter10_indexed_bootstrap_clt_gaussian_of_ae_tendsto_integrals
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {S : Matrix k k ℝ}
    (hmeas : ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω => bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω) μ)
    (hae : ∀ f : BoundedContinuousFunction (k → ℝ) ℝ,
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n => bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
          atTop
          (nhds (∫ z : EuclideanSpace ℝ k,
            f (z : k → ℝ) ∂(multivariateGaussian (0 : EuclideanSpace ℝ k) S))))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  have hweak :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
    TendstoInBootstrapWeakDistributionIndexed.of_ae_tendsto_integrals
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (Z := fun z : EuclideanSpace ℝ k => (z : k → ℝ))
      hmeas hae
  exact chapter10_indexed_bootstrap_clt_gaussian_of_weakDistribution
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (S := S)
    hweak hPstar hZstar hfrontier

/-- Positive-definite indexed Hansen Theorem 10.4 Gaussian bootstrap CLT from
pathwise conditional bounded-continuous integral convergence. -/
theorem chapter10_indexed_bootstrap_clt_gaussian_of_ae_tendsto_integrals_posDef
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hmeas : ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω => bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω) μ)
    (hae : ∀ f : BoundedContinuousFunction (k → ℝ) ℝ,
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n => bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
          atTop
          (nhds (∫ z : EuclideanSpace ℝ k,
            f (z : k → ℝ) ∂(multivariateGaussian (0 : EuclideanSpace ℝ k) S))))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω)) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_of_ae_tendsto_integrals
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (S := S)
    hmeas hae hPstar hZstar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Indexed-space Hansen Theorem 10.4 Gaussian bootstrap CLT from pathwise
conditional weak convergence in Mathlib's distributional form. -/
theorem chapter10_indexed_bootstrap_clt_gaussian_of_ae_tendstoInDistribution
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {S : Matrix k k ℝ}
    (hmeas : ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω => bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωboot n) => Zstar n ω ωs)
        atTop
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ))
        (fun n => Pstar n ω)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  have hweak :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
    TendstoInBootstrapWeakDistributionIndexed.of_ae_tendstoInDistribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (Z := fun z : EuclideanSpace ℝ k => (z : k → ℝ))
      hmeas hae
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := inferInstance
    infer_instance
  exact chapter10_indexed_bootstrap_clt_gaussian_of_weakDistribution
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (S := S)
    hweak hPfinite hZstar hfrontier

/-- Positive-definite indexed Hansen Theorem 10.4 Gaussian bootstrap CLT from
pathwise conditional weak convergence in Mathlib's distributional form. -/
theorem chapter10_indexed_bootstrap_clt_gaussian_of_ae_tendstoInDistribution_posDef
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hmeas : ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω => bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωboot n) => Zstar n ω ωs)
        atTop
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ))
        (fun n => Pstar n ω)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S))
    (hZstar : ∀ n ω, Measurable (Zstar n ω)) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_of_ae_tendstoInDistribution
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (S := S)
    hmeas hae hZstar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian CLT from a
pathwise conditional weak CLT for the normalized `Fin (n+1)` resample mean.

The finite-uniform bounded-continuous-integral measurability and the
bootstrap-statistic measurability premises are discharged internally; the
remaining mathematical input is the conditional CLT stated in Mathlib's
`TendstoInDistribution` form. -/
theorem chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_tendstoInDistribution
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Fin (n + 1) → Fin (n + 1)) => fun a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
        atTop
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ))
        (fun n =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  letI : ∀ n, Ω → IsProbabilityMeasure
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))) := fun n _ => by
    infer_instance
  exact chapter10_indexed_bootstrap_clt_gaussian_of_ae_tendstoInDistribution
    (μ := μ) (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (Zstar := fun n ω ωs a =>
      Real.sqrt (n + 1 : ℝ) *
        (empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω)
            (fun ωs t => ωs t) ωs a -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
    (S := S)
    (bootstrapBoundedContinuousIntegralIndexed_normalized_finSucc_resampleMean_aestronglyMeasurable
      (μ := μ) (Y := Y) hY)
    hae
    (fun n ω => normalized_finSucc_resampleMean_sub_empiricalMean_measurable (Y := Y) n ω)
    hfrontier

/-- Positive-definite ordinary nonparametric-bootstrap Hansen Theorem 10.4
Gaussian CLT from a pathwise conditional weak CLT for the normalized
`Fin (n+1)` resample mean. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_tendstoInDistribution_posDef
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Fin (n + 1) → Fin (n + 1)) => fun a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
        atTop
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ))
        (fun n =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_tendstoInDistribution
    (μ := μ) (Y := Y) (S := S) hY hae
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian CLT from an
almost-sure indexed Lindeberg/Cramér-Wold condition package for the normalized
`Fin (n+1)` resample mean.

The Chapter 6 indexed Lindeberg endpoint turns the supplied projection CLTs
into pathwise conditional weak convergence; the finite-uniform bootstrap
measurability and Hansen Definition 10.2 conversion are then discharged by the
ordinary-bootstrap pathwise CLT wrapper. -/
theorem chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_lindeberg
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hclt : ∀ᵐ ω ∂μ,
      MultivariateIndexedLindebergCLTConditions
        (fun n => Fin (n + 1) → Fin (n + 1))
        (fun n =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
        S)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  refine chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_tendstoInDistribution
    (μ := μ) (Y := Y) (S := S) hY ?_ hfrontier
  refine hclt.mono ?_
  intro ω hω
  have hEuclid := multivariateIndexedLindebergCLT_tendstoInDistribution hω
  have hMap := TendstoInDistribution.continuous_comp
    (g := (WithLp.ofLp : EuclideanSpace ℝ k → k → ℝ))
    (PiLp.continuous_ofLp 2 (fun _ : k => ℝ)) hEuclid
  simpa [Function.comp_def] using hMap

/-- Positive-definite ordinary nonparametric-bootstrap Hansen Theorem 10.4
Gaussian CLT from an almost-sure indexed Lindeberg/Cramér-Wold package for the
normalized `Fin (n+1)` resample mean. -/
theorem chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_lindeberg_posDef
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hclt : ∀ᵐ ω ∂μ,
      MultivariateIndexedLindebergCLTConditions
        (fun n => Fin (n + 1) → Fin (n + 1))
        (fun n =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
        S) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_lindeberg
    (μ := μ) (Y := Y) (S := S) hY hclt
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian CLT from
almost-sure scalar projection CLTs for the normalized `Fin (n+1)` resample mean.

This is the concrete Cramér-Wold face of the ordinary-bootstrap CLT route:
finite resampling-path measurability is discharged internally, and the supplied
scalar projection CLTs fill the Chapter 6 indexed Lindeberg/Cramér-Wold package. -/
theorem chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_projection_clt
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hproj : ∀ᵐ ω ∂μ, ∀ a : k → ℝ,
      TendstoInDistribution
        (fun n (ωs : Fin (n + 1) → Fin (n + 1)) =>
          (fun b =>
            Real.sqrt (n + 1 : ℝ) *
              (empiricalBootstrapResampleMean
                  (fun i : Fin (n + 1) => Y i.val ω)
                  (fun ωs t => ωs t) ωs b -
                empiricalMean (fun i : Fin (n + 1) => Y i.val ω) b)) ⬝ᵥ a)
        atTop
        (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a)
        (fun n =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (multivariateGaussian 0 S))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  refine chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_lindeberg
    (μ := μ) (Y := Y) (S := S) hY ?_ hfrontier
  refine hproj.mono ?_
  intro ω hω
  exact
    { aemeasurable := fun n =>
        (normalized_finSucc_resampleMean_sub_empiricalMean_measurable
          (Y := Y) n ω).aemeasurable
      projection_clt := hω }

/-- Ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian CLT from
almost-sure scalar bootstrap-mean CLTs for projected observations.

This variant states the Cramér-Wold premise directly in the one-dimensional
bootstrap statistic formed from `Y_i · a`. The vector-projection wrapper above
then supplies the Chapter 6 indexed Lindeberg/Cramér-Wold package. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_scalar_projection_clt
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hproj : ∀ᵐ ω ∂μ, ∀ a : k → ℝ,
      TendstoInDistribution
        (fun n (ωs : Fin (n + 1) → Fin (n + 1)) =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a)))
        atTop
        (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a)
        (fun n =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (multivariateGaussian 0 S))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  refine chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_projection_clt
    (μ := μ) (Y := Y) (S := S) hY ?_ hfrontier
  refine hproj.mono ?_
  intro ω hω a
  refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) (hω a)
  intro n
  exact ae_of_all
    (ProbabilityTheory.uniformOn
      (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
        Measure (Fin (n + 1) → Fin (n + 1))) (fun ωs =>
      (dotProduct_normalized_finSucc_resampleMean_sub_empiricalMean_eq
        (Y := Y) n ω ωs a).symm)

/-- Ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian CLT from
almost-sure characteristic-function convergence for projected bootstrap means.

This is the Lévy-continuity face of the scalar Cramér-Wold route: callers prove
pointwise convergence of the conditional characteristic functions of each
projected scalar bootstrap mean, and the indexed characteristic-function
constructor supplies the corresponding scalar distributional CLTs. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hchar : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ,
      Tendsto
        (fun n =>
          charFun
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1))).map
              (fun ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a))))
            t)
        atTop
        (𝓝 (charFun
          ((multivariateGaussian 0 S).map
            (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a))
          t)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  refine
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_scalar_projection_clt
      (μ := μ) (Y := Y) (S := S) hY ?_ hfrontier
  refine hchar.mono ?_
  intro ω hω a
  refine TendstoInDistribution.of_tendsto_charFun_indexed ?_ ?_ (hω a)
  · intro n
    have hvec : AEMeasurable
        (fun ωs : Fin (n + 1) → Fin (n + 1) => fun b =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs b -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) b))
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) :=
      (normalized_finSucc_resampleMean_sub_empiricalMean_measurable
        (Y := Y) n ω).aemeasurable
    have hdot : AEMeasurable
        (fun ωs : Fin (n + 1) → Fin (n + 1) =>
          (fun b =>
            Real.sqrt (n + 1 : ℝ) *
              (empiricalBootstrapResampleMean
                  (fun i : Fin (n + 1) => Y i.val ω)
                  (fun ωs t => ωs t) ωs b -
                empiricalMean (fun i : Fin (n + 1) => Y i.val ω) b)) ⬝ᵥ a)
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) :=
      ((continuous_id.dotProduct continuous_const).measurable.comp_aemeasurable hvec)
    exact hdot.congr
      (ae_of_all
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) fun ωs =>
        dotProduct_normalized_finSucc_resampleMean_sub_empiricalMean_eq
          (Y := Y) n ω ωs a)
  · exact ((continuous_id.dotProduct continuous_const).measurable.comp_aemeasurable
      ((PiLp.continuous_ofLp 2 (fun _ : k => ℝ)).measurable.aemeasurable))

/-- Ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian CLT from
almost-sure empirical one-draw characteristic-function power convergence.

This is the textbook characteristic-function face of the route: for every
projection and frequency, the centered empirical one-draw characteristic
function evaluated at the `1 / sqrt(n+1)` CLT scale, raised to `n+1`, converges
to the projected Gaussian characteristic function. The finite normalized
characteristic-function identity rewrites that condition into the Lévy route. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun_pow
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hchar : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ,
      Tendsto
        (fun n =>
          (charFun
            (((ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))).map
              (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a -
                empiricalMean
                  (fun j : Fin (n + 1) => Y j.val ω ⬝ᵥ a))))
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * t)) ^ Nat.succ n)
        atTop
        (𝓝 (charFun
          ((multivariateGaussian 0 S).map
            (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a))
          t)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  refine chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun
    (μ := μ) (Y := Y) (S := S) hY ?_ hfrontier
  refine hchar.mono ?_
  intro ω hω a t
  refine Tendsto.congr' ?_ (hω a t)
  exact Eventually.of_forall fun n =>
    (charFun_normalized_finSucc_resampleMean_sub_empiricalMean_eq_pow
      (Y := fun i ω => Y i ω ⬝ᵥ a) n ω t).symm

/-- Ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian CLT from
almost-sure empirical variance convergence and characteristic-function
remainders.

For each scalar projection, this wrapper turns convergence of the empirical
one-draw variance and the explicit `1 / sqrt(n+1)` Taylor remainder into
conditional characteristic-function convergence for the normalized bootstrap
mean, then applies the Lévy route. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun_remainder
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hS : S.PosSemidef)
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hvar : ∀ᵐ ω ∂μ, ∀ a : k → ℝ,
      Tendsto
        (fun n : ℕ =>
          empiricalVarianceFinSucc (fun i => Y i ω ⬝ᵥ a) n)
        atTop (𝓝 (a ⬝ᵥ (S *ᵥ a))))
    (hrem : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ,
      ((fun n : ℕ =>
          centeredEmpiricalCharFunFinSucc (fun i => Y i ω ⬝ᵥ a) n
              ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) -
            (1 +
              scalarGaussianCharFunExponent t
                  (empiricalVarianceFinSucc (fun i => Y i ω ⬝ᵥ a) n) *
                complexInvNatSucc n)) =o[atTop]
        (fun n : ℕ => complexInvNatSucc n)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  refine chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun
    (μ := μ) (Y := Y) (S := S) hY ?_ hfrontier
  filter_upwards [hvar, hrem] with ω hvarω hremω
  intro a t
  have hchar :=
    charFun_normalized_finSucc_resampleMean_sub_empiricalMean_tendsto_of_variance_tendsto
      (Y := fun i ω => Y i ω ⬝ᵥ a) (ω := ω)
      (σ2 := a ⬝ᵥ (S *ᵥ a)) (hvarω a) t (hremω a t)
  simpa [charFun_map_multivariateGaussian_zero_dotProduct_eq_exp hS a t] using hchar

/-- Positive-definite ordinary nonparametric-bootstrap Hansen Theorem 10.4
Gaussian CLT from almost-sure empirical variance convergence and
characteristic-function remainders. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun_remainder_posDef
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hvar : ∀ᵐ ω ∂μ, ∀ a : k → ℝ,
      Tendsto
        (fun n : ℕ =>
          empiricalVarianceFinSucc (fun i => Y i ω ⬝ᵥ a) n)
        atTop (𝓝 (a ⬝ᵥ (S *ᵥ a))))
    (hrem : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ,
      ((fun n : ℕ =>
          centeredEmpiricalCharFunFinSucc (fun i => Y i ω ⬝ᵥ a) n
              ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) -
            (1 +
              scalarGaussianCharFunExponent t
                  (empiricalVarianceFinSucc (fun i => Y i ω ⬝ᵥ a) n) *
                complexInvNatSucc n)) =o[atTop]
        (fun n : ℕ => complexInvNatSucc n))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun_remainder
    (μ := μ) (Y := Y) (S := S) hS.posSemidef hY hvar hrem
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian CLT from
almost-sure empirical variance convergence and centered Lindeberg tails.

For each scalar projection, the centered empirical square-tail condition
discharges the diagonal characteristic-function Taylor remainder, then the
existing characteristic-function remainder route applies. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun_tail
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hS : S.PosSemidef)
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hvar : ∀ᵐ ω ∂μ, ∀ a : k → ℝ,
      Tendsto
        (fun n : ℕ =>
          empiricalVarianceFinSucc (fun i => Y i ω ⬝ᵥ a) n)
        atTop (𝓝 (a ⬝ᵥ (S *ᵥ a))))
    (htail : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ, ∀ δ : ℝ, 0 < δ →
      Tendsto
        (fun n : ℕ =>
          centeredEmpiricalTailSqFinSucc (fun i => Y i ω ⬝ᵥ a) n
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) δ)
        atTop (𝓝 0))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  refine
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun_remainder
      (μ := μ) (Y := Y) (S := S) hS hY hvar ?_ hfrontier
  filter_upwards [hvar, htail] with ω hvarω htailω
  intro a t
  exact
    centeredEmpiricalCharFunFinSucc_remainder_isLittleO_of_variance_tendsto_tail
      (Y := fun i => Y i ω ⬝ᵥ a) (hvarω a) t (htailω a t)

/-- Positive-definite ordinary nonparametric-bootstrap Hansen Theorem 10.4
Gaussian CLT from almost-sure empirical variance convergence and centered
Lindeberg tails. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun_tail_posDef
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hvar : ∀ᵐ ω ∂μ, ∀ a : k → ℝ,
      Tendsto
        (fun n : ℕ =>
          empiricalVarianceFinSucc (fun i => Y i ω ⬝ᵥ a) n)
        atTop (𝓝 (a ⬝ᵥ (S *ᵥ a))))
    (htail : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ, ∀ δ : ℝ, 0 < δ →
      Tendsto
        (fun n : ℕ =>
          centeredEmpiricalTailSqFinSucc (fun i => Y i ω ⬝ᵥ a) n
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) δ)
        atTop (𝓝 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun_tail
    (μ := μ) (Y := Y) (S := S) hS.posSemidef hY hvar htail
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian CLT from
almost-sure empirical covariance convergence and characteristic-function
remainders.

This is the covariance-matrix version of
`chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun_remainder`:
pathwise convergence of the empirical covariance matrix supplies every
projected empirical variance through
`empiricalVarianceFinSucc_dotProduct_tendsto_of_covMat_tendsto`. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_covMat_remainder
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hS : S.PosSemidef)
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hcov : ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          covMat
            (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))
            (fun i a => Y i.val ω a))
        atTop (𝓝 S))
    (hrem : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ,
      ((fun n : ℕ =>
          centeredEmpiricalCharFunFinSucc (fun i => Y i ω ⬝ᵥ a) n
              ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) -
            (1 +
              scalarGaussianCharFunExponent t
                  (empiricalVarianceFinSucc (fun i => Y i ω ⬝ᵥ a) n) *
                complexInvNatSucc n)) =o[atTop]
        (fun n : ℕ => complexInvNatSucc n)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  refine
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun_remainder
      (μ := μ) (Y := Y) (S := S) hS hY ?_ hrem hfrontier
  filter_upwards [hcov] with ω hcovω
  intro a
  exact empiricalVarianceFinSucc_dotProduct_tendsto_of_covMat_tendsto
    (Y := fun i a => Y i ω a) hcovω a

/-- Positive-definite ordinary nonparametric-bootstrap Hansen Theorem 10.4
Gaussian CLT from almost-sure empirical covariance convergence and
characteristic-function remainders. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_covMat_remainder_posDef
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hcov : ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          covMat
            (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))
            (fun i a => Y i.val ω a))
        atTop (𝓝 S))
    (hrem : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ,
      ((fun n : ℕ =>
          centeredEmpiricalCharFunFinSucc (fun i => Y i ω ⬝ᵥ a) n
              ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) -
            (1 +
              scalarGaussianCharFunExponent t
                  (empiricalVarianceFinSucc (fun i => Y i ω ⬝ᵥ a) n) *
                complexInvNatSucc n)) =o[atTop]
        (fun n : ℕ => complexInvNatSucc n))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_covMat_remainder
    (μ := μ) (Y := Y) (S := S) hS.posSemidef hY hcov hrem
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian CLT from
almost-sure empirical covariance convergence and centered Lindeberg tails.

Pathwise empirical covariance-matrix convergence supplies every projected
empirical variance, while the centered tail condition discharges the diagonal
Taylor remainder. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_covMat_tail
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hS : S.PosSemidef)
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hcov : ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          covMat
            (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))
            (fun i a => Y i.val ω a))
        atTop (𝓝 S))
    (htail : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ, ∀ δ : ℝ, 0 < δ →
      Tendsto
        (fun n : ℕ =>
          centeredEmpiricalTailSqFinSucc (fun i => Y i ω ⬝ᵥ a) n
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) δ)
        atTop (𝓝 0))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  refine
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun_tail
      (μ := μ) (Y := Y) (S := S) hS hY ?_ htail hfrontier
  filter_upwards [hcov] with ω hcovω
  intro a
  exact empiricalVarianceFinSucc_dotProduct_tendsto_of_covMat_tendsto
    (Y := fun i a => Y i ω a) hcovω a

/-- Positive-definite ordinary nonparametric-bootstrap Hansen Theorem 10.4
Gaussian CLT from almost-sure empirical covariance convergence and centered
Lindeberg tails. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_covMat_tail_posDef
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hcov : ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          covMat
            (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))
            (fun i a => Y i.val ω a))
        atTop (𝓝 S))
    (htail : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ, ∀ δ : ℝ, 0 < δ →
      Tendsto
        (fun n : ℕ =>
          centeredEmpiricalTailSqFinSucc (fun i => Y i ω ⬝ᵥ a) n
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) δ)
        atTop (𝓝 0)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_covMat_tail
    (μ := μ) (Y := Y) (S := S) hS.posSemidef hY hcov htail
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Positive-definite ordinary nonparametric-bootstrap Hansen Theorem 10.4
Gaussian CLT from almost-sure scalar projection CLTs for the normalized
`Fin (n+1)` resample mean. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_projection_clt_posDef
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hproj : ∀ᵐ ω ∂μ, ∀ a : k → ℝ,
      TendstoInDistribution
        (fun n (ωs : Fin (n + 1) → Fin (n + 1)) =>
          (fun b =>
            Real.sqrt (n + 1 : ℝ) *
              (empiricalBootstrapResampleMean
                  (fun i : Fin (n + 1) => Y i.val ω)
                  (fun ωs t => ωs t) ωs b -
                empiricalMean (fun i : Fin (n + 1) => Y i.val ω) b)) ⬝ᵥ a)
        atTop
        (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a)
        (fun n =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (multivariateGaussian 0 S)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_projection_clt
    (μ := μ) (Y := Y) (S := S) hY hproj
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Positive-definite ordinary nonparametric-bootstrap Hansen Theorem 10.4
Gaussian CLT from almost-sure scalar bootstrap-mean CLTs for projected
observations. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_scalar_projection_clt_posDef
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hproj : ∀ᵐ ω ∂μ, ∀ a : k → ℝ,
      TendstoInDistribution
        (fun n (ωs : Fin (n + 1) → Fin (n + 1)) =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a)))
        atTop
        (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a)
        (fun n =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (multivariateGaussian 0 S)) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_scalar_projection_clt
    (μ := μ) (Y := Y) (S := S) hY hproj
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Positive-definite ordinary nonparametric-bootstrap Hansen Theorem 10.4
Gaussian CLT from almost-sure characteristic-function convergence for projected
bootstrap means. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun_posDef
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hchar : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ,
      Tendsto
        (fun n =>
          charFun
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1))).map
              (fun ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a))))
            t)
        atTop
        (𝓝 (charFun
          ((multivariateGaussian 0 S).map
            (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a))
          t))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun
    (μ := μ) (Y := Y) (S := S) hY hchar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Positive-definite ordinary nonparametric-bootstrap Hansen Theorem 10.4
Gaussian CLT from almost-sure empirical one-draw characteristic-function power
convergence. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun_pow_posDef
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hchar : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ,
      Tendsto
        (fun n =>
          (charFun
            (((ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))).map
              (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a -
                empiricalMean
                  (fun j : Fin (n + 1) => Y j.val ω ⬝ᵥ a))))
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * t)) ^ Nat.succ n)
        atTop
        (𝓝 (charFun
          ((multivariateGaussian 0 S).map
            (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a))
          t))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun_pow
    (μ := μ) (Y := Y) (S := S) hY hchar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Weak bootstrap convergence plus bounded-continuous integral
linearization implies Hansen's coordinate-CDF bootstrap distribution
convergence when the limiting lower orthants have null frontiers. -/
theorem TendstoInBootstrapDistribution.of_weakDistribution_integral_diff
    [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hdiff :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegral Pstar Zstar' f n ω -
              bootstrapBoundedContinuousIntegral Pstar Zstar f n ω)
          atTop (fun _ => 0))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZ : AEMeasurable Z ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y => vectorCDF ν Z y) x →
        (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar Zstar' ν Z := by
  letI : Fintype k := Fintype.ofFinite k
  intro x hx
  exact hweak.bootstrapVectorCDF_tendsto_of_integral_diff
    hdiff hPstar hZstar' hZ (hfrontier x hx)

/-- Indexed weak bootstrap convergence plus bounded-continuous integral
linearization implies indexed Hansen coordinate-CDF bootstrap distribution
convergence when the limiting lower orthants have null frontiers. -/
theorem TendstoInBootstrapDistributionIndexed.of_weakDistribution_integral_diff
    [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hdiff :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
          atTop (fun _ => 0))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZ : AEMeasurable Z ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y => vectorCDF ν Z y) x →
        (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar' ν Z := by
  letI : Fintype k := Fintype.ofFinite k
  intro x hx
  exact hweak.bootstrapVectorCDF_tendsto_of_integral_diff
    hdiff hPstar hZstar' hZ (hfrontier x hx)

/-- Clipped first moments converge under bootstrap weak convergence.

This is the bounded-continuous core of the Theorem 10.9
distribution-to-moment argument; the remaining UI/tail step removes the
clipping. -/
theorem TendstoInBootstrapWeakDistribution.integral_realClip_tendsto
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    {R : ℝ} (hR : 0 ≤ R) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
      atTop
      (fun _ => ∫ ωlim, realClip R (Z ωlim) ∂ν) := by
  simpa [bootstrapBoundedContinuousIntegral, realClipBoundedContinuousFunction_apply]
    using hZ (realClipBoundedContinuousFunction R hR)

/-- Indexed clipped first moments converge under indexed bootstrap weak
convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.integral_realClip_tendsto
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    {R : ℝ} (hR : 0 ≤ R) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
      atTop
      (fun _ => ∫ ωlim, realClip R (Z ωlim) ∂ν) := by
  simpa [bootstrapBoundedContinuousIntegralIndexed, realClipBoundedContinuousFunction_apply]
    using hZ (realClipBoundedContinuousFunction R hR)

/-- Clipped second moments converge under bootstrap weak convergence.

This is the bounded-continuous core used before the UI/tail argument upgrades
clipped second moments to the full conditional second moments in Hansen
Theorem 10.9. -/
theorem TendstoInBootstrapWeakDistribution.integral_realClip_sq_tendsto
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    {R : ℝ} (hR : 0 ≤ R) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
      atTop
      (fun _ => ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν) := by
  simpa [bootstrapBoundedContinuousIntegral, realClipBoundedContinuousFunction_apply]
    using hZ ((realClipBoundedContinuousFunction R hR) ^ (2 : ℕ))

/-- Indexed clipped second moments converge under indexed bootstrap weak
convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.integral_realClip_sq_tendsto
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    {R : ℝ} (hR : 0 ≤ R) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
      atTop
      (fun _ => ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν) := by
  simpa [bootstrapBoundedContinuousIntegralIndexed, realClipBoundedContinuousFunction_apply]
    using hZ ((realClipBoundedContinuousFunction R hR) ^ (2 : ℕ))

private theorem tendstoInMeasure_of_approx_limits_real
    {X : ℕ → Ω → ℝ} {c : ℝ}
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ cε : ℝ, dist cε c ≤ ε ∧
          TendstoInMeasure μ X atTop (fun _ => cε)) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  obtain ⟨cε, hcε, hX⟩ := happrox (ε / 2) (by positivity)
  rw [tendstoInMeasure_iff_dist] at hX
  have htail := hX (ε / 2) (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  have hωdist : ε ≤ dist (X n ω) c := hω
  have hdist : dist (X n ω) c ≤ dist (X n ω) cε + dist cε c :=
    dist_triangle (X n ω) cε c
  have : ε / 2 ≤ dist (X n ω) cε := by
    linarith
  exact this

private theorem tendstoInMeasure_of_approx_limits_real_tailProb
    {X : ℕ → Ω → ℝ} {c : ℝ}
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ Y : ℕ → Ω → ℝ, ∃ y : ℝ,
          dist y c ≤ ε ∧
            TendstoInMeasure μ Y atTop (fun _ => y) ∧
            Tendsto (fun n => μ {ω | ε ≤ dist (X n ω - Y n ω) 0})
              atTop (𝓝 0)) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  obtain ⟨Y, y, hyc, hY, herr⟩ := happrox (ε / 3) (by positivity)
  rw [tendstoInMeasure_iff_dist] at hY
  have hYtail := hY (ε / 3) (by positivity)
  have hsum := herr.add hYtail
  have hsum0 :
      Tendsto
        (fun n =>
          μ {ω | ε / 3 ≤ dist (X n ω - Y n ω) 0} +
            μ {ω | ε / 3 ≤ dist (Y n ω) y})
        atTop (𝓝 0) := by
    simpa using hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum0
    (fun _ => zero_le _) ?_
  intro n
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_cases herr_big : ε / 3 ≤ dist (X n ω - Y n ω) 0
  · exact Or.inl herr_big
  · right
    by_contra hY_not
    have herr_small : dist (X n ω - Y n ω) 0 < ε / 3 := not_le.mp herr_big
    have hY_small : dist (Y n ω) y < ε / 3 := not_le.mp hY_not
    have htri :
        dist (X n ω) c ≤
          dist (X n ω - Y n ω) 0 + dist (Y n ω) y + dist y c := by
      have h1 := dist_triangle (X n ω) y c
      have h2 := dist_triangle (X n ω) (Y n ω) y
      have hxy : dist (X n ω) (Y n ω) = dist (X n ω - Y n ω) 0 := by
        simp [Real.dist_eq]
      linarith
    have hlt : dist (X n ω) c < ε := by linarith
    exact (not_le.mpr hlt) hω

/-- Bootstrap weak convergence plus clipping-tail control gives full first
moment convergence.

This is the UI/tail assembly step for Hansen Theorem 10.9's conditional first
moment premise. -/
theorem TendstoInBootstrapWeakDistribution.integral_tendsto_of_realClip_tails
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω)[Zstar n ω] -
            (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[Zstar n ω])
      atTop (fun _ => ∫ ωlim, Z ωlim ∂ν) := by
  refine tendstoInMeasure_of_approx_limits_real (μ := μ) ?_
  intro ε hε
  obtain ⟨R, hR, hlim, htail⟩ := hTail ε hε
  let clipMean : ℕ → Ω → ℝ :=
    fun n ω => (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]
  let clipLimit : ℝ := ∫ ωlim, realClip R (Z ωlim) ∂ν
  have hclip :
      TendstoInMeasure μ clipMean atTop (fun _ => clipLimit) := by
    simpa [clipMean, clipLimit] using
      hZ.integral_realClip_tendsto hR
  have hclip0 :
      TendstoInMeasure μ (fun n ω => clipMean n ω - clipLimit)
        atTop (fun _ => 0) :=
    TendstoInMeasure.sub_limit_zero_real hclip
  have hsum := TendstoInMeasure.add_zero_real htail hclip0
  have hmean0 :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω)[Zstar n ω] - clipLimit)
        atTop (fun _ => 0) := by
    refine hsum.congr_left (fun n => ae_of_all μ fun ω => ?_)
    dsimp [clipMean]
    ring
  have hmean :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[Zstar n ω])
        atTop (fun _ => clipLimit) :=
    TendstoInMeasure.of_sub_limit_zero_real hmean0
  exact ⟨clipLimit, by simpa [clipLimit, Real.dist_eq, abs_sub_comm] using hlim, hmean⟩

/-- Indexed bootstrap weak convergence plus clipping-tail control gives full
first moment convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.integral_tendsto_of_realClip_tails
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω)[Zstar n ω] -
            (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[Zstar n ω])
      atTop (fun _ => ∫ ωlim, Z ωlim ∂ν) := by
  refine tendstoInMeasure_of_approx_limits_real (μ := μ) ?_
  intro ε hε
  obtain ⟨R, hR, hlim, htail⟩ := hTail ε hε
  let clipMean : ℕ → Ω → ℝ :=
    fun n ω => (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]
  let clipLimit : ℝ := ∫ ωlim, realClip R (Z ωlim) ∂ν
  have hclip :
      TendstoInMeasure μ clipMean atTop (fun _ => clipLimit) := by
    simpa [clipMean, clipLimit] using
      hZ.integral_realClip_tendsto hR
  have hclip0 :
      TendstoInMeasure μ (fun n ω => clipMean n ω - clipLimit)
        atTop (fun _ => 0) :=
    TendstoInMeasure.sub_limit_zero_real hclip
  have hsum := TendstoInMeasure.add_zero_real htail hclip0
  have hmean0 :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω)[Zstar n ω] - clipLimit)
        atTop (fun _ => 0) := by
    refine hsum.congr_left (fun n => ae_of_all μ fun ω => ?_)
    dsimp [clipMean]
    ring
  have hmean :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[Zstar n ω])
        atTop (fun _ => clipLimit) :=
    TendstoInMeasure.of_sub_limit_zero_real hmean0
  exact ⟨clipLimit, by simpa [clipLimit, Real.dist_eq, abs_sub_comm] using hlim, hmean⟩

/-- Bootstrap weak convergence plus tail-small-in-probability control gives
full first moment convergence.

This is the probability-mode version of the UI/tail assembly used in Hansen
Theorem 10.9: the chosen clipping error only needs to be small in probability
at the approximation tolerance. -/
theorem TendstoInBootstrapWeakDistribution.integral_tendsto_of_realClip_tailProb
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              ((Pstar n ω)[Zstar n ω] -
                (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[Zstar n ω])
      atTop (fun _ => ∫ ωlim, Z ωlim ∂ν) := by
  refine tendstoInMeasure_of_approx_limits_real_tailProb (μ := μ) ?_
  intro ε hε
  obtain ⟨R, hR, hlim, htail⟩ := hTail ε hε
  let clipMean : ℕ → Ω → ℝ :=
    fun n ω => (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]
  let clipLimit : ℝ := ∫ ωlim, realClip R (Z ωlim) ∂ν
  refine ⟨clipMean, clipLimit, ?_, ?_, ?_⟩
  · simpa [clipLimit, Real.dist_eq, abs_sub_comm] using hlim
  · simpa [clipMean, clipLimit] using hZ.integral_realClip_tendsto hR
  · simpa [clipMean] using htail

/-- Indexed bootstrap weak convergence plus tail-small-in-probability control
gives full first moment convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.integral_tendsto_of_realClip_tailProb
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              ((Pstar n ω)[Zstar n ω] -
                (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[Zstar n ω])
      atTop (fun _ => ∫ ωlim, Z ωlim ∂ν) := by
  refine tendstoInMeasure_of_approx_limits_real_tailProb (μ := μ) ?_
  intro ε hε
  obtain ⟨R, hR, hlim, htail⟩ := hTail ε hε
  let clipMean : ℕ → Ω → ℝ :=
    fun n ω => (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]
  let clipLimit : ℝ := ∫ ωlim, realClip R (Z ωlim) ∂ν
  refine ⟨clipMean, clipLimit, ?_, ?_, ?_⟩
  · simpa [clipLimit, Real.dist_eq, abs_sub_comm] using hlim
  · simpa [clipMean, clipLimit] using hZ.integral_realClip_tendsto hR
  · simpa [clipMean] using htail

/-- Bootstrap weak convergence plus clipping-tail control gives full second
moment convergence.

This is the UI/tail assembly step for Hansen Theorem 10.9's conditional second
moment premise. -/
theorem TendstoInBootstrapWeakDistribution.integral_sq_tendsto_of_realClip_tails
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω)[(Zstar n ω) ^ 2] -
            (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[(Zstar n ω) ^ 2])
      atTop (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) := by
  refine tendstoInMeasure_of_approx_limits_real (μ := μ) ?_
  intro ε hε
  obtain ⟨R, hR, hlim, htail⟩ := hTail ε hε
  let clipSecond : ℕ → Ω → ℝ :=
    fun n ω => (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]
  let clipLimit : ℝ := ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν
  have hclip :
      TendstoInMeasure μ clipSecond atTop (fun _ => clipLimit) := by
    simpa [clipSecond, clipLimit] using
      hZ.integral_realClip_sq_tendsto hR
  have hclip0 :
      TendstoInMeasure μ (fun n ω => clipSecond n ω - clipLimit)
        atTop (fun _ => 0) :=
    TendstoInMeasure.sub_limit_zero_real hclip
  have hsum := TendstoInMeasure.add_zero_real htail hclip0
  have hsecond0 :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω)[(Zstar n ω) ^ 2] - clipLimit)
        atTop (fun _ => 0) := by
    refine hsum.congr_left (fun n => ae_of_all μ fun ω => ?_)
    dsimp [clipSecond]
    ring
  have hsecond :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[(Zstar n ω) ^ 2])
        atTop (fun _ => clipLimit) :=
    TendstoInMeasure.of_sub_limit_zero_real hsecond0
  exact ⟨clipLimit, by simpa [clipLimit, Real.dist_eq, abs_sub_comm] using hlim, hsecond⟩

/-- Indexed bootstrap weak convergence plus clipping-tail control gives full
second moment convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.integral_sq_tendsto_of_realClip_tails
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω)[(Zstar n ω) ^ 2] -
            (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[(Zstar n ω) ^ 2])
      atTop (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) := by
  refine tendstoInMeasure_of_approx_limits_real (μ := μ) ?_
  intro ε hε
  obtain ⟨R, hR, hlim, htail⟩ := hTail ε hε
  let clipSecond : ℕ → Ω → ℝ :=
    fun n ω => (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]
  let clipLimit : ℝ := ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν
  have hclip :
      TendstoInMeasure μ clipSecond atTop (fun _ => clipLimit) := by
    simpa [clipSecond, clipLimit] using
      hZ.integral_realClip_sq_tendsto hR
  have hclip0 :
      TendstoInMeasure μ (fun n ω => clipSecond n ω - clipLimit)
        atTop (fun _ => 0) :=
    TendstoInMeasure.sub_limit_zero_real hclip
  have hsum := TendstoInMeasure.add_zero_real htail hclip0
  have hsecond0 :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω)[(Zstar n ω) ^ 2] - clipLimit)
        atTop (fun _ => 0) := by
    refine hsum.congr_left (fun n => ae_of_all μ fun ω => ?_)
    dsimp [clipSecond]
    ring
  have hsecond :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[(Zstar n ω) ^ 2])
        atTop (fun _ => clipLimit) :=
    TendstoInMeasure.of_sub_limit_zero_real hsecond0
  exact ⟨clipLimit, by simpa [clipLimit, Real.dist_eq, abs_sub_comm] using hlim, hsecond⟩

/-- Bootstrap weak convergence plus tail-small-in-probability control gives
full second moment convergence.

This is the probability-mode version of the UI/tail assembly used in Hansen
Theorem 10.9: the chosen squared clipping error only needs to be small in
probability at the approximation tolerance. -/
theorem TendstoInBootstrapWeakDistribution.integral_sq_tendsto_of_realClip_tailProb
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              ((Pstar n ω)[(Zstar n ω) ^ 2] -
                (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[(Zstar n ω) ^ 2])
      atTop (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) := by
  refine tendstoInMeasure_of_approx_limits_real_tailProb (μ := μ) ?_
  intro ε hε
  obtain ⟨R, hR, hlim, htail⟩ := hTail ε hε
  let clipSecond : ℕ → Ω → ℝ :=
    fun n ω => (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]
  let clipLimit : ℝ := ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν
  refine ⟨clipSecond, clipLimit, ?_, ?_, ?_⟩
  · simpa [clipLimit, Real.dist_eq, abs_sub_comm] using hlim
  · simpa [clipSecond, clipLimit] using hZ.integral_realClip_sq_tendsto hR
  · simpa [clipSecond] using htail

/-- Indexed bootstrap weak convergence plus tail-small-in-probability control
gives full second moment convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.integral_sq_tendsto_of_realClip_tailProb
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              ((Pstar n ω)[(Zstar n ω) ^ 2] -
                (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[(Zstar n ω) ^ 2])
      atTop (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) := by
  refine tendstoInMeasure_of_approx_limits_real_tailProb (μ := μ) ?_
  intro ε hε
  obtain ⟨R, hR, hlim, htail⟩ := hTail ε hε
  let clipSecond : ℕ → Ω → ℝ :=
    fun n ω => (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]
  let clipLimit : ℝ := ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν
  refine ⟨clipSecond, clipLimit, ?_, ?_, ?_⟩
  · simpa [clipLimit, Real.dist_eq, abs_sub_comm] using hlim
  · simpa [clipSecond, clipLimit] using hZ.integral_realClip_sq_tendsto hR
  · simpa [clipSecond] using htail

/-- Hansen Theorem 10.5, globally continuous weak-convergence face.

If `Zₙ* ->d* Z` in bounded-continuous-test-function form and `g` is continuous,
then `g(Zₙ*) ->d* g(Z)`.  The more general textbook discontinuity-set-null
form is obtained by replacing the global-continuity premise with the
Portmanteau/ae-continuity bridge. -/
theorem chapter10_bootstrap_continuous_mapping_distribution
    [TopologicalSpace E] [TopologicalSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E} {g : E → F}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hg : Continuous g) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ω => g (Z ω)) := by
  intro f
  let gc : C(E, F) := ⟨g, hg⟩
  simpa [bootstrapBoundedContinuousIntegral, Function.comp_def] using
    hZ (f.compContinuous gc)

/-- Indexed Hansen Theorem 10.5, globally continuous weak-convergence face.

This is the sample-size-dependent counterpart of
`chapter10_bootstrap_continuous_mapping_distribution`. -/
theorem chapter10_indexed_bootstrap_continuous_mapping_distribution
    [TopologicalSpace E] [TopologicalSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E} {g : E → F}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hg : Continuous g) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ω => g (Z ω)) := by
  intro f
  let gc : C(E, F) := ⟨g, hg⟩
  simpa [bootstrapBoundedContinuousIntegralIndexed, Function.comp_def] using
    hZ (f.compContinuous gc)

/-- Hansen Theorem 10.5, compact-range approximation to a globally continuous
mapping.

If `g(Zₙ*)` has the mapped weak bootstrap limit and another statistic `Zₙ*'`
is close to `g(Zₙ*)` in conditional bootstrap probability while both lie in a
fixed compact set, then `Zₙ*'` has the same mapped weak bootstrap limit. -/
theorem chapter10_bootstrap_continuous_mapping_distribution_of_compact_range_closeness
    [TopologicalSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [SecondCountableTopology F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E} {Zstar' : ℕ → Ω → Ωs → F}
    {ν : Measure Ωlim} {Z : Ωlim → E} {g : E → F} {K : Set F}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstarMapped : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZstarMapped_mem : ∀ n ω ωs, g (Zstar n ω ωs) ∈ K)
    (hZstar'_mem : ∀ n ω ωs, Zstar' n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (Zstar' n ω ωs) (g (Zstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistribution μ Pstar Zstar' ν (fun ωlim => g (Z ωlim)) :=
  (chapter10_bootstrap_continuous_mapping_distribution
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g) hZ hg).of_bootstrap_dist_tendsto_zero_compact_range
      hK hPstar hZstarMapped hZstar' hZstarMapped_mem hZstar'_mem hclose

/-- Indexed Hansen Theorem 10.5, compact-range approximation to a globally
continuous mapping. -/
theorem
    chapter10_indexed_bootstrap_continuous_mapping_distribution_of_compact_range_closeness
    [TopologicalSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [SecondCountableTopology F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E} {Zstar' : ∀ n, Ω → Ωboot n → F}
    {ν : Measure Ωlim} {Z : Ωlim → E} {g : E → F} {K : Set F}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstarMapped : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZstarMapped_mem : ∀ n ω ωs, g (Zstar n ω ωs) ∈ K)
    (hZstar'_mem : ∀ n ω ωs, Zstar' n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (Zstar' n ω ωs) (g (Zstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' ν
      (fun ωlim => g (Z ωlim)) :=
  (chapter10_indexed_bootstrap_continuous_mapping_distribution
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g) hZ hg).of_bootstrap_dist_tendsto_zero_compact_range
      hK hPstar hZstarMapped hZstar' hZstarMapped_mem hZstar'_mem hclose

/-- Hansen Theorem 10.5, compact-range approximation event-probability face
for globally continuous mappings. -/
theorem
    chapter10_bootstrap_continuous_mapping_event_probability_of_compact_range_closeness
    [TopologicalSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [SecondCountableTopology F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E} {Zstar' : ℕ → Ω → Ωs → F}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A K : Set F}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstarMapped : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZstarMapped_mem : ∀ n ω ωs, g (Zstar n ω ωs) ∈ K)
    (hZstar'_mem : ∀ n ω ωs, Zstar' n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (Zstar' n ω ωs) (g (Zstar n ω ωs))})
        atTop (fun _ => 0))
    (hZMapped : AEMeasurable (fun ωlim => g (Z ωlim)) ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar Zstar' A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  have hweak :
      TendstoInBootstrapWeakDistribution μ Pstar Zstar' ν (fun ωlim => g (Z ωlim)) :=
    chapter10_bootstrap_continuous_mapping_distribution_of_compact_range_closeness
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (Zstar' := Zstar')
      (ν := ν) (Z := Z) (g := g) (K := K)
      hZ hg hK hPstar hZstarMapped hZstar' hZstarMapped_mem hZstar'_mem hclose
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact hweak.event_probability_tendsto_of_null_frontier
    hPfinite hZstar' hZMapped hA hfrontier

/-- Indexed Hansen Theorem 10.5, compact-range approximation
event-probability face for globally continuous mappings. -/
theorem
    chapter10_indexed_bootstrap_continuous_mapping_event_probability_of_compact_range_closeness
    [TopologicalSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [OpensMeasurableSpace F]
    [SecondCountableTopology F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E} {Zstar' : ∀ n, Ω → Ωboot n → F}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A K : Set F}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstarMapped : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZstarMapped_mem : ∀ n ω ωs, g (Zstar n ω ωs) ∈ K)
    (hZstar'_mem : ∀ n ω ωs, Zstar' n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (Zstar' n ω ωs) (g (Zstar n ω ωs))})
        atTop (fun _ => 0))
    (hZMapped : AEMeasurable (fun ωlim => g (Z ωlim)) ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar Zstar' A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  have hweak :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' ν
        (fun ωlim => g (Z ωlim)) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution_of_compact_range_closeness
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (Zstar' := Zstar')
      (ν := ν) (Z := Z) (g := g) (K := K)
      hZ hg hK hPstar hZstarMapped hZstar' hZstarMapped_mem hZstar'_mem hclose
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact hweak.event_probability_tendsto_of_null_frontier
    hPfinite hZstar' hZMapped hA hfrontier

/-- Hansen Theorem 10.5, globally continuous finite-dimensional CDF face.

After a continuous transformation into `k → ℝ`, the bounded-continuous
bootstrap CMT implies Hansen Definition 10.2 whenever the transformed limiting
lower orthants have null frontier at the relevant continuity points.  The
measurability premises are stated for the transformed statistics so this wrapper
can also be used when measurability is supplied by a model-specific layer. -/
theorem chapter10_bootstrap_continuous_mapping_distribution_of_null_frontiers
    [TopologicalSpace E] [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstarMapped : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZMapped : AEMeasurable (fun ωlim => g (Z ωlim)) ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  exact
    TendstoInBootstrapDistribution.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim))
        (chapter10_bootstrap_continuous_mapping_distribution
          (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
          (g := g) hZ hg)
        hPstar hZstarMapped hZMapped hfrontier

/-- Indexed Hansen Theorem 10.5, globally continuous finite-dimensional CDF
face. -/
theorem chapter10_indexed_bootstrap_continuous_mapping_distribution_of_null_frontiers
    [TopologicalSpace E] [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstarMapped : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZMapped : AEMeasurable (fun ωlim => g (Z ωlim)) ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  exact
    TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim))
      (chapter10_indexed_bootstrap_continuous_mapping_distribution
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
        (g := g) hZ hg)
      hPstar hZstarMapped hZMapped hfrontier

/-- Hansen Theorem 10.5, compact-range approximation CDF face for globally
continuous mappings.

This combines the compact-range weak wrapper with the null-frontier
weak-to-CDF bridge for Hansen Definition 10.2. -/
theorem
    chapter10_bootstrap_continuous_mapping_distribution_of_compact_range_null_frontiers
    [TopologicalSpace E] [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E} {Zstar' : ℕ → Ω → Ωs → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ} {K : Set (k → ℝ)}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstarMapped : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZstarMapped_mem : ∀ n ω ωs, g (Zstar n ω ωs) ∈ K)
    (hZstar'_mem : ∀ n ω ωs, Zstar' n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (Zstar' n ω ωs) (g (Zstar n ω ωs))})
        atTop (fun _ => 0))
    (hZMapped : AEMeasurable (fun ωlim => g (Z ωlim)) ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar Zstar' ν (fun ωlim => g (Z ωlim)) := by
  have hweak :
      TendstoInBootstrapWeakDistribution μ Pstar Zstar' ν (fun ωlim => g (Z ωlim)) :=
    chapter10_bootstrap_continuous_mapping_distribution_of_compact_range_closeness
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (Zstar' := Zstar')
      (ν := ν) (Z := Z) (g := g) (K := K)
      hZ hg hK hPstar hZstarMapped hZstar' hZstarMapped_mem hZstar'_mem hclose
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    TendstoInBootstrapDistribution.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar') (ν := ν)
      (Z := fun ωlim => g (Z ωlim))
      hweak hPfinite hZstar' hZMapped hfrontier

/-- Indexed Hansen Theorem 10.5, compact-range approximation CDF face for
globally continuous mappings. -/
theorem
    chapter10_indexed_bootstrap_continuous_mapping_distribution_of_compact_range_null_frontiers
    [TopologicalSpace E] [Fintype k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Zstar' : ∀ n, Ω → Ωboot n → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ} {K : Set (k → ℝ)}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZstarMapped : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZstarMapped_mem : ∀ n ω ωs, g (Zstar n ω ωs) ∈ K)
    (hZstar'_mem : ∀ n ω ωs, Zstar' n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (Zstar' n ω ωs) (g (Zstar n ω ωs))})
        atTop (fun _ => 0))
    (hZMapped : AEMeasurable (fun ωlim => g (Z ωlim)) ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar' ν
      (fun ωlim => g (Z ωlim)) := by
  have hweak :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' ν
        (fun ωlim => g (Z ωlim)) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution_of_compact_range_closeness
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (Zstar' := Zstar')
      (ν := ν) (Z := Z) (g := g) (K := K)
      hZ hg hK hPstar hZstarMapped hZstar' hZstarMapped_mem hZstar'_mem hclose
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar') (ν := ν)
      (Z := fun ωlim => g (Z ωlim))
      hweak hPfinite hZstar' hZMapped hfrontier

/-- Hansen Theorem 10.5, globally continuous finite-dimensional CDF face with
measurability derived from the underlying statistic.

This is a convenience wrapper around
`chapter10_bootstrap_continuous_mapping_distribution_of_null_frontiers` for the
common case where `g` is globally continuous and the original bootstrap and
limit statistics are measurable. -/
theorem chapter10_bootstrap_continuous_mapping_distribution_of_null_frontiers_measurable
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZlim : AEMeasurable Z ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  refine
    chapter10_bootstrap_continuous_mapping_distribution_of_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) hZ hg hPstar ?_ ?_ hfrontier
  · intro n ω
    exact hg.measurable.comp (hZstar n ω)
  · have hg_ae : AEMeasurable g (ν.map Z) := hg.measurable.aemeasurable
    simpa [Function.comp_def] using hg_ae.comp_aemeasurable hZlim

/-- Indexed Hansen Theorem 10.5, globally continuous finite-dimensional CDF face
with measurability derived from the underlying statistic. -/
theorem chapter10_indexed_bootstrap_continuous_mapping_distribution_of_null_frontiers_measurable
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZlim : AEMeasurable Z ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  refine
    chapter10_indexed_bootstrap_continuous_mapping_distribution_of_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) hZ hg hPstar ?_ ?_ hfrontier
  · intro n ω
    exact hg.measurable.comp (hZstar n ω)
  · have hg_ae : AEMeasurable g (ν.map Z) := hg.measurable.aemeasurable
    simpa [Function.comp_def] using hg_ae.comp_aemeasurable hZlim

/-- Hansen Theorem 10.5, globally continuous event-probability face.

After a continuous transformation `g`, bounded-continuous lower/upper
sandwiches for an event `A` imply convergence in probability of the conditional
bootstrap event probabilities.  The remaining textbook discontinuity-set-null
case supplies these sandwiches from the null-boundary hypothesis. -/
theorem chapter10_bootstrap_continuous_mapping_event_probability
    [TopologicalSpace E] [TopologicalSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E} {g : E → F} {A : Set F} {c : ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ lower upper : BoundedContinuousFunction F ℝ,
        (∫ ωlim, lower (g (Z ωlim)) ∂ν) ≤ c ∧
          c ≤ (∫ ωlim, upper (g (Z ωlim)) ∂ν) ∧
          (∫ ωlim, upper (g (Z ωlim)) ∂ν) -
              (∫ ωlim, lower (g (Z ωlim)) ∂ν) ≤ ε ∧
          (∀ n ω,
            bootstrapBoundedContinuousIntegral Pstar
                (fun n ω ωs => g (Zstar n ω ωs)) lower n ω ≤
              bootstrapEventProbability Pstar
                (fun n ω ωs => g (Zstar n ω ωs)) A n ω) ∧
          (∀ n ω,
            bootstrapEventProbability Pstar
                (fun n ω ωs => g (Zstar n ω ωs)) A n ω ≤
              bootstrapBoundedContinuousIntegral Pstar
                (fun n ω ωs => g (Zstar n ω ωs)) upper n ω)) :
    TendstoInMeasure μ
      (bootstrapEventProbability Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => c) := by
  exact
    (chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) hZ hg).event_probability_tendsto_of_boundedContinuous_sandwich
        happrox

/-- Indexed Hansen Theorem 10.5, globally continuous event-probability face. -/
theorem chapter10_indexed_bootstrap_continuous_mapping_event_probability
    [TopologicalSpace E] [TopologicalSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E} {g : E → F} {A : Set F} {c : ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ lower upper : BoundedContinuousFunction F ℝ,
        (∫ ωlim, lower (g (Z ωlim)) ∂ν) ≤ c ∧
          c ≤ (∫ ωlim, upper (g (Z ωlim)) ∂ν) ∧
          (∫ ωlim, upper (g (Z ωlim)) ∂ν) -
              (∫ ωlim, lower (g (Z ωlim)) ∂ν) ≤ ε ∧
          (∀ n ω,
            bootstrapBoundedContinuousIntegralIndexed Pstar
                (fun n ω ωs => g (Zstar n ω ωs)) lower n ω ≤
              bootstrapEventProbabilityIndexed Pstar
                (fun n ω ωs => g (Zstar n ω ωs)) A n ω) ∧
          (∀ n ω,
            bootstrapEventProbabilityIndexed Pstar
                (fun n ω ωs => g (Zstar n ω ωs)) A n ω ≤
              bootstrapBoundedContinuousIntegralIndexed Pstar
                (fun n ω ωs => g (Zstar n ω ωs)) upper n ω)) :
    TendstoInMeasure μ
      (bootstrapEventProbabilityIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => c) := by
  exact
    (chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) hZ hg).event_probability_tendsto_of_sandwich happrox

/-- Hansen Theorem 10.5, globally continuous event-probability face with a
null-frontier event.

If `Zₙ* ->d* Z`, `g` is continuous, the conditional bootstrap laws are finite,
and the transformed limit law gives zero mass to the frontier of `A`, then
the conditional probabilities `P*[g(Zₙ*) ∈ A]` converge in probability to
`P[g(Z) ∈ A]`. -/
theorem chapter10_bootstrap_continuous_mapping_event_probability_of_null_frontier
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZlim : AEMeasurable Z ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbability Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  refine
    TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_null_frontier
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim)) (A := A)
      ?_ hPstar ?_ ?_ hA hfrontier
  · exact
      chapter10_bootstrap_continuous_mapping_distribution
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
        (g := g) hZ hg
  · intro n ω
    exact hg.measurable.comp (hZstar n ω)
  · have hg_ae : AEMeasurable g (ν.map Z) := hg.measurable.aemeasurable
    simpa [Function.comp_def] using hg_ae.comp_aemeasurable hZlim

/-- Indexed Hansen Theorem 10.5, globally continuous event-probability face
with a null-frontier event. -/
theorem chapter10_indexed_bootstrap_continuous_mapping_event_probability_of_null_frontier
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZlim : AEMeasurable Z ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbabilityIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  refine
    TendstoInBootstrapWeakDistributionIndexed.event_probability_tendsto_of_null_frontier
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim)) (A := A)
      ?_ hPstar ?_ ?_ hA hfrontier
  · exact
      chapter10_indexed_bootstrap_continuous_mapping_distribution
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
        (g := g) hZ hg
  · intro n ω
    exact hg.measurable.comp (hZstar n ω)
  · have hg_ae : AEMeasurable g (ν.map Z) := hg.measurable.aemeasurable
    simpa [Function.comp_def] using hg_ae.comp_aemeasurable hZlim

/-- Hansen Theorem 10.5, sandwich-mapped event-probability face with a
null-frontier event.

This is the theorem-facing composition of
`TendstoInBootstrapWeakDistribution.map_of_boundedContinuous_sandwich` with
the null-frontier event bridge.  It is useful when `g` is not globally
continuous but transformed bounded-continuous test functions have
lower/upper bounded-continuous approximations on the original space. -/
theorem chapter10_bootstrap_mapping_event_probability_of_sandwich_null_frontier
    [TopologicalSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction F ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZlim : AEMeasurable (fun ωlim => g (Z ωlim)) ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbability Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  refine
    TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_null_frontier
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim)) (A := A)
      ?_ hPstar hZstar hZlim hA hfrontier
  exact hZ.map_of_boundedContinuous_sandwich happrox

/-- Indexed Hansen Theorem 10.5, sandwich-mapped event-probability face with a
null-frontier event. -/
theorem chapter10_indexed_bootstrap_mapping_event_probability_of_sandwich_null_frontier
    [TopologicalSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction F ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZlim : AEMeasurable (fun ωlim => g (Z ωlim)) ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbabilityIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  refine
    TendstoInBootstrapWeakDistributionIndexed.event_probability_tendsto_of_null_frontier
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim)) (A := A)
      ?_ hPstar hZstar hZlim hA hfrontier
  exact hZ.map_of_boundedContinuous_sandwich happrox

/-- Hansen Theorem 10.5, sandwich-mapped finite-dimensional CDF face.

Bounded-continuous sandwich approximations give mapped weak convergence; null
frontiers for transformed lower orthants then recover Hansen Definition 10.2. -/
theorem chapter10_bootstrap_mapping_distribution_of_sandwich_null_frontiers
    [TopologicalSpace E] [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZlim : AEMeasurable (fun ωlim => g (Z ωlim)) ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  refine
    TendstoInBootstrapDistribution.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim))
      ?_ hPstar hZstar hZlim hfrontier
  exact hZ.map_of_boundedContinuous_sandwich happrox

/-- Indexed Hansen Theorem 10.5, sandwich-mapped finite-dimensional CDF face. -/
theorem chapter10_indexed_bootstrap_mapping_distribution_of_sandwich_null_frontiers
    [TopologicalSpace E] [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZlim : AEMeasurable (fun ωlim => g (Z ωlim)) ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  refine
    TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim))
      ?_ hPstar hZstar hZlim hfrontier
  exact hZ.map_of_boundedContinuous_sandwich happrox

/-- The textbook a.e.-continuity premise in Hansen Theorem 10.5.

This condition package is intentionally limit-law-facing: it records that the
transformed limit statistic is measurable and that the transformation is
continuous at `Z` outside a `ν`-null set.  The Portmanteau step deriving
transformed weak convergence from this premise is kept separate from the
event-probability wrappers below. -/
structure BootstrapAEMappingPremise
    [TopologicalSpace E] [TopologicalSpace F] [MeasurableSpace F]
    (ν : Measure Ωlim) (Z : Ωlim → E) (g : E → F) : Prop where
  aemeasurable : AEMeasurable (fun ωlim => g (Z ωlim)) ν
  ae_continuous : ∀ᵐ ωlim ∂ν, ContinuousAt g (Z ωlim)

/-- Global continuity supplies Hansen's a.e.-continuity mapping premise. -/
theorem BootstrapAEMappingPremise.of_continuous
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    {ν : Measure Ωlim} {Z : Ωlim → E} {g : E → F}
    (hZ : AEMeasurable Z ν) (hg : Continuous g) :
    BootstrapAEMappingPremise ν Z g := by
  exact
    { aemeasurable := hg.measurable.aemeasurable.comp_aemeasurable hZ
      ae_continuous := ae_of_all ν fun _ => hg.continuousAt }

/-- Law-level a.e.-continuity supplies Hansen's a.e.-continuity mapping
premise.

This is the textbook-facing constructor: the continuity condition is stated
under the limit law of `Z`, then pulled back to the underlying limit
probability space. -/
theorem BootstrapAEMappingPremise.of_law_ae_continuous
    [TopologicalSpace E] [MeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F]
    {ν : Measure Ωlim} {Z : Ωlim → E} {g : E → F}
    (hZ : AEMeasurable Z ν)
    (hg_meas : AEMeasurable g (ν.map Z))
    (hg_cont : ∀ᵐ x ∂ν.map Z, ContinuousAt g x) :
    BootstrapAEMappingPremise ν Z g :=
  { aemeasurable := hg_meas.comp_aemeasurable hZ
    ae_continuous := ae_of_ae_map hZ hg_cont }

/-- Null discontinuity sets under the limit law supply Hansen's
a.e.-continuity mapping premise. -/
theorem BootstrapAEMappingPremise.of_law_null_discontinuities
    [TopologicalSpace E] [MeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F]
    {ν : Measure Ωlim} {Z : Ωlim → E} {g : E → F}
    (hZ : AEMeasurable Z ν)
    (hg_meas : AEMeasurable g (ν.map Z))
    (hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0) :
    BootstrapAEMappingPremise ν Z g :=
  BootstrapAEMappingPremise.of_law_ae_continuous hZ hg_meas <| by
    rw [ae_iff]
    exact hg_disc

/-- Measurable transformations with law-level a.e.-continuity supply Hansen's
a.e.-continuity mapping premise. -/
theorem BootstrapAEMappingPremise.of_measurable_law_ae_continuous
    [TopologicalSpace E] [MeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F]
    {ν : Measure Ωlim} {Z : Ωlim → E} {g : E → F}
    (hZ : AEMeasurable Z ν)
    (hg_meas : Measurable g)
    (hg_cont : ∀ᵐ x ∂ν.map Z, ContinuousAt g x) :
    BootstrapAEMappingPremise ν Z g :=
  BootstrapAEMappingPremise.of_law_ae_continuous
    hZ hg_meas.aemeasurable hg_cont

/-- Measurable transformations whose discontinuities are null under the limit
law supply Hansen's a.e.-continuity mapping premise. -/
theorem BootstrapAEMappingPremise.of_measurable_law_null_discontinuities
    [TopologicalSpace E] [MeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F]
    {ν : Measure Ωlim} {Z : Ωlim → E} {g : E → F}
    (hZ : AEMeasurable Z ν)
    (hg_meas : Measurable g)
    (hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0) :
    BootstrapAEMappingPremise ν Z g :=
  BootstrapAEMappingPremise.of_law_null_discontinuities
    hZ hg_meas.aemeasurable hg_disc

/-- Hansen Theorem 10.5, a.e.-continuous transformed-event face.

The a.e.-continuity package records the textbook mapping premise, while the
transformed weak-convergence hypothesis is explicit.  This gives the
null-frontier event-probability conclusion without assuming that `g` is
globally continuous. -/
theorem chapter10_bootstrap_ae_continuous_mapping_event_probability_of_null_frontier
    [TopologicalSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hmap : BootstrapAEMappingPremise ν Z g)
    (hweakMapped :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbability Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  exact
    TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_null_frontier
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim)) (A := A)
      hweakMapped hPstar hZstar hmap.aemeasurable hA hfrontier

/-- Indexed Hansen Theorem 10.5, a.e.-continuous transformed-event face. -/
theorem chapter10_indexed_bootstrap_ae_continuous_mapping_event_probability_of_null_frontier
    [TopologicalSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hmap : BootstrapAEMappingPremise ν Z g)
    (hweakMapped :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbabilityIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  exact
    TendstoInBootstrapWeakDistributionIndexed.event_probability_tendsto_of_null_frontier
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim)) (A := A)
      hweakMapped hPstar hZstar hmap.aemeasurable hA hfrontier

/-- Hansen Theorem 10.5, a.e.-continuous finite-dimensional CDF face.

This is the Definition 10.2 counterpart of
`chapter10_bootstrap_ae_continuous_mapping_event_probability_of_null_frontier`.
The a.e.-continuity package records Hansen's mapping premise, while the
transformed weak-convergence hypothesis is explicit; null frontiers for
transformed lower orthants then give conditional-CDF convergence. -/
theorem chapter10_bootstrap_ae_continuous_mapping_distribution_of_null_frontiers
    [TopologicalSpace E] [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hmap : BootstrapAEMappingPremise ν Z g)
    (hweakMapped :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  exact
    TendstoInBootstrapDistribution.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim))
      hweakMapped hPstar hZstar hmap.aemeasurable hfrontier

/-- Indexed Hansen Theorem 10.5, a.e.-continuous finite-dimensional CDF face. -/
theorem chapter10_indexed_bootstrap_ae_continuous_mapping_distribution_of_null_frontiers
    [TopologicalSpace E] [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hmap : BootstrapAEMappingPremise ν Z g)
    (hweakMapped :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  exact
    TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim))
      hweakMapped hPstar hZstar hmap.aemeasurable hfrontier

/-- Hansen Theorem 10.5, law-level null-discontinuity transformed-event face.

This is the mapped-weak-convergence route stated with Hansen's textbook
discontinuity-set hypothesis under the law of `Z`. -/
theorem chapter10_bootstrap_law_null_disc_mapping_event_probability_of_null_frontier
    [TopologicalSpace E] [MeasurableSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0)
    (hweakMapped :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbability Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) :=
  chapter10_bootstrap_ae_continuous_mapping_event_probability_of_null_frontier
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g) (A := A)
    (BootstrapAEMappingPremise.of_measurable_law_null_discontinuities
      hZlim hg hg_disc)
    hweakMapped hPstar hZstar hA hfrontier

/-- Indexed Hansen Theorem 10.5, law-level null-discontinuity transformed-event
face. -/
theorem chapter10_indexed_bootstrap_law_null_disc_mapping_event_probability_of_null_frontier
    [TopologicalSpace E] [MeasurableSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0)
    (hweakMapped :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbabilityIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) :=
  chapter10_indexed_bootstrap_ae_continuous_mapping_event_probability_of_null_frontier
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g) (A := A)
    (BootstrapAEMappingPremise.of_measurable_law_null_discontinuities
      hZlim hg hg_disc)
    hweakMapped hPstar hZstar hA hfrontier

/-- Hansen Theorem 10.5, law-level null-discontinuity finite-dimensional CDF
face. -/
theorem chapter10_bootstrap_law_null_disc_mapping_distribution_of_null_frontiers
    [TopologicalSpace E] [MeasurableSpace E] [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0)
    (hweakMapped :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) :=
  chapter10_bootstrap_ae_continuous_mapping_distribution_of_null_frontiers
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g)
    (BootstrapAEMappingPremise.of_measurable_law_null_discontinuities
      hZlim hg hg_disc)
    hweakMapped hPstar hZstar hfrontier

/-- Indexed Hansen Theorem 10.5, law-level null-discontinuity
finite-dimensional CDF face. -/
theorem chapter10_indexed_bootstrap_law_null_disc_mapping_distribution_of_null_frontiers
    [TopologicalSpace E] [MeasurableSpace E] [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0)
    (hweakMapped :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) :=
  chapter10_indexed_bootstrap_ae_continuous_mapping_distribution_of_null_frontiers
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g)
    (BootstrapAEMappingPremise.of_measurable_law_null_discontinuities
      hZlim hg hg_disc)
    hweakMapped hPstar hZstar hfrontier

/-- Hansen Theorem 10.5, law-level a.e.-continuous transformed-event face.

This mapped-weak-convergence route states the continuity premise directly under
the limit law of `Z`, matching Hansen's a.e.-continuity formulation without
requiring callers to assemble `BootstrapAEMappingPremise` first. -/
theorem chapter10_bootstrap_law_ae_mapping_event_probability_of_null_frontier
    [TopologicalSpace E] [MeasurableSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_cont : ∀ᵐ x ∂ν.map Z, ContinuousAt g x)
    (hweakMapped :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbability Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) :=
  chapter10_bootstrap_ae_continuous_mapping_event_probability_of_null_frontier
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g) (A := A)
    (BootstrapAEMappingPremise.of_measurable_law_ae_continuous
      hZlim hg hg_cont)
    hweakMapped hPstar hZstar hA hfrontier

/-- Indexed Hansen Theorem 10.5, law-level a.e.-continuous transformed-event
face. -/
theorem chapter10_indexed_bootstrap_law_ae_mapping_event_probability_of_null_frontier
    [TopologicalSpace E] [MeasurableSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_cont : ∀ᵐ x ∂ν.map Z, ContinuousAt g x)
    (hweakMapped :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbabilityIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) :=
  chapter10_indexed_bootstrap_ae_continuous_mapping_event_probability_of_null_frontier
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g) (A := A)
    (BootstrapAEMappingPremise.of_measurable_law_ae_continuous
      hZlim hg hg_cont)
    hweakMapped hPstar hZstar hA hfrontier

/-- Hansen Theorem 10.5, law-level a.e.-continuous finite-dimensional CDF
face. -/
theorem chapter10_bootstrap_law_ae_mapping_distribution_of_null_frontiers
    [TopologicalSpace E] [MeasurableSpace E] [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_cont : ∀ᵐ x ∂ν.map Z, ContinuousAt g x)
    (hweakMapped :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) :=
  chapter10_bootstrap_ae_continuous_mapping_distribution_of_null_frontiers
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g)
    (BootstrapAEMappingPremise.of_measurable_law_ae_continuous
      hZlim hg hg_cont)
    hweakMapped hPstar hZstar hfrontier

/-- Indexed Hansen Theorem 10.5, law-level a.e.-continuous finite-dimensional
CDF face. -/
theorem chapter10_indexed_bootstrap_law_ae_mapping_distribution_of_null_frontiers
    [TopologicalSpace E] [MeasurableSpace E] [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_cont : ∀ᵐ x ∂ν.map Z, ContinuousAt g x)
    (hweakMapped :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) :=
  chapter10_indexed_bootstrap_ae_continuous_mapping_distribution_of_null_frontiers
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g)
    (BootstrapAEMappingPremise.of_measurable_law_ae_continuous
      hZlim hg hg_cont)
    hweakMapped hPstar hZstar hfrontier

/-- Hansen Theorem 10.5, law-level null-discontinuity weak-convergence
constructor from pathwise conditional weak convergence.

This is the theorem-facing a.e.-continuous CMT route: Mathlib's
Portmanteau-based CMT maps the conditional laws on almost every original sample
path, then the bootstrap weak-convergence bridge turns those pathwise limits
into convergence in bootstrap distribution. -/
theorem chapter10_bootstrap_law_null_disc_mapping_weakDistribution_of_ae_tendstoInDistribution
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E]
    [TopologicalSpace F] [MeasurableSpace F] [OpensMeasurableSpace F] [BorelSpace F]
    [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs} [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F}
    (hg : Measurable g)
    (hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0)
    (hmeas : ∀ f : BoundedContinuousFunction F ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          bootstrapBoundedContinuousIntegral Pstar
            (fun n ω ωs => g (Zstar n ω ωs)) f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωs) => Zstar n ω ωs)
        atTop Z (fun n => Pstar n ω) ν) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  refine
    TendstoInBootstrapWeakDistribution.of_ae_tendstoInDistribution_ae_continuous_comp
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) hg (D := {x | ¬ ContinuousAt g x}) hg_disc ?_ hmeas hae
  intro x hx
  exact not_not.mp hx

/-- Indexed Hansen Theorem 10.5, law-level null-discontinuity
weak-convergence constructor from pathwise conditional weak convergence. -/
theorem
    chapter10_indexed_bootstrap_law_null_disc_mapping_weakDistribution_of_ae_tendstoInDistribution
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E]
    [TopologicalSpace F] [MeasurableSpace F] [OpensMeasurableSpace F] [BorelSpace F]
    [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F}
    (hg : Measurable g)
    (hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0)
    (hmeas : ∀ f : BoundedContinuousFunction F ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          bootstrapBoundedContinuousIntegralIndexed Pstar
            (fun n ω ωs => g (Zstar n ω ωs)) f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωboot n) => Zstar n ω ωs)
        atTop Z (fun n => Pstar n ω) ν) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  refine
    TendstoInBootstrapWeakDistributionIndexed.of_ae_tendstoInDistribution_ae_continuous_comp
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) hg (D := {x | ¬ ContinuousAt g x}) hg_disc ?_ hmeas hae
  intro x hx
  exact not_not.mp hx

/-- Hansen Theorem 10.5, law-level null-discontinuity transformed-event face
from pathwise conditional weak convergence. -/
theorem
    chapter10_bootstrap_law_null_disc_mapping_event_probability_of_ae_tendstoInDistribution
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs} [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0)
    (hmeas : ∀ f : BoundedContinuousFunction F ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          bootstrapBoundedContinuousIntegral Pstar
            (fun n ω ωs => g (Zstar n ω ωs)) f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωs) => Zstar n ω ωs)
        atTop Z (fun n => Pstar n ω) ν)
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbability Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  have hweakMapped :=
    chapter10_bootstrap_law_null_disc_mapping_weakDistribution_of_ae_tendstoInDistribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) hg hg_disc hmeas hae
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    infer_instance
  have hZstarMapped : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)) := by
    intro n ω
    exact hg.comp (hZstar n ω)
  exact
    chapter10_bootstrap_law_null_disc_mapping_event_probability_of_null_frontier
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) (A := A)
      hZlim hg hg_disc hweakMapped hPfinite hZstarMapped hA hfrontier

/-- Indexed Hansen Theorem 10.5, law-level null-discontinuity transformed-event
face from pathwise conditional weak convergence. -/
theorem
    chapter10_indexed_bootstrap_law_null_disc_mapping_event_probability_of_ae_tendstoInDistribution
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0)
    (hmeas : ∀ f : BoundedContinuousFunction F ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          bootstrapBoundedContinuousIntegralIndexed Pstar
            (fun n ω ωs => g (Zstar n ω ωs)) f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωboot n) => Zstar n ω ωs)
        atTop Z (fun n => Pstar n ω) ν)
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbabilityIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  have hweakMapped :=
    chapter10_indexed_bootstrap_law_null_disc_mapping_weakDistribution_of_ae_tendstoInDistribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) hg hg_disc hmeas hae
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    infer_instance
  have hZstarMapped : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)) := by
    intro n ω
    exact hg.comp (hZstar n ω)
  exact
    chapter10_indexed_bootstrap_law_null_disc_mapping_event_probability_of_null_frontier
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) (A := A)
      hZlim hg hg_disc hweakMapped hPfinite hZstarMapped hA hfrontier

/-- Hansen Theorem 10.5, law-level null-discontinuity finite-dimensional CDF
face from pathwise conditional weak convergence. -/
theorem
    chapter10_bootstrap_law_null_disc_mapping_distribution_of_ae_tendstoInDistribution
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E] [Finite k] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs} [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0)
    (hmeas : ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          bootstrapBoundedContinuousIntegral Pstar
            (fun n ω ωs => g (Zstar n ω ωs)) f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωs) => Zstar n ω ωs)
        atTop Z (fun n => Pstar n ω) ν)
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  have hweakMapped :=
    chapter10_bootstrap_law_null_disc_mapping_weakDistribution_of_ae_tendstoInDistribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) hg hg_disc hmeas hae
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    infer_instance
  have hZstarMapped : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)) := by
    intro n ω
    exact hg.comp (hZstar n ω)
  exact
    chapter10_bootstrap_law_null_disc_mapping_distribution_of_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g)
      hZlim hg hg_disc hweakMapped hPfinite hZstarMapped hfrontier

/-- Indexed Hansen Theorem 10.5, law-level null-discontinuity
finite-dimensional CDF face from pathwise conditional weak convergence. -/
theorem
    chapter10_indexed_bootstrap_law_null_disc_mapping_distribution_of_ae_tendstoInDistribution
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E] [Finite k] [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0)
    (hmeas : ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          bootstrapBoundedContinuousIntegralIndexed Pstar
            (fun n ω ωs => g (Zstar n ω ωs)) f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωboot n) => Zstar n ω ωs)
        atTop Z (fun n => Pstar n ω) ν)
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  have hweakMapped :=
    chapter10_indexed_bootstrap_law_null_disc_mapping_weakDistribution_of_ae_tendstoInDistribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) hg hg_disc hmeas hae
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    infer_instance
  have hZstarMapped : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)) := by
    intro n ω
    exact hg.comp (hZstar n ω)
  exact
    chapter10_indexed_bootstrap_law_null_disc_mapping_distribution_of_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g)
      hZlim hg hg_disc hweakMapped hPfinite hZstarMapped hfrontier

/-- Hansen Theorem 10.5, law-level a.e.-continuous transformed-event face from
pathwise conditional weak convergence. -/
theorem chapter10_bootstrap_law_ae_mapping_event_probability_of_ae_tendstoInDistribution
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs} [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_cont : ∀ᵐ x ∂ν.map Z, ContinuousAt g x)
    (hmeas : ∀ f : BoundedContinuousFunction F ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          bootstrapBoundedContinuousIntegral Pstar
            (fun n ω ωs => g (Zstar n ω ωs)) f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωs) => Zstar n ω ωs)
        atTop Z (fun n => Pstar n ω) ν)
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbability Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  have hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0 := by
    rw [ae_iff] at hg_cont
    simpa using hg_cont
  exact
    chapter10_bootstrap_law_null_disc_mapping_event_probability_of_ae_tendstoInDistribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) (A := A)
      hZlim hg hg_disc hmeas hae hZstar hA hfrontier

/-- Indexed Hansen Theorem 10.5, law-level a.e.-continuous transformed-event
face from pathwise conditional weak convergence. -/
theorem
    chapter10_indexed_bootstrap_law_ae_mapping_event_probability_of_ae_tendstoInDistribution
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_cont : ∀ᵐ x ∂ν.map Z, ContinuousAt g x)
    (hmeas : ∀ f : BoundedContinuousFunction F ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          bootstrapBoundedContinuousIntegralIndexed Pstar
            (fun n ω ωs => g (Zstar n ω ωs)) f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωboot n) => Zstar n ω ωs)
        atTop Z (fun n => Pstar n ω) ν)
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbabilityIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  have hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0 := by
    rw [ae_iff] at hg_cont
    simpa using hg_cont
  exact
    chapter10_indexed_bootstrap_law_null_disc_mapping_event_probability_of_ae_tendstoInDistribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) (A := A)
      hZlim hg hg_disc hmeas hae hZstar hA hfrontier

/-- Hansen Theorem 10.5, law-level a.e.-continuous finite-dimensional CDF face
from pathwise conditional weak convergence. -/
theorem chapter10_bootstrap_law_ae_mapping_distribution_of_ae_tendstoInDistribution
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E] [Finite k] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs} [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_cont : ∀ᵐ x ∂ν.map Z, ContinuousAt g x)
    (hmeas : ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          bootstrapBoundedContinuousIntegral Pstar
            (fun n ω ωs => g (Zstar n ω ωs)) f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωs) => Zstar n ω ωs)
        atTop Z (fun n => Pstar n ω) ν)
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  have hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0 := by
    rw [ae_iff] at hg_cont
    simpa using hg_cont
  exact
    chapter10_bootstrap_law_null_disc_mapping_distribution_of_ae_tendstoInDistribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g)
      hZlim hg hg_disc hmeas hae hZstar hfrontier

/-- Indexed Hansen Theorem 10.5, law-level a.e.-continuous finite-dimensional
CDF face from pathwise conditional weak convergence. -/
theorem chapter10_indexed_bootstrap_law_ae_mapping_distribution_of_ae_tendstoInDistribution
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E] [Finite k] [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    [∀ n ω, IsProbabilityMeasure (Pstar n ω)]
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_cont : ∀ᵐ x ∂ν.map Z, ContinuousAt g x)
    (hmeas : ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          bootstrapBoundedContinuousIntegralIndexed Pstar
            (fun n ω ωs => g (Zstar n ω ωs)) f n ω) μ)
    (hae : ∀ᵐ ω ∂μ,
      TendstoInDistribution
        (fun n (ωs : Ωboot n) => Zstar n ω ωs)
        atTop Z (fun n => Pstar n ω) ν)
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  have hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0 := by
    rw [ae_iff] at hg_cont
    simpa using hg_cont
  exact
    chapter10_indexed_bootstrap_law_null_disc_mapping_distribution_of_ae_tendstoInDistribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g)
      hZlim hg hg_disc hmeas hae hZstar hfrontier

/-- Hansen Theorem 10.5, a.e.-continuous sandwich-mapped event face.

The a.e.-continuity package records Hansen's textbook mapping premise, while
the bounded-continuous sandwich premise supplies the Portmanteau approximation
step for the transformed test functions. This wrapper then gives the
null-frontier event conclusion without separately asking for mapped weak
convergence. -/
theorem
    chapter10_bootstrap_ae_continuous_mapping_event_probability_of_sandwich_null_frontier
    [TopologicalSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hmap : BootstrapAEMappingPremise ν Z g)
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction F ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbability Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) :=
  chapter10_bootstrap_mapping_event_probability_of_sandwich_null_frontier
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g) (A := A) hZ happrox hPstar hZstar hmap.aemeasurable hA hfrontier

/-- Indexed Hansen Theorem 10.5, a.e.-continuous sandwich-mapped event face. -/
theorem
    chapter10_indexed_bootstrap_ae_continuous_mapping_event_probability_of_sandwich_null_frontier
    [TopologicalSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hmap : BootstrapAEMappingPremise ν Z g)
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction F ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbabilityIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) :=
  chapter10_indexed_bootstrap_mapping_event_probability_of_sandwich_null_frontier
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g) (A := A) hZ happrox hPstar hZstar hmap.aemeasurable hA hfrontier

/-- Hansen Theorem 10.5, a.e.-continuous sandwich-mapped finite-dimensional
CDF face.

The bounded-continuous sandwich premise yields mapped weak convergence, and
the a.e.-continuity package supplies the transformed limit measurability needed
for the weak-to-CDF null-frontier bridge. -/
theorem
    chapter10_bootstrap_ae_continuous_mapping_distribution_of_sandwich_null_frontiers
    [TopologicalSpace E] [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hmap : BootstrapAEMappingPremise ν Z g)
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) :=
  chapter10_bootstrap_mapping_distribution_of_sandwich_null_frontiers
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g) hZ happrox hPstar hZstar hmap.aemeasurable hfrontier

/-- Indexed Hansen Theorem 10.5, a.e.-continuous sandwich-mapped
finite-dimensional CDF face. -/
theorem
    chapter10_indexed_bootstrap_ae_continuous_mapping_distribution_of_sandwich_null_frontiers
    [TopologicalSpace E] [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hmap : BootstrapAEMappingPremise ν Z g)
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) :=
  chapter10_indexed_bootstrap_mapping_distribution_of_sandwich_null_frontiers
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g) hZ happrox hPstar hZstar hmap.aemeasurable hfrontier

/-- Hansen Theorem 10.5, law-level null-discontinuity sandwich-mapped event
face.

This is the theorem-facing form closest to Hansen's textbook hypothesis: the
discontinuity set of `g` is null under the limit law of `Z`. The bounded
continuous sandwich premise supplies the Portmanteau approximation step for
transformed test functions. -/
theorem
    chapter10_bootstrap_law_null_disc_mapping_event_probability_of_sandwich
    [TopologicalSpace E] [MeasurableSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0)
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction F ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbability Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) :=
  chapter10_bootstrap_ae_continuous_mapping_event_probability_of_sandwich_null_frontier
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g) (A := A)
    (BootstrapAEMappingPremise.of_measurable_law_null_discontinuities
      hZlim hg hg_disc)
    hZ happrox hPstar hZstar hA hfrontier

/-- Indexed Hansen Theorem 10.5, law-level null-discontinuity sandwich-mapped
event face. -/
theorem
    chapter10_indexed_bootstrap_law_null_disc_mapping_event_probability_of_sandwich
    [TopologicalSpace E] [MeasurableSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0)
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction F ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbabilityIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) :=
  chapter10_indexed_bootstrap_ae_continuous_mapping_event_probability_of_sandwich_null_frontier
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g) (A := A)
    (BootstrapAEMappingPremise.of_measurable_law_null_discontinuities
      hZlim hg hg_disc)
    hZ happrox hPstar hZstar hA hfrontier

/-- Hansen Theorem 10.5, law-level null-discontinuity sandwich-mapped
finite-dimensional CDF face. -/
theorem
    chapter10_bootstrap_law_null_disc_mapping_distribution_of_sandwich
    [TopologicalSpace E] [MeasurableSpace E] [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0)
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) :=
  chapter10_bootstrap_ae_continuous_mapping_distribution_of_sandwich_null_frontiers
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g)
    (BootstrapAEMappingPremise.of_measurable_law_null_discontinuities
      hZlim hg hg_disc)
    hZ happrox hPstar hZstar hfrontier

/-- Indexed Hansen Theorem 10.5, law-level null-discontinuity sandwich-mapped
finite-dimensional CDF face. -/
theorem
    chapter10_indexed_bootstrap_law_null_disc_mapping_distribution_of_sandwich
    [TopologicalSpace E] [MeasurableSpace E] [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_disc : (ν.map Z) {x | ¬ ContinuousAt g x} = 0)
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) :=
  chapter10_indexed_bootstrap_ae_continuous_mapping_distribution_of_sandwich_null_frontiers
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g)
    (BootstrapAEMappingPremise.of_measurable_law_null_discontinuities
      hZlim hg hg_disc)
    hZ happrox hPstar hZstar hfrontier

/-- Hansen Theorem 10.5, law-level a.e.-continuous sandwich-mapped event face. -/
theorem
    chapter10_bootstrap_law_ae_mapping_event_probability_of_sandwich
    [TopologicalSpace E] [MeasurableSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_cont : ∀ᵐ x ∂ν.map Z, ContinuousAt g x)
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction F ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbability Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) :=
  chapter10_bootstrap_ae_continuous_mapping_event_probability_of_sandwich_null_frontier
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g) (A := A)
    (BootstrapAEMappingPremise.of_measurable_law_ae_continuous
      hZlim hg hg_cont)
    hZ happrox hPstar hZstar hA hfrontier

/-- Indexed Hansen Theorem 10.5, law-level a.e.-continuous sandwich-mapped
event face. -/
theorem
    chapter10_indexed_bootstrap_law_ae_mapping_event_probability_of_sandwich
    [TopologicalSpace E] [MeasurableSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_cont : ∀ᵐ x ∂ν.map Z, ContinuousAt g x)
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction F ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbabilityIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) :=
  chapter10_indexed_bootstrap_ae_continuous_mapping_event_probability_of_sandwich_null_frontier
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g) (A := A)
    (BootstrapAEMappingPremise.of_measurable_law_ae_continuous
      hZlim hg hg_cont)
    hZ happrox hPstar hZstar hA hfrontier

/-- Hansen Theorem 10.5, law-level a.e.-continuous sandwich-mapped
finite-dimensional CDF face. -/
theorem
    chapter10_bootstrap_law_ae_mapping_distribution_of_sandwich
    [TopologicalSpace E] [MeasurableSpace E] [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_cont : ∀ᵐ x ∂ν.map Z, ContinuousAt g x)
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) :=
  chapter10_bootstrap_ae_continuous_mapping_distribution_of_sandwich_null_frontiers
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g)
    (BootstrapAEMappingPremise.of_measurable_law_ae_continuous
      hZlim hg hg_cont)
    hZ happrox hPstar hZstar hfrontier

/-- Indexed Hansen Theorem 10.5, law-level a.e.-continuous sandwich-mapped
finite-dimensional CDF face. -/
theorem
    chapter10_indexed_bootstrap_law_ae_mapping_distribution_of_sandwich
    [TopologicalSpace E] [MeasurableSpace E] [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZlim : AEMeasurable Z ν)
    (hg : Measurable g)
    (hg_cont : ∀ᵐ x ∂ν.map Z, ContinuousAt g x)
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) :=
  chapter10_indexed_bootstrap_ae_continuous_mapping_distribution_of_sandwich_null_frontiers
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (g := g)
    (BootstrapAEMappingPremise.of_measurable_law_ae_continuous
      hZlim hg hg_cont)
    hZ happrox hPstar hZstar hfrontier

end BootstrapWeakDistribution

end HansenEconometrics
