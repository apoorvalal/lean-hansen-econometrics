import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Probability.StrongLaw

/-!
# Asymptotic utilities: WLLN wrapper and CMT for convergence in measure

This file contains small, reusable lemmas about convergence in probability
(`TendstoInMeasure`) that Hansen's Chapter 7 consistency proof needs but
Mathlib does not currently provide as named lemmas:

* `tendstoInMeasure_continuous_comp` — a **continuous-mapping theorem** for
  `TendstoInMeasure` along `atTop`. If `f n →ₚ g` and `h` is continuous then
  `h ∘ f n →ₚ h ∘ g`. Proved via Mathlib's subsequence characterization
  `exists_seq_tendstoInMeasure_atTop_iff`.
* `tendstoInMeasure_wlln` — a **weak law of large numbers** wrapper: strong
  law gives a.s. convergence, and in a finite-measure space a.s. convergence
  implies convergence in measure.
* `tendstoInMeasure_transformed_wlln` — Hansen Theorem 6.2 as a transformed
  WLLN wrapper over `tendstoInMeasure_wlln`.
* `tendstoInDistribution_continuous_comp` — Hansen Theorem 6.7 in the global
  continuous-map case, wrapping Mathlib's distributional CMT.
* `tendstoInDistribution_ae_continuous_comp` — Hansen Theorem 6.7 in its
  textbook a.s.-continuity form, proved from a Portmanteau closed-set argument.
* `TendstoInDistribution.tendsto_measure_preimage_of_null_frontier` — a
  reusable Portmanteau event-probability bridge for coverage and critical-region
  arguments.
* `TendstoInDistribution.integral_boundedContinuous_tendsto_indexed` — the
  bounded-continuous integral face of weak convergence when source spaces and
  laws vary with the sequence index.
* `cramerWold_tendstoInDistribution_indexed` — Cramér-Wold convergence for
  finite-dimensional statistics whose source spaces and laws vary with the
  sequence index.

Both are stated for general Banach-space codomains, so they specialize
directly to scalar, vector, and matrix random variables.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology MeasureTheory ProbabilityTheory Function

namespace HansenEconometrics

variable {α E F : Type*} {m : MeasurableSpace α} {μ : Measure α}

section StableInterfaces

open scoped Matrix

/-- Stable interface for an estimator or statistic with an asymptotic linear representation.

The statistic `Y` is the scaled estimator error, `A` is the fixed linear map, and `T` is the
driving score/statistic sequence. This records the reusable capability that downstream
distributional theorems need, while constructors remain responsible for proving the expansion from
finite-sample algebra, first-order conditions, or model assumptions. -/
structure AsymptoticallyLinearEstimator
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : Type*} [Fintype k]
    (Y : ℕ → Ω → k → ℝ) (A : Matrix k k ℝ) (T : ℕ → Ω → k → ℝ) where
  scaled_measurable : ∀ n, AEMeasurable (Y n) μ
  expansion : TendstoInMeasure μ (Y - fun n ω => A *ᵥ T n ω) atTop (fun _ => 0)

end StableInterfaces

section CMT

/-- **Continuous mapping theorem for convergence in probability** along `atTop`.

If a sequence `f : ℕ → α → E` of strongly measurable functions converges in
measure to `g : α → E`, and `h : E → F` is continuous, then
`fun n ω => h (f n ω)` converges in measure to `fun ω => h (g ω)`.

Proof strategy: Mathlib's `exists_seq_tendstoInMeasure_atTop_iff` says
`TendstoInMeasure ... atTop ...` is equivalent to "every subsequence has a
further subsequence that converges almost surely." Continuity lifts almost-sure
convergence directly; the iff then lifts the whole statement back to
convergence in measure. -/
theorem tendstoInMeasure_continuous_comp
    [IsFiniteMeasure μ]
    [PseudoEMetricSpace E] [PseudoEMetricSpace F] [TopologicalSpace.PseudoMetrizableSpace F]
    {f : ℕ → α → E} {g : α → E} {h : E → F}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfg : TendstoInMeasure μ f atTop g)
    (hh : Continuous h) :
    TendstoInMeasure μ (fun n ω => h (f n ω)) atTop (fun ω => h (g ω)) := by
  have hhf : ∀ n, AEStronglyMeasurable (fun ω => h (f n ω)) μ :=
    fun n => hh.comp_aestronglyMeasurable (hf n)
  rw [exists_seq_tendstoInMeasure_atTop_iff hhf]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ := (exists_seq_tendstoInMeasure_atTop_iff hf).mp hfg ns hns
  refine ⟨ns', hns', ?_⟩
  filter_upwards [hae] with ω hω
  exact (hh.tendsto _).comp hω

/-- **Local continuous mapping theorem for convergence in probability to a constant.**

If `f n →ₚ x` and `h` is continuous at `x`, then `h (f n) →ₚ h x`, provided
the composed sequence is a.e. strongly measurable. The explicit measurability
premise is necessary because continuity at one point does not imply global
measurability of `h`. -/
theorem tendstoInMeasure_continuousAt_const_comp
    [IsFiniteMeasure μ]
    [PseudoEMetricSpace E] [PseudoEMetricSpace F] [TopologicalSpace.PseudoMetrizableSpace F]
    {f : ℕ → α → E} {x : E} {h : E → F}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hhf : ∀ n, AEStronglyMeasurable (fun ω => h (f n ω)) μ)
    (hfx : TendstoInMeasure μ f atTop (fun _ => x))
    (hh : ContinuousAt h x) :
    TendstoInMeasure μ (fun n ω => h (f n ω)) atTop (fun _ => h x) := by
  rw [exists_seq_tendstoInMeasure_atTop_iff hhf]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ := (exists_seq_tendstoInMeasure_atTop_iff hf).mp hfx ns hns
  refine ⟨ns', hns', ?_⟩
  filter_upwards [hae] with ω hω
  exact hh.tendsto.comp hω

/-- **Hansen Theorem 6.7, global continuous-mapping theorem in distribution.**

If `Xₙ ⇒ Z` and `g` is globally continuous, then `g(Xₙ) ⇒ g(Z)`. This is the
Mathlib-backed global-continuity face of Hansen's distributional CMT; see
`tendstoInDistribution_ae_continuous_comp` for the textbook a.s.-continuity
form. -/
theorem tendstoInDistribution_continuous_comp
    {Ω Ω' E F : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    {X : ℕ → Ω → E} {Z : Ω' → E} {g : E → F}
    (hX : TendstoInDistribution X atTop Z P ν) (hg : Continuous g) :
    TendstoInDistribution (fun n ω => g (X n ω)) atTop (fun ω => g (Z ω)) P ν := by
  simpa [Function.comp_def] using hX.continuous_comp hg

/-- **Push-forward CMT for maps continuous outside a limit-null set.**

If probability laws `νs` converge weakly to `ν`, and a measurable map `g` is
continuous away from a `ν`-null set `D`, then the push-forward laws converge
weakly.  This is the probability-measure core of Hansen's a.s.-continuity
continuous-mapping theorem.

The proof is the standard Portmanteau closed-set argument: for closed `C`, the
closure of `g ⁻¹' C` is contained in `g ⁻¹' C ∪ D`; weak convergence controls
the closed closure, and the null set removes the discontinuity contribution. -/
theorem probabilityMeasure_tendsto_map_of_tendsto_of_ae_continuous
    {ι E F : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    {νs : ι → ProbabilityMeasure E} {ν : ProbabilityMeasure E}
    (hν : Tendsto νs L (𝓝 ν))
    {g : E → F} (hg : Measurable g) {D : Set E}
    (hD : (ν : Measure E) D = 0)
    (hcont : ∀ x, x ∉ D → ContinuousAt g x) :
    Tendsto (fun i => (νs i).map (hg.aemeasurable : AEMeasurable g (νs i)))
      L (𝓝 (ν.map (hg.aemeasurable : AEMeasurable g ν))) := by
  refine tendsto_of_forall_isClosed_limsup_le' ?_
  intro C hC
  let A : Set E := g ⁻¹' C
  have hclosure_subset : closure A ⊆ A ∪ D := by
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inr hxD
    · left
      have hxC_closure : g x ∈ closure C :=
        (hcont x hxD).continuousWithinAt.mem_closure hx (by intro y hy; exact hy)
      exact hC.closure_subset hxC_closure
  have hpre_le :
      (fun i => ((νs i).map (hg.aemeasurable : AEMeasurable g (νs i)) : Measure F) C)
        ≤ᶠ[L] fun i => (νs i : Measure E) (closure A) := by
    refine Filter.Eventually.of_forall ?_
    intro i
    change ((νs i : Measure E).map g) C ≤ (νs i : Measure E) (closure A)
    rw [Measure.map_apply_of_aemeasurable (hg.aemeasurable : AEMeasurable g (νs i))
      hC.measurableSet]
    exact measure_mono subset_closure
  have hclosed_bound :
      L.limsup (fun i => (νs i : Measure E) (closure A)) ≤
        (ν : Measure E) (closure A) :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hν isClosed_closure
  have hlimit_le : (ν : Measure E) (closure A) ≤ (ν : Measure E) A := by
    calc
      (ν : Measure E) (closure A) ≤ (ν : Measure E) (A ∪ D) :=
        measure_mono hclosure_subset
      _ ≤ (ν : Measure E) A + (ν : Measure E) D := measure_union_le A D
      _ = (ν : Measure E) A := by simp [hD]
  calc
    L.limsup
        (fun i => ((νs i).map (hg.aemeasurable : AEMeasurable g (νs i)) : Measure F) C)
        ≤ L.limsup (fun i => (νs i : Measure E) (closure A)) :=
          limsup_le_limsup hpre_le
    _ ≤ (ν : Measure E) (closure A) := hclosed_bound
    _ ≤ (ν : Measure E) A := hlimit_le
    _ = ((ν.map (hg.aemeasurable : AEMeasurable g ν) : ProbabilityMeasure F) : Measure F) C := by
      change (ν : Measure E) A = ((ν : Measure E).map g) C
      rw [Measure.map_apply_of_aemeasurable (hg.aemeasurable : AEMeasurable g ν)
        hC.measurableSet]

/-- **Hansen Theorem 6.7, a.s.-continuity CMT in distribution.**

If `Xₙ ⇒ Z` and a measurable map `g` is continuous off a set with zero
limit-law probability, then `g(Xₙ) ⇒ g(Z)`.  This is the textbook
a.s.-continuity face of the continuous-mapping theorem; the null set is stated
on the law of `Z`, i.e. `(ν.map Z) D = 0`. -/
theorem tendstoInDistribution_ae_continuous_comp
    {Ω Ω' E F : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    {X : ℕ → Ω → E} {Z : Ω' → E} {g : E → F}
    (hX : TendstoInDistribution X atTop Z P ν)
    (hg : Measurable g) {D : Set E}
    (hD : (ν.map Z) D = 0)
    (hcont : ∀ x, x ∉ D → ContinuousAt g x) :
    TendstoInDistribution (fun n ω => g (X n ω)) atTop (fun ω => g (Z ω)) P ν := by
  have hcomp :
      TendstoInDistribution (fun n => g ∘ X n) atTop (g ∘ Z) P ν := by
    refine ⟨?_, ?_, ?_⟩
    · intro n
      exact hg.comp_aemeasurable (hX.forall_aemeasurable n)
    · exact hg.comp_aemeasurable hX.aemeasurable_limit
    let law : ℕ → ProbabilityMeasure E := fun n =>
      ⟨(P n).map (X n), Measure.isProbabilityMeasure_map (hX.forall_aemeasurable n)⟩
    let lawZ : ProbabilityMeasure E :=
      ⟨ν.map Z, Measure.isProbabilityMeasure_map hX.aemeasurable_limit⟩
    have hmap :=
      probabilityMeasure_tendsto_map_of_tendsto_of_ae_continuous
        (νs := law) (ν := lawZ) (L := atTop) hX.tendsto hg
        (by simpa [lawZ] using hD) hcont
    convert hmap with n
    · simp only [law, ProbabilityMeasure.map, ProbabilityMeasure.coe_mk, Subtype.mk.injEq]
      rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable (hX.forall_aemeasurable n)]
    · apply ProbabilityMeasure.toMeasure_injective
      simp only [lawZ, ProbabilityMeasure.map, ProbabilityMeasure.coe_mk]
      rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hX.aemeasurable_limit]
  simpa [Function.comp_def] using hcomp

/-- **Portmanteau lower-bound wrapper for bounded continuous moments.**

If `Xₙ ⇒ Z`, then every nonnegative bounded continuous test function has
limit-law expectation bounded by the liminf of the sequence expectations. This
is the weak-convergence-facing core behind Hansen Theorems 6.13 and 6.15; the
unbounded norm and uniform-integrability wrappers build on this Portmanteau
direction. -/
theorem TendstoInDistribution.integral_boundedContinuous_nonneg_le_liminf
    {Ω Ω' E : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E]
    {X : ℕ → Ω → E} {Z : Ω' → E}
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (f : BoundedContinuousFunction E ℝ) (hf_nonneg : 0 ≤ f) :
    ∫ ω, f (Z ω) ∂ν ≤
      atTop.liminf (fun n => ∫ ω, f (X n ω) ∂μ) := by
  let law : ℕ → ProbabilityMeasure E := fun n =>
    ⟨μ.map (X n), Measure.isProbabilityMeasure_map (hX.forall_aemeasurable n)⟩
  let lawZ : ProbabilityMeasure E :=
    ⟨ν.map Z, Measure.isProbabilityMeasure_map hX.aemeasurable_limit⟩
  have hlaw : Tendsto law atTop (𝓝 lawZ) := by
    simpa [law, lawZ] using hX.tendsto
  haveI : ∀ n, IsProbabilityMeasure (μ.map (X n)) :=
    fun n => Measure.isProbabilityMeasure_map (hX.forall_aemeasurable n)
  have hopens : ∀ G : Set E, IsOpen G →
      (ν.map Z) G ≤ atTop.liminf (fun n => (μ.map (X n)) G) := by
    intro G hG
    simpa [law, lawZ] using
      (ProbabilityMeasure.le_liminf_measure_open_of_tendsto
        (μs_lim := hlaw) (G_open := hG))
  have hlower :
      ∫ x, f x ∂(ν.map Z) ≤
        atTop.liminf (fun n => ∫ x, f x ∂(μ.map (X n))) :=
    integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure
      (μ := ν.map Z) (μs := fun n => μ.map (X n))
      (f := f) hf_nonneg hopens
  have hlimit :
      ∫ x, f x ∂(ν.map Z) = ∫ ω, f (Z ω) ∂ν := by
    rw [integral_map hX.aemeasurable_limit (by fun_prop)]
  have hseq :
      (fun n => ∫ x, f x ∂(μ.map (X n))) =
        fun n => ∫ ω, f (X n ω) ∂μ := by
    funext n
    rw [integral_map (hX.forall_aemeasurable n) (by fun_prop)]
  simpa [hlimit, hseq] using hlower

/-- **Hansen Theorem 6.13, bounded continuous weak-moment face.**

If `Xₙ ⇒ Z` and the expectations of a nonnegative bounded continuous transform
are eventually bounded by `C`, then the limit-law expectation of the same
transform is bounded by `C`. This is the direct bounded-continuous Portmanteau
face of bounded first moments passing to the weak limit. -/
theorem TendstoInDistribution.integral_boundedContinuous_nonneg_limit_le_of_eventually_bound
    {Ω Ω' E : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [HasOuterApproxClosed E]
    {X : ℕ → Ω → E} {Z : Ω' → E}
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (f : BoundedContinuousFunction E ℝ) (hf_nonneg : 0 ≤ f) {C : ℝ}
    (hBound : ∀ᶠ n in atTop, ∫ ω, f (X n ω) ∂μ ≤ C) :
    ∫ ω, f (Z ω) ∂ν ≤ C := by
  have hlower :=
    TendstoInDistribution.integral_boundedContinuous_nonneg_le_liminf
      (μ := μ) (ν := ν) (X := X) (Z := Z) hX f hf_nonneg
  have hliminf_le :
      atTop.liminf (fun n => ∫ ω, f (X n ω) ∂μ) ≤ C := by
    have hbelow : atTop.IsBoundedUnder (fun x y : ℝ => x ≥ y)
        (fun n => ∫ ω, f (X n ω) ∂μ) :=
      isBoundedUnder_of_eventually_ge
        (Eventually.of_forall fun n => integral_nonneg (fun ω => hf_nonneg (X n ω)))
    refine liminf_le_of_le hbelow ?_
    intro b hb
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hb.and hBound)
    exact ((hN N le_rfl).1).trans ((hN N le_rfl).2)
  exact hlower.trans hliminf_le

/-- Bounded continuous truncation of the norm: `x ↦ min ‖x‖ R`.

The nonnegative bound `hR` is included so the function has range in `[0, R]`.
This is the truncation used for the weak-convergence-facing bounded-moment
layer in Hansen Theorem 6.13. -/
noncomputable def normTruncBoundedContinuousFunction
    (E : Type*) [SeminormedAddCommGroup E] (R : ℝ) (hR : 0 ≤ R) :
    BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.mkOfBound (α := E) (β := ℝ)
    ⟨fun x : E => min ‖x‖ R, continuous_norm.min continuous_const⟩ R
    (fun x y => by
      rw [Real.dist_eq]
      change |min ‖x‖ R - min ‖y‖ R| ≤ R
      have hx0 : 0 ≤ min ‖x‖ R := le_min (norm_nonneg x) hR
      have hy0 : 0 ≤ min ‖y‖ R := le_min (norm_nonneg y) hR
      have hxR : min ‖x‖ R ≤ R := min_le_right _ _
      have hyR : min ‖y‖ R ≤ R := min_le_right _ _
      exact abs_le.mpr ⟨by linarith, by linarith⟩)

@[simp]
theorem normTruncBoundedContinuousFunction_apply
    {E : Type*} [SeminormedAddCommGroup E] {R : ℝ} (hR : 0 ≤ R) (x : E) :
    normTruncBoundedContinuousFunction E R hR x = min ‖x‖ R :=
  rfl

/-- The norm truncation is nonnegative. -/
theorem normTruncBoundedContinuousFunction_nonneg
    {E : Type*} [SeminormedAddCommGroup E] {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ normTruncBoundedContinuousFunction E R hR :=
  fun x => by
    change (0 : ℝ) ≤ normTruncBoundedContinuousFunction E R hR x
    rw [normTruncBoundedContinuousFunction_apply]
    exact le_min (norm_nonneg x) hR

/-- The norm truncation is bounded above by the norm. -/
theorem normTruncBoundedContinuousFunction_le_norm
    {E : Type*} [SeminormedAddCommGroup E] {R : ℝ} (hR : 0 ≤ R) (x : E) :
    normTruncBoundedContinuousFunction E R hR x ≤ ‖x‖ := by
  rw [normTruncBoundedContinuousFunction_apply]
  exact min_le_left _ _

/-- **Hansen Theorem 6.13, norm-truncation weak-moment layer.**

If `Xₙ ⇒ Z` and the expected norms of `Xₙ` are eventually bounded by `C`, then
every bounded continuous norm truncation of the limit has expectation at most
`C`. This is the reusable truncation step toward the textbook unbounded norm
statement. -/
theorem TendstoInDistribution.integral_normTrunc_limit_le_of_eventually_integral_norm_bound
    {Ω Ω' E : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    [SeminormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [BorelSpace E] [HasOuterApproxClosed E]
    {X : ℕ → Ω → E} {Z : Ω' → E}
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    {C R : ℝ} (hR : 0 ≤ R)
    (hBound : ∀ᶠ n in atTop,
      Integrable (fun ω => ‖X n ω‖) μ ∧ ∫ ω, ‖X n ω‖ ∂μ ≤ C) :
    ∫ ω, normTruncBoundedContinuousFunction E R hR (Z ω) ∂ν ≤ C := by
  let f := normTruncBoundedContinuousFunction E R hR
  have hfBound : ∀ᶠ n in atTop, ∫ ω, f (X n ω) ∂μ ≤ C := by
    filter_upwards [hBound] with n hn
    have hf_map_int : Integrable f (μ.map (X n)) :=
      f.integrable (μ := μ.map (X n))
    have hf_int : Integrable (fun ω => f (X n ω)) μ := by
      simpa [Function.comp_def] using
        hf_map_int.comp_aemeasurable (hX.forall_aemeasurable n)
    have hle : ∫ ω, f (X n ω) ∂μ ≤ ∫ ω, ‖X n ω‖ ∂μ :=
      integral_mono hf_int hn.1
        (fun ω => normTruncBoundedContinuousFunction_le_norm hR (X n ω))
    exact hle.trans hn.2
  exact TendstoInDistribution.integral_boundedContinuous_nonneg_limit_le_of_eventually_bound
    (μ := μ) (ν := ν) (X := X) (Z := Z) hX f
    (normTruncBoundedContinuousFunction_nonneg hR) hfBound

/-- **Hansen Theorem 6.13, limit-integrability weak-moment face.**

If `Xₙ ⇒ Z` and the expected norms of `Xₙ` are eventually bounded by `C`, then
the limit-law norm is integrable. The proof bounds all bounded continuous norm
truncations and passes to the monotone limit at the `lintegral` level. -/
theorem TendstoInDistribution.integrable_norm_limit_of_eventually_integral_norm_bound
    {Ω Ω' E : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    [SeminormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [BorelSpace E] [HasOuterApproxClosed E]
    {X : ℕ → Ω → E} {Z : Ω' → E}
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    {C : ℝ}
    (hBound : ∀ᶠ n in atTop,
      Integrable (fun ω => ‖X n ω‖) μ ∧ ∫ ω, ‖X n ω‖ ∂μ ≤ C) :
    Integrable (fun ω => ‖Z ω‖) ν := by
  have htrunc_bound :
      ∀ n : ℕ, ∫ ω, min ‖Z ω‖ (n : ℝ) ∂ν ≤ C := by
    intro n
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    simpa [normTruncBoundedContinuousFunction_apply] using
      TendstoInDistribution.integral_normTrunc_limit_le_of_eventually_integral_norm_bound
        (μ := μ) (ν := ν) (X := X) (Z := Z) hX hn_nonneg hBound
  have hnorm_aemeas : AEMeasurable (fun ω => ‖Z ω‖) ν :=
    continuous_norm.measurable.comp_aemeasurable hX.aemeasurable_limit
  have htrunc_int :
      ∀ n : ℕ, Integrable (fun ω => min ‖Z ω‖ (n : ℝ)) ν := by
    intro n
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    let f := normTruncBoundedContinuousFunction E (n : ℝ) hn_nonneg
    have hf_map_int : Integrable f (ν.map Z) :=
      f.integrable (μ := ν.map Z)
    have hf_int : Integrable (fun ω => f (Z ω)) ν := by
      simpa [Function.comp_def] using
        hf_map_int.comp_aemeasurable hX.aemeasurable_limit
    simpa [f, normTruncBoundedContinuousFunction_apply] using hf_int
  have htrunc_lintegral_bound :
      ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (min ‖Z ω‖ (n : ℝ)) ∂ν ≤ ENNReal.ofReal C := by
    intro n
    have hnn : 0 ≤ᵐ[ν] fun ω => min ‖Z ω‖ (n : ℝ) :=
      ae_of_all ν (fun ω => le_min (norm_nonneg _) (by positivity))
    rw [← ofReal_integral_eq_lintegral_ofReal (htrunc_int n) hnn]
    exact ENNReal.ofReal_le_ofReal (htrunc_bound n)
  have htrunc_lintegral_tendsto :
      Tendsto
        (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (min ‖Z ω‖ (n : ℝ)) ∂ν)
        atTop (𝓝 (∫⁻ ω, ENNReal.ofReal ‖Z ω‖ ∂ν)) := by
    refine lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
    · intro n
      exact (hnorm_aemeas.min aemeasurable_const).ennreal_ofReal
    · exact ae_of_all ν (fun ω => by
        intro n m hnm
        exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (by exact_mod_cast hnm)))
    · exact ae_of_all ν (fun ω => by
        have hreal :
            Tendsto (fun n : ℕ => min ‖Z ω‖ (n : ℝ)) atTop (𝓝 ‖Z ω‖) := by
          have hcast : ∀ᶠ n : ℕ in atTop, ‖Z ω‖ ≤ (n : ℝ) :=
            (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
              (eventually_ge_atTop (‖Z ω‖))
          have heq :
              (fun n : ℕ => min ‖Z ω‖ (n : ℝ)) =ᶠ[atTop] fun _ => ‖Z ω‖ := by
            filter_upwards [hcast] with n hn
            exact min_eq_left hn
          rw [tendsto_congr' heq]
          exact tendsto_const_nhds
        exact ENNReal.tendsto_ofReal hreal)
  have hlimit_lintegral_bound :
      ∫⁻ ω, ENNReal.ofReal ‖Z ω‖ ∂ν ≤ ENNReal.ofReal C :=
    le_of_tendsto' htrunc_lintegral_tendsto htrunc_lintegral_bound
  refine ⟨?_, ?_⟩
  · rw [aestronglyMeasurable_iff_aemeasurable]
    exact hnorm_aemeas
  · rw [hasFiniteIntegral_iff_ofReal (ae_of_all ν (fun ω => norm_nonneg (Z ω)))]
    exact hlimit_lintegral_bound.trans_lt ENNReal.ofReal_lt_top

/-- **Hansen Theorem 6.13, integrable-limit norm weak-moment face.**

If `Xₙ ⇒ Z`, the expected norms of `Xₙ` are eventually bounded by `C`, and the
limit norm is integrable, then the limit-law expected norm is at most `C`. The
proof applies the norm-truncation bound for every truncation level and then
uses monotone convergence. -/
theorem TendstoInDistribution.integral_norm_limit_le_of_eventually_integral_norm_bound_of_integrable
    {Ω Ω' E : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    [SeminormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [BorelSpace E] [HasOuterApproxClosed E]
    {X : ℕ → Ω → E} {Z : Ω' → E}
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    {C : ℝ}
    (hBound : ∀ᶠ n in atTop,
      Integrable (fun ω => ‖X n ω‖) μ ∧ ∫ ω, ‖X n ω‖ ∂μ ≤ C)
    (hZNorm : Integrable (fun ω => ‖Z ω‖) ν) :
    ∫ ω, ‖Z ω‖ ∂ν ≤ C := by
  have htrunc_bound :
      ∀ n : ℕ, ∫ ω, min ‖Z ω‖ (n : ℝ) ∂ν ≤ C := by
    intro n
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    simpa [normTruncBoundedContinuousFunction_apply] using
      TendstoInDistribution.integral_normTrunc_limit_le_of_eventually_integral_norm_bound
        (μ := μ) (ν := ν) (X := X) (Z := Z) hX hn_nonneg hBound
  have htrunc_tendsto :
      Tendsto (fun n : ℕ => ∫ ω, min ‖Z ω‖ (n : ℝ) ∂ν) atTop
        (𝓝 (∫ ω, ‖Z ω‖ ∂ν)) := by
    refine integral_tendsto_of_tendsto_of_monotone ?_ hZNorm ?_ ?_
    · intro n
      refine hZNorm.mono' ?_ ?_
      · rw [aestronglyMeasurable_iff_aemeasurable]
        exact hZNorm.aestronglyMeasurable.aemeasurable.min aemeasurable_const
      · exact ae_of_all ν (fun ω => by
          have hnonneg : 0 ≤ min ‖Z ω‖ (n : ℝ) :=
            le_min (norm_nonneg _) (by positivity)
          rw [Real.norm_of_nonneg hnonneg]
          exact min_le_left _ _)
    · exact ae_of_all ν (fun ω => by
        intro n m hnm
        exact min_le_min le_rfl (by exact_mod_cast hnm))
    · exact ae_of_all ν (fun ω => by
        have hcast : ∀ᶠ n : ℕ in atTop, ‖Z ω‖ ≤ (n : ℝ) :=
          (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
            (eventually_ge_atTop (‖Z ω‖))
        have heq :
            (fun n : ℕ => min ‖Z ω‖ (n : ℝ)) =ᶠ[atTop] fun _ => ‖Z ω‖ := by
          filter_upwards [hcast] with n hn
          exact min_eq_left hn
        rw [tendsto_congr' heq]
        exact tendsto_const_nhds)
  exact le_of_tendsto' htrunc_tendsto htrunc_bound

/-- **Hansen Theorem 6.13, weak-convergence bounded first moments pass to the limit.**

If `Xₙ ⇒ Z` and the expected norms of `Xₙ` are eventually bounded by `C`, then
the limit-law expected norm is at most `C`. -/
theorem TendstoInDistribution.integral_norm_limit_le_of_eventually_integral_norm_bound
    {Ω Ω' E : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    [SeminormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [BorelSpace E] [HasOuterApproxClosed E]
    {X : ℕ → Ω → E} {Z : Ω' → E}
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    {C : ℝ}
    (hBound : ∀ᶠ n in atTop,
      Integrable (fun ω => ‖X n ω‖) μ ∧ ∫ ω, ‖X n ω‖ ∂μ ≤ C) :
    ∫ ω, ‖Z ω‖ ∂ν ≤ C := by
  have hZNorm :
      Integrable (fun ω => ‖Z ω‖) ν :=
    TendstoInDistribution.integrable_norm_limit_of_eventually_integral_norm_bound
      (μ := μ) (ν := ν) (X := X) (Z := Z) hX hBound
  exact
    TendstoInDistribution.integral_norm_limit_le_of_eventually_integral_norm_bound_of_integrable
      (μ := μ) (ν := ν) (X := X) (Z := Z) hX hBound hZNorm

/-- Real identity clipped to `[-R, R]`. -/
def realClip (R x : ℝ) : ℝ :=
  max (-R) (min x R)

/-- Bounded continuous clipping of the real identity to `[-R, R]`. -/
noncomputable def realClipBoundedContinuousFunction (R : ℝ) (hR : 0 ≤ R) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound (α := ℝ) (β := ℝ)
    ⟨realClip R, by
      simpa [realClip] using
        (continuous_const.max (continuous_id.min continuous_const) : Continuous
          (fun x : ℝ => max (-R) (min x R)))⟩ (2 * R)
    (fun x y => by
      rw [Real.dist_eq]
      change |max (-R) (min x R) - max (-R) (min y R)| ≤ 2 * R
      have hx_lo : -R ≤ max (-R) (min x R) := le_max_left _ _
      have hy_lo : -R ≤ max (-R) (min y R) := le_max_left _ _
      have hx_hi : max (-R) (min x R) ≤ R :=
        max_le (by linarith) (min_le_right _ _)
      have hy_hi : max (-R) (min y R) ≤ R :=
        max_le (by linarith) (min_le_right _ _)
      exact abs_le.mpr ⟨by linarith, by linarith⟩)

@[simp]
theorem realClipBoundedContinuousFunction_apply {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    realClipBoundedContinuousFunction R hR x = realClip R x :=
  rfl

/-- Real clipping agrees with the identity inside the clipping interval. -/
theorem realClip_eq_self_of_abs_le {R x : ℝ} (hx : |x| ≤ R) :
    realClip R x = x := by
  have hx_interval := abs_le.mp hx
  rw [realClip, min_eq_left hx_interval.2, max_eq_right hx_interval.1]

/-- Real clipping agrees with the identity inside the clipping interval. -/
theorem realClipBoundedContinuousFunction_eq_self_of_abs_le
    {R x : ℝ} (hR : 0 ≤ R) (hx : |x| ≤ R) :
    realClipBoundedContinuousFunction R hR x = x := by
  rw [realClipBoundedContinuousFunction_apply, realClip_eq_self_of_abs_le hx]

/-- The clipped value stays in absolute value below the clipping radius. -/
theorem abs_realClip_le (R x : ℝ) (hR : 0 ≤ R) :
    |realClip R x| ≤ R := by
  have hlo : -R ≤ realClip R x := by
    rw [realClip]
    exact le_max_left _ _
  have hhi : realClip R x ≤ R := by
    rw [realClip]
    exact max_le (by linarith) (min_le_right _ _)
  exact abs_le.mpr ⟨hlo, hhi⟩

/-- Clipping cannot increase absolute value when the clipping radius is nonnegative. -/
theorem abs_realClip_le_abs (R x : ℝ) (hR : 0 ≤ R) :
    |realClip R x| ≤ |x| := by
  by_cases hx : |x| ≤ R
  · rw [realClip_eq_self_of_abs_le hx]
  · exact (abs_realClip_le R x hR).trans (le_of_lt (lt_of_not_ge hx))

/-- The clipping error is supported on the large-tail event, up to a factor two. -/
theorem abs_sub_realClip_le_two_mul_tail_abs (R x : ℝ) (hR : 0 ≤ R) :
    |x - realClip R x| ≤
      2 * Set.indicator {y : ℝ | R ≤ |y|} (fun y => |y|) x := by
  by_cases htail : x ∈ {y : ℝ | R ≤ |y|}
  · rw [Set.indicator_of_mem htail]
    calc
      |x - realClip R x| ≤ |x| + |realClip R x| := by
        simpa [sub_eq_add_neg] using abs_add_le x (-(realClip R x))
      _ ≤ |x| + |x| := by
        linarith [abs_realClip_le_abs R x hR]
      _ = 2 * |x| := by ring
  · rw [Set.indicator_of_notMem htail]
    have hx : |x| ≤ R := le_of_not_ge htail
    rw [realClip_eq_self_of_abs_le hx, sub_self, abs_zero, mul_zero]

/-- Integral tail bound for replacing an integrable real variable by its clip. -/
theorem abs_integral_sub_realClip_le_two_mul_integral_tail_abs
    [IsFiniteMeasure μ] {Y : α → ℝ} (hY : Integrable Y μ) {R : ℝ} (hR : 0 ≤ R) :
    |(∫ ω, Y ω ∂μ) - ∫ ω, realClip R (Y ω) ∂μ| ≤
      2 * ∫ ω, Set.indicator {ω | R ≤ |Y ω|} (fun ω => |Y ω|) ω ∂μ := by
  let clip := realClipBoundedContinuousFunction R hR
  have hclip_int : Integrable (fun ω => realClip R (Y ω)) μ := by
    have hmap : Integrable clip (μ.map Y) := clip.integrable (μ := μ.map Y)
    simpa [clip, Function.comp_def, realClipBoundedContinuousFunction_apply] using
      hmap.comp_aemeasurable hY.aemeasurable
  have htail_null : NullMeasurableSet {ω | R ≤ |Y ω|} μ :=
    nullMeasurableSet_le aemeasurable_const
      (continuous_abs.measurable.comp_aemeasurable hY.aemeasurable)
  have htail_int :
      Integrable (Set.indicator {ω | R ≤ |Y ω|} (fun ω => |Y ω|)) μ := by
    simpa [Real.norm_eq_abs] using hY.norm.indicator₀ htail_null
  have hmono :
      ∫ ω, |Y ω - realClip R (Y ω)| ∂μ ≤
        ∫ ω, 2 * Set.indicator {ω | R ≤ |Y ω|} (fun ω => |Y ω|) ω ∂μ := by
    refine integral_mono (hY.sub hclip_int).norm (htail_int.const_mul 2) ?_
    intro ω
    exact abs_sub_realClip_le_two_mul_tail_abs R (Y ω) hR
  calc
    |(∫ ω, Y ω ∂μ) - ∫ ω, realClip R (Y ω) ∂μ| =
        |∫ ω, Y ω - realClip R (Y ω) ∂μ| := by
      rw [integral_sub hY hclip_int]
    _ ≤ ∫ ω, |Y ω - realClip R (Y ω)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, 2 * Set.indicator {ω | R ≤ |Y ω|} (fun ω => |Y ω|) ω ∂μ := hmono
    _ = 2 * ∫ ω, Set.indicator {ω | R ≤ |Y ω|} (fun ω => |Y ω|) ω ∂μ := by
      rw [integral_const_mul]

/-- The squared clipping error is supported on the large-tail event, up to a factor two. -/
theorem abs_sq_sub_realClip_sq_le_two_mul_tail_sq (R x : ℝ) (hR : 0 ≤ R) :
    |x ^ 2 - (realClip R x) ^ 2| ≤
      2 * Set.indicator {y : ℝ | R ≤ |y|} (fun y => y ^ 2) x := by
  by_cases htail : x ∈ {y : ℝ | R ≤ |y|}
  · rw [Set.indicator_of_mem htail]
    have htri :
        |x ^ 2 - (realClip R x) ^ 2| ≤ |x ^ 2| + |(realClip R x) ^ 2| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (x ^ 2) (-((realClip R x) ^ 2))
    have hclip_abs : |realClip R x| ≤ |x| := abs_realClip_le_abs R x hR
    have hclip_sq : (realClip R x) ^ 2 ≤ x ^ 2 := by
      have hpow := pow_le_pow_left₀ (abs_nonneg _) hclip_abs 2
      simpa [sq_abs] using hpow
    calc
      |x ^ 2 - (realClip R x) ^ 2| ≤ |x ^ 2| + |(realClip R x) ^ 2| := htri
      _ = x ^ 2 + (realClip R x) ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg x), abs_of_nonneg (sq_nonneg (realClip R x))]
      _ ≤ x ^ 2 + x ^ 2 := by nlinarith
      _ = 2 * x ^ 2 := by ring
  · rw [Set.indicator_of_notMem htail]
    have hx : |x| ≤ R := le_of_not_ge htail
    rw [realClip_eq_self_of_abs_le hx, sub_self, abs_zero, mul_zero]

/-- Integral tail bound for replacing a square-integrable real variable's
second moment by its clipped second moment. -/
theorem abs_integral_sq_sub_realClip_sq_le_two_mul_integral_tail_sq
    [IsFiniteMeasure μ] {Y : α → ℝ} (hY : MemLp Y 2 μ) {R : ℝ} (hR : 0 ≤ R) :
    |(∫ ω, (Y ω) ^ 2 ∂μ) - ∫ ω, (realClip R (Y ω)) ^ 2 ∂μ| ≤
      2 * ∫ ω, Set.indicator {ω | R ≤ |Y ω|} (fun ω => (Y ω) ^ 2) ω ∂μ := by
  let clipSq := (realClipBoundedContinuousFunction R hR) ^ (2 : ℕ)
  have hYsq_int : Integrable (fun ω => (Y ω) ^ 2) μ := hY.integrable_sq
  have hclip_int : Integrable (fun ω => (realClip R (Y ω)) ^ 2) μ := by
    have hmap : Integrable clipSq (μ.map Y) := clipSq.integrable (μ := μ.map Y)
    simpa [clipSq, Function.comp_def, realClipBoundedContinuousFunction_apply] using
      hmap.comp_aemeasurable hY.aestronglyMeasurable.aemeasurable
  have htail_null : NullMeasurableSet {ω | R ≤ |Y ω|} μ :=
    nullMeasurableSet_le aemeasurable_const
      (continuous_abs.measurable.comp_aemeasurable hY.aestronglyMeasurable.aemeasurable)
  have htail_int :
      Integrable (Set.indicator {ω | R ≤ |Y ω|} (fun ω => (Y ω) ^ 2)) μ :=
    hYsq_int.indicator₀ htail_null
  have hmono :
      ∫ ω, |(Y ω) ^ 2 - (realClip R (Y ω)) ^ 2| ∂μ ≤
        ∫ ω, 2 * Set.indicator {ω | R ≤ |Y ω|} (fun ω => (Y ω) ^ 2) ω ∂μ := by
    refine integral_mono (hYsq_int.sub hclip_int).norm (htail_int.const_mul 2) ?_
    intro ω
    exact abs_sq_sub_realClip_sq_le_two_mul_tail_sq R (Y ω) hR
  calc
    |(∫ ω, (Y ω) ^ 2 ∂μ) - ∫ ω, (realClip R (Y ω)) ^ 2 ∂μ| =
        |∫ ω, (Y ω) ^ 2 - (realClip R (Y ω)) ^ 2 ∂μ| := by
      rw [integral_sub hYsq_int hclip_int]
    _ ≤ ∫ ω, |(Y ω) ^ 2 - (realClip R (Y ω)) ^ 2| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, 2 * Set.indicator {ω | R ≤ |Y ω|} (fun ω => (Y ω) ^ 2) ω ∂μ := hmono
    _ = 2 * ∫ ω, Set.indicator {ω | R ≤ |Y ω|} (fun ω => (Y ω) ^ 2) ω ∂μ := by
      rw [integral_const_mul]

/-- For thresholds at least one, the absolute tail integral is bounded by the
squared tail integral. -/
theorem integral_tail_abs_le_integral_tail_sq_of_one_le
    [IsFiniteMeasure μ] {Y : α → ℝ} (hY : MemLp Y 2 μ) {R : ℝ} (hR : 1 ≤ R) :
    ∫ ω, Set.indicator {ω | R ≤ |Y ω|} (fun ω => |Y ω|) ω ∂μ ≤
      ∫ ω, Set.indicator {ω | R ≤ |Y ω|} (fun ω => (Y ω) ^ 2) ω ∂μ := by
  have hY_int : Integrable Y μ :=
    memLp_one_iff_integrable.mp (hY.mono_exponent one_le_two)
  have hYsq_int : Integrable (fun ω => (Y ω) ^ 2) μ := hY.integrable_sq
  have htail_null : NullMeasurableSet {ω | R ≤ |Y ω|} μ :=
    nullMeasurableSet_le aemeasurable_const
      (continuous_abs.measurable.comp_aemeasurable hY.aestronglyMeasurable.aemeasurable)
  have htail_abs_int :
      Integrable (Set.indicator {ω | R ≤ |Y ω|} (fun ω => |Y ω|)) μ := by
    simpa [Real.norm_eq_abs] using hY_int.norm.indicator₀ htail_null
  have htail_sq_int :
      Integrable (Set.indicator {ω | R ≤ |Y ω|} (fun ω => (Y ω) ^ 2)) μ :=
    hYsq_int.indicator₀ htail_null
  refine integral_mono htail_abs_int htail_sq_int ?_
  intro ω
  by_cases htail : R ≤ |Y ω|
  · have hone : 1 ≤ |Y ω| := hR.trans htail
    have hle : |Y ω| ≤ (Y ω) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hone (abs_nonneg (Y ω))
      simpa [sq_abs, pow_two] using hmul
    simp [htail, hle]
  · simp [htail]

/-- Raising the tail threshold can only reduce the real absolute-tail integral. -/
theorem integral_tail_abs_mono_threshold
    [IsFiniteMeasure μ] {Y : α → ℝ} (hY : Integrable Y μ) {C R : ℝ} (hCR : C ≤ R) :
    ∫ ω, Set.indicator {ω | R ≤ |Y ω|} (fun ω => |Y ω|) ω ∂μ ≤
      ∫ ω, Set.indicator {ω | C ≤ |Y ω|} (fun ω => |Y ω|) ω ∂μ := by
  have hR_null : NullMeasurableSet {ω | R ≤ |Y ω|} μ :=
    nullMeasurableSet_le aemeasurable_const
      (continuous_abs.measurable.comp_aemeasurable hY.aemeasurable)
  have hC_null : NullMeasurableSet {ω | C ≤ |Y ω|} μ :=
    nullMeasurableSet_le aemeasurable_const
      (continuous_abs.measurable.comp_aemeasurable hY.aemeasurable)
  have hR_int :
      Integrable (Set.indicator {ω | R ≤ |Y ω|} (fun ω => |Y ω|)) μ := by
    simpa [Real.norm_eq_abs] using hY.norm.indicator₀ hR_null
  have hC_int :
      Integrable (Set.indicator {ω | C ≤ |Y ω|} (fun ω => |Y ω|)) μ := by
    simpa [Real.norm_eq_abs] using hY.norm.indicator₀ hC_null
  refine integral_mono hR_int hC_int ?_
  intro ω
  by_cases hωR : R ≤ |Y ω|
  · have hωC : C ≤ |Y ω| := hCR.trans hωR
    simp [hωR, hωC]
  · have hnot : ω ∉ {ω | R ≤ |Y ω|} := hωR
    rw [Set.indicator_of_notMem hnot]
    exact Set.indicator_nonneg (fun ω _ => abs_nonneg (Y ω)) ω

/-- Convert Mathlib's `L¹` tail seminorm bound into a real absolute-tail integral bound. -/
theorem integral_tail_abs_le_of_eLpNorm_tail
    [IsFiniteMeasure μ] {Y : α → ℝ} (hY : Integrable Y μ) {C : ℝ≥0} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hTail : eLpNorm ({ω | C ≤ ‖Y ω‖₊}.indicator Y) 1 μ ≤ ENNReal.ofReal ε) :
    ∫ ω, Set.indicator {ω | (C : ℝ) ≤ |Y ω|} (fun ω => |Y ω|) ω ∂μ ≤ ε := by
  let sNN : Set α := {ω | C ≤ ‖Y ω‖₊}
  let sR : Set α := {ω | (C : ℝ) ≤ |Y ω|}
  have hs_eq : sNN = sR := by
    ext ω
    simp [sNN, sR, Real.norm_eq_abs, ← NNReal.coe_le_coe]
  have hsNN_null : NullMeasurableSet sNN μ :=
    by
      simpa [sNN] using
        (aestronglyMeasurable_const.nullMeasurableSet_le hY.aestronglyMeasurable.nnnorm :
          NullMeasurableSet {ω | C ≤ ‖Y ω‖₊} μ)
  have hg_aesm : AEStronglyMeasurable (sNN.indicator Y) μ :=
    hY.aestronglyMeasurable.indicator₀ hsNN_null
  have htail_eq :
      (fun ω => Set.indicator sR (fun ω => |Y ω|) ω) =
        fun ω => ‖sNN.indicator Y ω‖ := by
    funext ω
    by_cases hω : ω ∈ sNN
    · have hωR : ω ∈ sR := by simpa [hs_eq] using hω
      rw [Set.indicator_of_mem hωR, Set.indicator_of_mem hω, Real.norm_eq_abs]
    · have hωR : ω ∉ sR := by simpa [hs_eq] using hω
      rw [Set.indicator_of_notMem hωR, Set.indicator_of_notMem hω, norm_zero]
  have hreal_eq :
      ∫ ω, Set.indicator {ω | (C : ℝ) ≤ |Y ω|} (fun ω => |Y ω|) ω ∂μ =
        (eLpNorm ({ω | C ≤ ‖Y ω‖₊}.indicator Y) 1 μ).toReal := by
    calc
      ∫ ω, Set.indicator {ω | (C : ℝ) ≤ |Y ω|} (fun ω => |Y ω|) ω ∂μ =
          ∫ ω, ‖sNN.indicator Y ω‖ ∂μ := by
        rw [show {ω | (C : ℝ) ≤ |Y ω|} = sR by rfl, htail_eq]
      _ = (∫⁻ ω, ‖sNN.indicator Y ω‖ₑ ∂μ).toReal :=
        integral_norm_eq_lintegral_enorm hg_aesm
      _ = (eLpNorm ({ω | C ≤ ‖Y ω‖₊}.indicator Y) 1 μ).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm]
  rw [hreal_eq]
  exact ENNReal.toReal_le_of_le_ofReal hε hTail

/-- Square integrability makes the squared tail small for all sufficiently
large thresholds. -/
theorem integral_tail_sq_eventual_le_of_memLp_two
    [IsFiniteMeasure μ] {Y : α → ℝ} (hY : MemLp Y 2 μ) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
      ∀ R : ℝ, R₀ ≤ R →
        (∫ ω, Set.indicator {ω | R ≤ |Y ω|}
          (fun ω => (Y ω) ^ 2) ω ∂μ) ≤ ε := by
  intro ε hε
  have hYsq_int : Integrable (fun ω => (Y ω) ^ 2) μ :=
    hY.integrable_sq
  have hYsq_mem : MemLp (fun ω => (Y ω) ^ 2) 1 μ :=
    memLp_one_iff_integrable.mpr hYsq_int
  obtain ⟨M, hM_nonneg, hMtail⟩ :=
    MemLp.integral_indicator_norm_ge_nonneg_le
      (μ := μ) (f := fun ω => (Y ω) ^ 2) hYsq_mem hε
  let C : ℝ≥0 := ⟨M, hM_nonneg⟩
  have hMtail_e :
      eLpNorm
        ({ω | C ≤ ‖(Y ω) ^ 2‖₊}.indicator
          (fun ω => (Y ω) ^ 2)) 1 μ ≤ ENNReal.ofReal ε := by
    have hset :
        {ω | C ≤ ‖Y ω‖₊ ^ 2} =
          {ω | M ≤ (Y ω) ^ 2} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [← NNReal.coe_le_coe]
      simp [C]
    simpa [eLpNorm_one_eq_lintegral_enorm, hset] using hMtail
  have hMtail_real :
      ∫ ω,
        Set.indicator {ω | M ≤ (Y ω) ^ 2}
          (fun ω => (Y ω) ^ 2) ω ∂μ ≤ ε := by
    simpa [C] using
      integral_tail_abs_le_of_eLpNorm_tail
        (μ := μ) (Y := fun ω => (Y ω) ^ 2)
        hYsq_int hε.le hMtail_e
  refine ⟨max 1 M, le_max_left _ _, fun R hR => ?_⟩
  have hR_null : NullMeasurableSet {ω | R ≤ |Y ω|} μ :=
    nullMeasurableSet_le aemeasurable_const
      (continuous_abs.measurable.comp_aemeasurable
        hY.aestronglyMeasurable.aemeasurable)
  have hR_int :
      Integrable
        (Set.indicator {ω | R ≤ |Y ω|} (fun ω => (Y ω) ^ 2)) μ :=
    hYsq_int.indicator₀ hR_null
  have hM_null : NullMeasurableSet {ω | M ≤ (Y ω) ^ 2} μ :=
    nullMeasurableSet_le aemeasurable_const
      hYsq_int.aemeasurable
  have hM_int :
      Integrable
        (Set.indicator {ω | M ≤ (Y ω) ^ 2}
          (fun ω => (Y ω) ^ 2)) μ :=
    hYsq_int.indicator₀ hM_null
  have hmono :
      (∫ ω, Set.indicator {ω | R ≤ |Y ω|}
        (fun ω => (Y ω) ^ 2) ω ∂μ) ≤
      ∫ ω,
        Set.indicator {ω | M ≤ (Y ω) ^ 2}
          (fun ω => (Y ω) ^ 2) ω ∂μ := by
    refine integral_mono hR_int hM_int ?_
    intro ω
    by_cases htail : R ≤ |Y ω|
    · have hR₀_tail : max 1 M ≤ |Y ω| := hR.trans htail
      have hone_tail : 1 ≤ |Y ω| := (le_max_left 1 M).trans hR₀_tail
      have hM_tail_abs : M ≤ |Y ω| := (le_max_right 1 M).trans hR₀_tail
      have habs_le_sq : |Y ω| ≤ (Y ω) ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hone_tail (abs_nonneg (Y ω))
        simpa [sq_abs, pow_two] using hmul
      have hM_tail_sq : M ≤ (Y ω) ^ 2 :=
        hM_tail_abs.trans habs_le_sq
      simp [htail, hM_tail_sq]
    · have hleft_zero :
          Set.indicator {ω | R ≤ |Y ω|} (fun ω => (Y ω) ^ 2) ω = 0 := by
        simp [Set.indicator, htail]
      exact hleft_zero.trans_le
        (Set.indicator_nonneg (fun ω _ => sq_nonneg (Y ω)) ω)
  exact hmono.trans hMtail_real

/-- **Hansen Theorem 6.15, bounded continuous weak-moment face.**

Weak convergence is exactly convergence of expectations for bounded continuous
test functions. This records the theorem-facing integral version for random
variables: if `Xₙ ⇒ Z`, then `∫ f(Xₙ) → ∫ f(Z)` for every bounded continuous
real transform `f`. The unbounded/UI moment theorem needs an additional
truncation layer on top of this bounded-continuous core. -/
theorem TendstoInDistribution.integral_boundedContinuous_tendsto
    {Ω Ω' E : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {X : ℕ → Ω → E} {Z : Ω' → E}
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (f : BoundedContinuousFunction E ℝ) :
    Tendsto (fun n => ∫ ω, f (X n ω) ∂μ) atTop
      (𝓝 (∫ ω, f (Z ω) ∂ν)) := by
  have hmap :
      Tendsto (fun n => ∫ x, f x ∂(μ.map (X n))) atTop
        (𝓝 (∫ x, f x ∂(ν.map Z))) := by
    let lawZ : ProbabilityMeasure E :=
      ⟨ν.map Z, Measure.isProbabilityMeasure_map hX.aemeasurable_limit⟩
    have hcont :=
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).tendsto lawZ
    simpa [lawZ] using hcont.comp hX.tendsto
  have hlimit :
      ∫ x, f x ∂(ν.map Z) = ∫ ω, f (Z ω) ∂ν := by
    rw [integral_map hX.aemeasurable_limit (by fun_prop)]
  have hseq :
      (fun n => ∫ x, f x ∂(μ.map (X n))) =
        fun n => ∫ ω, f (X n ω) ∂μ := by
    funext n
    rw [integral_map (hX.forall_aemeasurable n) (by fun_prop)]
  simpa [hlimit, hseq] using hmap

/-- Bounded-continuous integral convergence from weak convergence with
sample-size-dependent source spaces.

This is the indexed-space form of
`TendstoInDistribution.integral_boundedContinuous_tendsto`. It is useful for
ordinary nonparametric bootstrap laws, where the resampling space varies with
`n`. -/
theorem TendstoInDistribution.integral_boundedContinuous_tendsto_indexed
    {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)}
    {Ω' E : Type*} {mΩ' : MeasurableSpace Ω'}
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {X : ∀ n, Ω n → E} {Z : Ω' → E}
    (hX : TendstoInDistribution X atTop Z μ ν)
    (f : BoundedContinuousFunction E ℝ) :
    Tendsto (fun n => ∫ ω, f (X n ω) ∂μ n) atTop
      (𝓝 (∫ ω, f (Z ω) ∂ν)) := by
  have hmap :
      Tendsto (fun n => ∫ x, f x ∂((μ n).map (X n))) atTop
        (𝓝 (∫ x, f x ∂(ν.map Z))) := by
    let lawZ : ProbabilityMeasure E :=
      ⟨ν.map Z, Measure.isProbabilityMeasure_map hX.aemeasurable_limit⟩
    have hcont :=
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).tendsto lawZ
    simpa [lawZ] using hcont.comp hX.tendsto
  have hlimit :
      ∫ x, f x ∂(ν.map Z) = ∫ ω, f (Z ω) ∂ν := by
    rw [integral_map hX.aemeasurable_limit (by fun_prop)]
  have hseq :
      (fun n => ∫ x, f x ∂((μ n).map (X n))) =
        fun n => ∫ ω, f (X n ω) ∂μ n := by
    funext n
    rw [integral_map (hX.forall_aemeasurable n) (by fun_prop)]
  simpa [hlimit, hseq] using hmap

/-- **Hansen Theorem 6.15, clipped real weak-moment face.**

If `Xₙ ⇒ Z`, then expectations of every bounded continuous clipped identity
`x ↦ max (-R) (min x R)` converge. This is the truncation bridge used before
adding the tail-control step for the full uniform-integrability theorem. -/
theorem TendstoInDistribution.integral_realClip_tendsto
    {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    {R : ℝ} (hR : 0 ≤ R) :
    Tendsto
      (fun n => ∫ ω, realClip R (X n ω) ∂μ)
      atTop
      (𝓝 (∫ ω, realClip R (Z ω) ∂ν)) := by
  simpa [realClipBoundedContinuousFunction_apply] using
    TendstoInDistribution.integral_boundedContinuous_tendsto
      (μ := μ) (ν := ν) (X := X) (Z := Z) hX
      (realClipBoundedContinuousFunction R hR)

/-- **Hansen Theorem 6.15, weak-moment tail-control assembly.**

If clipped expectations converge by weak convergence and the source and limit
integral tails can be made uniformly small, then the untruncated real
expectations converge. The remaining theorem-facing task is to derive the tail
premise from Mathlib uniform integrability. -/
theorem TendstoInDistribution.integral_tendsto_of_realClip_tails
    {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (hTail : ∀ ε > 0, ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ω, Z ω ∂ν) - ∫ ω, realClip R (Z ω) ∂ν| ≤ ε ∧
      ∀ᶠ n in atTop,
        |(∫ ω, X n ω ∂μ) - ∫ ω, realClip R (X n ω) ∂μ| ≤ ε) :
    Tendsto (fun n => ∫ ω, X n ω ∂μ) atTop (𝓝 (∫ ω, Z ω ∂ν)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / 4 with hη_def
  have hη_pos : 0 < η := by positivity
  obtain ⟨R, hR, hTailZ, hTailX⟩ := hTail η hη_pos
  have hClip :
      ∀ᶠ n in atTop,
        dist (∫ ω, realClip R (X n ω) ∂μ) (∫ ω, realClip R (Z ω) ∂ν) < η :=
    eventually_atTop.2
      ((Metric.tendsto_atTop.1
        (TendstoInDistribution.integral_realClip_tendsto
          (μ := μ) (ν := ν) (X := X) (Z := Z) hX hR)) η hη_pos)
  have hEventually :
      ∀ᶠ n in atTop, dist (∫ ω, X n ω ∂μ) (∫ ω, Z ω ∂ν) < ε := by
    filter_upwards [hClip, hTailX] with n hClip_n hTailX_n
    rw [Real.dist_eq] at hClip_n ⊢
    have hTailZ' :
        |(∫ ω, realClip R (Z ω) ∂ν) - ∫ ω, Z ω ∂ν| ≤ η := by
      simpa [abs_sub_comm] using hTailZ
    calc
      |(∫ ω, X n ω ∂μ) - ∫ ω, Z ω ∂ν| ≤
          |(∫ ω, X n ω ∂μ) - ∫ ω, realClip R (X n ω) ∂μ| +
            |(∫ ω, realClip R (X n ω) ∂μ) -
              ∫ ω, realClip R (Z ω) ∂ν| +
            |(∫ ω, realClip R (Z ω) ∂ν) - ∫ ω, Z ω ∂ν| := by
        have hdecomp :
            (∫ ω, X n ω ∂μ) - ∫ ω, Z ω ∂ν =
              ((∫ ω, X n ω ∂μ) - ∫ ω, realClip R (X n ω) ∂μ) +
                ((∫ ω, realClip R (X n ω) ∂μ) -
                  ∫ ω, realClip R (Z ω) ∂ν) +
                ((∫ ω, realClip R (Z ω) ∂ν) - ∫ ω, Z ω ∂ν) := by
          ring
        rw [hdecomp]
        calc
          |((∫ ω, X n ω ∂μ) - ∫ ω, realClip R (X n ω) ∂μ) +
                ((∫ ω, realClip R (X n ω) ∂μ) -
                  ∫ ω, realClip R (Z ω) ∂ν) +
                ((∫ ω, realClip R (Z ω) ∂ν) - ∫ ω, Z ω ∂ν)| ≤
              |((∫ ω, X n ω ∂μ) - ∫ ω, realClip R (X n ω) ∂μ) +
                ((∫ ω, realClip R (X n ω) ∂μ) -
                  ∫ ω, realClip R (Z ω) ∂ν)| +
                |(∫ ω, realClip R (Z ω) ∂ν) - ∫ ω, Z ω ∂ν| := by
            exact abs_add_le _ _
          _ ≤
              |(∫ ω, X n ω ∂μ) - ∫ ω, realClip R (X n ω) ∂μ| +
                |(∫ ω, realClip R (X n ω) ∂μ) -
                  ∫ ω, realClip R (Z ω) ∂ν| +
                |(∫ ω, realClip R (Z ω) ∂ν) - ∫ ω, Z ω ∂ν| := by
            gcongr
            exact abs_add_le _ _
      _ < ε := by
        linarith
  exact eventually_atTop.1 hEventually

/-- **Hansen Theorem 6.15, weak-convergence UI moment wrapper.**

If `Xₙ ⇒ Z` and the source sequence is uniformly integrable in `L¹`, then the
real expectations converge.  The proof derives the explicit clipping-tail
premise from Mathlib's `UniformIntegrable` tail characterization and the
limit-law integrability supplied by the bounded-first-moment weak-convergence
wrapper above. -/
theorem TendstoInDistribution.integral_tendsto_of_uniformIntegrable
    {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (hUI : UniformIntegrable X 1 μ) :
    Tendsto (fun n => ∫ ω, X n ω ∂μ) atTop (𝓝 (∫ ω, Z ω ∂ν)) := by
  have hX_int : ∀ n, Integrable (X n) μ :=
    fun n => memLp_one_iff_integrable.mp (hUI.memLp n)
  obtain ⟨B, hB⟩ := hUI.2.2
  have hBound :
      ∀ᶠ n in atTop,
        Integrable (fun ω => ‖X n ω‖) μ ∧ ∫ ω, ‖X n ω‖ ∂μ ≤ (B : ℝ) :=
    Eventually.of_forall fun n => by
      have hreal_eq :
          ∫ ω, ‖X n ω‖ ∂μ = (eLpNorm (X n) 1 μ).toReal := by
        calc
          ∫ ω, ‖X n ω‖ ∂μ = (∫⁻ ω, ‖X n ω‖ₑ ∂μ).toReal :=
            integral_norm_eq_lintegral_enorm (hX_int n).aestronglyMeasurable
          _ = (eLpNorm (X n) 1 μ).toReal := by
            rw [eLpNorm_one_eq_lintegral_enorm]
      refine ⟨(hX_int n).norm, ?_⟩
      rw [hreal_eq]
      exact ENNReal.toReal_le_of_le_ofReal (NNReal.coe_nonneg B) (by
        simpa [ENNReal.ofReal_coe_nnreal] using hB n)
  have hZ_norm_int : Integrable (fun ω => ‖Z ω‖) ν :=
    TendstoInDistribution.integrable_norm_limit_of_eventually_integral_norm_bound
      (μ := μ) (ν := ν) (X := X) (Z := Z) hX hBound
  have hZ_aesm : AEStronglyMeasurable Z ν := by
    rw [aestronglyMeasurable_iff_aemeasurable]
    exact hX.aemeasurable_limit
  have hZ_int : Integrable Z ν :=
    (integrable_norm_iff hZ_aesm).mp hZ_norm_int
  have hZ_memLp : MemLp Z 1 ν :=
    memLp_one_iff_integrable.mpr hZ_int
  refine TendstoInDistribution.integral_tendsto_of_realClip_tails
    (μ := μ) (ν := ν) (X := X) (Z := Z) hX ?_
  intro ε hε
  set η : ℝ := ε / 2 with hη_def
  have hη_pos : 0 < η := by positivity
  have hη_nonneg : 0 ≤ η := hη_pos.le
  obtain ⟨Csrc, hCsrc_tail⟩ :=
    UniformIntegrable.spec (μ := μ) (f := X)
      (p := (1 : ℝ≥0∞)) (by simp) (by simp) hUI hη_pos
  obtain ⟨Mlim, hMlim_nonneg, hMlim_tail⟩ :=
    MemLp.integral_indicator_norm_ge_nonneg_le (μ := ν) (f := Z) hZ_memLp hη_pos
  let Clim : ℝ≥0 := ⟨Mlim, hMlim_nonneg⟩
  set R : ℝ := max (Csrc : ℝ) (Clim : ℝ) with hR_def
  have hR_nonneg : 0 ≤ R := by
    rw [hR_def]
    exact (NNReal.coe_nonneg Csrc).trans (le_max_left _ _)
  refine ⟨R, hR_nonneg, ?_, ?_⟩
  · have hMlim_tail_e :
        eLpNorm ({ω | Clim ≤ ‖Z ω‖₊}.indicator Z) 1 ν ≤ ENNReal.ofReal η := by
      have hset :
          {ω | Clim ≤ ‖Z ω‖₊} = {ω | Mlim ≤ (‖Z ω‖₊ : ℝ)} := by
        ext ω
        simp [Clim, ← NNReal.coe_le_coe]
      simpa [eLpNorm_one_eq_lintegral_enorm, hset] using hMlim_tail
    have htail_base :
        ∫ ω, Set.indicator {ω | (Clim : ℝ) ≤ |Z ω|} (fun ω => |Z ω|) ω ∂ν ≤ η :=
      integral_tail_abs_le_of_eLpNorm_tail (μ := ν) hZ_int hη_nonneg hMlim_tail_e
    have htail_R :
        ∫ ω, Set.indicator {ω | R ≤ |Z ω|} (fun ω => |Z ω|) ω ∂ν ≤ η :=
      (integral_tail_abs_mono_threshold (μ := ν) hZ_int
        (C := (Clim : ℝ)) (R := R) (by
          rw [hR_def]
          exact le_max_right _ _)).trans htail_base
    have hclip :=
      abs_integral_sub_realClip_le_two_mul_integral_tail_abs
        (μ := ν) (Y := Z) hZ_int hR_nonneg
    calc
      |(∫ ω, Z ω ∂ν) - ∫ ω, realClip R (Z ω) ∂ν| ≤
          2 * ∫ ω, Set.indicator {ω | R ≤ |Z ω|} (fun ω => |Z ω|) ω ∂ν := hclip
      _ ≤ 2 * η := by nlinarith
      _ = ε := by
        rw [hη_def]
        ring
  · exact Eventually.of_forall fun n => by
      have htail_base :
          ∫ ω, Set.indicator {ω | (Csrc : ℝ) ≤ |X n ω|} (fun ω => |X n ω|) ω ∂μ ≤
            η :=
        integral_tail_abs_le_of_eLpNorm_tail (μ := μ) (Y := X n)
          (hX_int n) hη_nonneg (hCsrc_tail n)
      have htail_R :
          ∫ ω, Set.indicator {ω | R ≤ |X n ω|} (fun ω => |X n ω|) ω ∂μ ≤ η :=
        (integral_tail_abs_mono_threshold (μ := μ) (Y := X n) (hX_int n)
          (C := (Csrc : ℝ)) (R := R) (by
            rw [hR_def]
            exact le_max_left _ _)).trans htail_base
      have hclip :=
        abs_integral_sub_realClip_le_two_mul_integral_tail_abs
          (μ := μ) (Y := X n) (hX_int n) hR_nonneg
      calc
        |(∫ ω, X n ω ∂μ) - ∫ ω, realClip R (X n ω) ∂μ| ≤
            2 * ∫ ω, Set.indicator {ω | R ≤ |X n ω|} (fun ω => |X n ω|) ω ∂μ := hclip
        _ ≤ 2 * η := by nlinarith
        _ = ε := by
          rw [hη_def]
          ring

/-- Square-root continuous mapping at zero for nonnegative real-valued sequences.

This avoids any additional measurability side condition by comparing the tail
events `{sqrt Xₙ ≥ ε}` and `{Xₙ ≥ ε²}` directly. -/
theorem TendstoInMeasure.sqrt_nonneg_zero_real
    {X : ℕ → α → ℝ}
    (hX : TendstoInMeasure μ X atTop (fun _ => 0))
    (hX_nonneg : ∀ n ω, 0 ≤ X n ω) :
    TendstoInMeasure μ (fun n ω => Real.sqrt (X n ω)) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro ε hε
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have htail := hX (ε ^ 2) hε2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  have hsqrt : ε ≤ Real.sqrt (X n ω) := by
    simpa [Real.dist_eq, abs_of_nonneg (Real.sqrt_nonneg _)] using hω
  have hsquare : ε ^ 2 ≤ (Real.sqrt (X n ω)) ^ 2 := by
    exact pow_le_pow_left₀ hε.le hsqrt 2
  have hdist : ε ^ 2 ≤ dist (X n ω) 0 := by
    rw [Real.sq_sqrt (hX_nonneg n ω)] at hsquare
    simpa [Real.dist_eq, abs_of_nonneg (hX_nonneg n ω)] using hsquare
  exact hdist

/-- **Hansen Theorem 6.13, convergence-in-measure bounded-moment wrapper.**

If a real sequence converges in measure and has eventually bounded `L¹`
seminorm, the limit has the same `L¹` bound. This is the
convergence-in-measure face of Hansen's bounded-first-moment passage to the
limit; the textbook weak-convergence statement is stronger. -/
theorem eLpNorm_one_limit_le_of_tendstoInMeasure_bound
    {Z : ℕ → α → ℝ} {Zlim : α → ℝ} {C : ℝ≥0∞}
    (hBound : ∀ᶠ n in atTop, eLpNorm (Z n) 1 μ ≤ C)
    (hZ : TendstoInMeasure μ Z atTop Zlim)
    (hMeas : ∀ n, AEStronglyMeasurable (Z n) μ) :
    eLpNorm Zlim 1 μ ≤ C := by
  exact eLpNorm_le_of_tendstoInMeasure
    (μ := μ) (f := Z) (g := Zlim) (p := (1 : ℝ≥0∞)) hBound hZ hMeas

/-- **Hansen Theorem 6.15, convergence-in-measure UI moment wrapper.**

If real random variables are uniformly integrable and converge in measure, then
their expectations converge. This is the Vitali/convergence-in-measure face of
Hansen's moment-convergence theorem; the textbook weak-convergence version has a
stronger mode-of-convergence premise than this wrapper exposes. -/
theorem tendsto_integral_of_tendstoInMeasure_uniformIntegrable
    [IsFiniteMeasure μ]
    {Z : ℕ → α → ℝ} {Zlim : α → ℝ}
    (hUI : UniformIntegrable Z 1 μ)
    (hZ : TendstoInMeasure μ Z atTop Zlim) :
    Tendsto (fun n => ∫ ω, Z n ω ∂μ) atTop (𝓝 (∫ ω, Zlim ω ∂μ)) := by
  have hZlim_mem : MemLp Zlim 1 μ := hUI.memLp_of_tendstoInMeasure hZ
  have hLp : Tendsto (fun n => eLpNorm (Z n - Zlim) 1 μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure
      (μ := μ) (f := Z) (g := Zlim) le_rfl ENNReal.one_ne_top
      (fun n => hUI.aestronglyMeasurable n) hZlim_mem hUI.unifIntegrable hZ
  exact tendsto_integral_of_L1' Zlim (memLp_one_iff_integrable.mp hZlim_mem)
    (Eventually.of_forall fun n => memLp_one_iff_integrable.mp (hUI.memLp n)) hLp

/-- **Coordinate projection of `TendstoInMeasure`**: if a sequence of `∀ b, X b`-valued
functions converges in measure, then each coordinate converges in measure.

This is the easy direction of the "Pi ⇔ coordinatewise" characterization. The reverse
direction (coordinatewise ⇒ joint) is `tendstoInMeasure_pi`. -/
theorem TendstoInMeasure.pi_apply
    {β : Type*} [Fintype β] {X : β → Type*} [∀ b, EDist (X b)]
    {f : ℕ → α → ∀ b, X b} {g : α → ∀ b, X b}
    (hfg : TendstoInMeasure μ f atTop g) (b : β) :
    TendstoInMeasure μ (fun n ω => f n ω b) atTop (fun ω => g ω b) := by
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hfg ε hε)
    (fun _ => zero_le _) (fun n => ?_)
  refine measure_mono (fun ω hω => ?_)
  exact le_trans hω (edist_le_pi_edist _ _ _)

/-- **Coordinatewise ⇒ joint `TendstoInMeasure`** for Pi types over a `Fintype`:
if every coordinate sequence converges in measure, so does the joint sequence. -/
theorem tendstoInMeasure_pi
    {β : Type*} [Fintype β] {X : β → Type*} [∀ b, EDist (X b)]
    {f : ℕ → α → ∀ b, X b} {g : α → ∀ b, X b}
    (h : ∀ b, TendstoInMeasure μ (fun n ω => f n ω b) atTop (fun ω => g ω b)) :
    TendstoInMeasure μ f atTop g := by
  intro ε hε
  have hcover : ∀ n,
      {ω | ε ≤ edist (f n ω) (g ω)} ⊆ ⋃ b, {ω | ε ≤ edist (f n ω b) (g ω b)} := by
    intro n ω hω
    have hω' : ε ≤ Finset.sup Finset.univ (fun b => edist (f n ω b) (g ω b)) := by
      simpa [edist_pi_def] using hω
    obtain ⟨b, -, hb⟩ := (Finset.le_sup_iff (bot_lt_iff_ne_bot.mpr hε.ne')).mp hω'
    exact Set.mem_iUnion.2 ⟨b, hb⟩
  have hbound : ∀ n,
      μ {ω | ε ≤ edist (f n ω) (g ω)} ≤
        ∑ b : β, μ {ω | ε ≤ edist (f n ω b) (g ω b)} := fun n =>
    (measure_mono (hcover n)).trans
      (measure_iUnion_fintype_le μ (fun b => {ω | ε ≤ edist (f n ω b) (g ω b)}))
  have hsum : Tendsto
      (fun n => ∑ b : β, μ {ω | ε ≤ edist (f n ω b) (g ω b)}) atTop (𝓝 0) := by
    have : Tendsto (fun n => ∑ b : β, μ {ω | ε ≤ edist (f n ω b) (g ω b)}) atTop
        (𝓝 (∑ _ : β, (0 : ℝ≥0∞))) :=
      tendsto_finset_sum Finset.univ (fun b _ => h b ε hε)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le _) hbound

end CMT

section CramerWold

/-- Characteristic functions of an `E`-valued pushforward can be evaluated as
the one-dimensional characteristic function of the corresponding inner-product
projection.

This is the small bridge needed to apply Mathlib's Lévy continuity theorem to
finite-dimensional Cramér-Wold arguments. -/
theorem charFun_map_eq_charFun_dualMap_one
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} {X : Ω → E} (hX : AEMeasurable X μ) (t : E) :
    charFun (μ.map X) t =
      charFun (μ.map (fun ω => (InnerProductSpace.toDualMap ℝ E t) (X ω))) 1 := by
  rw [charFun_eq_charFunDual_toDualMap]
  rw [charFunDual_eq_charFun_map_one]
  rw [AEMeasurable.map_map_of_aemeasurable]
  · rfl
  · exact (InnerProductSpace.toDualMap ℝ E t).continuous.aemeasurable
  · exact hX

/-- **Cramér-Wold convergence bridge for finite-dimensional inner-product spaces.**

If every fixed inner-product projection of `T n` converges in distribution to
the matching projection of `Z`, then `T n` converges in distribution to `Z`.
The proof compares characteristic functions projectionwise and then uses
Mathlib's Lévy convergence theorem for probability measures. -/
theorem cramerWold_tendstoInDistribution
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {T : ℕ → Ω → E} {Z : Ω' → E}
    (hT : ∀ n, AEMeasurable (T n) μ)
    (hZ : AEMeasurable Z ν)
    (hproj : ∀ t : E,
      TendstoInDistribution
        (fun n ω => (InnerProductSpace.toDualMap ℝ E t) (T n ω)) atTop
        (fun ω => (InnerProductSpace.toDualMap ℝ E t) (Z ω)) (fun _ => μ) ν) :
    TendstoInDistribution T atTop Z (fun _ => μ) ν := by
  refine ⟨hT, hZ, ?_⟩
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t
  have hscalar := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp (hproj t).tendsto) 1
  convert hscalar using 1
  · ext n
    exact charFun_map_eq_charFun_dualMap_one (hT n) t
  · change 𝓝 (charFun (ν.map Z) t) =
      𝓝 (charFun (ν.map (fun ω => (InnerProductSpace.toDualMap ℝ E t) (Z ω))) 1)
    exact congrArg 𝓝 (charFun_map_eq_charFun_dualMap_one hZ t)

/-- Indexed Cramér-Wold convergence bridge for finite-dimensional inner-product
spaces.

This is the source-space-indexed analogue of
`cramerWold_tendstoInDistribution`: if every fixed inner-product projection
converges in distribution and the measures/source spaces may vary with the
sequence index, then the vector statistic converges in distribution. -/
theorem cramerWold_tendstoInDistribution_indexed
    {Ω : ℕ → Type*} {Ω' E : Type*}
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [BorelSpace E]
    {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {T : ∀ n, Ω n → E} {Z : Ω' → E}
    (hT : ∀ n, AEMeasurable (T n) (μ n))
    (hZ : AEMeasurable Z ν)
    (hproj : ∀ t : E,
      TendstoInDistribution
        (fun n ω => (InnerProductSpace.toDualMap ℝ E t) (T n ω)) atTop
        (fun ω => (InnerProductSpace.toDualMap ℝ E t) (Z ω)) μ ν) :
    TendstoInDistribution T atTop Z μ ν := by
  refine ⟨hT, hZ, ?_⟩
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t
  have hscalar := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp (hproj t).tendsto) 1
  convert hscalar using 1
  · ext i
    exact charFun_map_eq_charFun_dualMap_one (hT i) t
  · change 𝓝 (charFun (ν.map Z) t) =
      𝓝 (charFun (ν.map (fun ω => (InnerProductSpace.toDualMap ℝ E t) (Z ω))) 1)
    exact congrArg 𝓝 (charFun_map_eq_charFun_dualMap_one hZ t)

end CramerWold

section MatrixInverse

open scoped Matrix.Norms.Elementwise

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- **Measurability of the matrix inverse.** If `A : α → Matrix k k ℝ`
is strongly measurable a.e., so is `fun ω => (A ω)⁻¹`. Derived from
`Matrix.inv_def` (`A⁻¹ = Ring.inverse A.det • A.adjugate`) and measurability
of scalar reciprocal / continuity of det and adjugate. -/
theorem aestronglyMeasurable_matrix_inv
    {A : α → Matrix k k ℝ} (hmeas : AEStronglyMeasurable A μ) :
    AEStronglyMeasurable (fun ω => (A ω)⁻¹) μ := by
  have hdet : AEStronglyMeasurable (fun ω => (A ω).det) μ :=
    (Continuous.matrix_det continuous_id).comp_aestronglyMeasurable hmeas
  have hadj : AEStronglyMeasurable (fun ω => (A ω).adjugate) μ :=
    (Continuous.matrix_adjugate continuous_id).comp_aestronglyMeasurable hmeas
  have hrinv : AEStronglyMeasurable (fun ω => Ring.inverse ((A ω).det)) μ := by
    have heq : (fun ω => Ring.inverse ((A ω).det)) = (fun ω => ((A ω).det)⁻¹) := by
      funext ω
      exact Ring.inverse_eq_inv _
    rw [heq]
    exact (measurable_inv.comp_aemeasurable hdet.aemeasurable).aestronglyMeasurable
  have heq : (fun ω => (A ω)⁻¹) =
      (fun ω => Ring.inverse ((A ω).det) • (A ω).adjugate) := by
    funext ω
    exact Matrix.inv_def (A ω)
  rw [heq]
  exact hrinv.smul hadj

/-- **CMT for matrix inversion.** If `A n →ₚ A'` in measure and `A' ω` is nonsingular
for every `ω`, then `(A n)⁻¹ →ₚ (A')⁻¹` in measure.

Pointwise a.s. convergence follows from Mathlib's `continuousAt_matrix_inv`, which
gives continuity of matrix inversion at each nonsingular limit point. Measurability
of the inverse sequence reuses `aestronglyMeasurable_matrix_inv`. -/
theorem tendstoInMeasure_matrix_inv
    [IsFiniteMeasure μ]
    {A : ℕ → α → Matrix k k ℝ} {A' : α → Matrix k k ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (A n) μ)
    (hconv : TendstoInMeasure μ A atTop A')
    (hinv : ∀ ω, IsUnit (A' ω).det) :
    TendstoInMeasure μ (fun n ω => (A n ω)⁻¹) atTop (fun ω => (A' ω)⁻¹) := by
  have hmeas_inv : ∀ n, AEStronglyMeasurable (fun ω => (A n ω)⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (hmeas n)
  rw [exists_seq_tendstoInMeasure_atTop_iff hmeas_inv]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ :=
    (exists_seq_tendstoInMeasure_atTop_iff hmeas).mp hconv ns hns
  refine ⟨ns', hns', ?_⟩
  filter_upwards [hae] with ω hω
  have hcont : ContinuousAt Inv.inv (A' ω) := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ ((hinv ω).ne_zero)
  exact hcont.tendsto.comp hω

end MatrixInverse

section MulVec

open scoped Matrix Matrix.Norms.Elementwise

/-- **Joint `TendstoInMeasure` on a product.** If `f n →ₚ finf` and `g n →ₚ ginf`, then
`(f n, g n) →ₚ (finf, ginf)` in the product E-metric. -/
theorem tendstoInMeasure_prodMk
    {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    {f : ℕ → α → E} {finf : α → E} {g : ℕ → α → F} {ginf : α → F}
    (hf : TendstoInMeasure μ f atTop finf)
    (hg : TendstoInMeasure μ g atTop ginf) :
    TendstoInMeasure μ (fun n ω => (f n ω, g n ω)) atTop (fun ω => (finf ω, ginf ω)) := by
  intro ε hε
  have hcover : ∀ n,
      {ω | ε ≤ edist (f n ω, g n ω) (finf ω, ginf ω)} ⊆
        {ω | ε ≤ edist (f n ω) (finf ω)} ∪ {ω | ε ≤ edist (g n ω) (ginf ω)} := by
    intro n ω hω
    rcases le_max_iff.mp (by simpa [Prod.edist_eq] using hω) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hbound : ∀ n,
      μ {ω | ε ≤ edist (f n ω, g n ω) (finf ω, ginf ω)} ≤
        μ {ω | ε ≤ edist (f n ω) (finf ω)} + μ {ω | ε ≤ edist (g n ω) (ginf ω)} := fun n =>
    (measure_mono (hcover n)).trans (measure_union_le _ _)
  have hsum : Tendsto
      (fun n => μ {ω | ε ≤ edist (f n ω) (finf ω)} + μ {ω | ε ≤ edist (g n ω) (ginf ω)})
      atTop (𝓝 0) := by
    simpa using (hf ε hε).add (hg ε hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le _) hbound

set_option maxHeartbeats 400000 in
-- Heartbeat bump: PseudoMetrizable synthesis on the product `E × E` via the
-- scoped elementwise norm is expensive for vector/matrix instantiations.
/-- **Additive CMT for `TendstoInMeasure`.** If `f n →ₚ finf` and `g n →ₚ ginf`
in a pseudo-metrizable additive topological group, then
`f n + g n →ₚ finf + ginf`. Mathlib lacks a named additive glue for
`TendstoInMeasure`; we assemble it from the product CMT and continuity of `+`. -/
theorem tendstoInMeasure_add
    [IsFiniteMeasure μ]
    {E : Type*} [PseudoEMetricSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    [Add E] [ContinuousAdd E]
    {f g : ℕ → α → E} {finf ginf : α → E}
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg_meas : ∀ n, AEStronglyMeasurable (g n) μ)
    (hf : TendstoInMeasure μ f atTop finf)
    (hg : TendstoInMeasure μ g atTop ginf) :
    TendstoInMeasure μ (fun n ω => f n ω + g n ω) atTop (fun ω => finf ω + ginf ω) := by
  have hprod_meas : ∀ n, AEStronglyMeasurable (fun ω => (f n ω, g n ω)) μ :=
    fun n => (hf_meas n).prodMk (hg_meas n)
  exact tendstoInMeasure_continuous_comp hprod_meas
    (tendstoInMeasure_prodMk hf hg) continuous_add

set_option maxHeartbeats 400000 in
-- Heartbeat bump: PseudoMetrizable synthesis on the product
-- `Matrix k k ℝ × (k → ℝ)` with scoped elementwise norm is expensive.
/-- **Matrix-vector multiplication CMT.** If `A n →ₚ Ainf` (matrix in measure) and
`v n →ₚ vinf` (vector in measure), then `A n *ᵥ v n →ₚ Ainf *ᵥ vinf`. -/
theorem tendstoInMeasure_mulVec
    [IsFiniteMeasure μ]
    {k : Type*} [Fintype k]
    {A : ℕ → α → Matrix k k ℝ} {Ainf : α → Matrix k k ℝ}
    {v : ℕ → α → k → ℝ} {vinf : α → k → ℝ}
    (hA_meas : ∀ n, AEStronglyMeasurable (A n) μ)
    (hv_meas : ∀ n, AEStronglyMeasurable (v n) μ)
    (hA : TendstoInMeasure μ A atTop Ainf)
    (hv : TendstoInMeasure μ v atTop vinf) :
    TendstoInMeasure μ (fun n ω => A n ω *ᵥ v n ω) atTop (fun ω => Ainf ω *ᵥ vinf ω) := by
  have hprod_meas : ∀ n, AEStronglyMeasurable (fun ω => (A n ω, v n ω)) μ :=
    fun n => (hA_meas n).prodMk (hv_meas n)
  have hcont : Continuous (fun p : Matrix k k ℝ × (k → ℝ) => p.1 *ᵥ p.2) :=
    Continuous.matrix_mulVec continuous_fst continuous_snd
  exact tendstoInMeasure_continuous_comp hprod_meas (tendstoInMeasure_prodMk hA hv) hcont

set_option maxHeartbeats 600000 in
-- Heartbeat bump: PseudoMetrizable synthesis on the product
-- `Matrix m n ℝ × (n → ℝ)` with scoped elementwise norm is expensive.
/-- **Rectangular matrix-vector multiplication CMT.** If `A n →ₚ Ainf` and
`v n →ₚ vinf` in measure, then `A n *ᵥ v n →ₚ Ainf *ᵥ vinf`, allowing
rectangular matrices. -/
theorem tendstoInMeasure_mulVec_rect
    [IsFiniteMeasure μ]
    {m n : Type*} [Fintype m] [Fintype n]
    {A : ℕ → α → Matrix m n ℝ} {Ainf : α → Matrix m n ℝ}
    {v : ℕ → α → n → ℝ} {vinf : α → n → ℝ}
    (hA_meas : ∀ n, AEStronglyMeasurable (A n) μ)
    (hv_meas : ∀ n, AEStronglyMeasurable (v n) μ)
    (hA : TendstoInMeasure μ A atTop Ainf)
    (hv : TendstoInMeasure μ v atTop vinf) :
    TendstoInMeasure μ (fun n ω => A n ω *ᵥ v n ω) atTop
      (fun ω => Ainf ω *ᵥ vinf ω) := by
  have hprod_meas : ∀ n, AEStronglyMeasurable (fun ω => (A n ω, v n ω)) μ :=
    fun n => (hA_meas n).prodMk (hv_meas n)
  have hcont : Continuous (fun p : Matrix m n ℝ × (n → ℝ) => p.1 *ᵥ p.2) :=
    Continuous.matrix_mulVec continuous_fst continuous_snd
  exact tendstoInMeasure_continuous_comp hprod_meas
    (tendstoInMeasure_prodMk hA hv) hcont

set_option maxHeartbeats 1200000 in
-- Heartbeat bump: PseudoMetrizable synthesis on the product
-- `Matrix k k ℝ × Matrix k k ℝ` with scoped elementwise norm is expensive.
/-- **Matrix multiplication CMT.** If `A n →ₚ Ainf` and `B n →ₚ Binf` in
measure, then `A n * B n →ₚ Ainf * Binf`. -/
theorem tendstoInMeasure_matrix_mul
    [IsFiniteMeasure μ]
    {k : Type*} [Fintype k]
    {A B : ℕ → α → Matrix k k ℝ} {Ainf Binf : α → Matrix k k ℝ}
    (hA_meas : ∀ n, AEStronglyMeasurable (A n) μ)
    (hB_meas : ∀ n, AEStronglyMeasurable (B n) μ)
    (hA : TendstoInMeasure μ A atTop Ainf)
    (hB : TendstoInMeasure μ B atTop Binf) :
    TendstoInMeasure μ (fun n ω => A n ω * B n ω) atTop
      (fun ω => Ainf ω * Binf ω) := by
  have hprod_meas : ∀ n, AEStronglyMeasurable (fun ω => (A n ω, B n ω)) μ :=
    fun n => (hA_meas n).prodMk (hB_meas n)
  have hcont : Continuous (fun p : Matrix k k ℝ × Matrix k k ℝ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  exact tendstoInMeasure_continuous_comp hprod_meas
    (tendstoInMeasure_prodMk hA hB) hcont

set_option maxHeartbeats 1200000 in
-- Heartbeat bump: same product-space synthesis cost as the square matrix CMT,
-- now with three independent finite index types.
/-- **Rectangular matrix multiplication CMT.** If `A n →ₚ Ainf` and
`B n →ₚ Binf` in measure, then `A n * B n →ₚ Ainf * Binf`, allowing
rectangular dimensions. -/
theorem tendstoInMeasure_matrix_mul_rect
    [IsFiniteMeasure μ]
    {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    {A : ℕ → α → Matrix m n ℝ} {B : ℕ → α → Matrix n p ℝ}
    {Ainf : α → Matrix m n ℝ} {Binf : α → Matrix n p ℝ}
    (hA_meas : ∀ n, AEStronglyMeasurable (A n) μ)
    (hB_meas : ∀ n, AEStronglyMeasurable (B n) μ)
    (hA : TendstoInMeasure μ A atTop Ainf)
    (hB : TendstoInMeasure μ B atTop Binf) :
    TendstoInMeasure μ (fun n ω => A n ω * B n ω) atTop
      (fun ω => Ainf ω * Binf ω) := by
  have hprod_meas : ∀ n, AEStronglyMeasurable (fun ω => (A n ω, B n ω)) μ :=
    fun n => (hA_meas n).prodMk (hB_meas n)
  have hcont : Continuous (fun p : Matrix m n ℝ × Matrix n p ℝ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  exact tendstoInMeasure_continuous_comp hprod_meas
    (tendstoInMeasure_prodMk hA hB) hcont

end MulVec

section StochasticOrder

open scoped Matrix.Norms.Elementwise

/-- Sum of two real-valued `oₚ(1)` sequences is `oₚ(1)`.

This direct scalar version avoids extra measurability hypotheses, using only the
triangle inequality and a union bound. -/
theorem TendstoInMeasure.add_zero_real
    {X Y : ℕ → α → ℝ}
    (hX : TendstoInMeasure μ X atTop (fun _ => 0))
    (hY : TendstoInMeasure μ Y atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => X n ω + Y n ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hX hY ⊢
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  have hsum := (hX (ε / 2) hε2).add (hY (ε / 2) hε2)
  have hsum0 : Tendsto
      (fun (n : ℕ) =>
        μ {ω | ε / 2 ≤ dist (X n ω) 0} +
        μ {ω | ε / 2 ≤ dist (Y n ω) 0})
      atTop (𝓝 0) := by
    simpa using hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum0
    (fun _ => zero_le _) (fun n => ?_)
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_cases hXbig : ε / 2 ≤ dist (X n ω) 0
  · exact Or.inl hXbig
  · right
    by_contra hYsmall_not
    have hXsmall : dist (X n ω) 0 < ε / 2 := not_le.mp hXbig
    have hYsmall : dist (Y n ω) 0 < ε / 2 := not_le.mp hYsmall_not
    have htri : dist (X n ω + Y n ω) 0 ≤ dist (X n ω) 0 + dist (Y n ω) 0 := by
      rw [Real.dist_eq, Real.dist_eq, Real.dist_eq]
      simpa using abs_add_le (X n ω) (Y n ω)
    have hlt : dist (X n ω + Y n ω) 0 < ε := by linarith
    exact (not_le.mpr hlt) hω

/-- Sum of two finite-dimensional vector-valued `oₚ(1)` sequences is `oₚ(1)`. -/
theorem TendstoInMeasure.add_zero_vector
    {k : Type*} [Fintype k] {X Y : ℕ → α → k → ℝ}
    (hX : TendstoInMeasure μ X atTop (fun _ => 0))
    (hY : TendstoInMeasure μ Y atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => X n ω + Y n ω) atTop (fun _ => 0) := by
  refine tendstoInMeasure_pi (fun i => ?_)
  have hXi := TendstoInMeasure.pi_apply hX i
  have hYi := TendstoInMeasure.pi_apply hY i
  have hsum := TendstoInMeasure.add_zero_real hXi hYi
  simpa [Pi.add_apply] using hsum

/-- Product of two real-valued `oₚ(1)` sequences is `oₚ(1)`.

This direct version avoids measurability hypotheses, using the containment
`{|XY| ≥ ε} ⊆ {|X| ≥ √ε} ∪ {|Y| ≥ √ε}`. -/
theorem TendstoInMeasure.mul_zero_real
    {X Y : ℕ → α → ℝ}
    (hX : TendstoInMeasure μ X atTop (fun _ => 0))
    (hY : TendstoInMeasure μ Y atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => X n ω * Y n ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hX hY ⊢
  intro ε hε
  let η := Real.sqrt ε
  have hη : 0 < η := Real.sqrt_pos.2 hε
  have hsum := (hX η hη).add (hY η hη)
  have hsum0 : Tendsto
      (fun (n : ℕ) =>
        μ {ω | η ≤ dist (X n ω) 0} +
        μ {ω | η ≤ dist (Y n ω) 0})
      atTop (𝓝 0) := by
    simpa [η] using hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum0
    (fun _ => zero_le _) (fun n => ?_)
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_cases hXbig : η ≤ dist (X n ω) 0
  · exact Or.inl hXbig
  · right
    by_contra hYsmall_not
    have hXsmall : dist (X n ω) 0 < η := not_le.mp hXbig
    have hYsmall : dist (Y n ω) 0 < η := not_le.mp hYsmall_not
    have hprod_abs : |X n ω * Y n ω| < ε := by
      rw [abs_mul]
      have hXabs : |X n ω| < η := by
        simpa [Real.dist_eq] using hXsmall
      have hYabs : |Y n ω| < η := by
        simpa [Real.dist_eq] using hYsmall
      have hle : |X n ω| * |Y n ω| ≤ |X n ω| * η :=
        mul_le_mul_of_nonneg_left hYabs.le (abs_nonneg _)
      have hlt : |X n ω| * η < η * η :=
        mul_lt_mul_of_pos_right hXabs hη
      have hsqrt : η * η = ε := by
        simpa [η, pow_two] using Real.sq_sqrt hε.le
      exact lt_of_le_of_lt hle (by simpa [hsqrt] using hlt)
    have hprod : dist (X n ω * Y n ω) 0 < ε := by
      simpa [Real.dist_eq] using hprod_abs
    exact (not_le.mpr hprod) hω

/-- Constant multiple of a real-valued `oₚ(1)` sequence is `oₚ(1)`. -/
theorem TendstoInMeasure.const_mul_zero_real
    {X : ℕ → α → ℝ} (c : ℝ)
    (hX : TendstoInMeasure μ X atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => c * X n ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro ε hε
  by_cases hc : c = 0
  · simp [hc, not_le_of_gt hε]
  · have hcpos : 0 < |c| := abs_pos.mpr hc
    have hscale : 0 < ε / |c| := div_pos hε hcpos
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hX (ε / |c|) hscale) (fun _ => zero_le _) (fun n => ?_)
    refine measure_mono ?_
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have habs : ε ≤ |c| * |X n ω| := by
      simpa [Real.dist_eq, abs_mul] using hω
    have hdiv : ε / |c| ≤ |X n ω| := (div_le_iff₀ hcpos).2 (by
      simpa [mul_comm] using habs)
    simpa [Real.dist_eq] using hdiv

/-- Multiplying a real-valued `oₚ(1)` sequence by an eventually bounded
deterministic scalar sequence preserves `oₚ(1)`. -/
theorem TendstoInMeasure.mul_deterministic_bounded_zero_real
    {r : ℕ → ℝ} {X : ℕ → α → ℝ} {M : ℝ}
    (hM : 0 < M) (hr : ∀ᶠ n in atTop, |r n| ≤ M)
    (hX : TendstoInMeasure μ X atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => r n * X n ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  have hscale : 0 < ε / M := div_pos hε hM
  have hXevent := (hX (ε / M) hscale).eventually_lt_const hδ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hXevent.and hr)
  refine ⟨N, fun n hn => ?_⟩
  have hXn : μ {ω | ε / M ≤ dist (X n ω) 0} < δ := (hN n hn).1
  have hrn : |r n| ≤ M := (hN n hn).2
  have hcover :
      {ω | ε ≤ dist (r n * X n ω) 0} ⊆ {ω | ε / M ≤ dist (X n ω) 0} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hprod : ε ≤ |r n| * |X n ω| := by
      simpa [Real.dist_eq, abs_mul] using hω
    have hle : |r n| * |X n ω| ≤ M * |X n ω| :=
      mul_le_mul_of_nonneg_right hrn (abs_nonneg _)
    have hdiv : ε / M ≤ |X n ω| := (div_le_iff₀ hM).2 (by
      simpa [mul_comm] using le_trans hprod hle)
    simpa [Real.dist_eq] using hdiv
  exact le_of_lt (lt_of_le_of_lt (measure_mono hcover) hXn)

/-- Negation of a real-valued `oₚ(1)` sequence is `oₚ(1)`. -/
theorem TendstoInMeasure.neg_zero_real
    {X : ℕ → α → ℝ}
    (hX : TendstoInMeasure μ X atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => -X n ω) atTop (fun _ => 0) := by
  simpa using TendstoInMeasure.const_mul_zero_real (μ := μ) (-1) hX

/-- Difference of two real-valued `oₚ(1)` sequences is `oₚ(1)`. -/
theorem TendstoInMeasure.sub_zero_real
    {X Y : ℕ → α → ℝ}
    (hX : TendstoInMeasure μ X atTop (fun _ => 0))
    (hY : TendstoInMeasure μ Y atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => X n ω - Y n ω) atTop (fun _ => 0) := by
  simpa [sub_eq_add_neg] using
    TendstoInMeasure.add_zero_real hX (TendstoInMeasure.neg_zero_real hY)

/-- Real-valued squeeze to zero in probability by an absolute-value bound. -/
theorem TendstoInMeasure.of_abs_le_zero_real
    {X Y : ℕ → α → ℝ}
    (hY : TendstoInMeasure μ Y atTop (fun _ => 0))
    (hbound : ∀ n ω, |X n ω| ≤ |Y n ω|) :
    TendstoInMeasure μ X atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hY ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hY ε hε) (fun _ => zero_le _) (fun n => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hx : ε ≤ |X n ω| := by
    simpa [Real.dist_eq] using hω
  have hy : ε ≤ |Y n ω| := le_trans hx (hbound n ω)
  simpa [Real.dist_eq] using hy

/-- Center a real-valued convergence-in-measure statement at its scalar limit. -/
theorem TendstoInMeasure.sub_limit_zero_real
    {X : ℕ → α → ℝ} {c : ℝ}
    (hX : TendstoInMeasure μ X atTop (fun _ => c)) :
    TendstoInMeasure μ (fun n ω => X n ω - c) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro ε hε
  simpa [Real.dist_eq] using hX ε hε

/-- Uncenter a real-valued `oₚ(1)` statement at a scalar limit. -/
theorem TendstoInMeasure.of_sub_limit_zero_real
    {X : ℕ → α → ℝ} {c : ℝ}
    (hX : TendstoInMeasure μ (fun n ω => X n ω - c) atTop (fun _ => 0)) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro ε hε
  simpa [Real.dist_eq] using hX ε hε

/-- If `Xₙ - Yₙ = oₚ(1)` and `Yₙ ->p c`, then `Xₙ ->p c`. -/
theorem TendstoInMeasure.of_sub_tendsto_zero_real
    {X Y : ℕ → α → ℝ} {c : ℝ}
    (hXY : TendstoInMeasure μ (fun n ω => X n ω - Y n ω) atTop (fun _ => 0))
    (hY : TendstoInMeasure μ Y atTop (fun _ => c)) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  have hY0 := TendstoInMeasure.sub_limit_zero_real hY
  have hsum := TendstoInMeasure.add_zero_real hXY hY0
  have hX0 :
      TendstoInMeasure μ (fun n ω => X n ω - c) atTop (fun _ => 0) := by
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hsum
    exact ae_of_all μ fun ω => by ring
  exact TendstoInMeasure.of_sub_limit_zero_real hX0

/-- If `Xₙ - Yₙ = oₚ(1)` and `Yₙ ->p c`, then `Xₙ ->p c` for
finite-dimensional real vectors. -/
theorem TendstoInMeasure.of_sub_tendsto_zero_vector
    {k : Type*} [Fintype k]
    {X Y : ℕ → α → k → ℝ} {c : k → ℝ}
    (hXY : TendstoInMeasure μ (fun n ω => X n ω - Y n ω) atTop (fun _ => 0))
    (hY : TendstoInMeasure μ Y atTop (fun _ => c)) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  refine tendstoInMeasure_pi (fun a => ?_)
  have hXYa :
      TendstoInMeasure μ (fun n ω => X n ω a - Y n ω a)
        atTop (fun _ => 0) := by
    simpa using TendstoInMeasure.pi_apply hXY a
  exact TendstoInMeasure.of_sub_tendsto_zero_real hXYa
    (TendstoInMeasure.pi_apply hY a)

/-- If `Xₙ - Yₙ = oₚ(1)` and `Yₙ ->p C`, then `Xₙ ->p C` for
finite-dimensional real matrices. -/
theorem TendstoInMeasure.of_sub_tendsto_zero_matrix
    {r c : Type*} [Fintype r] [Fintype c]
    {X Y : ℕ → α → Matrix r c ℝ} {C : Matrix r c ℝ}
    (hXY : TendstoInMeasure μ (fun n ω => X n ω - Y n ω) atTop (fun _ => 0))
    (hY : TendstoInMeasure μ Y atTop (fun _ => C)) :
    TendstoInMeasure μ X atTop (fun _ => C) := by
  refine tendstoInMeasure_pi (fun a => ?_)
  refine tendstoInMeasure_pi (fun b => ?_)
  have hXYab :
      TendstoInMeasure μ (fun n ω => X n ω a b - Y n ω a b)
        atTop (fun _ => 0) := by
    simpa using TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hXY a) b
  exact TendstoInMeasure.of_sub_tendsto_zero_real hXYab
    (TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hY a) b)

/-- Product of two real-valued sequences converging in measure to scalar limits
converges in measure to the product of the limits. -/
theorem TendstoInMeasure.mul_limits_real
    {X Y : ℕ → α → ℝ} {c d : ℝ}
    (hX : TendstoInMeasure μ X atTop (fun _ => c))
    (hY : TendstoInMeasure μ Y atTop (fun _ => d)) :
    TendstoInMeasure μ (fun n ω => X n ω * Y n ω) atTop (fun _ => c * d) := by
  have hX0 := TendstoInMeasure.sub_limit_zero_real hX
  have hY0 := TendstoInMeasure.sub_limit_zero_real hY
  have hprod := TendstoInMeasure.mul_zero_real hX0 hY0
  have hcY := TendstoInMeasure.const_mul_zero_real (μ := μ) c hY0
  have hdX := TendstoInMeasure.const_mul_zero_real (μ := μ) d hX0
  have hsum :=
    TendstoInMeasure.add_zero_real
      (TendstoInMeasure.add_zero_real hprod hcY) hdX
  have hcenter : TendstoInMeasure μ
      (fun n ω => X n ω * Y n ω - c * d) atTop (fun _ => 0) := by
    refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
    ring
  exact TendstoInMeasure.of_sub_limit_zero_real hcenter

/-- A deterministic real sequence converging to a scalar also converges in
measure when viewed as a constant random variable sequence. -/
theorem tendstoInMeasure_const_real
    {r : ℕ → ℝ} {c : ℝ} (hr : Tendsto r atTop (𝓝 c)) :
    TendstoInMeasure μ (fun n (_ : α) => r n) atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  have hevent : ∀ᶠ n in atTop, dist (r n) c < ε :=
    eventually_atTop.2 ((Metric.tendsto_atTop.1 hr) ε hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨N, fun n hn => ?_⟩
  have hempty : {ω : α | ε ≤ dist (r n) c} = ∅ := by
    ext ω
    simp [not_le_of_gt (hN n hn)]
  rw [hempty, measure_empty]
  exact le_of_lt hδ

/-- If a real sequence of random variables converges in probability to a positive
constant, then the bad event where the sequence is nonpositive has probability
tending to zero. This is the probabilistic replacement for pointwise eventual
standard-error positivity in confidence-interval arguments. -/
theorem tendsto_measure_nonpos_of_tendstoInMeasure_const_pos
    {se : ℕ → α → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hse : TendstoInMeasure μ se atTop (fun _ => c)) :
    Tendsto (fun n => μ {ω | se n ω ≤ 0}) atTop (𝓝 0) := by
  have htail := hse (ENNReal.ofReal c) (ENNReal.ofReal_pos.mpr hc)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  have hle : se n ω ≤ 0 := hω
  have hdist : c ≤ dist (se n ω) c := by
    rw [Real.dist_eq]
    have hnonpos : se n ω - c ≤ 0 := by linarith
    rw [abs_of_nonpos hnonpos]
    linarith
  change ENNReal.ofReal c ≤ edist (se n ω) c
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal hdist

/-- A finite sum of real-valued `oₚ(1)` sequences is `oₚ(1)`.

This is the scalar finite-coordinate glue used by dot-product arguments. -/
theorem tendstoInMeasure_finset_sum_zero_real
    {ι : Type*} (s : Finset ι) {X : ι → ℕ → α → ℝ}
    (hX : ∀ i ∈ s, TendstoInMeasure μ (X i) atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => ∑ i ∈ s, X i n ω) atTop (fun _ => 0) := by
  classical
  revert hX
  refine Finset.induction_on s ?base ?step
  · intro hX
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    simp [not_le_of_gt hε]
  · intro a s has ih hX
    have ha : TendstoInMeasure μ (X a) atTop (fun _ => 0) := by
      exact hX a (by simp [has])
    have hs : TendstoInMeasure μ (fun n ω => ∑ i ∈ s, X i n ω) atTop (fun _ => 0) :=
      ih (fun i hi => hX i (by simp [hi]))
    have hsum := TendstoInMeasure.add_zero_real ha hs
    simpa [Finset.sum_insert has] using hsum

/-- Dot product of two coordinatewise real `oₚ(1)` vector sequences is `oₚ(1)`. -/
theorem tendstoInMeasure_dotProduct_zero_real
    {ι : Type*} [Fintype ι] {X Y : ℕ → α → ι → ℝ}
    (hX : ∀ i : ι, TendstoInMeasure μ (fun n ω => X n ω i) atTop (fun _ => 0))
    (hY : ∀ i : ι, TendstoInMeasure μ (fun n ω => Y n ω i) atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => X n ω ⬝ᵥ Y n ω) atTop (fun _ => 0) := by
  classical
  have hprod : ∀ i ∈ (Finset.univ : Finset ι),
      TendstoInMeasure μ (fun n ω => X n ω i * Y n ω i) atTop (fun _ => 0) := by
    intro i _
    exact TendstoInMeasure.mul_zero_real (hX i) (hY i)
  have hsum := tendstoInMeasure_finset_sum_zero_real (μ := μ)
    (s := (Finset.univ : Finset ι))
    (X := fun i n ω => X n ω i * Y n ω i) hprod
  refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  simp [dotProduct]

/-- A real-valued sequence of random variables is bounded in probability (`Oₚ(1)`).

This formulation is intentionally minimal: for every probability tolerance `δ`,
there is a positive deterministic bound `M` such that the tail event
`{ω | M ≤ ‖Xₙ ω‖}` has measure at most `δ`, eventually in `n`. -/
def BoundedInProbability (μ : Measure α) (X : ℕ → α → ℝ) : Prop :=
  ∀ δ : ℝ≥0∞, 0 < δ → ∃ M : ℝ, 0 < M ∧
    ∀ᶠ n in atTop, μ {ω | M ≤ ‖X n ω‖} ≤ δ

/-- Uniform integrability of real random variables passes to absolute values.

Mathlib's probability-theory `UniformIntegrable` is norm-based, so this is a
thin real-valued bridge used when textbook arguments write averages of
`|Xᵢ|`. -/
theorem uniformIntegrable_abs
    {p : ℝ≥0∞} {X : ℕ → α → ℝ}
    (hX : UniformIntegrable X p μ) :
    UniformIntegrable (fun n ω => |X n ω|) p μ := by
  refine ⟨fun n => continuous_abs.comp_aestronglyMeasurable (hX.aestronglyMeasurable n), ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := hX.unifIntegrable hε
    refine ⟨δ, hδ, fun n s hs hμs => ?_⟩
    refine (eLpNorm_mono_ae (p := p) (μ := μ) ?_).trans (hsmall n s hs hμs)
    refine ae_of_all μ fun ω => ?_
    by_cases hω : ω ∈ s <;> simp [hω, Real.norm_eq_abs]
  · obtain ⟨C, hC⟩ := hX.2.2
    refine ⟨C, fun n => ?_⟩
    refine (eLpNorm_mono_ae (p := p) (μ := μ) ?_).trans (hC n)
    refine ae_of_all μ fun ω => ?_
    simp [Real.norm_eq_abs]

/-- Real convergence in distribution implies boundedness in probability.

This is the tightness bridge behind the scalar CLT step in Chapter 7: if the
laws of `Xₙ` converge weakly on `ℝ`, then the sequence is `Oₚ(1)`. -/
theorem BoundedInProbability.of_tendstoInDistribution
    {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ => μ) ν) :
    BoundedInProbability μ X := by
  let law : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨μ.map (X n), Measure.isProbabilityMeasure_map (h.forall_aemeasurable n)⟩
  let lawZ : ProbabilityMeasure ℝ :=
    ⟨ν.map Z, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩
  have hlaw : Tendsto law atTop (𝓝 lawZ) := by
    simpa [law, lawZ] using h.tendsto
  have hcompact_insert : IsCompact (insert lawZ (Set.range law)) :=
    hlaw.isCompact_insert_range
  have hclosure_subset : closure (Set.range law) ⊆ insert lawZ (Set.range law) :=
    closure_minimal (by intro x hx; exact Or.inr hx) hcompact_insert.isClosed
  have hcompact_closure : IsCompact (closure (Set.range law)) :=
    hcompact_insert.of_isClosed_subset isClosed_closure hclosure_subset
  have htight : IsTightMeasureSet
      {((ρ : ProbabilityMeasure ℝ) : Measure ℝ) | ρ ∈ Set.range law} :=
    isTightMeasureSet_of_isCompact_closure (S := Set.range law) hcompact_closure
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  intro δ hδ
  obtain ⟨K, hKcompact, hKtail⟩ := htight δ hδ
  obtain ⟨M, hMpos, hKball⟩ := hKcompact.isBounded.subset_ball_lt 0 (0 : ℝ)
  refine ⟨M, hMpos, Eventually.of_forall ?_⟩
  intro n
  have htail_meas : MeasurableSet {x : ℝ | M ≤ ‖x‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have htail_subset : {x : ℝ | M ≤ ‖x‖} ⊆ Kᶜ := by
    intro x hx hxK
    have hxball := hKball hxK
    have hxlt : ‖x‖ < M := by
      simpa [Metric.mem_ball, dist_eq_norm] using hxball
    exact (not_le_of_gt hxlt) hx
  have hlawK : ((law n : ProbabilityMeasure ℝ) : Measure ℝ) Kᶜ ≤ δ := by
    exact hKtail ((law n : ProbabilityMeasure ℝ) : Measure ℝ)
      ⟨law n, ⟨n, rfl⟩, rfl⟩
  have hmap_tail :
      (μ.map (X n)) {x : ℝ | M ≤ ‖x‖} =
        μ {ω | M ≤ ‖X n ω‖} := by
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) htail_meas]
    rfl
  calc
    μ {ω | M ≤ ‖X n ω‖}
        = (μ.map (X n)) {x : ℝ | M ≤ ‖x‖} := hmap_tail.symm
    _ = ((law n : ProbabilityMeasure ℝ) : Measure ℝ) {x : ℝ | M ≤ ‖x‖} := rfl
    _ ≤ ((law n : ProbabilityMeasure ℝ) : Measure ℝ) Kᶜ := measure_mono htail_subset
    _ ≤ δ := hlawK

/-- Real convergence in probability to a constant implies boundedness in
probability. -/
theorem BoundedInProbability.of_tendstoInMeasure_const
    {μ : Measure α} {X : ℕ → α → ℝ} {c : ℝ}
    (hX : TendstoInMeasure μ X atTop (fun _ => c)) :
    BoundedInProbability μ X := by
  rw [tendstoInMeasure_iff_dist] at hX
  intro δ hδ
  refine ⟨|c| + 1, by positivity, ?_⟩
  have htail := (hX 1 zero_lt_one).eventually_lt_const hδ
  filter_upwards [htail] with n hn
  have hcover : {ω | |c| + 1 ≤ ‖X n ω‖} ⊆ {ω | 1 ≤ dist (X n ω) c} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs] at hω ⊢
    have habs : |X n ω| ≤ |X n ω - c| + |c| := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        (abs_add_le (X n ω - c) c)
    have hdist : 1 ≤ |X n ω - c| := by
      linarith
    simpa [Real.dist_eq] using hdist
  exact le_of_lt (lt_of_le_of_lt (measure_mono hcover) hn)

/-- A uniform eventual first absolute-moment bound implies scalar `Oₚ(1)`.

This is the Markov-inequality face of Hansen Theorem 6.12 for the case
`aₙ = 1` and moment exponent one. Higher-moment statements reduce to this
after applying the theorem to the nonnegative transformed sequence. -/
theorem BoundedInProbability.of_eventually_integral_norm_bound
    [IsFiniteMeasure μ] {X : ℕ → α → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hInt : ∀ n, Integrable (fun ω => ‖X n ω‖) μ)
    (hBound : ∀ᶠ n in atTop, ∫ ω, ‖X n ω‖ ∂μ ≤ C) :
    BoundedInProbability μ X := by
  intro δ hδ
  by_cases hδtop : δ = ∞
  · refine ⟨1, by norm_num, Eventually.of_forall ?_⟩
    intro n
    rw [hδtop]
    exact le_top
  have hδreal_pos : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
  let M : ℝ := (C + 1) / δ.toReal
  have hC1pos : 0 < C + 1 := by linarith
  have hMpos : 0 < M := div_pos hC1pos hδreal_pos
  refine ⟨M, hMpos, hBound.mono ?_⟩
  intro n hn
  have hmarkov :
      M * μ.real {ω | M ≤ ‖X n ω‖} ≤ ∫ ω, ‖X n ω‖ ∂μ :=
    mul_meas_ge_le_integral_of_nonneg
      (ae_of_all μ fun ω => norm_nonneg (X n ω)) (hInt n) M
  have hreal_le : μ.real {ω | M ≤ ‖X n ω‖} ≤ C / M := by
    have hmul_le : μ.real {ω | M ≤ ‖X n ω‖} * M ≤ C := by
      calc
        μ.real {ω | M ≤ ‖X n ω‖} * M
            = M * μ.real {ω | M ≤ ‖X n ω‖} := by ring
        _ ≤ ∫ ω, ‖X n ω‖ ∂μ := hmarkov
        _ ≤ C := hn
    exact (le_div_iff₀ hMpos).2 hmul_le
  have hratio : C / M ≤ δ.toReal := by
    dsimp [M]
    have hC1ne : C + 1 ≠ 0 := by linarith
    have hδne : δ.toReal ≠ 0 := hδreal_pos.ne'
    field_simp [hC1ne, hδne]
    nlinarith [hC, hδreal_pos.le]
  have htail_ofReal :
      μ {ω | M ≤ ‖X n ω‖} ≤ ENNReal.ofReal (C / M) := by
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (div_nonneg hC hMpos.le)]
    simpa [measureReal_def] using hreal_le
  have htail_delta : ENNReal.ofReal (C / M) ≤ δ := by
    rw [ENNReal.ofReal_le_iff_le_toReal hδtop]
    exact hratio
  exact htail_ofReal.trans htail_delta

/-- A uniformly integrable real sequence is bounded in probability.

For `p = 1`, Mathlib's `UniformIntegrable` includes a uniform `L¹` bound; the
claim is the Markov-inequality `Oₚ(1)` consequence of that bound. -/
theorem BoundedInProbability.of_uniformIntegrable_one
    [IsFiniteMeasure μ] {X : ℕ → α → ℝ}
    (hX : UniformIntegrable X 1 μ) :
    BoundedInProbability μ X := by
  obtain ⟨C, hC⟩ := hX.2.2
  refine BoundedInProbability.of_eventually_integral_norm_bound
    (C := (C : ℝ)) (NNReal.coe_nonneg C) ?_ ?_
  · intro n
    exact (memLp_one_iff_integrable.mp (hX.memLp n)).norm
  · refine Eventually.of_forall fun n => ?_
    have hIntX : Integrable (X n) μ :=
      memLp_one_iff_integrable.mp (hX.memLp n)
    have hEq :
        ENNReal.ofReal (∫ ω, ‖X n ω‖ ∂μ) = eLpNorm (X n) 1 μ := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      exact ofReal_integral_norm_eq_lintegral_enorm hIntX
    have hInt_nonneg : 0 ≤ ∫ ω, ‖X n ω‖ ∂μ :=
      integral_nonneg_of_ae (ae_of_all μ fun ω => norm_nonneg (X n ω))
    have hleReal := ENNReal.toReal_mono ENNReal.coe_ne_top (hC n)
    rw [← hEq, ENNReal.toReal_ofReal hInt_nonneg] at hleReal
    simpa using hleReal

/-- An eventual higher natural-moment bound implies scalar `Oₚ(1)`.

This is the natural-power Markov-inequality face of Hansen Theorem 6.12.
The positive-real-exponent face is
`BoundedInProbability.of_eventually_integral_norm_rpow_bound`; this wrapper
keeps the common integer-moment cases convenient. -/
theorem BoundedInProbability.of_eventually_integral_norm_pow_bound
    [IsFiniteMeasure μ] {X : ℕ → α → ℝ} {C : ℝ} {r : ℕ}
    (hr : r ≠ 0)
    (hC : 0 ≤ C)
    (hInt : ∀ n, Integrable (fun ω => ‖X n ω‖ ^ r) μ)
    (hBound : ∀ᶠ n in atTop, ∫ ω, ‖X n ω‖ ^ r ∂μ ≤ C) :
    BoundedInProbability μ X := by
  intro δ hδ
  by_cases hδtop : δ = ∞
  · refine ⟨1, by norm_num, Eventually.of_forall ?_⟩
    intro n
    rw [hδtop]
    exact le_top
  have hδreal_pos : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
  let B : ℝ := (C + 1) / δ.toReal
  let M : ℝ := B + 1
  have hC1pos : 0 < C + 1 := by linarith
  have hBpos : 0 < B := div_pos hC1pos hδreal_pos
  have hMpos : 0 < M := by dsimp [M]; linarith
  have hMge_one : 1 ≤ M := by dsimp [M]; linarith
  let T : ℝ := M ^ r
  have hTpos : 0 < T := pow_pos hMpos r
  refine ⟨M, hMpos, hBound.mono ?_⟩
  intro n hn
  have hcover :
      {ω | M ≤ ‖X n ω‖} ⊆ {ω | T ≤ ‖X n ω‖ ^ r} := by
    intro ω hω
    exact pow_le_pow_left₀ hMpos.le hω r
  have hmarkov :
      T * μ.real {ω | T ≤ ‖X n ω‖ ^ r} ≤ ∫ ω, ‖X n ω‖ ^ r ∂μ :=
    mul_meas_ge_le_integral_of_nonneg
      (ae_of_all μ fun ω => pow_nonneg (norm_nonneg (X n ω)) r) (hInt n) T
  have hreal_le : μ.real {ω | T ≤ ‖X n ω‖ ^ r} ≤ C / T := by
    have hmul_le : μ.real {ω | T ≤ ‖X n ω‖ ^ r} * T ≤ C := by
      calc
        μ.real {ω | T ≤ ‖X n ω‖ ^ r} * T
            = T * μ.real {ω | T ≤ ‖X n ω‖ ^ r} := by ring
        _ ≤ ∫ ω, ‖X n ω‖ ^ r ∂μ := hmarkov
        _ ≤ C := hn
    exact (le_div_iff₀ hTpos).2 hmul_le
  have hratio : C / T ≤ δ.toReal := by
    have hB_le_M : B ≤ M := by dsimp [M]; linarith
    have hM_le_T : M ≤ T := by
      dsimp [T]
      exact Bound.le_self_pow_of_pos hMge_one (Nat.pos_of_ne_zero hr)
    have hB_le_T : B ≤ T := hB_le_M.trans hM_le_T
    have hδB_le : δ.toReal * B ≤ δ.toReal * T :=
      mul_le_mul_of_nonneg_left hB_le_T hδreal_pos.le
    have hδB : δ.toReal * B = C + 1 := by
      dsimp [B]
      field_simp [hδreal_pos.ne']
    exact (div_le_iff₀ hTpos).2 (by nlinarith)
  have htail_power :
      μ {ω | T ≤ ‖X n ω‖ ^ r} ≤ ENNReal.ofReal (C / T) := by
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (div_nonneg hC hTpos.le)]
    simpa [measureReal_def] using hreal_le
  have htail_delta : ENNReal.ofReal (C / T) ≤ δ := by
    rw [ENNReal.ofReal_le_iff_le_toReal hδtop]
    exact hratio
  exact (measure_mono hcover).trans (htail_power.trans htail_delta)

/-- An eventual positive-real moment bound implies scalar `Oₚ(1)`.

This is the arbitrary positive-real-exponent Markov-inequality face of Hansen
Theorem 6.12 for the unit scale: if `E|Xₙ|^p` is eventually bounded for some
`p > 0`, then `Xₙ = Oₚ(1)`. -/
theorem BoundedInProbability.of_eventually_integral_norm_rpow_bound
    [IsFiniteMeasure μ] {X : ℕ → α → ℝ} {C p : ℝ}
    (hp : 0 < p)
    (hC : 0 ≤ C)
    (hInt : ∀ n, Integrable (fun ω => ‖X n ω‖ ^ p) μ)
    (hBound : ∀ᶠ n in atTop, ∫ ω, ‖X n ω‖ ^ p ∂μ ≤ C) :
    BoundedInProbability μ X := by
  intro δ hδ
  by_cases hδtop : δ = ∞
  · refine ⟨1, by norm_num, Eventually.of_forall ?_⟩
    intro n
    rw [hδtop]
    exact le_top
  have hδreal_pos : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
  let B : ℝ := (C + 1) / δ.toReal
  let T : ℝ := B + 1
  let M : ℝ := T ^ p⁻¹
  have hC1pos : 0 < C + 1 := by linarith
  have hBpos : 0 < B := div_pos hC1pos hδreal_pos
  have hTpos : 0 < T := by dsimp [T]; linarith
  have hMpos : 0 < M := Real.rpow_pos_of_pos hTpos p⁻¹
  have hMpow : M ^ p = T := by
    dsimp [M]
    simpa using Real.rpow_inv_rpow hTpos.le hp.ne'
  refine ⟨M, hMpos, hBound.mono ?_⟩
  intro n hn
  have hcover :
      {ω | M ≤ ‖X n ω‖} ⊆ {ω | T ≤ ‖X n ω‖ ^ p} := by
    intro ω hω
    have hpow : M ^ p ≤ ‖X n ω‖ ^ p :=
      Real.rpow_le_rpow hMpos.le hω hp.le
    simpa [hMpow] using hpow
  have hmarkov :
      T * μ.real {ω | T ≤ ‖X n ω‖ ^ p} ≤ ∫ ω, ‖X n ω‖ ^ p ∂μ :=
    mul_meas_ge_le_integral_of_nonneg
      (ae_of_all μ fun ω => Real.rpow_nonneg (norm_nonneg (X n ω)) p) (hInt n) T
  have hreal_le : μ.real {ω | T ≤ ‖X n ω‖ ^ p} ≤ C / T := by
    have hmul_le : μ.real {ω | T ≤ ‖X n ω‖ ^ p} * T ≤ C := by
      calc
        μ.real {ω | T ≤ ‖X n ω‖ ^ p} * T
            = T * μ.real {ω | T ≤ ‖X n ω‖ ^ p} := by ring
        _ ≤ ∫ ω, ‖X n ω‖ ^ p ∂μ := hmarkov
        _ ≤ C := hn
    exact (le_div_iff₀ hTpos).2 hmul_le
  have hratio : C / T ≤ δ.toReal := by
    have hδB : δ.toReal * B = C + 1 := by
      dsimp [B]
      field_simp [hδreal_pos.ne']
    exact (div_le_iff₀ hTpos).2 (by
      dsimp [T]
      nlinarith [hδB, hδreal_pos])
  have htail_power :
      μ {ω | T ≤ ‖X n ω‖ ^ p} ≤ ENNReal.ofReal (C / T) := by
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (div_nonneg hC hTpos.le)]
    simpa [measureReal_def] using hreal_le
  have htail_delta : ENNReal.ofReal (C / T) ≤ δ := by
    rw [ENNReal.ofReal_le_iff_le_toReal hδtop]
    exact hratio
  exact (measure_mono hcover).trans (htail_power.trans htail_delta)

/-- Scaled natural-moment bounds imply scaled scalar `Oₚ(1)`.

If `E|Xₙ|^m` is eventually bounded by `C aₙ^m` for a positive deterministic
scale `aₙ`, then `aₙ⁻¹ Xₙ` is bounded in probability. This is the integer-power
scaled version of Hansen Theorem 6.12; see
`BoundedInProbability.of_eventually_integral_norm_rpow_scaled_bound` for the
positive-real-exponent version. -/
theorem BoundedInProbability.of_eventually_integral_norm_pow_scaled_bound
    [IsFiniteMeasure μ] {X : ℕ → α → ℝ} {a : ℕ → ℝ} {C : ℝ} {r : ℕ}
    (hr : r ≠ 0)
    (hC : 0 ≤ C)
    (ha : ∀ᶠ n in atTop, 0 < a n)
    (hInt : ∀ n, Integrable (fun ω => ‖X n ω‖ ^ r) μ)
    (hBound : ∀ᶠ n in atTop, ∫ ω, ‖X n ω‖ ^ r ∂μ ≤ C * (a n) ^ r) :
    BoundedInProbability μ (fun n ω => (a n)⁻¹ * X n ω) := by
  refine BoundedInProbability.of_eventually_integral_norm_pow_bound
    (C := C) (r := r) hr hC ?_ ?_
  · intro n
    simpa [norm_mul, mul_pow, mul_comm, mul_left_comm, mul_assoc] using
      (hInt n).const_mul (‖(a n)⁻¹‖ ^ r)
  · filter_upwards [ha, hBound] with n hapos hn
    have hscale_nonneg : 0 ≤ ‖(a n)⁻¹‖ ^ r := pow_nonneg (norm_nonneg _) r
    calc
      ∫ ω, ‖(a n)⁻¹ * X n ω‖ ^ r ∂μ
          = ∫ ω, ‖(a n)⁻¹‖ ^ r * ‖X n ω‖ ^ r ∂μ := by
            congr 1
            ext ω
            simp [norm_mul, mul_pow]
      _ = ‖(a n)⁻¹‖ ^ r * ∫ ω, ‖X n ω‖ ^ r ∂μ := by
            rw [integral_const_mul]
      _ ≤ ‖(a n)⁻¹‖ ^ r * (C * (a n) ^ r) :=
            mul_le_mul_of_nonneg_left hn hscale_nonneg
      _ = C := by
            have hpow_ne : (a n) ^ r ≠ 0 := pow_ne_zero r hapos.ne'
            rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hapos), inv_pow]
            field_simp [hpow_ne]

/-- Scaled positive-real moment bounds imply scaled scalar `Oₚ(1)`.

If `E|Xₙ|^p` is eventually bounded by `C aₙ^p` for a positive deterministic
scale `aₙ` and `p > 0`, then `aₙ⁻¹ Xₙ` is bounded in probability. This is the
positive-real-exponent scaled face of Hansen Theorem 6.12. -/
theorem BoundedInProbability.of_eventually_integral_norm_rpow_scaled_bound
    [IsFiniteMeasure μ] {X : ℕ → α → ℝ} {a : ℕ → ℝ} {C p : ℝ}
    (hp : 0 < p)
    (hC : 0 ≤ C)
    (ha : ∀ᶠ n in atTop, 0 < a n)
    (hInt : ∀ n, Integrable (fun ω => ‖X n ω‖ ^ p) μ)
    (hBound : ∀ᶠ n in atTop, ∫ ω, ‖X n ω‖ ^ p ∂μ ≤ C * (a n) ^ p) :
    BoundedInProbability μ (fun n ω => (a n)⁻¹ * X n ω) := by
  refine BoundedInProbability.of_eventually_integral_norm_rpow_bound
    (C := C) (p := p) hp hC ?_ ?_
  · intro n
    have hEq :
        (fun ω => ‖(a n)⁻¹ * X n ω‖ ^ p) =
          fun ω => ‖(a n)⁻¹‖ ^ p * ‖X n ω‖ ^ p := by
      funext ω
      rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    rw [hEq]
    exact (hInt n).const_mul (‖(a n)⁻¹‖ ^ p)
  · filter_upwards [ha, hBound] with n hapos hn
    have hscale_nonneg : 0 ≤ ‖(a n)⁻¹‖ ^ p :=
      Real.rpow_nonneg (norm_nonneg _) p
    calc
      ∫ ω, ‖(a n)⁻¹ * X n ω‖ ^ p ∂μ
          = ∫ ω, ‖(a n)⁻¹‖ ^ p * ‖X n ω‖ ^ p ∂μ := by
            congr 1
            ext ω
            rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
      _ = ‖(a n)⁻¹‖ ^ p * ∫ ω, ‖X n ω‖ ^ p ∂μ := by
            rw [integral_const_mul]
      _ ≤ ‖(a n)⁻¹‖ ^ p * (C * (a n) ^ p) :=
            mul_le_mul_of_nonneg_left hn hscale_nonneg
      _ = C := by
            rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hapos), Real.inv_rpow hapos.le p]
            have hpow_ne : (a n) ^ p ≠ 0 := (Real.rpow_pos_of_pos hapos p).ne'
            field_simp [hpow_ne]

/-- Scaled positive-real moments tending to zero imply scaled `oₚ(1)`.

This is the little-`oₚ` Markov-inequality face of Hansen Theorem 6.12: if
`E|Xₙ|^p / aₙ^p → 0` for a positive deterministic scale `aₙ` and `p > 0`, then
`aₙ⁻¹ Xₙ →ₚ 0`. -/
theorem TendstoInMeasure.of_integral_norm_rpow_scaled_tendsto_zero
    [IsFiniteMeasure μ] {X : ℕ → α → ℝ} {a : ℕ → ℝ} {p : ℝ}
    (hp : 0 < p)
    (ha : ∀ᶠ n in atTop, 0 < a n)
    (hInt : ∀ n, Integrable (fun ω => ‖X n ω‖ ^ p) μ)
    (hScaled :
      Tendsto (fun n => (∫ ω, ‖X n ω‖ ^ p ∂μ) / (a n) ^ p) atTop (𝓝 0)) :
    TendstoInMeasure μ (fun n ω => (a n)⁻¹ * X n ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  by_cases hδtop : δ = ∞
  · refine ⟨0, fun n _ => ?_⟩
    rw [hδtop]
    exact le_top
  have hδreal_pos : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' hδtop
  let T : ℝ := ε ^ p
  have hTpos : 0 < T := Real.rpow_pos_of_pos hε p
  have htarget_pos : 0 < δ.toReal * T := mul_pos hδreal_pos hTpos
  have hsmall : ∀ᶠ n in atTop,
      dist ((∫ ω, ‖X n ω‖ ^ p ∂μ) / (a n) ^ p) 0 < δ.toReal * T :=
    eventually_atTop.2 ((Metric.tendsto_atTop.1 hScaled) (δ.toReal * T) htarget_pos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ha.and hsmall)
  refine ⟨N, fun n hn => ?_⟩
  have hapos : 0 < a n := (hN n hn).1
  have hsmalln :
      dist ((∫ ω, ‖X n ω‖ ^ p ∂μ) / (a n) ^ p) 0 < δ.toReal * T :=
    (hN n hn).2
  have hscaled_eq :
      ∫ ω, ‖(a n)⁻¹ * X n ω‖ ^ p ∂μ =
        (∫ ω, ‖X n ω‖ ^ p ∂μ) / (a n) ^ p := by
    calc
      ∫ ω, ‖(a n)⁻¹ * X n ω‖ ^ p ∂μ
          = ∫ ω, ‖(a n)⁻¹‖ ^ p * ‖X n ω‖ ^ p ∂μ := by
            congr 1
            ext ω
            rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
      _ = ‖(a n)⁻¹‖ ^ p * ∫ ω, ‖X n ω‖ ^ p ∂μ := by
            rw [integral_const_mul]
      _ = (∫ ω, ‖X n ω‖ ^ p ∂μ) / (a n) ^ p := by
            rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hapos), Real.inv_rpow hapos.le p]
            ring
  have hscaled_nonneg :
      0 ≤ (∫ ω, ‖X n ω‖ ^ p ∂μ) / (a n) ^ p := by
    rw [← hscaled_eq]
    exact integral_nonneg_of_ae (ae_of_all μ fun ω =>
      Real.rpow_nonneg (norm_nonneg ((a n)⁻¹ * X n ω)) p)
  have hratio_lt :
      (∫ ω, ‖X n ω‖ ^ p ∂μ) / (a n) ^ p < δ.toReal * T := by
    have hdist_eq :
        dist ((∫ ω, ‖X n ω‖ ^ p ∂μ) / (a n) ^ p) 0 =
          (∫ ω, ‖X n ω‖ ^ p ∂μ) / (a n) ^ p := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hscaled_nonneg]
    rwa [hdist_eq] at hsmalln
  have hscaled_lt :
      ∫ ω, ‖(a n)⁻¹ * X n ω‖ ^ p ∂μ < δ.toReal * T := by
    rw [hscaled_eq]
    exact hratio_lt
  let A : Set α := {ω | ε ≤ dist ((a n)⁻¹ * X n ω) 0}
  let B : Set α := {ω | T ≤ ‖(a n)⁻¹ * X n ω‖ ^ p}
  have hcover : A ⊆ B := by
    intro ω hω
    have hnorm : ε ≤ ‖(a n)⁻¹ * X n ω‖ := by
      simpa [A, Real.dist_eq] using hω
    exact Real.rpow_le_rpow hε.le hnorm hp.le
  have hint_scaled : Integrable (fun ω => ‖(a n)⁻¹ * X n ω‖ ^ p) μ := by
    have hEq :
        (fun ω => ‖(a n)⁻¹ * X n ω‖ ^ p) =
          fun ω => ‖(a n)⁻¹‖ ^ p * ‖X n ω‖ ^ p := by
      funext ω
      rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    rw [hEq]
    exact (hInt n).const_mul (‖(a n)⁻¹‖ ^ p)
  have hmarkov :
      T * μ.real B ≤ ∫ ω, ‖(a n)⁻¹ * X n ω‖ ^ p ∂μ :=
    mul_meas_ge_le_integral_of_nonneg
      (ae_of_all μ fun ω => Real.rpow_nonneg (norm_nonneg ((a n)⁻¹ * X n ω)) p)
      hint_scaled T
  have hreal_B_lt : μ.real B < δ.toReal := by
    have hle : μ.real B ≤ (∫ ω, ‖(a n)⁻¹ * X n ω‖ ^ p ∂μ) / T := by
      exact (le_div_iff₀ hTpos).2 (by
        calc
          μ.real B * T = T * μ.real B := by ring
          _ ≤ ∫ ω, ‖(a n)⁻¹ * X n ω‖ ^ p ∂μ := hmarkov)
    have hdiv_lt : (∫ ω, ‖(a n)⁻¹ * X n ω‖ ^ p ∂μ) / T < δ.toReal := by
      exact (div_lt_iff₀ hTpos).2 (by
        simpa [mul_comm] using hscaled_lt)
    exact lt_of_le_of_lt hle hdiv_lt
  have hB_lt : μ B < ENNReal.ofReal δ.toReal := by
    rw [ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top μ B)]
    simpa [measureReal_def] using hreal_B_lt
  have hA_lt : μ A < ENNReal.ofReal δ.toReal :=
    lt_of_le_of_lt (measure_mono hcover) hB_lt
  exact le_of_lt (by simpa [A, ENNReal.ofReal_toReal hδtop] using hA_lt)

/-- Scaled first absolute-moment bounds imply scaled scalar `Oₚ(1)`.

This is the `δ = 1` scaled face of Hansen Theorem 6.12: if the first absolute
moment of `Xₙ` is eventually bounded by a positive deterministic scale `aₙ`,
then `aₙ⁻¹ Xₙ` is bounded in probability. -/
theorem BoundedInProbability.of_eventually_integral_norm_scaled_bound
    [IsFiniteMeasure μ] {X : ℕ → α → ℝ} {a : ℕ → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (ha : ∀ᶠ n in atTop, 0 < a n)
    (hInt : ∀ n, Integrable (fun ω => ‖X n ω‖) μ)
    (hBound : ∀ᶠ n in atTop, ∫ ω, ‖X n ω‖ ∂μ ≤ C * a n) :
    BoundedInProbability μ (fun n ω => (a n)⁻¹ * X n ω) := by
  refine BoundedInProbability.of_eventually_integral_norm_bound (C := C) hC ?_ ?_
  · intro n
    simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc] using
      (hInt n).const_mul ‖(a n)⁻¹‖
  · filter_upwards [ha, hBound] with n hapos hn
    have hscale_nonneg : 0 ≤ ‖(a n)⁻¹‖ := norm_nonneg _
    calc
      ∫ ω, ‖(a n)⁻¹ * X n ω‖ ∂μ
          = ∫ ω, ‖(a n)⁻¹‖ * ‖X n ω‖ ∂μ := by
            congr 1
            ext ω
            simp [norm_mul]
      _ = ‖(a n)⁻¹‖ * ∫ ω, ‖X n ω‖ ∂μ := by
            rw [integral_const_mul]
      _ ≤ ‖(a n)⁻¹‖ * (C * a n) := mul_le_mul_of_nonneg_left hn hscale_nonneg
      _ = C := by
            rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hapos)]
            field_simp [hapos.ne']

/-- A pointwise absolute bound transfers boundedness in probability. -/
theorem BoundedInProbability.of_abs_le
    {μ : Measure α} {X Y : ℕ → α → ℝ}
    (hY : BoundedInProbability μ Y)
    (hXY : ∀ n ω, |X n ω| ≤ |Y n ω|) :
    BoundedInProbability μ X := by
  intro δ hδ
  rcases hY δ hδ with ⟨M, hMpos, hM⟩
  refine ⟨M, hMpos, hM.mono ?_⟩
  intro n hn
  have hcover : {ω | M ≤ ‖X n ω‖} ⊆ {ω | M ≤ ‖Y n ω‖} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs] at hω ⊢
    exact le_trans hω (hXY n ω)
  exact le_trans (measure_mono hcover) hn

/-- Real-valued `Oₚ(1)` sequences are closed under addition. -/
theorem BoundedInProbability.add
    {μ : Measure α} {X Y : ℕ → α → ℝ}
    (hX : BoundedInProbability μ X)
    (hY : BoundedInProbability μ Y) :
    BoundedInProbability μ (fun n ω => X n ω + Y n ω) := by
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.div_pos hδ.ne' ENNReal.ofNat_ne_top
  rcases hX (δ / 2) hδ2 with ⟨MX, hMXpos, hMX⟩
  rcases hY (δ / 2) hδ2 with ⟨MY, hMYpos, hMY⟩
  refine ⟨MX + MY, add_pos hMXpos hMYpos, ?_⟩
  filter_upwards [hMX, hMY] with n hnX hnY
  have hcover :
      {ω | MX + MY ≤ ‖X n ω + Y n ω‖} ⊆
        {ω | MX ≤ ‖X n ω‖} ∪ {ω | MY ≤ ‖Y n ω‖} := by
    intro ω hω
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_cases hXbig : MX ≤ ‖X n ω‖
    · exact Or.inl hXbig
    · right
      have hXlt : ‖X n ω‖ < MX := not_le.mp hXbig
      by_contra hYbig
      have hYlt : ‖Y n ω‖ < MY := not_le.mp hYbig
      have hsum_lt : ‖X n ω + Y n ω‖ < MX + MY := by
        exact lt_of_le_of_lt (norm_add_le _ _) (add_lt_add hXlt hYlt)
      exact (not_le_of_gt hsum_lt) hω
  calc
    μ {ω | MX + MY ≤ ‖X n ω + Y n ω‖}
        ≤ μ ({ω | MX ≤ ‖X n ω‖} ∪ {ω | MY ≤ ‖Y n ω‖}) := measure_mono hcover
    _ ≤ μ {ω | MX ≤ ‖X n ω‖} + μ {ω | MY ≤ ‖Y n ω‖} := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hnX hnY
    _ = δ := ENNReal.add_halves δ

/-- Real-valued `Oₚ(1)` sequences are closed under multiplication. -/
theorem BoundedInProbability.mul
    {μ : Measure α} {X Y : ℕ → α → ℝ}
    (hX : BoundedInProbability μ X)
    (hY : BoundedInProbability μ Y) :
    BoundedInProbability μ (fun n ω => X n ω * Y n ω) := by
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.div_pos hδ.ne' ENNReal.ofNat_ne_top
  rcases hX (δ / 2) hδ2 with ⟨MX, hMXpos, hMX⟩
  rcases hY (δ / 2) hδ2 with ⟨MY, hMYpos, hMY⟩
  refine ⟨MX * MY, mul_pos hMXpos hMYpos, ?_⟩
  filter_upwards [hMX, hMY] with n hnX hnY
  have hcover :
      {ω | MX * MY ≤ ‖X n ω * Y n ω‖} ⊆
        {ω | MX ≤ ‖X n ω‖} ∪ {ω | MY ≤ ‖Y n ω‖} := by
    intro ω hω
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_cases hXbig : MX ≤ ‖X n ω‖
    · exact Or.inl hXbig
    · right
      have hXlt : ‖X n ω‖ < MX := not_le.mp hXbig
      by_contra hYbig
      have hYlt : ‖Y n ω‖ < MY := not_le.mp hYbig
      have hprod_lt : ‖X n ω * Y n ω‖ < MX * MY := by
        rw [norm_mul]
        exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos
          hXlt hYlt.le (norm_nonneg _) hMYpos
      exact (not_le_of_gt hprod_lt) hω
  calc
    μ {ω | MX * MY ≤ ‖X n ω * Y n ω‖}
        ≤ μ ({ω | MX ≤ ‖X n ω‖} ∪ {ω | MY ≤ ‖Y n ω‖}) := measure_mono hcover
    _ ≤ μ {ω | MX ≤ ‖X n ω‖} + μ {ω | MY ≤ ‖Y n ω‖} := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hnX hnY
    _ = δ := ENNReal.add_halves δ

/-- **Portmanteau event-probability bridge for distributional limits.**

If `Xₙ ⇒ Z` and `E` is a Borel set whose frontier has zero mass under the
limit law, then the probabilities of the events `{Xₙ ∈ E}` converge to the
limit-law probability of `E`. This is the reusable coverage/critical-region
bridge for events in arbitrary spaces where Mathlib's portmanteau theorem
applies. -/
theorem TendstoInDistribution.tendsto_measure_preimage_of_null_frontier
    {Ω Ω' E₀ : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {mE₀ : MeasurableSpace E₀} [TopologicalSpace E₀] [OpensMeasurableSpace E₀]
    [HasOuterApproxClosed E₀]
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → E₀} {Z : Ω' → E₀} {E : Set E₀}
    (h : TendstoInDistribution X atTop Z P ν)
    (hE : MeasurableSet E)
    (hfrontier : (ν.map Z) (frontier E) = 0) :
    Tendsto (fun n => P n {ω | X n ω ∈ E})
      atTop (𝓝 ((ν.map Z) E)) := by
  let law : ℕ → ProbabilityMeasure E₀ := fun n =>
    ⟨(P n).map (X n), Measure.isProbabilityMeasure_map (h.forall_aemeasurable n)⟩
  let lawZ : ProbabilityMeasure E₀ :=
    ⟨ν.map Z, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩
  have hlaw : Tendsto law atTop (𝓝 lawZ) := by
    simpa [law, lawZ] using h.tendsto
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (μ := lawZ) (μs := law) hlaw (by simpa [lawZ] using hfrontier)
  have hseq_eq :
      (fun n => ((law n : ProbabilityMeasure E₀) : Measure E₀) E) =
        fun n => P n {ω | X n ω ∈ E} := by
    funext n
    change (Measure.map (X n) (P n)) E = P n {ω | X n ω ∈ E}
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hE]
    rfl
  simpa [hseq_eq, lawZ] using hport

/-- **Portmanteau event-probability bridge for real distributional limits.**

If `Xₙ ⇒ Z` and `E` is a Borel set whose frontier has zero mass under the
limit law, then the probabilities of the events `{Xₙ ∈ E}` converge to the
limit-law probability of `E`. This is the reusable coverage/critical-region
bridge for Chapter 7's t and Wald statistics. -/
theorem TendstoInDistribution.tendsto_measure_preimage_of_null_frontier_real
    {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {E : Set ℝ}
    (h : TendstoInDistribution X atTop Z P ν)
    (hE : MeasurableSet E)
    (hfrontier : (ν.map Z) (frontier E) = 0) :
    Tendsto (fun n => P n {ω | X n ω ∈ E})
      atTop (𝓝 ((ν.map Z) E)) := by
  let law : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨(P n).map (X n), Measure.isProbabilityMeasure_map (h.forall_aemeasurable n)⟩
  let lawZ : ProbabilityMeasure ℝ :=
    ⟨ν.map Z, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩
  have hlaw : Tendsto law atTop (𝓝 lawZ) := by
    simpa [law, lawZ] using h.tendsto
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (μ := lawZ) (μs := law) hlaw (by simpa [lawZ] using hfrontier)
  have hseq_eq :
      (fun n => ((law n : ProbabilityMeasure ℝ) : Measure ℝ) E) =
        fun n => P n {ω | X n ω ∈ E} := by
    funext n
    change (Measure.map (X n) (P n)) E = P n {ω | X n ω ∈ E}
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) hE]
    rfl
  simpa [hseq_eq, lawZ] using hport

/-- If `Xₙ = oₚ(1)` and `Yₙ = Oₚ(1)`, then `XₙYₙ = oₚ(1)`.

This is the scalar product rule needed for the Chapter 7 inverse-gap argument:
after rewriting the random-inverse remainder coordinatewise, the inverse gap
will supply the `oₚ(1)` factor and the scaled score will supply the `Oₚ(1)`
factor. -/
theorem TendstoInMeasure.mul_boundedInProbability
    {X Y : ℕ → α → ℝ}
    (hX : TendstoInMeasure μ X atTop (fun _ => 0))
    (hY : BoundedInProbability μ Y) :
    TendstoInMeasure μ (fun n ω => X n ω * Y n ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.div_pos hδ.ne' ENNReal.ofNat_ne_top
  obtain ⟨M, hMpos, hYevent⟩ := hY (δ / 2) hδ2
  have hXMpos : 0 < ε / M := div_pos hε hMpos
  have hXevent := (hX (ε / M) hXMpos).eventually_lt_const hδ2
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hXevent.and hYevent)
  refine ⟨N, fun n hn => ?_⟩
  have hXn : μ {ω | ε / M ≤ dist (X n ω) 0} ≤ δ / 2 :=
    le_of_lt (hN n hn).1
  have hYn : μ {ω | M ≤ ‖Y n ω‖} ≤ δ / 2 := (hN n hn).2
  have hcover :
      {ω | ε ≤ dist (X n ω * Y n ω) 0} ⊆
        {ω | ε / M ≤ dist (X n ω) 0} ∪ {ω | M ≤ ‖Y n ω‖} := by
    intro ω hω
    by_cases hYbig : M ≤ ‖Y n ω‖
    · exact Or.inr hYbig
    · left
      have hYlt : ‖Y n ω‖ < M := not_le.mp hYbig
      have hprod : ε ≤ ‖X n ω * Y n ω‖ := by
        simpa [Real.dist_eq] using hω
      have hprod_norm : ε ≤ ‖X n ω‖ * ‖Y n ω‖ := by
        simpa [norm_mul] using hprod
      have hprod_pos : 0 < ‖X n ω‖ * ‖Y n ω‖ := lt_of_lt_of_le hε hprod_norm
      have hXpos : 0 < ‖X n ω‖ := pos_of_mul_pos_left hprod_pos (norm_nonneg _)
      have hlt_mul : ‖X n ω‖ * ‖Y n ω‖ < ‖X n ω‖ * M :=
        mul_lt_mul_of_pos_left hYlt hXpos
      have hlt : ε < ‖X n ω‖ * M := lt_of_le_of_lt hprod_norm hlt_mul
      have hdiv : ε / M < ‖X n ω‖ := (div_lt_iff₀ hMpos).2 (by simpa [mul_comm] using hlt)
      simpa [Real.dist_eq] using le_of_lt hdiv
  calc
    μ {ω | ε ≤ dist (X n ω * Y n ω) 0}
        ≤ μ ({ω | ε / M ≤ dist (X n ω) 0} ∪ {ω | M ≤ ‖Y n ω‖}) :=
          measure_mono hcover
    _ ≤ μ {ω | ε / M ≤ dist (X n ω) 0} + μ {ω | M ≤ ‖Y n ω‖} :=
          measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hXn hYn
    _ = δ := ENNReal.add_halves δ

end StochasticOrder

section WLLN

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Weak law of large numbers** (Banach-valued, pairwise-independent form).

If `X : ℕ → Ω → E` is a sequence of pairwise-independent, identically distributed,
integrable `E`-valued random variables on a finite-measure space, then the sample
mean `(1/n) ∑_{i<n} X i` converges in probability to `𝔼[X 0]`.

This is the direct composition of Mathlib's `strong_law_ae` with
`tendstoInMeasure_of_tendsto_ae`. Provided here as a named lemma to match the
econometrics literature's WLLN statement. -/
theorem tendstoInMeasure_wlln
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [IsFiniteMeasure μ]
    (X : ℕ → Ω → E)
    (hint : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      atTop
      (fun _ => μ[X 0]) := by
  have hae : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) atTop (𝓝 μ[X 0]) :=
    ProbabilityTheory.strong_law_ae X hint hindep hident
  have hmeas_each : ∀ i, AEStronglyMeasurable (X i) μ :=
    fun i => ((hident i).integrable_iff.mpr hint).aestronglyMeasurable
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) μ := by
    intro n
    have hsum : AEStronglyMeasurable (∑ i ∈ Finset.range n, X i) μ :=
      Finset.aestronglyMeasurable_sum (Finset.range n) (fun i _ => hmeas_each i)
    have hscaled := hsum.const_smul ((n : ℝ)⁻¹)
    have heq : (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) =
        ((n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i) := by
      funext ω
      simp [Finset.sum_apply]
    rw [heq]
    exact hscaled
  exact tendstoInMeasure_of_tendsto_ae hmeas hae

/-- **Hansen Theorem 6.2, transformed WLLN.**

If `X i` are pairwise-independent and identically distributed and `h (X 0)` is integrable,
then the sample mean of the transformed variables `h (X i)` converges in probability to
`𝔼[h (X 0)]`. This is the textbook transformed WLLN packaged as composition of the
Banach-valued WLLN with measurable-map preservation of independence and identical distribution. -/
theorem tendstoInMeasure_transformed_wlln
    {E F : Type*}
    [MeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F]
    [IsFiniteMeasure μ]
    (X : ℕ → Ω → E) (h : E → F)
    (hh : Measurable h)
    (hint : Integrable (fun ω => h (X 0 ω)) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, h (X i ω))
      atTop
      (fun _ => μ[fun ω => h (X 0 ω)]) :=
  tendstoInMeasure_wlln
    (fun i ω => h (X i ω))
    hint
    (fun _ _ hij => IndepFun.comp (hindep hij) hh hh)
    (fun i => (hident i).comp hh)

end WLLN

end HansenEconometrics
