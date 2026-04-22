import Mathlib
import HansenEconometrics.Basic

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

Both are stated for general Banach-space codomains, so they specialize
directly to scalar, vector, and matrix random variables.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Function

namespace HansenEconometrics

variable {α E F : Type*} {m : MeasurableSpace α} {μ : Measure α}

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

end WLLN

end HansenEconometrics
