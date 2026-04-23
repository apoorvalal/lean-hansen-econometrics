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

/-- **Scalar-scaled matrix inverse (unconditional).** For `c : ℝ` and any square
matrix `M` over `ℝ`, the total inverse `Matrix.nonsingInv` satisfies
`(c • M)⁻¹ = c⁻¹ • M⁻¹`. Mathlib's `Matrix.inv_smul` requires `Invertible c`
and `IsUnit M.det`; we dispatch the singular cases by hand so the identity
holds on all of `Ω`, as needed by the Chapter 7 consistency argument where
`Q̂ₙ = n⁻¹ • (Xᵀ X)` is scaled by a sample-dependent but possibly zero-at-`ω`
factor. -/
theorem nonsingInv_smul (c : ℝ) (M : Matrix k k ℝ) :
    (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  by_cases hc : c = 0
  · subst hc
    simp [Matrix.inv_zero]
  by_cases hM : IsUnit M.det
  · have : Invertible c := invertibleOfNonzero hc
    rw [Matrix.inv_smul _ _ hM, invOf_eq_inv]
  · have hM' : M.det = 0 := by
      rwa [isUnit_iff_ne_zero, ne_eq, not_not] at hM
    have hcMdet : ¬ IsUnit (c • M).det := by
      rw [Matrix.det_smul, hM', mul_zero]
      simp
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hcMdet,
        Matrix.nonsing_inv_apply_not_isUnit _ hM, smul_zero]

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

end MulVec

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
