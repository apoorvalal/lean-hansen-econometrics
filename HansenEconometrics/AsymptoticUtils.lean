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

section StochasticOrder

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

/-- A real-valued sequence of random variables is bounded in probability (`Oₚ(1)`).

This formulation is intentionally minimal: for every probability tolerance `δ`,
there is a positive deterministic bound `M` such that the tail event
`{ω | M ≤ ‖Xₙ ω‖}` has measure at most `δ`, eventually in `n`. -/
def BoundedInProbability (μ : Measure α) (X : ℕ → α → ℝ) : Prop :=
  ∀ δ : ℝ≥0∞, 0 < δ → ∃ M : ℝ, 0 < M ∧
    ∀ᶠ n in atTop, μ {ω | M ≤ ‖X n ω‖} ≤ δ

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

end WLLN

end HansenEconometrics
