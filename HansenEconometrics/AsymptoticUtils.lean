import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
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
private theorem charFun_map_eq_charFun_dualMap_one
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
private theorem TendstoInMeasure.neg_zero_real
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

end WLLN

end HansenEconometrics
