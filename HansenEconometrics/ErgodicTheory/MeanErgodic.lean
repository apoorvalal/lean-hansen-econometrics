import HansenEconometrics.ErgodicTheory.PathShift
import HansenEconometrics.ErgodicTheory.Koopman
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The L¹ mean ergodic theorem and Hansen's Ergodic Theorems (14.7–14.9)

This file promotes the `L²` von Neumann mean ergodic theorem (built in
`HansenEconometrics.ErgodicTheory.Koopman`) to the `L¹` mean ergodic theorem, and packages it as
**Hansen's Econometrics Theorem 14.9** (the ergodic theorem) for a strictly stationary ergodic
process, in its honest textbook form: convergence of the sample mean in `L¹` and in probability
(NOT the pointwise/a.s. Birkhoff statement, which needs a maximal inequality absent from Mathlib).

It also derives the two ergodic corollaries built directly on the von Neumann theorem: **Hansen
Theorem 14.7** (Cesàro decay of autocovariances) and **Hansen Theorem 14.8** (ergodicity ⟺ Cesàro
mixing of events), via a reusable generic Cesàro–inner-product engine on an abstract ergodic
system.

## Main declarations

* `ProbabilityTheory.eLpNorm_birkhoffAverage_le` — for a measure-preserving map, the `L¹` norm of a
  Birkhoff average is bounded by the `L¹` norm of the integrand (measure-preservation contraction).
* `ProbabilityTheory.Ergodic.tendsto_birkhoffAverage_integral_L1` — the **`L¹` mean ergodic
  theorem**: for an ergodic map on a probability space and `g ∈ L¹`, the Birkhoff averages of `g`
  converge in `L¹` to the constant `∫ g`. Proved by Hansen's truncation split `g = w + r` with `w`
  bounded (handled by the `L²` theorem) and `r` a small tail.
* `ProbabilityTheory.birkhoffSum_pathShift_eval` — the bridge identifying the Birkhoff sum of the
  coordinate-zero evaluation under the path shift with the partial sum `∑ k < n, x k` of a path.
* `ProbabilityTheory.IsErgodicProcess.tendsto_average_eLpNorm_one` — **Hansen Theorem 14.9(a)**:
  the sample mean of a strictly stationary ergodic integrable process converges to `𝔼[X₀]` in `L¹`.
* `ProbabilityTheory.IsErgodicProcess.tendstoInMeasure_average` — **Hansen Theorem 14.9(b)**: the
  sample mean converges to `𝔼[X₀]` in probability.
* `ProbabilityTheory.IsErgodicProcess.tendstoInMeasure_average_pi` — the coordinatewise vector form
  for an `(Fin m → ℝ)`-valued process.
* `ProbabilityTheory.Ergodic.tendsto_cesaro_inner_koopman` — the **generic Cesàro–von-Neumann
  engine**: for an ergodic map and `g h ∈ L²`, `(1/n) ∑_{k<n} ⟪Koopman^k g, h⟫ → (∫ g)(∫ h)`.
* `ProbabilityTheory.Ergodic.tendsto_cesaro_measureReal_inter` and
  `ProbabilityTheory.Ergodic.of_cesaro_inter` — the indicator (forward) and `0/1`-law (converse)
  engines specializing the previous theorem to events.
* `ProbabilityTheory.isErgodicProcess_iff_cesaro_inter` — **Hansen Theorem 14.8**: a strictly
  stationary process is ergodic iff every pair of path-space events has the Cesàro correlation limit
  `(1/n) ∑_{ℓ<n} P(T^{-(ℓ+1)} A ∩ B) → P(A) · P(B)`.
* `ProbabilityTheory.IsErgodicProcess.cesaro_autocov_tendsto_zero` — **Hansen Theorem 14.7**: for a
  strictly stationary ergodic `L²` process, `(1/n) ∑_{ℓ<n} γ(ℓ+1) → 0`.
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace ProbabilityTheory

section Generic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α}

/-- The pointwise Birkhoff average of an a.e.-strongly-measurable integrand is
a.e. strongly measurable, when `f` preserves `μ`. -/
private theorem aestronglyMeasurable_birkhoffAverage (hf : MeasurePreserving f μ μ) {r : α → ℝ}
    (hr : AEStronglyMeasurable r μ) (n : ℕ) :
    AEStronglyMeasurable (birkhoffAverage ℝ f r n) μ := by
  have hbs : birkhoffSum f r n = ∑ k ∈ Finset.range n, (r ∘ f^[k]) := by
    funext x
    rw [Finset.sum_apply]
    rfl
  have hsum : AEStronglyMeasurable (birkhoffSum f r n) μ := by
    rw [hbs]
    exact Finset.aestronglyMeasurable_sum _
      (fun k _ => hr.comp_measurePreserving (hf.iterate k))
  have hba : birkhoffAverage ℝ f r n = (n : ℝ)⁻¹ • birkhoffSum f r n := rfl
  rw [hba]
  exact hsum.const_smul _

/-- **Measure-preservation contraction of Birkhoff averaging in `L¹`.** For a measure-preserving map
`f`, the `L¹` seminorm of the Birkhoff average `birkhoffAverage ℝ f r n` is at most the `L¹`
seminorm of `r`. Each composed term `r ∘ f^[k]` has the same `L¹` norm as `r` (measure
preservation), so the triangle inequality over the `n`-term sum, divided by `n`, gives the bound.
This is the reusable tail estimate behind the `L¹` mean ergodic theorem. -/
theorem eLpNorm_birkhoffAverage_le (hf : MeasurePreserving f μ μ) {r : α → ℝ}
    (hr : AEStronglyMeasurable r μ) (n : ℕ) :
    eLpNorm (birkhoffAverage ℝ f r n) 1 μ ≤ eLpNorm r 1 μ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hbs : birkhoffSum f r n = ∑ k ∈ Finset.range n, (r ∘ f^[k]) := by
    funext x
    rw [Finset.sum_apply]
    rfl
  have hstep : eLpNorm (birkhoffSum f r n) 1 μ ≤ (n : ℝ≥0∞) * eLpNorm r 1 μ := by
    rw [hbs]
    calc eLpNorm (∑ k ∈ Finset.range n, (r ∘ f^[k])) 1 μ
        ≤ ∑ k ∈ Finset.range n, eLpNorm (r ∘ f^[k]) 1 μ :=
          eLpNorm_sum_le (fun k _ => hr.comp_measurePreserving (hf.iterate k)) le_rfl
      _ = ∑ _k ∈ Finset.range n, eLpNorm r 1 μ :=
          Finset.sum_congr rfl fun k _ => eLpNorm_comp_measurePreserving hr (hf.iterate k)
      _ = (n : ℝ≥0∞) * eLpNorm r 1 μ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hba : birkhoffAverage ℝ f r n = (n : ℝ)⁻¹ • birkhoffSum f r n := rfl
  rw [hba, eLpNorm_const_smul]
  have hnorm : ‖(n : ℝ)⁻¹‖ₑ * (n : ℝ≥0∞) = 1 := by
    have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    calc ‖(n : ℝ)⁻¹‖ₑ * (n : ℝ≥0∞)
        = ‖(n : ℝ)⁻¹‖ₑ * ‖(n : ℝ)‖ₑ := by rw [Real.enorm_natCast]
      _ = ‖(n : ℝ)⁻¹ * (n : ℝ)‖ₑ := (enorm_mul _ _).symm
      _ = 1 := by rw [inv_mul_cancel₀ hne, enorm_one]
  calc ‖(n : ℝ)⁻¹‖ₑ * eLpNorm (birkhoffSum f r n) 1 μ
      ≤ ‖(n : ℝ)⁻¹‖ₑ * ((n : ℝ≥0∞) * eLpNorm r 1 μ) := by gcongr
    _ = eLpNorm r 1 μ := by rw [← mul_assoc, hnorm, one_mul]

/-- The `L¹` mean ergodic theorem for a strongly measurable integrand. Proved by Hansen's
truncation split `g = w + r`, with `w` bounded (so the `L²` mean ergodic theorem applies and
`L¹ ≤ L²` on a probability space) and `r` a small tail. -/
private theorem tendsto_birkhoffAverage_integral_L1_of_stronglyMeasurable (hf : Ergodic f μ)
    [IsProbabilityMeasure μ] {g : α → ℝ} (hgm : StronglyMeasurable g) (hg : Integrable g μ) :
    Tendsto (fun n => eLpNorm (fun x => birkhoffAverage ℝ f g n x - ∫ y, g y ∂μ) 1 μ) atTop
      (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact ⟨0, fun n _ => le_top⟩
  -- The tail budget `δ = ε / 4`.
  set δ : ℝ≥0∞ := ε / 4 with hδdef
  have hδpos : 0 < δ := ENNReal.div_pos hε.ne' (by norm_num)
  have hδtop : δ ≠ ⊤ := ENNReal.div_ne_top hεtop (by norm_num)
  have hε2pos : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  have hδsum : δ + δ = ε / 2 := by
    rw [hδdef, ENNReal.div_add_div_same, ← two_mul,
      show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
      ENNReal.mul_div_mul_left ε 2 (by norm_num) (by norm_num)]
  -- Truncation: `r` is the tail of `g` above level `M`, chosen so `‖r‖₁ ≤ δ`.
  obtain ⟨M, hM0, hMtail⟩ := (memLp_one_iff_integrable.mpr hg).integral_indicator_norm_ge_nonneg_le
    (ε := δ.toReal) (ENNReal.toReal_pos hδpos.ne' hδtop)
  set T : Set α := {x | M ≤ ‖g x‖₊} with hTdef
  have hTmeas : MeasurableSet T :=
    measurableSet_le measurable_const hgm.nnnorm.measurable.coe_nnreal_real
  set r : α → ℝ := T.indicator g with hrdef
  set w : α → ℝ := g - r with hwdef
  have hrm : StronglyMeasurable r := hgm.indicator hTmeas
  have hwm : StronglyMeasurable w := hgm.sub hrm
  have hr_int : Integrable r μ := hg.indicator hTmeas
  have hw_int : Integrable w μ := hg.sub hr_int
  have hr_eLp : eLpNorm r 1 μ ≤ δ := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ENNReal.ofReal_toReal hδtop]
    exact hMtail
  -- `w` is bounded by `M`, hence square-integrable.
  have hwbd : ∀ x, ‖w x‖ ≤ M := by
    intro x
    rw [hwdef, Pi.sub_apply, hrdef]
    by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx, sub_self, norm_zero]; exact hM0
    · rw [Set.indicator_of_notMem hx, sub_zero]
      simp only [hTdef, Set.mem_setOf_eq, not_le] at hx
      calc ‖g x‖ = (‖g x‖₊ : ℝ) := by rw [coe_nnnorm]
        _ ≤ M := le_of_lt hx
  have hw2 : MemLp w 2 μ := MemLp.of_bound hwm.aestronglyMeasurable M (ae_of_all _ hwbd)
  -- `g = w + r`, so the centred Birkhoff average splits.
  have hgwr : g = w + r := by rw [hwdef]; abel
  have hsplit : ∀ n, (fun x => birkhoffAverage ℝ f g n x - ∫ y, g y ∂μ)
      = (fun x => birkhoffAverage ℝ f w n x - ∫ y, w y ∂μ)
        + (fun x => birkhoffAverage ℝ f r n x - ∫ y, r y ∂μ) := by
    intro n
    have hba : birkhoffAverage ℝ f g n
        = birkhoffAverage ℝ f w n + birkhoffAverage ℝ f r n := by
      rw [hgwr, birkhoffAverage_add]; rfl
    have hint : ∫ y, g y ∂μ = (∫ y, w y ∂μ) + ∫ y, r y ∂μ := by
      rw [hgwr]; simp only [Pi.add_apply]; exact integral_add hw_int hr_int
    funext x
    rw [hba, hint, Pi.add_apply, Pi.add_apply]
    ring
  -- The bounded part converges in `L²`, hence eventually below `ε / 2`.
  have hL2 := Ergodic.tendsto_birkhoffAverage_integral_L2 hf hw2
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp hL2 (ε / 2) hε2pos
  refine ⟨N, fun n hn => ?_⟩
  rw [hsplit n]
  have hAsm : AEStronglyMeasurable (fun x => birkhoffAverage ℝ f w n x - ∫ y, w y ∂μ) μ :=
    (aestronglyMeasurable_birkhoffAverage hf.toMeasurePreserving hwm.aestronglyMeasurable n).sub
      aestronglyMeasurable_const
  have hBsm : AEStronglyMeasurable (fun x => birkhoffAverage ℝ f r n x - ∫ y, r y ∂μ) μ :=
    (aestronglyMeasurable_birkhoffAverage hf.toMeasurePreserving hrm.aestronglyMeasurable n).sub
      aestronglyMeasurable_const
  refine le_trans (eLpNorm_add_le hAsm hBsm le_rfl) ?_
  have hA : eLpNorm (fun x => birkhoffAverage ℝ f w n x - ∫ y, w y ∂μ) 1 μ ≤ ε / 2 :=
    le_trans (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hAsm) (hN n hn)
  have hB : eLpNorm (fun x => birkhoffAverage ℝ f r n x - ∫ y, r y ∂μ) 1 μ ≤ ε / 2 := by
    have hsub : (fun x => birkhoffAverage ℝ f r n x - ∫ y, r y ∂μ)
        = birkhoffAverage ℝ f r n - (fun _ => ∫ y, r y ∂μ) := rfl
    rw [hsub]
    refine le_trans (eLpNorm_sub_le
      (aestronglyMeasurable_birkhoffAverage hf.toMeasurePreserving hrm.aestronglyMeasurable n)
      aestronglyMeasurable_const le_rfl) ?_
    have h1 : eLpNorm (birkhoffAverage ℝ f r n) 1 μ ≤ δ :=
      le_trans (eLpNorm_birkhoffAverage_le hf.toMeasurePreserving hrm.aestronglyMeasurable n) hr_eLp
    have h2 : eLpNorm (fun _ : α => ∫ y, r y ∂μ) 1 μ ≤ δ := by
      rw [eLpNorm_const _ one_ne_zero (IsProbabilityMeasure.ne_zero μ)]
      simp only [measure_univ, ENNReal.one_rpow, mul_one]
      calc ‖∫ y, r y ∂μ‖ₑ ≤ ∫⁻ x, ‖r x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm r
        _ = eLpNorm r 1 μ := (eLpNorm_one_eq_lintegral_enorm).symm
        _ ≤ δ := hr_eLp
    calc eLpNorm (birkhoffAverage ℝ f r n) 1 μ + eLpNorm (fun _ : α => ∫ y, r y ∂μ) 1 μ
        ≤ δ + δ := add_le_add h1 h2
      _ = ε / 2 := hδsum
  calc eLpNorm (fun x => birkhoffAverage ℝ f w n x - ∫ y, w y ∂μ) 1 μ
        + eLpNorm (fun x => birkhoffAverage ℝ f r n x - ∫ y, r y ∂μ) 1 μ
      ≤ ε / 2 + ε / 2 := add_le_add hA hB
    _ = ε := ENNReal.add_halves ε

/-- **Ergodic theorem in `L¹` (map form).** For an ergodic map on a probability space and an
integrable `g`, the pointwise Birkhoff averages of `g` converge in `L¹` to the constant `∫ g`. This
is the `L¹` mean ergodic theorem: the honest textbook conclusion of Hansen's Theorem 14.9 (no
pointwise/a.s. statement, which would need a maximal inequality absent from Mathlib). It is proved
from the `L²` mean ergodic theorem `Ergodic.tendsto_birkhoffAverage_integral_L2` by Hansen's
truncation argument. -/
theorem Ergodic.tendsto_birkhoffAverage_integral_L1 (hf : Ergodic f μ) [IsProbabilityMeasure μ]
    {g : α → ℝ} (hg : Integrable g μ) :
    Tendsto (fun n => eLpNorm (fun x => birkhoffAverage ℝ f g n x - ∫ y, g y ∂μ) 1 μ) atTop
      (𝓝 0) := by
  set g' := hg.1.mk g with hg'def
  have hg'meas : StronglyMeasurable g' := hg.1.stronglyMeasurable_mk
  have hgg' : g =ᵐ[μ] g' := hg.1.ae_eq_mk
  have hg'_int : Integrable g' μ := hg.congr hgg'
  have hbase := tendsto_birkhoffAverage_integral_L1_of_stronglyMeasurable hf hg'meas hg'_int
  refine hbase.congr (fun n => eLpNorm_congr_ae ?_)
  filter_upwards
    [hf.toMeasurePreserving.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ hgg'.symm n]
    with x hx
  rw [hx, integral_congr_ae hgg'.symm]

end Generic

section Bridge

/-- **Bridge lemma.** The Birkhoff sum of the coordinate-zero evaluation `y ↦ y 0` under the path
shift, evaluated at a path `x`, is the partial sum `∑ k < n, x k`: iterating the shift `k` times and
reading coordinate `0` returns coordinate `k`. -/
theorem birkhoffSum_pathShift_eval (x : ℤ → ℝ) (n : ℕ) :
    birkhoffSum (pathShift ℝ) (fun y => y 0) n x = ∑ k ∈ Finset.range n, x (k : ℤ) := by
  change ∑ k ∈ Finset.range n, ((pathShift ℝ)^[k] x) 0 = ∑ k ∈ Finset.range n, x (k : ℤ)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [pathShift_iterate, zero_add]

/-- The Birkhoff-average form of `birkhoffSum_pathShift_eval`: the average of the coordinate-zero
evaluation under the path shift is the sample mean `(1/n) ∑ k < n, x k` of the path. -/
theorem birkhoffAverage_pathShift_eval (x : ℤ → ℝ) (n : ℕ) :
    birkhoffAverage ℝ (pathShift ℝ) (fun y => y 0) n x
      = (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, x (k : ℤ) := by
  change (n : ℝ)⁻¹ • birkhoffSum (pathShift ℝ) (fun y => y 0) n x = _
  rw [birkhoffSum_pathShift_eval, smul_eq_mul]

end Bridge

section Process

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℤ → Ω → ℝ} {P : Measure Ω}

/-- **Hansen Theorem 14.9(a): `L¹` convergence of the sample mean.** For a strictly stationary
ergodic integrable scalar process, the sample mean `(1/n) ∑ t < n, Xₜ` converges to `𝔼[X₀]` in `L¹`.
Ergodicity of the process (`IsErgodicProcess`) already encodes shift-invariance of the path law, so
strict stationarity is not needed as a separate hypothesis. Proved by transferring the `L¹` mean
ergodic theorem `Ergodic.tendsto_birkhoffAverage_integral_L1` from the path space `pathLaw X P` back
to `Ω` along the path map, using `birkhoffAverage_pathShift_eval` to identify the Birkhoff average
of the coordinate-zero evaluation with the sample mean. -/
theorem IsErgodicProcess.tendsto_average_eLpNorm_one [IsProbabilityMeasure P]
    (he : IsErgodicProcess X P) (hmeas : ∀ t, AEMeasurable (X t) P)
    (hint : Integrable (X 0) P) :
    Tendsto (fun n : ℕ => eLpNorm
        (fun ω => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, X (t : ℤ) ω - ∫ ω, X 0 ω ∂P) 1 P)
      atTop (𝓝 0) := by
  have he' : Ergodic (pathShift ℝ) (pathLaw X P) := he
  haveI : IsProbabilityMeasure (pathLaw X P) := isProbabilityMeasure_pathLaw hmeas
  have hΦ_ae : AEMeasurable (fun ω : Ω => fun t => X t ω) P := aemeasurable_pi_iff.mpr hmeas
  have heval : AEStronglyMeasurable (fun y : ℤ → ℝ => y 0) (pathLaw X P) :=
    (measurable_pi_apply 0).aestronglyMeasurable
  -- Integrability of the coordinate-zero evaluation under the path law, from `Integrable (X 0) P`.
  have hg : Integrable (fun y : ℤ → ℝ => y 0) (pathLaw X P) :=
    (integrable_map_measure heval hΦ_ae).mpr hint
  -- The constant `∫ y₀ d(pathLaw)` equals `𝔼[X₀]`.
  have hC : ∫ z, (fun y : ℤ → ℝ => y 0) z ∂(pathLaw X P) = ∫ ω, X 0 ω ∂P :=
    integral_map hΦ_ae heval
  -- The `L¹` mean ergodic theorem on the path space.
  have hMET := Ergodic.tendsto_birkhoffAverage_integral_L1 he' hg
  refine hMET.congr (fun n => ?_)
  have hpath_asm : AEStronglyMeasurable
      (fun y : ℤ → ℝ => birkhoffAverage ℝ (pathShift ℝ) (fun y : ℤ → ℝ => y 0) n y
        - ∫ z, (fun y : ℤ → ℝ => y 0) z ∂(pathLaw X P)) (pathLaw X P) :=
    (aestronglyMeasurable_birkhoffAverage he'.toMeasurePreserving heval n).sub
      aestronglyMeasurable_const
  have hmap : eLpNorm
        (fun y : ℤ → ℝ => birkhoffAverage ℝ (pathShift ℝ) (fun y : ℤ → ℝ => y 0) n y
          - ∫ z, (fun y : ℤ → ℝ => y 0) z ∂(pathLaw X P)) 1 (pathLaw X P)
      = eLpNorm ((fun y : ℤ → ℝ => birkhoffAverage ℝ (pathShift ℝ) (fun y : ℤ → ℝ => y 0) n y
          - ∫ z, (fun y : ℤ → ℝ => y 0) z ∂(pathLaw X P)) ∘ (fun ω : Ω => fun t => X t ω)) 1 P :=
    eLpNorm_map_measure hpath_asm hΦ_ae
  rw [hmap]
  congr 1
  funext ω
  simp only [Function.comp_apply]
  rw [birkhoffAverage_pathShift_eval, hC]

/-- **Hansen Theorem 14.9(b): convergence of the sample mean in probability.** For a strictly
stationary ergodic integrable scalar process, the sample mean converges to `𝔼[X₀]` in probability.
Obtained from the `L¹` statement `IsErgodicProcess.tendsto_average_eLpNorm_one` by Markov's
inequality (`tendstoInMeasure_of_tendsto_eLpNorm`). This is the `o_p(1)` form consumed downstream by
the least-squares consistency results (14.29). -/
theorem IsErgodicProcess.tendstoInMeasure_average [IsProbabilityMeasure P]
    (he : IsErgodicProcess X P) (hmeas : ∀ t, AEMeasurable (X t) P)
    (hint : Integrable (X 0) P) :
    TendstoInMeasure P
      (fun n : ℕ => fun ω => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, X (t : ℤ) ω)
      atTop (fun _ => ∫ ω, X 0 ω ∂P) := by
  refine tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero (fun n => ?_) aestronglyMeasurable_const
    (he.tendsto_average_eLpNorm_one hmeas hint)
  have hsum : AEStronglyMeasurable (∑ t ∈ Finset.range n, X (t : ℤ)) P :=
    Finset.aestronglyMeasurable_sum _ (fun t _ => (hmeas (t : ℤ)).aestronglyMeasurable)
  have heq : (fun ω => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, X (t : ℤ) ω)
      = (fun ω => (n : ℝ)⁻¹ * (∑ t ∈ Finset.range n, X (t : ℤ)) ω) := by
    funext ω; rw [Finset.sum_apply]
  rw [heq]
  exact hsum.const_mul _

/-- **Hansen Theorem 14.9, vector form (coordinatewise).** For a strictly stationary ergodic
integrable `(Fin m → ℝ)`-valued process, each coordinate of the sample mean converges to the
corresponding coordinate of `𝔼[X₀]` in probability. Following the repository's componentwise idiom
for vector limits, this is stated coordinatewise rather than in a bundled Euclidean space: each
coordinate process `t ↦ Xₜ i` is strictly stationary ergodic (via
`IsErgodicProcess.comp_shiftEquivariant`, Hansen 14.5) and integrable, so the scalar
`IsErgodicProcess.tendstoInMeasure_average` applies. -/
theorem IsErgodicProcess.tendstoInMeasure_average_pi {m : ℕ} {X : ℤ → Ω → Fin m → ℝ}
    [IsProbabilityMeasure P] (he : IsErgodicProcess X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hint : Integrable (X 0) P) (i : Fin m) :
    TendstoInMeasure P
      (fun n : ℕ => fun ω => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, X (t : ℤ) ω i)
      atTop (fun _ => ∫ ω, X 0 ω i ∂P) := by
  have hφmeas : Measurable (fun y : ℤ → Fin m → ℝ => y 0 i) :=
    (measurable_pi_apply i).comp (measurable_pi_apply 0)
  have herg0 : IsErgodicProcess (fun t ω => X (t + 0) ω i) P :=
    he.comp_shiftEquivariant hφmeas hmeas
  have hfun : (fun t (ω : Ω) => X (t + 0) ω i) = (fun t ω => X t ω i) := by
    funext t ω; rw [add_zero]
  rw [hfun] at herg0
  have hcmeas : ∀ t, AEMeasurable (fun ω => X t ω i) P :=
    fun t => (measurable_pi_apply i).comp_aemeasurable (hmeas t)
  have hcint : Integrable (fun ω => X 0 ω i) P :=
    hint.mono ((measurable_pi_apply i).comp_aemeasurable (hmeas 0)).aestronglyMeasurable
      (ae_of_all _ fun ω => norm_le_pi_norm (X 0 ω) i)
  exact herg0.tendstoInMeasure_average hcmeas hcint

end Process

section Cesaro

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α}

/-- The real `L²`-scalar inner product is multiplication (`re`/conjugation are trivial on `ℝ`). -/
private theorem real_inner_eq_mul (p q : ℝ) : (inner ℝ p q : ℝ) = p * q :=
  mul_comm _ _

/-- The `k`-th iterate of the Koopman operator is composition with `f^[k]` at the `L²` level.
Re-derived here from the public `koopmanL2_apply` and `Lp.compMeasurePreserving_iterate` (the
analogous fact inside `Koopman` is private). -/
private theorem koopman_iterate_eq_comp (hf : MeasurePreserving f μ μ) (k : ℕ) :
    (⇑(koopmanL2 hf))^[k] = ⇑(Lp.compMeasurePreserving f^[k] (hf.iterate k)) := by
  rw [show ⇑(koopmanL2 hf) = ⇑(Lp.compMeasurePreserving f hf) from funext (koopmanL2_apply hf)]
  exact Lp.compMeasurePreserving_iterate hf k

/-- The coercion of the `k`-th Koopman iterate of `a` is a.e. `⇑a ∘ f^[k]`. -/
private theorem koopman_iterate_coeFn (hf : MeasurePreserving f μ μ) (a : Lp ℝ 2 μ) (k : ℕ) :
    ⇑((⇑(koopmanL2 hf))^[k] a) =ᵐ[μ] ⇑a ∘ f^[k] := by
  rw [koopman_iterate_eq_comp hf k]
  exact Lp.coeFn_compMeasurePreserving a (hf.iterate k)

/-- The `L²` inner product of the `k`-th Koopman iterate of `a` with `b` is the integral of the
product `(⇑a ∘ f^[k]) · ⇑b`. -/
private theorem inner_koopman_iterate_eq (hf : MeasurePreserving f μ μ) (a b : Lp ℝ 2 μ) (k : ℕ) :
    (inner ℝ ((⇑(koopmanL2 hf))^[k] a) b : ℝ) = ∫ x, (⇑a) (f^[k] x) * (⇑b) x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [koopman_iterate_coeFn hf a k] with x hx
  rw [hx, Function.comp_apply, real_inner_eq_mul]

/-- The `L²` inner product of the `j`-th Koopman iterate of an indicator `1_A` with `1_B` is the
measure of the intersection `f^[j] ⁻¹' A ∩ B`. This is the Koopman reading of Hansen's event
correlation `P(T^{-j} A ∩ B)`. -/
private theorem inner_koopman_iterate_indicator [IsProbabilityMeasure μ]
    (hf : MeasurePreserving f μ μ)
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (hμA : μ A ≠ ∞) (hμB : μ B ≠ ∞)
    (j : ℕ) :
    (inner ℝ ((⇑(koopmanL2 hf))^[j] (indicatorConstLp 2 hA hμA (1 : ℝ)))
        (indicatorConstLp 2 hB hμB (1 : ℝ)) : ℝ) = μ.real (f^[j] ⁻¹' A ∩ B) := by
  rw [koopman_iterate_eq_comp hf j,
    Lp.indicatorConstLp_compMeasurePreserving hA hμA 1 (hf.iterate j),
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one]

/-- **Generic Cesàro–von-Neumann inner-product theorem.** For an ergodic map on a probability
space and `g h ∈ L²`, the Cesàro averages of the Koopman inner products
`⟪(koopman f)^k g, h⟫` converge to `(∫ g)(∫ h)`. This is the reusable Hilbert-space engine behind
Hansen's Theorems 14.7 and 14.8: the birkhoff average of `g` under the Koopman operator converges in
`L²` to the constant `∫ g` (the `L²` mean ergodic theorem), and pairing with the continuous
functional `⟪·, h⟫` yields the limit. -/
theorem Ergodic.tendsto_cesaro_inner_koopman (hf : Ergodic f μ) [IsProbabilityMeasure μ]
    (g h : Lp ℝ 2 μ) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        (inner ℝ ((⇑(koopmanL2 hf.toMeasurePreserving))^[k] g) h : ℝ)) atTop
      (𝓝 ((∫ x, g x ∂μ) * ∫ x, h x ∂μ)) := by
  set cg : ℝ := ∫ x, g x ∂μ with hcg
  -- the constant `cg = ∫ g` as an `L²` element
  have hconstmem : MemLp (fun _ : α => cg) 2 μ := memLp_const cg
  set cgLp : Lp ℝ 2 μ := hconstmem.toLp _ with hcgLp
  have hcgcoe : ⇑cgLp =ᵐ[μ] (fun _ : α => cg) := hconstmem.coeFn_toLp
  -- the pointwise Birkhoff averages converge to `cg` in `L²` (public `L²` MET)
  have hA := Ergodic.tendsto_birkhoffAverage_integral_L2 hf (Lp.memLp g)
  -- the operator Birkhoff averages converge to `cgLp` in `L²`
  have hBtend : Tendsto (fun n => birkhoffAverage ℝ (koopmanL2 hf.toMeasurePreserving) id n g) atTop
      (𝓝 cgLp) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine hA.congr (fun n => (eLpNorm_congr_ae ?_).symm)
    filter_upwards [koopmanL2_birkhoffAverage_coeFn hf.toMeasurePreserving g n, hcgcoe]
      with x hb hc
    rw [Pi.sub_apply, hb, hc]
  -- pairing with `h` is continuous, and gives `⟪cgLp, h⟫ = cg * ∫ h`
  have hinner : Tendsto (fun n => (inner ℝ
        (birkhoffAverage ℝ (koopmanL2 hf.toMeasurePreserving) id n g) h : ℝ)) atTop
      (𝓝 (inner ℝ cgLp h : ℝ)) :=
    hBtend.inner (tendsto_const_nhds (x := h))
  have hlim : (inner ℝ cgLp h : ℝ) = cg * ∫ x, h x ∂μ := by
    rw [L2.inner_def, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hcgcoe] with a ha
    rw [ha, real_inner_eq_mul]
  rw [hlim] at hinner
  -- rewrite the operator inner product as the Cesàro sum
  have hseq : (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        (inner ℝ ((⇑(koopmanL2 hf.toMeasurePreserving))^[k] g) h : ℝ))
      = fun n => (inner ℝ (birkhoffAverage ℝ (koopmanL2 hf.toMeasurePreserving) id n g) h : ℝ) := by
    funext n
    rw [show birkhoffAverage ℝ (koopmanL2 hf.toMeasurePreserving) id n g
          = (n : ℝ)⁻¹ • birkhoffSum (koopmanL2 hf.toMeasurePreserving) id n g from rfl,
        real_inner_smul_left,
        show birkhoffSum (koopmanL2 hf.toMeasurePreserving) id n g
          = ∑ k ∈ Finset.range n, (⇑(koopmanL2 hf.toMeasurePreserving))^[k] g from rfl,
        sum_inner]
  rw [hseq]
  exact hinner

/-- **Cesàro event-correlation limit (14.8 forward engine).** For an ergodic map on a probability
space and measurable sets `A B`, the Cesàro averages of the event correlations
`μ(f^[k+1] ⁻¹' A ∩ B)` converge to `μ(A) · μ(B)`. This is `tendsto_cesaro_inner_koopman` applied to
the indicators `1_A` and `1_B`, after one Koopman step to align the `k+1` shift. -/
theorem Ergodic.tendsto_cesaro_measureReal_inter (hf : Ergodic f μ) [IsProbabilityMeasure μ]
    {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
        μ.real (f^[k + 1] ⁻¹' A ∩ B)) atTop (𝓝 (μ.real A * μ.real B)) := by
  set oneA : Lp ℝ 2 μ := indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ) with honeA
  set oneB : Lp ℝ 2 μ := indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ) with honeB
  have hkey := Ergodic.tendsto_cesaro_inner_koopman hf (koopmanL2 hf.toMeasurePreserving oneA) oneB
  -- the two limit integrals are `μ(A)` and `μ(B)`
  have hlimA : ∫ x, (koopmanL2 hf.toMeasurePreserving oneA) x ∂μ = μ.real A := by
    rw [honeA, koopmanL2_apply,
      Lp.indicatorConstLp_compMeasurePreserving hA (measure_ne_top μ A) 1 hf.toMeasurePreserving,
      integral_indicatorConstLp]
    simp only [smul_eq_mul, mul_one]
    exact hf.toMeasurePreserving.measureReal_preimage hA.nullMeasurableSet
  have hlimB : ∫ x, oneB x ∂μ = μ.real B := by
    rw [honeB, integral_indicatorConstLp]; simp
  rw [hlimA, hlimB] at hkey
  -- each summand is an event correlation
  refine hkey.congr (fun n => ?_)
  refine congrArg _ (Finset.sum_congr rfl (fun k _ => ?_))
  rw [show (⇑(koopmanL2 hf.toMeasurePreserving))^[k] (koopmanL2 hf.toMeasurePreserving oneA)
        = (⇑(koopmanL2 hf.toMeasurePreserving))^[k + 1] oneA from
      (Function.iterate_succ_apply (⇑(koopmanL2 hf.toMeasurePreserving)) k oneA).symm, honeA, honeB,
    inner_koopman_iterate_indicator hf.toMeasurePreserving hA hB (measure_ne_top μ A)
      (measure_ne_top μ B) (k + 1)]

/-- **Converse ergodicity criterion (14.8 converse engine).** A measure-preserving map on a
probability space for which every pair of measurable events has the Cesàro correlation limit
`μ(f^[k+1] ⁻¹' A ∩ B) → μ(A) · μ(B)` is ergodic. Taking `A = B` an invariant set forces
`μ(A) = μ(A)²`, hence `μ(A) ∈ {0, 1}`. This was the campaign's flagged highest-risk direction; the
proof reuses the `0/1`-law packaging of `ergodic_pathShift_infinitePi`. -/
theorem Ergodic.of_cesaro_inter (hf : MeasurePreserving f μ μ) [IsProbabilityMeasure μ]
    (hces : ∀ A B, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, μ.real (f^[k + 1] ⁻¹' A ∩ B)) atTop
        (𝓝 (μ.real A * μ.real B))) :
    Ergodic f μ := by
  refine ⟨hf, ⟨fun s hs hfs => ?_⟩⟩
  have hce := hces s s hs hs
  -- on the invariant `s`, every term is `μ.real s`, so the limit is `μ.real s`
  have hconst : (fun n : ℕ => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, μ.real (f^[k + 1] ⁻¹' s ∩ s))
      =ᶠ[atTop] fun _ => μ.real s := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpre : ∀ k : ℕ, f^[k + 1] ⁻¹' s ∩ s = s := fun k => by
      rw [Function.IsFixedPt.preimage_iterate hfs (k + 1), Set.inter_self]
    rw [Finset.sum_congr rfl (fun k _ => by rw [hpre k]), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  have hsq : μ.real s * μ.real s = μ.real s :=
    tendsto_nhds_unique (hce.congr' hconst) tendsto_const_nhds
  -- the `0/1` law
  have hfin : μ s ≠ ∞ := measure_ne_top μ s
  have hnu : μ s = ENNReal.ofReal (μ.real s) := by
    rw [measureReal_def, ENNReal.ofReal_toReal hfin]
  have hdich : μ s = 0 ∨ μ s = 1 := by
    have hfac : μ.real s * (1 - μ.real s) = 0 := by rw [mul_sub, mul_one, hsq, sub_self]
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (by rw [hnu, h]; simp)
    · refine Or.inr ?_
      have h1 : μ.real s = 1 := by linarith
      rw [hnu, h1]; simp
  rw [Filter.eventuallyConst_set']
  rcases hdich with h0 | h1
  · exact Or.inl (ae_eq_empty.mpr h0)
  · exact Or.inr (ae_eq_univ.mpr (by rw [measure_compl hs hfin, measure_univ, h1, tsub_self]))

end Cesaro

section EventCorrelation

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  {X : ℤ → Ω → E} {P : Measure Ω}

/-- **Hansen Theorem 14.8: ergodicity ⟺ Cesàro mixing of events.** A strictly stationary
`AEMeasurable` process on a probability space is ergodic iff, for every pair of events `A B` in path
space, the Cesàro averages of the correlations `P(T^{-(ℓ+1)} A ∩ B)` converge to `P(A) · P(B)` (with
`T` the path shift and `P` the path law). The forward direction is the von Neumann mean ergodic
theorem applied to indicators (`Ergodic.tendsto_cesaro_measureReal_inter`); the converse takes
`A = B` an invariant event to force the `0/1` law (`Ergodic.of_cesaro_inter`). The events are stated
directly on path space `ℤ → E`, which is Hansen's `A_ℓ` correlation once events are read as path
events. -/
theorem isErgodicProcess_iff_cesaro_inter [IsProbabilityMeasure P]
    (hSS : IsStrictlyStationary X P) (hmeas : ∀ t, AEMeasurable (X t) P) :
    IsErgodicProcess X P ↔
      ∀ A B : Set (ℤ → E), MeasurableSet A → MeasurableSet B →
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ ℓ ∈ Finset.range n,
            (pathLaw X P).real ((pathShift E)^[ℓ + 1] ⁻¹' A ∩ B)) atTop
          (𝓝 ((pathLaw X P).real A * (pathLaw X P).real B)) := by
  haveI : IsProbabilityMeasure (pathLaw X P) := isProbabilityMeasure_pathLaw hmeas
  refine ⟨fun he A B hA hB => ?_, fun hces => ?_⟩
  · have he' : Ergodic (pathShift E) (pathLaw X P) := he
    exact Ergodic.tendsto_cesaro_measureReal_inter he' hA hB
  · change Ergodic (pathShift E) (pathLaw X P)
    exact Ergodic.of_cesaro_inter (hSS.measurePreserving_pathShift hmeas) hces

end EventCorrelation

section Autocov

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℤ → Ω → ℝ} {P : Measure Ω}

/-- **Hansen Theorem 14.7: Cesàro decay of autocovariances.** For a strictly stationary ergodic
square-integrable scalar process, the Cesàro averages of the autocovariances
`(1/n) ∑_{ℓ<n} γ(ℓ+1)` converge to `0`. This is `tendsto_cesaro_inner_koopman` applied to the
centered coordinate `Y₀ − μ` (whose path-space integral vanishes), so the limit `(∫ · )(∫ ·) = 0`;
the summand `⟪Koopman^{ℓ+1}(Y₀−μ), Y₀−μ⟫` equals `γ(ℓ+1)` after transporting to `P` along the path
map. Hansen's sum runs over lags `ℓ = 1, …, n`; the `ℓ+1` indexing matches it after reindexing. -/
theorem IsErgodicProcess.cesaro_autocov_tendsto_zero [IsProbabilityMeasure P]
    (hSS : IsStrictlyStationary X P) (he : IsErgodicProcess X P)
    (hmeas : ∀ t, AEMeasurable (X t) P) (hL2 : MemLp (X 0) 2 P) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ ℓ ∈ Finset.range n, autocov X P (ℓ + 1)) atTop
      (𝓝 0) := by
  have he' : Ergodic (pathShift ℝ) (pathLaw X P) := he
  haveI : IsProbabilityMeasure (pathLaw X P) := isProbabilityMeasure_pathLaw hmeas
  have hΦ_ae : AEMeasurable (fun ω : Ω => fun t => X t ω) P := aemeasurable_pi_iff.mpr hmeas
  set m : ℝ := ∫ ω, X 0 ω ∂P with hm
  -- Mean stationarity: every coordinate has the same integral `m`.
  have hmean : ∀ j : ℤ, ∫ ω, X j ω ∂P = m := by
    intro j
    have hmem : (0 : ℤ) ∈ ({0} : Finset ℤ) := Finset.mem_singleton.mpr rfl
    have hid : IdentDistrib (X (0 + j)) (X 0) P P :=
      (hSS {0} j).comp (u := fun g : ({0} : Finset ℤ) → ℝ => g ⟨0, hmem⟩) (measurable_pi_apply _)
    have hie := hid.integral_eq
    rwa [zero_add] at hie
  -- The coordinate-zero evaluation is square-integrable under the path law.
  have hev : MemLp (fun y : ℤ → ℝ => y 0) 2 (pathLaw X P) := by
    rw [show pathLaw X P = P.map (fun ω t => X t ω) from rfl,
      memLp_map_measure_iff (measurable_pi_apply 0).aestronglyMeasurable hΦ_ae]
    exact hL2
  -- The centered coordinate `e₀ = Y₀ − m` in `L²`.
  have hconstm : MemLp (fun _ : ℤ → ℝ => m) 2 (pathLaw X P) := memLp_const m
  set e₀ : Lp ℝ 2 (pathLaw X P) := hev.toLp _ - hconstm.toLp _ with he0
  have he0coe : ⇑e₀ =ᵐ[pathLaw X P] fun y => y 0 - m := by
    rw [he0]
    filter_upwards [Lp.coeFn_sub (hev.toLp _) (hconstm.toLp _), hev.coeFn_toLp,
      hconstm.coeFn_toLp] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  -- The centered coordinate integrates to `0`.
  have hint0 : ∫ y, e₀ y ∂(pathLaw X P) = 0 := by
    have hy0 : ∫ y : ℤ → ℝ, y 0 ∂(pathLaw X P) = m := by
      rw [show pathLaw X P = P.map (fun ω t => X t ω) from rfl,
        integral_map hΦ_ae (measurable_pi_apply 0).aestronglyMeasurable]
    rw [integral_congr_ae he0coe, integral_sub (hev.integrable one_le_two) (integrable_const m),
      hy0, integral_const]
    simp
  -- Each Koopman iterate inner product is the autocovariance at that lag.
  have hcov : ∀ j : ℕ, (inner ℝ ((⇑(koopmanL2 he'.toMeasurePreserving))^[j] e₀) e₀ : ℝ)
      = autocov X P (j : ℤ) := by
    intro j
    rw [inner_koopman_iterate_eq]
    have hintegrand : (fun x => (⇑e₀) ((pathShift ℝ)^[j] x) * (⇑e₀) x)
        =ᵐ[pathLaw X P] fun x : ℤ → ℝ => (x (j : ℤ) - m) * (x 0 - m) := by
      have hpush : (fun x => (⇑e₀) ((pathShift ℝ)^[j] x))
          =ᵐ[pathLaw X P] fun x : ℤ → ℝ => x (j : ℤ) - m := by
        refine (he0coe.comp_tendsto
          (he'.toMeasurePreserving.iterate j).quasiMeasurePreserving.tendsto_ae).trans
          (Eventually.of_forall fun x => ?_)
        simp only [Function.comp_apply, pathShift_iterate, zero_add]
      filter_upwards [hpush, he0coe] with x hp hx
      rw [hp, hx]
    rw [integral_congr_ae hintegrand,
      show pathLaw X P = P.map (fun ω t => X t ω) from rfl,
      integral_map hΦ_ae
        (((measurable_pi_apply (j : ℤ)).sub measurable_const).mul
          ((measurable_pi_apply 0).sub measurable_const)).aestronglyMeasurable,
      autocov, autocovAt, zero_add, covariance]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    rw [hmean (j : ℤ), hmean 0]
    ring
  -- Assemble via the generic Cesàro engine with `g = Koopman e₀`, `h = e₀`.
  have hkey := Ergodic.tendsto_cesaro_inner_koopman he'
    (koopmanL2 he'.toMeasurePreserving e₀) e₀
  rw [hint0, mul_zero] at hkey
  refine hkey.congr (fun n => congrArg _ (Finset.sum_congr rfl fun ℓ _ => ?_))
  rw [show (⇑(koopmanL2 he'.toMeasurePreserving))^[ℓ] (koopmanL2 he'.toMeasurePreserving e₀)
        = (⇑(koopmanL2 he'.toMeasurePreserving))^[ℓ + 1] e₀ from
      (Function.iterate_succ_apply (⇑(koopmanL2 he'.toMeasurePreserving)) ℓ e₀).symm, hcov (ℓ + 1)]
  push_cast
  ring_nf

end Autocov

end ProbabilityTheory

