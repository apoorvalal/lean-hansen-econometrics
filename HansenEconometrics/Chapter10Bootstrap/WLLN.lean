import HansenEconometrics.AsymptoticUtils.MaxBounds
import HansenEconometrics.BootstrapUtils
import HansenEconometrics.Chapter10Bootstrap.Empirical

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Elementwise Function

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

/-- Hansen Theorem 10.1, chapter-facing name.

Ordinary convergence in probability implies bootstrap convergence in
probability when the sequence is non-random under the bootstrap resampling law. -/
theorem chapter10_bootstrap_convergence_in_probability_of_convergence_in_probability
    [PseudoMetricSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zseq : ℕ → Ω → E} {Z : Ω → E}
    (hZ : TendstoInMeasure μ Zseq atTop Z) :
    TendstoInBootstrapProbability μ Pstar (fun n ω _ => Zseq n ω) Z :=
  tendstoInBootstrapProbability_of_tendstoInMeasure hPstar hZ

/-- Hansen Theorem 10.3, chapter-facing name.

If `Zₙ* ->p* c` and `g` is continuous at `c`, then
`g(Zₙ*) ->p* g(c)`. -/
theorem chapter10_bootstrap_continuous_mapping_probability
    [PseudoMetricSpace E] [PseudoMetricSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zstar : ℕ → Ω → Ωs → E} {c : E} {g : E → F}
    (hZ : TendstoInBootstrapProbability μ Pstar Zstar (fun _ => c))
    (hg : ContinuousAt g c) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) (fun _ => g c) :=
  hZ.continuousAt_const_comp hPstar hg

/-- Chapter 10 bootstrap-probability mapping bridge for globally Lipschitz
transformations.

This is the reusable form needed by theorem wrappers whose statistic is a
linear or otherwise globally controlled transformation of a bootstrap statistic. -/
theorem chapter10_bootstrap_lipschitz_mapping_probability
    [PseudoMetricSpace E] [PseudoMetricSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zstar : ℕ → Ω → Ωs → E} {Z : Ω → E} {g : E → F} {C : ℝ}
    (hC : 0 < C)
    (hg : ∀ x y, dist (g x) (g y) ≤ C * dist x y)
    (hZ : TendstoInBootstrapProbability μ Pstar Zstar Z) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) (fun ω => g (Z ω)) :=
  hZ.lipschitz_comp hPstar hC hg

/-- Chapter 10 bootstrap-probability scalar-multiplication bridge.

This is the named normalization wrapper used when a bootstrap statistic is
multiplied by a fixed real scalar. -/
theorem chapter10_bootstrap_smul_probability
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (c : ℝ)
    {Zstar : ℕ → Ω → Ωs → E} {Z : Ω → E}
    (hZ : TendstoInBootstrapProbability μ Pstar Zstar Z) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => c • Zstar n ω ωs) (fun ω => c • Z ω) :=
  hZ.smul hPstar c

/-- Hansen Theorem 10.2, centered WLLN from the conditional tail bound.

This is the reusable form of the textbook proof: Markov's inequality and the
conditional variance calculation supply `hle`; the Marcinkiewicz/WLLN argument
supplies `hbound`. -/
theorem chapter10_bootstrap_wlln_centered_of_tail_bound
    [SeminormedAddCommGroup E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {YbarStar : ℕ → Ω → Ωs → E} {Ybar : ℕ → Ω → E}
    {bound : ℝ → ℕ → Ω → ℝ}
    (hbound :
      ∀ η : ℝ, 0 < η →
        TendstoInMeasure μ (fun n ω => bound η n ω) atTop (fun _ => 0))
    (hle :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapTailProb Pstar
          (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0)
          η n ω ≤ bound η n ω) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) :=
  tendstoInBootstrapProbability_of_tail_bound hbound hle

/-- Hansen Theorem 10.2, second conclusion from the centered bootstrap WLLN.

Once the centered bootstrap sample mean satisfies
`Ybar* - Ybar ->p* 0`, and the ordinary sample mean satisfies
`Ybar ->p μY`, the bootstrap sample mean itself satisfies
`Ybar* ->p* μY`.  This is the bootstrap Slutsky/addition step used in the
textbook proof after the centered WLLN is established by the conditional
variance bound. -/
theorem chapter10_bootstrap_wlln_level_from_centered
    [SeminormedAddCommGroup E]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ℕ → Ω → Ωs → E} {Ybar : ℕ → Ω → E} {μY : E}
    (hcenter :
      TendstoInBootstrapProbability μ Pstar
        (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0))
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbability μ Pstar YbarStar (fun _ => μY) := by
  have hYbar_boot :
      TendstoInBootstrapProbability μ Pstar (fun n ω _ => Ybar n ω) (fun _ => μY) :=
    tendstoInBootstrapProbability_of_tendstoInMeasure hPstar hYbar
  have hsum :=
    hcenter.add hPstar hYbar_boot
  exact hsum.congr
    (fun n ω ωs => by simp)
    (fun ω => by simp)

section MarcinkiewiczWLLN

/-- Sample average of absolute values, `n⁻¹ ∑_{i<n} |uᵢ|`.

This is the `Oₚ(1)` factor in Hansen's proof of Theorem 10.20. -/
noncomputable def sampleAbsMean (u : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  (∑ i ∈ Finset.range n, fun ω => |u i ω|) / (n : Ω → ℝ)

/-- Natural-power version of Hansen's Marcinkiewicz WLLN statistic,
`n^{-p} ∑_{i<n} |uᵢ|^p`.

The textbook states the result for every real `r > 1`; this natural-power face
is the one used by the Chapter 10 variance and Lindeberg applications
(`p = 2` and `p = 4`). -/
noncomputable def marcinkiewiczWLLNStatisticNat
    (u : ℕ → Ω → ℝ) (p n : ℕ) (ω : Ω) : ℝ :=
  ((n : ℝ)⁻¹) ^ p * ∑ i ∈ Finset.range n, |u i ω| ^ p

/-- Real-power version of Hansen's Marcinkiewicz WLLN statistic,
`n^{-r} ∑_{i<n} |uᵢ|^r`. -/
noncomputable def marcinkiewiczWLLNStatisticRpow
    (u : ℕ → Ω → ℝ) (r : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((n : ℝ)⁻¹) ^ r * ∑ i ∈ Finset.range n, |u i ω| ^ r

private theorem abs_le_maxNNNorm
    {u : ℕ → Ω → ℝ} {n i : ℕ} {ω : Ω}
    (hi : i ∈ Finset.range n) :
    |u i ω| ≤ (maxNNNorm u n ω : ℝ) := by
  have hle_nn : ‖u i ω‖₊ ≤ maxNNNorm u n ω := by
    dsimp [maxNNNorm]
    exact Finset.le_sup (s := Finset.range n) (f := fun j => ‖u j ω‖₊) hi
  rw [← NNReal.coe_le_coe] at hle_nn
  simpa [Real.norm_eq_abs] using hle_nn

private theorem sampleAbsMean_nonneg
    (u : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ sampleAbsMean u n ω := by
  have hsum : 0 ≤ ∑ i ∈ Finset.range n, |u i ω| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  simpa [sampleAbsMean, div_eq_inv_mul, mul_comm] using
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) hsum

private theorem marcinkiewiczWLLNStatisticNat_nonneg
    (u : ℕ → Ω → ℝ) (p n : ℕ) (ω : Ω) :
    0 ≤ marcinkiewiczWLLNStatisticNat u p n ω := by
  have hscale : 0 ≤ ((n : ℝ)⁻¹) ^ p :=
    pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) p
  have hsum : 0 ≤ ∑ i ∈ Finset.range n, |u i ω| ^ p :=
    Finset.sum_nonneg fun i _ => pow_nonneg (abs_nonneg _) p
  exact mul_nonneg hscale hsum

private theorem marcinkiewiczWLLNStatisticRpow_nonneg
    (u : ℕ → Ω → ℝ) (r : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ marcinkiewiczWLLNStatisticRpow u r n ω := by
  have hscale : 0 ≤ ((n : ℝ)⁻¹) ^ r :=
    Real.rpow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) r
  have hsum : 0 ≤ ∑ i ∈ Finset.range n, |u i ω| ^ r :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) r
  exact mul_nonneg hscale hsum

/-- Deterministic inequality in Hansen's proof of Theorem 10.20.

For natural powers `p ≥ 2`,
`n^{-p} ∑ |uᵢ|^p` is bounded by
`(n^{-1} max |uᵢ|)^{p-1} (n^{-1} ∑ |uᵢ|)`. -/
theorem marcinkiewiczWLLNStatisticNat_le_max_mul_sampleAbsMean
    {u : ℕ → Ω → ℝ} {p n : ℕ} {ω : Ω}
    (hp : 2 ≤ p) :
    marcinkiewiczWLLNStatisticNat u p n ω ≤
      (scaledMaxNNNorm u n ω) ^ (p - 1) * sampleAbsMean u n ω := by
  let a : ℝ := (n : ℝ)⁻¹
  let M : ℝ := (maxNNNorm u n ω : ℝ)
  let S : ℝ := ∑ i ∈ Finset.range n, |u i ω|
  let Sp : ℝ := ∑ i ∈ Finset.range n, |u i ω| ^ p
  have hp1 : 1 ≤ p := (by norm_num : 1 ≤ 2).trans hp
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact inv_nonneg.mpr (Nat.cast_nonneg n)
  have hsum_le : Sp ≤ M ^ (p - 1) * S := by
    calc
      Sp = ∑ i ∈ Finset.range n, |u i ω| ^ p := rfl
      _ ≤ ∑ i ∈ Finset.range n, M ^ (p - 1) * |u i ω| := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have habs_le : |u i ω| ≤ M := by
          simpa [M] using abs_le_maxNNNorm (u := u) (ω := ω) hi
        have hpow_le : |u i ω| ^ (p - 1) ≤ M ^ (p - 1) :=
          pow_le_pow_left₀ (abs_nonneg _) habs_le (p - 1)
        have hpow_eq : |u i ω| ^ p = |u i ω| ^ (p - 1) * |u i ω| := by
          rw [← pow_succ, Nat.sub_add_cancel hp1]
        rw [hpow_eq]
        exact mul_le_mul_of_nonneg_right hpow_le (abs_nonneg _)
      _ = M ^ (p - 1) * S := by
        simp [S, Finset.mul_sum]
  have hscale_le :
      a ^ p * Sp ≤ a ^ p * (M ^ (p - 1) * S) :=
    mul_le_mul_of_nonneg_left hsum_le (pow_nonneg ha_nonneg p)
  have hsample : sampleAbsMean u n ω = a * S := by
    simp [sampleAbsMean, a, S, div_eq_inv_mul]
  have hscaled : scaledMaxNNNorm u n ω = a * M := by
    simp [scaledMaxNNNorm, a, M]
  have hpow_a : a ^ p = a ^ (p - 1) * a := by
    rw [← pow_succ, Nat.sub_add_cancel hp1]
  have hrhs :
      a ^ p * (M ^ (p - 1) * S) =
        (scaledMaxNNNorm u n ω) ^ (p - 1) * sampleAbsMean u n ω := by
    calc
      a ^ p * (M ^ (p - 1) * S)
          = (a ^ (p - 1) * M ^ (p - 1)) * (a * S) := by
            rw [hpow_a]
            ring
      _ = (a * M) ^ (p - 1) * (a * S) := by
            rw [mul_pow]
      _ = (scaledMaxNNNorm u n ω) ^ (p - 1) * sampleAbsMean u n ω := by
            rw [hscaled, hsample]
  change a ^ p * Sp ≤
    (scaledMaxNNNorm u n ω) ^ (p - 1) * sampleAbsMean u n ω
  exact hscale_le.trans_eq hrhs

/-- Deterministic inequality in Hansen's proof of Theorem 10.20 for real
exponents `r > 1`.

This is the textbook display
`n^{-r} ∑ |uᵢ|^r ≤ (n^{-1} max |uᵢ|)^{r-1} (n^{-1} ∑ |uᵢ|)`. -/
theorem marcinkiewiczWLLNStatisticRpow_le_max_mul_sampleAbsMean
    {u : ℕ → Ω → ℝ} {r : ℝ} {n : ℕ} {ω : Ω}
    (hr : 1 < r) :
    marcinkiewiczWLLNStatisticRpow u r n ω ≤
      (scaledMaxNNNorm u n ω) ^ (r - 1) * sampleAbsMean u n ω := by
  let a : ℝ := (n : ℝ)⁻¹
  let M : ℝ := (maxNNNorm u n ω : ℝ)
  let S : ℝ := ∑ i ∈ Finset.range n, |u i ω|
  let Sr : ℝ := ∑ i ∈ Finset.range n, |u i ω| ^ r
  let q : ℝ := r - 1
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact sub_nonneg.mpr hr.le
  have hr_eq : r = q + 1 := by
    dsimp [q]
    ring
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact inv_nonneg.mpr (Nat.cast_nonneg n)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact NNReal.coe_nonneg _
  have hsum_le : Sr ≤ M ^ q * S := by
    calc
      Sr = ∑ i ∈ Finset.range n, |u i ω| ^ r := rfl
      _ ≤ ∑ i ∈ Finset.range n, M ^ q * |u i ω| := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have habs_le : |u i ω| ≤ M := by
          simpa [M] using abs_le_maxNNNorm (u := u) (ω := ω) hi
        have hpow_le : |u i ω| ^ q ≤ M ^ q :=
          Real.rpow_le_rpow (abs_nonneg _) habs_le hq_nonneg
        have hpow_eq : |u i ω| ^ r = |u i ω| ^ q * |u i ω| := by
          rw [hr_eq, Real.rpow_add_of_nonneg (abs_nonneg _) hq_nonneg zero_le_one,
            Real.rpow_one]
        rw [hpow_eq]
        exact mul_le_mul_of_nonneg_right hpow_le (abs_nonneg _)
      _ = M ^ q * S := by
        simp [S, Finset.mul_sum]
  have hscale_le :
      a ^ r * Sr ≤ a ^ r * (M ^ q * S) :=
    mul_le_mul_of_nonneg_left hsum_le (Real.rpow_nonneg ha_nonneg r)
  have hsample : sampleAbsMean u n ω = a * S := by
    simp [sampleAbsMean, a, S, div_eq_inv_mul]
  have hscaled : scaledMaxNNNorm u n ω = a * M := by
    simp [scaledMaxNNNorm, a, M]
  have hpow_a : a ^ r = a ^ q * a := by
    rw [hr_eq, Real.rpow_add_of_nonneg ha_nonneg hq_nonneg zero_le_one, Real.rpow_one]
  have hrhs :
      a ^ r * (M ^ q * S) =
        (scaledMaxNNNorm u n ω) ^ (r - 1) * sampleAbsMean u n ω := by
    calc
      a ^ r * (M ^ q * S)
          = (a ^ q * M ^ q) * (a * S) := by
            rw [hpow_a]
            ring
      _ = (a * M) ^ q * (a * S) := by
            rw [Real.mul_rpow ha_nonneg hM_nonneg]
      _ = (scaledMaxNNNorm u n ω) ^ (r - 1) * sampleAbsMean u n ω := by
            rw [hscaled, hsample]
  change a ^ r * Sr ≤
    (scaledMaxNNNorm u n ω) ^ (r - 1) * sampleAbsMean u n ω
  exact hscale_le.trans_eq hrhs

private theorem tendstoInMeasure_pow_nat_zero_real
    {X : ℕ → Ω → ℝ}
    (hX : TendstoInMeasure μ X atTop (fun _ => 0))
    {q : ℕ} (hq : 0 < q) :
    TendstoInMeasure μ (fun n ω => (X n ω) ^ q) atTop (fun _ => 0) := by
  induction q with
  | zero =>
      exact (Nat.lt_irrefl 0 hq).elim
  | succ q ih =>
      by_cases hq0 : q = 0
      · subst q
        simpa using hX
      · have hq_pos : 0 < q := Nat.pos_of_ne_zero hq0
        have hpow := ih hq_pos
        have hmul := TendstoInMeasure.mul_zero_real hpow hX
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul

private theorem tendstoInMeasure_rpow_pos_zero_real
    {X : ℕ → Ω → ℝ}
    (hX_nonneg : ∀ n ω, 0 ≤ X n ω)
    (hX : TendstoInMeasure μ X atTop (fun _ => 0))
    {q : ℝ} (hq : 0 < q) :
    TendstoInMeasure μ (fun n ω => (X n ω) ^ q) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro ε hε
  let δ : ℝ := ε ^ q⁻¹
  have hδ_pos : 0 < δ := Real.rpow_pos_of_pos hε q⁻¹
  have hδ_nonneg : 0 ≤ δ := hδ_pos.le
  have hδ_pow : δ ^ q = ε := by
    dsimp [δ]
    simpa using Real.rpow_inv_rpow hε.le hq.ne'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hX δ hδ_pos) (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  have hXpow_nonneg : 0 ≤ (X n ω) ^ q :=
    Real.rpow_nonneg (hX_nonneg n ω) q
  have htail_power : ε ≤ (X n ω) ^ q := by
    simpa [Real.dist_eq, abs_of_nonneg hXpow_nonneg] using hω
  have hδ_le_X : δ ≤ X n ω := by
    rw [← Real.rpow_le_rpow_iff hδ_nonneg (hX_nonneg n ω) hq]
    simpa [hδ_pow] using htail_power
  simpa [Real.dist_eq, abs_of_nonneg (hX_nonneg n ω)] using hδ_le_X

/-- Uniform integrability makes `n⁻¹ ∑ |uᵢ|` bounded in probability.

This is the `Oₚ(1)` sample-mean factor used in Hansen's proof of Theorem
10.20. -/
theorem sampleAbsMean_boundedInProbability_of_uniformIntegrable
    [IsFiniteMeasure μ] {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ) :
    BoundedInProbability μ (sampleAbsMean u) := by
  have hAbsUI : UniformIntegrable (fun i ω => |u i ω|) 1 μ :=
    uniformIntegrable_abs hu
  have hAvgUI : UniformIntegrable (sampleAbsMean u) 1 μ := by
    simpa [sampleAbsMean] using
      (uniformIntegrable_average_real (μ := μ) (p := (1 : ℝ≥0∞))
        (f := fun i ω => |u i ω|) le_rfl hAbsUI)
  exact BoundedInProbability.of_uniformIntegrable_one hAvgUI

/-- Hansen Theorem 10.20, natural-power convergence engine.

If the scaled maximum `n⁻¹ max |uᵢ|` is `oₚ(1)` and the absolute sample mean is
`Oₚ(1)`, then `n^{-p} ∑ |uᵢ|^p = oₚ(1)` for every natural `p ≥ 2`. -/
theorem chapter10_marcinkiewicz_wlln_natPower_of_max_and_absMean
    {u : ℕ → Ω → ℝ} {p : ℕ}
    (hp : 2 ≤ p)
    (hmax : TendstoInMeasure μ (scaledMaxNNNorm u) atTop (fun _ => 0))
    (hmean : BoundedInProbability μ (sampleAbsMean u)) :
    TendstoInMeasure μ (marcinkiewiczWLLNStatisticNat u p) atTop (fun _ => 0) := by
  have hp_gt_one : 1 < p := (by norm_num : 1 < 2).trans_le hp
  have hp_sub_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp_gt_one
  have hpow :
      TendstoInMeasure μ
        (fun n ω => (scaledMaxNNNorm u n ω) ^ (p - 1)) atTop (fun _ => 0) :=
    tendstoInMeasure_pow_nat_zero_real hmax hp_sub_pos
  have hprod :
      TendstoInMeasure μ
        (fun n ω => (scaledMaxNNNorm u n ω) ^ (p - 1) * sampleAbsMean u n ω)
        atTop (fun _ => 0) :=
    TendstoInMeasure.mul_boundedInProbability hpow hmean
  exact tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := marcinkiewiczWLLNStatisticNat u p)
    (g := fun n ω => (scaledMaxNNNorm u n ω) ^ (p - 1) * sampleAbsMean u n ω)
    (marcinkiewiczWLLNStatisticNat_nonneg u p)
    (fun n ω =>
      marcinkiewiczWLLNStatisticNat_le_max_mul_sampleAbsMean
        (u := u) (p := p) (n := n) (ω := ω) hp)
    hprod

/-- Hansen Theorem 10.20, natural-power uniformly-integrable wrapper.

For natural `p ≥ 2`, uniform integrability of the real sequence `uᵢ` implies
`n^{-p} ∑ |uᵢ|^p ->p 0`.  The textbook states the same argument for every real
`r > 1`; this wrapper records the integer-power surface needed by the Chapter
10 bootstrap variance and Lindeberg proofs. -/
theorem chapter10_marcinkiewicz_wlln_natPower_of_uniformIntegrable
    [IsFiniteMeasure μ] {u : ℕ → Ω → ℝ} {p : ℕ}
    (hp : 2 ≤ p)
    (hu : UniformIntegrable u 1 μ) :
    TendstoInMeasure μ (marcinkiewiczWLLNStatisticNat u p) atTop (fun _ => 0) :=
  chapter10_marcinkiewicz_wlln_natPower_of_max_and_absMean
    (μ := μ) (u := u) hp
    (max_norm_scaled_tendstoInMeasure_zero_of_uniformIntegrable_norm_r (μ := μ) (Z := u) hu)
    (sampleAbsMean_boundedInProbability_of_uniformIntegrable (μ := μ) hu)

/-- Shifted `Fin (n+1)` version of Hansen Theorem 10.20.

Ordinary nonparametric bootstrap support uses `Fin (n+1)` to avoid the empty
sample at `n = 0`; this is the corresponding shifted Marcinkiewicz WLLN. -/
theorem marcinkiewiczWLLNStatisticNat_succ_tendsto_zero_of_uniformIntegrable
    [IsFiniteMeasure μ] {u : ℕ → Ω → ℝ} {p : ℕ}
    (hp : 2 ≤ p)
    (hu : UniformIntegrable u 1 μ) :
    TendstoInMeasure μ
      (fun n ω => marcinkiewiczWLLNStatisticNat u p (n + 1) ω)
      atTop (fun _ => 0) := by
  have h :=
    chapter10_marcinkiewicz_wlln_natPower_of_uniformIntegrable
      (μ := μ) (u := u) (p := p) hp hu
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  simpa [Function.comp_def] using
    (h ε hε).comp (tendsto_add_atTop_nat 1)

private theorem memLp_norm_sq_one_of_memLp_two
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [IsFiniteMeasure μ]
    {Y : Ω → E} (hY : MemLp Y 2 μ) :
    MemLp (fun ω => ‖Y ω‖ ^ 2) 1 μ := by
  have hsq_int : Integrable (fun ω => ‖Y ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).1 hY
  exact memLp_one_iff_integrable.mpr hsq_int

/-- The shifted empirical fourth-moment Marcinkiewicz step in Hansen Theorem
10.4.

If `Y₀` has a finite second moment and the observations are identically
distributed, then applying Theorem 10.20 to `uᵢ = ‖Yᵢ‖²` gives
`(n+1)^{-2} sum_{i<n+1} ‖Yᵢ‖⁴ ->p 0`. -/
theorem marcinkiewicz_norm_sq_finSucc_tendsto_zero_of_identDistrib_memLp_two
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [IsFiniteMeasure μ]
    (Y : ℕ → Ω → E)
    (hY : MemLp (Y 0) 2 μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInMeasure μ
      (fun n ω =>
        marcinkiewiczWLLNStatisticNat (fun i ω => ‖Y i ω‖ ^ 2) 2 (n + 1) ω)
      atTop (fun _ => 0) := by
  have hYnormSq : MemLp (fun ω => ‖Y 0 ω‖ ^ 2) 1 μ :=
    memLp_norm_sq_one_of_memLp_two (μ := μ) hY
  have hnormSq_ident :
      ∀ i,
        IdentDistrib (fun ω => ‖Y i ω‖ ^ 2) (fun ω => ‖Y 0 ω‖ ^ 2) μ μ := by
    intro i
    simpa [Function.comp_def] using (hident i).comp ((continuous_norm.pow 2).measurable)
  exact marcinkiewiczWLLNStatisticNat_succ_tendsto_zero_of_uniformIntegrable
    (μ := μ) (u := fun i ω => ‖Y i ω‖ ^ 2) (p := 2) (by norm_num)
    (uniformIntegrable_one_of_identDistrib_memLp
      (μ := μ) (Z := fun i ω => ‖Y i ω‖ ^ 2) hYnormSq hnormSq_ident)

/-- Empirical fourth-moment form of the shifted Marcinkiewicz step.

For the ordinary `Fin (n+1)` empirical law, the quantity
`(n+1)^{-1} E*[‖Y_i^*‖⁴]` is exactly the shifted Marcinkiewicz statistic for
`uᵢ = ‖Yᵢ‖²`, hence it converges to zero under the finite-second-moment
identical-distribution assumptions. -/
theorem scaled_integral_norm_fourth_uniformOn_finSucc_tendsto_zero_of_identDistrib_memLp_two
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [IsFiniteMeasure μ]
    (Y : ℕ → Ω → E)
    (hY : MemLp (Y 0) 2 μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInMeasure μ
      (fun n ω =>
        (((n + 1 : ℕ) : ℝ)⁻¹) *
          ∫ i : Fin (n + 1), ‖Y i.val ω‖ ^ 4
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))))
      atTop (fun _ => 0) := by
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl
    (marcinkiewicz_norm_sq_finSucc_tendsto_zero_of_identDistrib_memLp_two
      (μ := μ) Y hY hident)
  exact ae_of_all μ fun ω => by
    change
      marcinkiewiczWLLNStatisticNat (fun i ω => ‖Y i ω‖ ^ 2) 2 (n + 1) ω =
        (((n + 1 : ℕ) : ℝ)⁻¹) *
          ∫ i : Fin (n + 1), ‖Y i.val ω‖ ^ 4
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))
    rw [integral_norm_fourth_uniformOn_univ_eq_card_inv_smul_sum
      (Y := fun i : Fin (n + 1) => Y i.val ω)]
    have hcoeff :
        (((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal) =
          (((n + 1 : ℕ) : ℝ)⁻¹) := by
      have htoReal :
          ((Fintype.card (Fin (n + 1)) : ℝ≥0∞).toReal) =
            (n + 1 : ℝ) := by
        rw [Fintype.card_fin]
        simpa using ENNReal.toReal_natCast (n + 1)
      rw [ENNReal.toReal_inv, htoReal]
      simp [Nat.cast_add, Nat.cast_one]
    have hsum :
        (∑ i : Fin (n + 1), ‖Y i.val ω‖ ^ 4) =
          ∑ i ∈ Finset.range (n + 1), ‖Y i ω‖ ^ 4 := by
      rw [Finset.sum_range]
    rw [hcoeff, hsum]
    simp [marcinkiewiczWLLNStatisticNat, smul_eq_mul, pow_two,
      Nat.cast_add, Nat.cast_one]
    ring_nf

/-- Hansen Theorem 10.20, real-exponent convergence engine.

If the scaled maximum `n⁻¹ max |uᵢ|` is `oₚ(1)` and the absolute sample mean is
`Oₚ(1)`, then `n^{-r} ∑ |uᵢ|^r = oₚ(1)` for every real `r > 1`. -/
theorem chapter10_marcinkiewicz_wlln_rpow_of_max_and_absMean
    {u : ℕ → Ω → ℝ} {r : ℝ}
    (hr : 1 < r)
    (hmax : TendstoInMeasure μ (scaledMaxNNNorm u) atTop (fun _ => 0))
    (hmean : BoundedInProbability μ (sampleAbsMean u)) :
    TendstoInMeasure μ (marcinkiewiczWLLNStatisticRpow u r) atTop (fun _ => 0) := by
  have hq_pos : 0 < r - 1 := sub_pos.mpr hr
  have hscaled_nonneg : ∀ n ω, 0 ≤ scaledMaxNNNorm u n ω := by
    intro n ω
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (NNReal.coe_nonneg _)
  have hpow :
      TendstoInMeasure μ
        (fun n ω => (scaledMaxNNNorm u n ω) ^ (r - 1)) atTop (fun _ => 0) :=
    tendstoInMeasure_rpow_pos_zero_real hscaled_nonneg hmax hq_pos
  have hprod :
      TendstoInMeasure μ
        (fun n ω => (scaledMaxNNNorm u n ω) ^ (r - 1) * sampleAbsMean u n ω)
        atTop (fun _ => 0) :=
    TendstoInMeasure.mul_boundedInProbability hpow hmean
  exact tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := marcinkiewiczWLLNStatisticRpow u r)
    (g := fun n ω => (scaledMaxNNNorm u n ω) ^ (r - 1) * sampleAbsMean u n ω)
    (marcinkiewiczWLLNStatisticRpow_nonneg u r)
    (fun n ω =>
      marcinkiewiczWLLNStatisticRpow_le_max_mul_sampleAbsMean
        (u := u) (r := r) (n := n) (ω := ω) hr)
    hprod

/-- **Hansen Theorem 10.20, Marcinkiewicz WLLN.**

If `uᵢ` is uniformly integrable, then for every real `r > 1`,
`n^{-r} ∑ |uᵢ|^r ->p 0`.  Hansen states the theorem with independence as a
sufficient condition for the ordinary WLLN step; this formulation is slightly
stronger because Mathlib's probability-theory uniform integrability already
provides the `Oₚ(1)` absolute-mean factor, and Chapter 6's maximum theorem
provides the `oₚ(1)` scaled-maximum factor. -/
theorem chapter10_marcinkiewicz_wlln_rpow_of_uniformIntegrable
    [IsFiniteMeasure μ] {u : ℕ → Ω → ℝ} {r : ℝ}
    (hr : 1 < r)
    (hu : UniformIntegrable u 1 μ) :
    TendstoInMeasure μ (marcinkiewiczWLLNStatisticRpow u r) atTop (fun _ => 0) :=
  chapter10_marcinkiewicz_wlln_rpow_of_max_and_absMean
    (μ := μ) (u := u) hr
    (max_norm_scaled_tendstoInMeasure_zero_of_uniformIntegrable_norm_r (μ := μ) (Z := u) hu)
    (sampleAbsMean_boundedInProbability_of_uniformIntegrable (μ := μ) hu)

/-- Shifted real-exponent version of Hansen Theorem 10.20.

Ordinary nonparametric bootstrap support uses `Fin (n+1)` to avoid the empty
sample at `n = 0`; this is the corresponding shifted form of Hansen's stated
real-exponent Marcinkiewicz WLLN. -/
theorem marcinkiewiczWLLNStatisticRpow_succ_tendsto_zero_of_uniformIntegrable
    [IsFiniteMeasure μ] {u : ℕ → Ω → ℝ} {r : ℝ}
    (hr : 1 < r)
    (hu : UniformIntegrable u 1 μ) :
    TendstoInMeasure μ
      (fun n ω => marcinkiewiczWLLNStatisticRpow u r (n + 1) ω)
      atTop (fun _ => 0) := by
  have h :=
    chapter10_marcinkiewicz_wlln_rpow_of_uniformIntegrable
      (μ := μ) (u := u) hr hu
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  simpa using (h ε hε).comp (tendsto_add_atTop_nat 1)

end MarcinkiewiczWLLN

section BootstrapWLLNSecondMoment

/-- Hansen Theorem 10.2 second-moment bound.

The textbook proof bounds the centered bootstrap sample-mean tail probability
by `η^{-2} n^{-2} ∑ |u_i|^2`; in vector applications `u_i` is the norm of the
original observation. -/
noncomputable def bootstrapWLLNSecondMomentBound
    (u : ℕ → Ω → ℝ) (η : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  η⁻¹ ^ 2 * marcinkiewiczWLLNStatisticNat u 2 n ω

/-- The second-moment bound in Hansen's bootstrap WLLN proof is `oₚ(1)`.

This is exactly the Marcinkiewicz WLLN step in the proof of Theorem 10.2, with
natural power `p = 2`. -/
theorem bootstrapWLLNSecondMomentBound_tendsto_zero
    [IsFiniteMeasure μ] {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ) {η : ℝ} (_hη : 0 < η) :
    TendstoInMeasure μ (fun n ω => bootstrapWLLNSecondMomentBound u η n ω)
      atTop (fun _ => 0) := by
  have hmarc :
      TendstoInMeasure μ (marcinkiewiczWLLNStatisticNat u 2) atTop (fun _ => 0) :=
    chapter10_marcinkiewicz_wlln_natPower_of_uniformIntegrable
      (μ := μ) (u := u) (p := 2) (by norm_num) hu
  change TendstoInMeasure μ
    (fun n ω => η⁻¹ ^ 2 * marcinkiewiczWLLNStatisticNat u 2 n ω)
    atTop (fun _ => 0)
  exact TendstoInMeasure.const_mul_zero_real (μ := μ) (η⁻¹ ^ 2) hmarc

/-- Vector-valued `L²` Markov bound for bootstrap tails.

This is the conditional-probability form of
`P*(‖Z*‖ ≥ η) ≤ η⁻² ‖Z*‖²_{L²(P*)}`.  The right side is written with
Mathlib's `eLpNorm` because this is the reusable layer that applies before a
particular empirical covariance calculation has identified the `L²` seminorm. -/
noncomputable def bootstrapL2ENNTailBound
    [NormedAddCommGroup E]
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → E)
    (η : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (((ENNReal.ofReal η)⁻¹ ^ (2 : ℝ)) *
    eLpNorm (Zstar n ω) 2 (Pstar n ω) ^ (2 : ℝ)).toReal

/-- Conditional Markov inequality for vector-valued bootstrap statistics. -/
theorem bootstrapTailProb_zero_le_l2_eLpNorm_bound
    [NormedAddCommGroup E]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → E}
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {η : ℝ} (hη : 0 < η) (n : ℕ) (ω : Ω) :
    bootstrapTailProb Pstar Zstar (fun _ => 0) η n ω ≤
      bootstrapL2ENNTailBound Pstar Zstar η n ω := by
  have htail :
      (Pstar n ω)
          {ωs : Ωs | ENNReal.ofReal η ≤ ‖Zstar n ω ωs‖ₑ} ≤
        (ENNReal.ofReal η)⁻¹ ^ (2 : ℝ) *
          eLpNorm (Zstar n ω) 2 (Pstar n ω) ^ (2 : ℝ) := by
    simpa using
      (MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm
        (μ := Pstar n ω) (p := (2 : ℝ≥0∞)) (f := Zstar n ω)
        (by norm_num) (by simp) (hZ n ω).1
        (ε := ENNReal.ofReal η) (by simp [hη])
        (by intro htop; exact (ENNReal.ofReal_ne_top htop).elim))
  have hset :
      {ωs : Ωs | η ≤ dist (Zstar n ω ωs) ((fun _ : Ω => (0 : E)) ω)} =
        {ωs : Ωs | ENNReal.ofReal η ≤ ‖Zstar n ω ωs‖ₑ} := by
    ext ωs
    simp only [Set.mem_setOf_eq]
    rw [dist_eq_norm, sub_zero, ← ofReal_norm_eq_enorm]
    exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).symm
  have hmeasure :
      (Pstar n ω)
          {ωs : Ωs | η ≤ dist (Zstar n ω ωs) ((fun _ : Ω => (0 : E)) ω)} ≤
        (ENNReal.ofReal η)⁻¹ ^ (2 : ℝ) *
          eLpNorm (Zstar n ω) 2 (Pstar n ω) ^ (2 : ℝ) := by
    rw [hset]
    exact htail
  have hrhs_ne_top :
      (ENNReal.ofReal η)⁻¹ ^ (2 : ℝ) *
          eLpNorm (Zstar n ω) 2 (Pstar n ω) ^ (2 : ℝ) ≠ ∞ := by
    have hnorm_ne_top : eLpNorm (Zstar n ω) 2 (Pstar n ω) ≠ ∞ :=
      (hZ n ω).eLpNorm_ne_top
    finiteness
  have hreal := ENNReal.toReal_mono hrhs_ne_top hmeasure
  simpa [bootstrapTailProb, bootstrapL2ENNTailBound] using hreal

/-- Conditional Markov inequality for vector bootstrap statistics, written as
a concrete second moment.

This is the textbook-facing form of the `L²` tail bridge:
`P*(‖Z*‖ ≥ η) ≤ E*[‖Z*‖²] / η²`.  It is designed for empirical-bootstrap
specializations where the conditional second moment is then identified by a
finite covariance or norm calculation. -/
theorem bootstrapTailProb_zero_le_integral_norm_sq_div
    [NormedAddCommGroup E]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → E}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {η : ℝ} (hη : 0 < η) (n : ℕ) (ω : Ω) :
    bootstrapTailProb Pstar Zstar (fun _ => 0) η n ω ≤
      (∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω) / η ^ 2 := by
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  let A : Set Ωs :=
    {ωs | η ≤ dist (Zstar n ω ωs) ((fun _ : Ω => (0 : E)) ω)}
  let B : Set Ωs := {ωs | η ^ 2 ≤ ‖Zstar n ω ωs‖ ^ 2}
  have hAB : A ⊆ B := by
    intro ωs hωs
    have hnorm : η ≤ ‖Zstar n ω ωs‖ := by
      simpa [A, dist_eq_norm, sub_zero] using hωs
    exact pow_le_pow_left₀ hη.le hnorm 2
  have hA_le_B : (Pstar n ω).real A ≤ (Pstar n ω).real B :=
    measureReal_mono hAB
  have hInt :
      Integrable (fun ωs => ‖Zstar n ω ωs‖ ^ 2) (Pstar n ω) :=
    (memLp_two_iff_integrable_sq_norm (hZ n ω).1).1 (hZ n ω)
  have hmarkov :
      η ^ 2 * (Pstar n ω).real B ≤
        ∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω := by
    simpa [B] using
      (mul_meas_ge_le_integral_of_nonneg
        (μ := Pstar n ω) (f := fun ωs => ‖Zstar n ω ωs‖ ^ 2)
        (ae_of_all _ fun ωs => pow_nonneg (norm_nonneg (Zstar n ω ωs)) 2)
        hInt (η ^ 2))
  have hB_le :
      (Pstar n ω).real B ≤
        (∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω) / η ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hη)).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmarkov)
  calc
    bootstrapTailProb Pstar Zstar (fun _ => 0) η n ω
        = (Pstar n ω).real A := by
          simp [bootstrapTailProb, A, measureReal_def]
    _ ≤ (Pstar n ω).real B := hA_le_B
    _ ≤ (∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω) / η ^ 2 := hB_le

/-- Conditional Chebyshev inequality for centered scalar bootstrap statistics.

If a scalar bootstrap statistic has conditional mean zero, then its conditional
tail probability is bounded by its conditional variance divided by `η²`. -/
theorem bootstrapTailProb_centered_real_le_variance_div_sq
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hmean : ∀ n ω, (Pstar n ω)[Zstar n ω] = 0)
    {η : ℝ} (hη : 0 < η) (n : ℕ) (ω : Ω) :
    bootstrapTailProb Pstar Zstar (fun _ => 0) η n ω ≤
      Var[Zstar n ω; Pstar n ω] / η ^ 2 := by
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  have hcheb :=
    ProbabilityTheory.meas_ge_le_variance_div_sq
      (μ := Pstar n ω) (X := Zstar n ω) (hZ n ω) hη
  have hset :
      {ωs : Ωs | η ≤ dist (Zstar n ω ωs) ((fun _ : Ω => (0 : ℝ)) ω)} =
        {ωs : Ωs | η ≤ |Zstar n ω ωs - (Pstar n ω)[Zstar n ω]|} := by
    ext ωs
    simp [hmean n ω]
  have hmeasure :
      (Pstar n ω)
          {ωs : Ωs | η ≤ dist (Zstar n ω ωs) ((fun _ : Ω => (0 : ℝ)) ω)} ≤
        ENNReal.ofReal (Var[Zstar n ω; Pstar n ω] / η ^ 2) := by
    rw [hset]
    exact hcheb
  have hnonneg :
      0 ≤ Var[Zstar n ω; Pstar n ω] / η ^ 2 :=
    div_nonneg (ProbabilityTheory.variance_nonneg (Zstar n ω) (Pstar n ω))
      (sq_nonneg η)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  simpa [bootstrapTailProb, ENNReal.toReal_ofReal hnonneg] using hreal

/-- Hansen Theorem 10.2, centered WLLN from the textbook second-moment bound.

Once Chebyshev/Markov and the empirical variance calculation give the
conditional tail bound `hle`, the Marcinkiewicz WLLN proves that bound is
`oₚ(1)`, hence the centered bootstrap sample mean converges in bootstrap
probability to zero. -/
theorem chapter10_bootstrap_wlln_centered_of_second_moment_bound
    [SeminormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {YbarStar : ℕ → Ω → Ωs → E} {Ybar : ℕ → Ω → E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hle :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapTailProb Pstar
          (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0)
          η n ω ≤ bootstrapWLLNSecondMomentBound u η n ω) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) :=
  chapter10_bootstrap_wlln_centered_of_tail_bound
    (bound := fun η n ω => bootstrapWLLNSecondMomentBound u η n ω)
    (fun η hη => bootstrapWLLNSecondMomentBound_tendsto_zero (μ := μ) (η := η) hu hη)
    hle

/-- Hansen Theorem 10.2, scalar centered WLLN from a conditional variance
bound.

This is the Chebyshev/Marcinkiewicz constructor for the scalar case: if the
conditional variance of the centered bootstrap sample mean is bounded by the
textbook `n^{-2} ∑ |u_i|²` term, then the centered bootstrap WLLN follows. -/
theorem chapter10_bootstrap_wlln_centered_real_of_conditional_variance_bound
    [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ℕ → Ω → Ωs → ℝ} {Ybar : ℕ → Ω → ℝ}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hmean :
      ∀ n ω, (Pstar n ω)[fun ωs => YbarStar n ω ωs - Ybar n ω] = 0)
    (hvar :
      ∀ n ω,
        Var[fun ωs => YbarStar n ω ωs - Ybar n ω; Pstar n ω] ≤
          marcinkiewiczWLLNStatisticNat u 2 n ω) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) := by
  refine chapter10_bootstrap_wlln_centered_of_second_moment_bound
    (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
    (u := u) hu ?_
  intro η hη n ω
  calc
    bootstrapTailProb Pstar
        (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) η n ω
        ≤ Var[fun ωs => YbarStar n ω ωs - Ybar n ω; Pstar n ω] / η ^ 2 :=
          bootstrapTailProb_centered_real_le_variance_div_sq
            (Pstar := Pstar)
            (Zstar := fun n ω ωs => YbarStar n ω ωs - Ybar n ω)
            hPstar hZ hmean hη n ω
    _ ≤ marcinkiewiczWLLNStatisticNat u 2 n ω / η ^ 2 :=
          div_le_div_of_nonneg_right (hvar n ω) (sq_nonneg η)
    _ = bootstrapWLLNSecondMomentBound u η n ω := by
          rw [bootstrapWLLNSecondMomentBound]
          field_simp [hη.ne']

/-- Hansen Theorem 10.2, scalar level WLLN from a conditional variance bound.

This packages the scalar conditional-Chebyshev centered result with the
ordinary-sample WLLN for `Ybar`, giving the textbook level conclusion
`Ybar* ->p* μY`. -/
theorem chapter10_bootstrap_wlln_level_real_of_conditional_variance_bound
    [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ℕ → Ω → Ωs → ℝ} {Ybar : ℕ → Ω → ℝ} {μY : ℝ}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hmean :
      ∀ n ω, (Pstar n ω)[fun ωs => YbarStar n ω ωs - Ybar n ω] = 0)
    (hvar :
      ∀ n ω,
        Var[fun ωs => YbarStar n ω ωs - Ybar n ω; Pstar n ω] ≤
          marcinkiewiczWLLNStatisticNat u 2 n ω)
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbability μ Pstar YbarStar (fun _ => μY) :=
  chapter10_bootstrap_wlln_level_from_centered
    (μ := μ) hPstar
    (chapter10_bootstrap_wlln_centered_real_of_conditional_variance_bound
      (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
      (u := u) hPstar hu hZ hmean hvar)
    hYbar

/-- Hansen Theorem 10.2, vector centered WLLN from a bootstrap `L²` seminorm
bound.

This is the vector-valued conditional Markov constructor.  The remaining
empirical-bootstrap specialization identifies the displayed `L²` seminorm
through the finite empirical covariance/norm calculation. -/
theorem chapter10_bootstrap_wlln_centered_of_l2_eLpNorm_bound
    [NormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {YbarStar : ℕ → Ω → Ωs → E} {Ybar : ℕ → Ω → E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hbound :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapL2ENNTailBound Pstar
          (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) η n ω ≤
            bootstrapWLLNSecondMomentBound u η n ω) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) := by
  refine chapter10_bootstrap_wlln_centered_of_second_moment_bound
    (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
    (u := u) hu ?_
  intro η hη n ω
  exact (bootstrapTailProb_zero_le_l2_eLpNorm_bound
    (Pstar := Pstar)
    (Zstar := fun n ω ωs => YbarStar n ω ωs - Ybar n ω)
    hZ hη n ω).trans (hbound η hη n ω)

/-- Hansen Theorem 10.2, vector centered WLLN from a conditional second-moment
bound.

This is the finite-empirical target form of the vector proof: once the
conditional second moment of the centered bootstrap mean is bounded by
`n^{-2} ∑ ‖uᵢ‖²`, the Marcinkiewicz WLLN gives the centered bootstrap
conclusion. -/
theorem chapter10_bootstrap_wlln_centered_of_integral_norm_sq_bound
    [NormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ℕ → Ω → Ωs → E} {Ybar : ℕ → Ω → E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hbound :
      ∀ n ω,
        (∫ ωs, ‖YbarStar n ω ωs - Ybar n ω‖ ^ 2 ∂Pstar n ω) ≤
          marcinkiewiczWLLNStatisticNat u 2 n ω) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) := by
  refine chapter10_bootstrap_wlln_centered_of_second_moment_bound
    (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
    (u := u) hu ?_
  intro η hη n ω
  calc
    bootstrapTailProb Pstar
        (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) η n ω
        ≤ (∫ ωs, ‖YbarStar n ω ωs - Ybar n ω‖ ^ 2 ∂Pstar n ω) / η ^ 2 :=
          bootstrapTailProb_zero_le_integral_norm_sq_div
            (Pstar := Pstar)
            (Zstar := fun n ω ωs => YbarStar n ω ωs - Ybar n ω)
            hPstar hZ hη n ω
    _ ≤ marcinkiewiczWLLNStatisticNat u 2 n ω / η ^ 2 :=
          div_le_div_of_nonneg_right (hbound n ω) (sq_nonneg η)
    _ = bootstrapWLLNSecondMomentBound u η n ω := by
          rw [bootstrapWLLNSecondMomentBound]
          field_simp [hη.ne']

/-- Hansen Theorem 10.2, vector level WLLN from a bootstrap `L²` seminorm
bound.

This packages the vector conditional-Markov centered result with the
ordinary-sample WLLN for `Ybar`, giving the textbook level conclusion
`Ybar* ->p* μY`. -/
theorem chapter10_bootstrap_wlln_level_of_l2_eLpNorm_bound
    [NormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ℕ → Ω → Ωs → E} {Ybar : ℕ → Ω → E} {μY : E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hbound :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapL2ENNTailBound Pstar
          (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) η n ω ≤
            bootstrapWLLNSecondMomentBound u η n ω)
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbability μ Pstar YbarStar (fun _ => μY) :=
  chapter10_bootstrap_wlln_level_from_centered
    (μ := μ) hPstar
    (chapter10_bootstrap_wlln_centered_of_l2_eLpNorm_bound
      (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
      (u := u) hu hZ hbound)
    hYbar

/-- Hansen Theorem 10.2, vector level WLLN from a conditional second-moment
bound.

This packages the conditional-second-moment centered constructor with the
ordinary-sample WLLN for `Ybar`, giving the textbook level conclusion
`Ybar* ->p* μY`. -/
theorem chapter10_bootstrap_wlln_level_of_integral_norm_sq_bound
    [NormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ℕ → Ω → Ωs → E} {Ybar : ℕ → Ω → E} {μY : E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hbound :
      ∀ n ω,
        (∫ ωs, ‖YbarStar n ω ωs - Ybar n ω‖ ^ 2 ∂Pstar n ω) ≤
          marcinkiewiczWLLNStatisticNat u 2 n ω)
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbability μ Pstar YbarStar (fun _ => μY) :=
  chapter10_bootstrap_wlln_level_from_centered
    (μ := μ) hPstar
    (chapter10_bootstrap_wlln_centered_of_integral_norm_sq_bound
      (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
      (u := u) hPstar hu hZ hbound)
    hYbar

/-- Hansen Theorem 10.2, level WLLN from the textbook second-moment bound.

This packages the centered second-moment/Marcinkiewicz proof with the
ordinary-sample WLLN for `Ybar`, giving the textbook conclusion
`Ybar* ->p* μY`. -/
theorem chapter10_bootstrap_wlln_level_of_second_moment_bound
    [SeminormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ℕ → Ω → Ωs → E} {Ybar : ℕ → Ω → E} {μY : E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hle :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapTailProb Pstar
          (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0)
          η n ω ≤ bootstrapWLLNSecondMomentBound u η n ω)
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbability μ Pstar YbarStar (fun _ => μY) :=
  chapter10_bootstrap_wlln_level_from_centered
    (μ := μ) hPstar
    (chapter10_bootstrap_wlln_centered_of_second_moment_bound
      (μ := μ) (u := u) hu hle)
    hYbar

end BootstrapWLLNSecondMoment

section IndexedBootstrapWLLN

variable {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]

/-- Conditional bootstrap tail probability when the bootstrap sample space may
depend on the sample size. -/
noncomputable def bootstrapTailProbIndexed [PseudoMetricSpace E]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → E) (Z : Ω → E)
    (η : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((Pstar n ω) {ωs | η ≤ dist (Zstar n ω ωs) (Z ω)}).toReal

/-- Indexed-space version of Hansen Definition 10.1.

This is useful for the ordinary finite nonparametric bootstrap, where the
resampling space at sample size `n` is naturally `Fin n -> Fin n`. -/
def TendstoInBootstrapProbabilityIndexed [PseudoMetricSpace E]
    (μ : Measure Ω) (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → E) (Z : Ω → E) : Prop :=
  ∀ η : ℝ, 0 < η →
    TendstoInMeasure μ
      (fun n ω => bootstrapTailProbIndexed Pstar Zstar Z η n ω)
      atTop (fun _ => 0)

/-- Indexed-space bootstrap convergence from a conditional tail-probability
bound. -/
theorem tendstoInBootstrapProbabilityIndexed_of_tail_bound
    [PseudoMetricSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E} {Z : Ω → E}
    {bound : ℝ → ℕ → Ω → ℝ}
    (hbound :
      ∀ η : ℝ, 0 < η →
        TendstoInMeasure μ (fun n ω => bound η n ω) atTop (fun _ => 0))
    (hle :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapTailProbIndexed Pstar Zstar Z η n ω ≤ bound η n ω) :
    TendstoInBootstrapProbabilityIndexed μ Pstar Zstar Z := by
  intro η hη
  exact tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω => bootstrapTailProbIndexed Pstar Zstar Z η n ω)
    (g := fun n ω => bound η n ω)
    (fun _ _ => ENNReal.toReal_nonneg)
    (hle η hη)
    (hbound η hη)

/-- Indexed conditional Chebyshev inequality for centered scalar bootstrap
statistics.

This is the sample-size-dependent bootstrap-space version of
`bootstrapTailProb_centered_real_le_variance_div_sq`. -/
theorem bootstrapTailProbIndexed_centered_real_le_variance_div_sq
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hmean : ∀ n ω, (Pstar n ω)[Zstar n ω] = 0)
    {η : ℝ} (hη : 0 < η) (n : ℕ) (ω : Ω) :
    bootstrapTailProbIndexed Pstar Zstar (fun _ => 0) η n ω ≤
      Var[Zstar n ω; Pstar n ω] / η ^ 2 := by
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  have hcheb :=
    ProbabilityTheory.meas_ge_le_variance_div_sq
      (μ := Pstar n ω) (X := Zstar n ω) (hZ n ω) hη
  have hset :
      {ωs : Ωboot n | η ≤ dist (Zstar n ω ωs) ((fun _ : Ω => (0 : ℝ)) ω)} =
        {ωs : Ωboot n | η ≤ |Zstar n ω ωs - (Pstar n ω)[Zstar n ω]|} := by
    ext ωs
    simp [hmean n ω]
  have hmeasure :
      (Pstar n ω)
          {ωs : Ωboot n |
            η ≤ dist (Zstar n ω ωs) ((fun _ : Ω => (0 : ℝ)) ω)} ≤
        ENNReal.ofReal (Var[Zstar n ω; Pstar n ω] / η ^ 2) := by
    rw [hset]
    exact hcheb
  have hnonneg :
      0 ≤ Var[Zstar n ω; Pstar n ω] / η ^ 2 :=
    div_nonneg (ProbabilityTheory.variance_nonneg (Zstar n ω) (Pstar n ω))
      (sq_nonneg η)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  simpa [bootstrapTailProbIndexed, ENNReal.toReal_ofReal hnonneg] using hreal

/-- Indexed version of the bootstrap `L²` seminorm tail bound. -/
noncomputable def bootstrapL2ENNTailBoundIndexed
    [NormedAddCommGroup E]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → E)
    (η : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((ENNReal.ofReal η)⁻¹ ^ (2 : ℝ) *
    eLpNorm (Zstar n ω) 2 (Pstar n ω) ^ (2 : ℝ)).toReal

/-- Indexed conditional Markov inequality for vector-valued bootstrap
statistics. -/
theorem bootstrapTailProbIndexed_zero_le_l2_eLpNorm_bound
    [NormedAddCommGroup E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {η : ℝ} (hη : 0 < η) (n : ℕ) (ω : Ω) :
    bootstrapTailProbIndexed Pstar Zstar (fun _ => 0) η n ω ≤
      bootstrapL2ENNTailBoundIndexed Pstar Zstar η n ω := by
  have htail :
      (Pstar n ω)
          {ωs : Ωboot n | ENNReal.ofReal η ≤ ‖Zstar n ω ωs‖ₑ} ≤
        (ENNReal.ofReal η)⁻¹ ^ (2 : ℝ) *
          eLpNorm (Zstar n ω) 2 (Pstar n ω) ^ (2 : ℝ) := by
    simpa using
      (MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm
        (μ := Pstar n ω) (p := (2 : ℝ≥0∞)) (f := Zstar n ω)
        (by norm_num) (by simp) (hZ n ω).1
        (ε := ENNReal.ofReal η) (by simp [hη])
        (by intro htop; exact (ENNReal.ofReal_ne_top htop).elim))
  have hset :
      {ωs : Ωboot n | η ≤ dist (Zstar n ω ωs) ((fun _ : Ω => (0 : E)) ω)} =
        {ωs : Ωboot n | ENNReal.ofReal η ≤ ‖Zstar n ω ωs‖ₑ} := by
    ext ωs
    simp only [Set.mem_setOf_eq]
    rw [dist_eq_norm, sub_zero, ← ofReal_norm_eq_enorm]
    exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).symm
  have hmeasure :
      (Pstar n ω)
          {ωs : Ωboot n | η ≤ dist (Zstar n ω ωs) ((fun _ : Ω => (0 : E)) ω)} ≤
        (ENNReal.ofReal η)⁻¹ ^ (2 : ℝ) *
          eLpNorm (Zstar n ω) 2 (Pstar n ω) ^ (2 : ℝ) := by
    rw [hset]
    exact htail
  have hrhs_ne_top :
      (ENNReal.ofReal η)⁻¹ ^ (2 : ℝ) *
          eLpNorm (Zstar n ω) 2 (Pstar n ω) ^ (2 : ℝ) ≠ ∞ := by
    have hnorm_ne_top : eLpNorm (Zstar n ω) 2 (Pstar n ω) ≠ ∞ :=
      (hZ n ω).eLpNorm_ne_top
    finiteness
  have hreal := ENNReal.toReal_mono hrhs_ne_top hmeasure
  simpa [bootstrapTailProbIndexed, bootstrapL2ENNTailBoundIndexed] using hreal

/-- Indexed Hansen Theorem 10.2, centered WLLN from a conditional tail bound.

This is the sample-size-dependent bootstrap-space version of
`chapter10_bootstrap_wlln_centered_of_tail_bound`. -/
theorem chapter10_indexed_bootstrap_wlln_centered_of_tail_bound
    [SeminormedAddCommGroup E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {YbarStar : ∀ n, Ω → Ωboot n → E} {Ybar : ℕ → Ω → E}
    {bound : ℝ → ℕ → Ω → ℝ}
    (hbound :
      ∀ η : ℝ, 0 < η →
        TendstoInMeasure μ (fun n ω => bound η n ω) atTop (fun _ => 0))
    (hle :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapTailProbIndexed Pstar
          (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0)
          η n ω ≤ bound η n ω) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) :=
  tendstoInBootstrapProbabilityIndexed_of_tail_bound hbound hle

/-- Indexed Hansen Theorem 10.2, centered WLLN from Hansen's textbook
second-moment bound.

This is the sample-size-dependent bootstrap-space version of
`chapter10_bootstrap_wlln_centered_of_second_moment_bound`. -/
theorem chapter10_indexed_bootstrap_wlln_centered_of_second_moment_bound
    [SeminormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {YbarStar : ∀ n, Ω → Ωboot n → E} {Ybar : ℕ → Ω → E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hle :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapTailProbIndexed Pstar
          (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0)
          η n ω ≤ bootstrapWLLNSecondMomentBound u η n ω) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) :=
  chapter10_indexed_bootstrap_wlln_centered_of_tail_bound
    (bound := fun η n ω => bootstrapWLLNSecondMomentBound u η n ω)
    (fun η hη => bootstrapWLLNSecondMomentBound_tendsto_zero (μ := μ) (η := η) hu hη)
    hle

/-- Indexed Hansen Theorem 10.2, vector centered WLLN from a bootstrap `L²`
seminorm bound.

This is the sample-size-dependent bootstrap-space version of
`chapter10_bootstrap_wlln_centered_of_l2_eLpNorm_bound`. -/
theorem chapter10_indexed_bootstrap_wlln_centered_of_l2_eLpNorm_bound
    [NormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {YbarStar : ∀ n, Ω → Ωboot n → E} {Ybar : ℕ → Ω → E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hbound :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapL2ENNTailBoundIndexed Pstar
          (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) η n ω ≤
            bootstrapWLLNSecondMomentBound u η n ω) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) := by
  refine chapter10_indexed_bootstrap_wlln_centered_of_second_moment_bound
    (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
    (u := u) hu ?_
  intro η hη n ω
  exact (bootstrapTailProbIndexed_zero_le_l2_eLpNorm_bound
    (Pstar := Pstar)
    (Zstar := fun n ω ωs => YbarStar n ω ωs - Ybar n ω)
    hZ hη n ω).trans (hbound η hη n ω)

/-- Indexed Hansen Theorem 10.2, scalar centered WLLN from a conditional
variance bound.

This is the sample-size-dependent bootstrap-space version of
`chapter10_bootstrap_wlln_centered_real_of_conditional_variance_bound`. -/
theorem chapter10_indexed_bootstrap_wlln_centered_real_of_conditional_variance_bound
    [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ∀ n, Ω → Ωboot n → ℝ} {Ybar : ℕ → Ω → ℝ}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hmean :
      ∀ n ω, (Pstar n ω)[fun ωs => YbarStar n ω ωs - Ybar n ω] = 0)
    (hvar :
      ∀ n ω,
        Var[fun ωs => YbarStar n ω ωs - Ybar n ω; Pstar n ω] ≤
          marcinkiewiczWLLNStatisticNat u 2 n ω) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) := by
  refine chapter10_indexed_bootstrap_wlln_centered_of_second_moment_bound
    (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
    (u := u) hu ?_
  intro η hη n ω
  calc
    bootstrapTailProbIndexed Pstar
        (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) η n ω
        ≤ Var[fun ωs => YbarStar n ω ωs - Ybar n ω; Pstar n ω] / η ^ 2 :=
          bootstrapTailProbIndexed_centered_real_le_variance_div_sq
            (Pstar := Pstar)
            (Zstar := fun n ω ωs => YbarStar n ω ωs - Ybar n ω)
            hPstar hZ hmean hη n ω
    _ ≤ marcinkiewiczWLLNStatisticNat u 2 n ω / η ^ 2 :=
          div_le_div_of_nonneg_right (hvar n ω) (sq_nonneg η)
    _ = bootstrapWLLNSecondMomentBound u η n ω := by
          rw [bootstrapWLLNSecondMomentBound]
          field_simp [hη.ne']

/-- Indexed-space version of Hansen Theorem 10.1.

If `Zₙ ->p Z` under the original-sample law, then the same statistic, viewed as
constant under each sample-size-dependent bootstrap law, converges to `Z` in
indexed bootstrap probability. -/
theorem tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure
    [PseudoMetricSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zseq : ℕ → Ω → E} {Z : Ω → E}
    (hZ : TendstoInMeasure μ Zseq atTop Z) :
    TendstoInBootstrapProbabilityIndexed μ Pstar (fun n ω _ => Zseq n ω) Z := by
  classical
  intro η hη
  let A : ℕ → Set Ω := fun n => {ω | η ≤ dist (Zseq n ω) (Z ω)}
  have hA : Tendsto (fun n => μ (A n)) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_dist.mp hZ) η hη
  have hindicator :
      TendstoInMeasure μ (fun n ω => if ω ∈ A n then (1 : ℝ) else 0)
        atTop (fun _ => 0) :=
    tendstoInMeasure_indicator_zero_of_tendsto_measure (μ := μ) hA
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hindicator
  refine Filter.Eventually.of_forall ?_
  intro ω
  by_cases hω : ω ∈ A n
  · have hset :
        {ωs : Ωboot n | η ≤ dist (Zseq n ω) (Z ω)} = Set.univ := by
      have htail : η ≤ dist (Zseq n ω) (Z ω) := by simpa [A] using hω
      ext ωs
      simp [htail]
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    simp [bootstrapTailProbIndexed, A, hω, hset]
  · have hset :
        {ωs : Ωboot n | η ≤ dist (Zseq n ω) (Z ω)} = ∅ := by
      have htail : ¬ η ≤ dist (Zseq n ω) (Z ω) := by simpa [A] using hω
      ext ωs
      simp [htail]
    simp [bootstrapTailProbIndexed, A, hω, hset]

/-- Indexed Hansen Theorem 10.1, chapter-facing name.

Ordinary convergence in probability implies indexed bootstrap convergence in
probability when the sequence is non-random under the bootstrap resampling law
and the bootstrap sample space may vary with `n`. -/
theorem chapter10_indexed_bootstrap_convergence_in_probability_of_convergence_in_probability
    [PseudoMetricSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zseq : ℕ → Ω → E} {Z : Ω → E}
    (hZ : TendstoInMeasure μ Zseq atTop Z) :
    TendstoInBootstrapProbabilityIndexed μ Pstar (fun n ω _ => Zseq n ω) Z :=
  tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure hPstar hZ

namespace TendstoInBootstrapProbabilityIndexed

/-- Indexed bootstrap convergence is invariant under pointwise equality of the
bootstrap statistic and limit target. -/
theorem congr [PseudoMetricSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E} {Z Z' : Ω → E}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapProbabilityIndexed μ Pstar Zstar Z) :
    TendstoInBootstrapProbabilityIndexed μ Pstar Zstar' Z' := by
  intro η hη
  simpa [bootstrapTailProbIndexed, hstar, hlim] using hZ η hη

/-- Indexed-space Hansen Theorem 10.3, bootstrap continuous-mapping theorem in
probability.

If `Zₙ* ->p* c` on sample-size-dependent bootstrap spaces and `g` is
continuous at `c`, then `g(Zₙ*) ->p* g(c)`. -/
theorem continuousAt_const_comp [PseudoMetricSpace E] [PseudoMetricSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zstar : ∀ n, Ω → Ωboot n → E} {c : E} {g : E → F}
    (hZ : TendstoInBootstrapProbabilityIndexed μ Pstar Zstar (fun _ => c))
    (hg : ContinuousAt g c) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) (fun _ => g c) := by
  intro η hη
  obtain ⟨δ, hδ, hδ_eventually⟩ := (Metric.continuousAt_iff.mp hg) η hη
  refine tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω =>
      bootstrapTailProbIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) (fun _ => g c) η n ω)
    (g := fun n ω => bootstrapTailProbIndexed Pstar Zstar (fun _ => c) δ n ω)
    ?_ ?_ (hZ δ hδ)
  · intro n ω
    exact ENNReal.toReal_nonneg
  · intro n ω
    refine ENNReal.toReal_mono ?_ (measure_mono ?_)
    · haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      exact measure_ne_top (Pstar n ω)
        {ωs | δ ≤ dist (Zstar n ω ωs) c}
    · intro ωs hωs
      by_contra hnot
      have hlt : dist (Zstar n ω ωs) c < δ := lt_of_not_ge hnot
      exact (not_lt_of_ge hωs) (hδ_eventually hlt)

/-- Indexed bootstrap convergence in probability is preserved by globally
Lipschitz maps. -/
theorem lipschitz_comp [PseudoMetricSpace E] [PseudoMetricSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zstar : ∀ n, Ω → Ωboot n → E} {Z : Ω → E} {g : E → F} {C : ℝ}
    (hC : 0 < C)
    (hg : ∀ x y, dist (g x) (g y) ≤ C * dist x y)
    (hZ : TendstoInBootstrapProbabilityIndexed μ Pstar Zstar Z) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) (fun ω => g (Z ω)) := by
  intro η hη
  have hδ : 0 < η / C := div_pos hη hC
  refine tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω =>
      bootstrapTailProbIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) (fun ω => g (Z ω))
        η n ω)
    (g := fun n ω => bootstrapTailProbIndexed Pstar Zstar Z (η / C) n ω)
    ?_ ?_ (hZ (η / C) hδ)
  · intro n ω
    exact ENNReal.toReal_nonneg
  · intro n ω
    refine ENNReal.toReal_mono ?_ (measure_mono ?_)
    · haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      exact measure_ne_top (Pstar n ω)
        {ωs | η / C ≤ dist (Zstar n ω ωs) (Z ω)}
    · intro ωs hωs
      by_contra hnot
      have hlt : dist (Zstar n ω ωs) (Z ω) < η / C := lt_of_not_ge hnot
      have hmap_lt : dist (g (Zstar n ω ωs)) (g (Z ω)) < η := by
        calc
          dist (g (Zstar n ω ωs)) (g (Z ω))
              ≤ C * dist (Zstar n ω ωs) (Z ω) := hg _ _
          _ < C * (η / C) := mul_lt_mul_of_pos_left hlt hC
          _ = η := by
            field_simp [ne_of_gt hC]
      exact (not_lt_of_ge hωs) hmap_lt

/-- Indexed bootstrap convergence in probability is closed under forming
product statistics. -/
theorem prodMk [PseudoMetricSpace E] [PseudoMetricSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Xstar : ∀ n, Ω → Ωboot n → E} {X : Ω → E}
    {Ystar : ∀ n, Ω → Ωboot n → F} {Y : Ω → F}
    (hX : TendstoInBootstrapProbabilityIndexed μ Pstar Xstar X)
    (hY : TendstoInBootstrapProbabilityIndexed μ Pstar Ystar Y) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
      (fun ω => (X ω, Y ω)) := by
  intro η hη
  refine tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω =>
      bootstrapTailProbIndexed Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (fun ω => (X ω, Y ω)) η n ω)
    (g := fun n ω =>
      bootstrapTailProbIndexed Pstar Xstar X η n ω +
        bootstrapTailProbIndexed Pstar Ystar Y η n ω)
    ?_ ?_
    (tendstoInMeasure_add_nonneg_zero
      (μ := μ)
      (f := fun n ω => bootstrapTailProbIndexed Pstar Xstar X η n ω)
      (g := fun n ω => bootstrapTailProbIndexed Pstar Ystar Y η n ω)
      (fun _ _ => ENNReal.toReal_nonneg)
      (fun _ _ => ENNReal.toReal_nonneg)
      (hX η hη) (hY η hη))
  · intro n ω
    exact ENNReal.toReal_nonneg
  · intro n ω
    let C : Set (Ωboot n) :=
      {ωs | η ≤ dist (Xstar n ω ωs, Ystar n ω ωs) (X ω, Y ω)}
    let A : Set (Ωboot n) := {ωs | η ≤ dist (Xstar n ω ωs) (X ω)}
    let B : Set (Ωboot n) := {ωs | η ≤ dist (Ystar n ω ωs) (Y ω)}
    have hsubset : C ⊆ A ∪ B := by
      intro ωs hωs
      rcases le_max_iff.mp (by simpa [C, A, B, Prod.dist_eq] using hωs) with h | h
      · exact Or.inl h
      · exact Or.inr h
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    calc
      bootstrapTailProbIndexed Pstar
          (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
          (fun ω => (X ω, Y ω)) η n ω
          = ((Pstar n ω) C).toReal := rfl
      _ ≤ ((Pstar n ω) (A ∪ B)).toReal :=
          ENNReal.toReal_mono (measure_ne_top (Pstar n ω) (A ∪ B))
            (measure_mono hsubset)
      _ ≤ ((Pstar n ω) A + (Pstar n ω) B).toReal :=
          ENNReal.toReal_mono
            (ENNReal.add_ne_top.2
              ⟨measure_ne_top (Pstar n ω) A, measure_ne_top (Pstar n ω) B⟩)
            (measure_union_le A B)
      _ ≤ ((Pstar n ω) A).toReal + ((Pstar n ω) B).toReal :=
          ENNReal.toReal_add_le
      _ = bootstrapTailProbIndexed Pstar Xstar X η n ω +
          bootstrapTailProbIndexed Pstar Ystar Y η n ω := rfl

/-- Indexed bootstrap convergence in probability is closed under addition. -/
theorem add [SeminormedAddCommGroup E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Xstar Ystar : ∀ n, Ω → Ωboot n → E} {X Y : Ω → E}
    (hX : TendstoInBootstrapProbabilityIndexed μ Pstar Xstar X)
    (hY : TendstoInBootstrapProbabilityIndexed μ Pstar Ystar Y) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => Xstar n ω ωs + Ystar n ω ωs)
      (fun ω => X ω + Y ω) := by
  intro η hη
  have hhalf : 0 < η / 2 := by linarith
  refine tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω =>
      bootstrapTailProbIndexed Pstar
        (fun n ω ωs => Xstar n ω ωs + Ystar n ω ωs)
        (fun ω => X ω + Y ω) η n ω)
    (g := fun n ω =>
      bootstrapTailProbIndexed Pstar Xstar X (η / 2) n ω +
        bootstrapTailProbIndexed Pstar Ystar Y (η / 2) n ω)
    ?_ ?_
    (tendstoInMeasure_add_nonneg_zero
      (μ := μ)
      (f := fun n ω => bootstrapTailProbIndexed Pstar Xstar X (η / 2) n ω)
      (g := fun n ω => bootstrapTailProbIndexed Pstar Ystar Y (η / 2) n ω)
      (fun _ _ => ENNReal.toReal_nonneg)
      (fun _ _ => ENNReal.toReal_nonneg)
      (hX (η / 2) hhalf) (hY (η / 2) hhalf))
  · intro n ω
    exact ENNReal.toReal_nonneg
  · intro n ω
    let C : Set (Ωboot n) :=
      {ωs | η ≤ dist (Xstar n ω ωs + Ystar n ω ωs) (X ω + Y ω)}
    let A : Set (Ωboot n) := {ωs | η / 2 ≤ dist (Xstar n ω ωs) (X ω)}
    let B : Set (Ωboot n) := {ωs | η / 2 ≤ dist (Ystar n ω ωs) (Y ω)}
    have hsubset : C ⊆ A ∪ B := by
      intro ωs hωs
      by_cases hA : η / 2 ≤ dist (Xstar n ω ωs) (X ω)
      · exact Or.inl hA
      · right
        by_contra hB
        have hX_lt : dist (Xstar n ω ωs) (X ω) < η / 2 := lt_of_not_ge hA
        have hY_lt : dist (Ystar n ω ωs) (Y ω) < η / 2 := lt_of_not_ge hB
        have hdist_le :
            dist (Xstar n ω ωs + Ystar n ω ωs) (X ω + Y ω) ≤
              dist (Xstar n ω ωs) (X ω) + dist (Ystar n ω ωs) (Y ω) :=
          dist_add_add_le _ _ _ _
        have hdist_lt :
            dist (Xstar n ω ωs + Ystar n ω ωs) (X ω + Y ω) < η := by
          linarith
        exact (not_lt_of_ge hωs) hdist_lt
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    calc
      bootstrapTailProbIndexed Pstar
          (fun n ω ωs => Xstar n ω ωs + Ystar n ω ωs)
          (fun ω => X ω + Y ω) η n ω
          = ((Pstar n ω) C).toReal := rfl
      _ ≤ ((Pstar n ω) (A ∪ B)).toReal :=
          ENNReal.toReal_mono (measure_ne_top (Pstar n ω) (A ∪ B))
            (measure_mono hsubset)
      _ ≤ ((Pstar n ω) A + (Pstar n ω) B).toReal :=
          ENNReal.toReal_mono
            (ENNReal.add_ne_top.2
              ⟨measure_ne_top (Pstar n ω) A, measure_ne_top (Pstar n ω) B⟩)
            (measure_union_le A B)
      _ ≤ ((Pstar n ω) A).toReal + ((Pstar n ω) B).toReal :=
          ENNReal.toReal_add_le
      _ = bootstrapTailProbIndexed Pstar Xstar X (η / 2) n ω +
          bootstrapTailProbIndexed Pstar Ystar Y (η / 2) n ω := rfl

/-- Indexed bootstrap convergence in probability is closed under negation. -/
theorem neg [SeminormedAddCommGroup E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E} {Z : Ω → E}
    (hZ : TendstoInBootstrapProbabilityIndexed μ Pstar Zstar Z) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => -Zstar n ω ωs) (fun ω => -Z ω) := by
  intro η hη
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl (hZ η hη)
  refine ae_of_all μ fun ω => ?_
  simp [bootstrapTailProbIndexed]

/-- Indexed bootstrap convergence in probability is closed under subtraction. -/
theorem sub [SeminormedAddCommGroup E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Xstar Ystar : ∀ n, Ω → Ωboot n → E} {X Y : Ω → E}
    (hX : TendstoInBootstrapProbabilityIndexed μ Pstar Xstar X)
    (hY : TendstoInBootstrapProbabilityIndexed μ Pstar Ystar Y) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => Xstar n ω ωs - Ystar n ω ωs)
      (fun ω => X ω - Y ω) := by
  have hsum := hX.add hPstar hY.neg
  exact hsum.congr
    (fun n ω ωs => by simp [sub_eq_add_neg])
    (fun ω => by simp [sub_eq_add_neg])

/-- Indexed bootstrap convergence in probability is closed under scalar
multiplication by a fixed real constant. -/
theorem smul [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (c : ℝ)
    {Zstar : ∀ n, Ω → Ωboot n → E} {Z : Ω → E}
    (hZ : TendstoInBootstrapProbabilityIndexed μ Pstar Zstar Z) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => c • Zstar n ω ωs) (fun ω => c • Z ω) := by
  have hC : 0 < |c| + 1 := by
    nlinarith [abs_nonneg c]
  refine hZ.lipschitz_comp hPstar hC ?_
  intro x y
  calc
    dist (c • x) (c • y) ≤ |c| * dist x y := by
      simpa [Real.norm_eq_abs] using dist_smul_le c x y
    _ ≤ (|c| + 1) * dist x y :=
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg c]) dist_nonneg

end TendstoInBootstrapProbabilityIndexed

/-- Indexed-space Hansen Theorem 10.3, chapter-facing name.

If `Zₙ* ->p* c` on sample-size-dependent bootstrap spaces and `g` is
continuous at `c`, then `g(Zₙ*) ->p* g(c)`. -/
theorem chapter10_indexed_bootstrap_continuous_mapping_probability
    [PseudoMetricSpace E] [PseudoMetricSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zstar : ∀ n, Ω → Ωboot n → E} {c : E} {g : E → F}
    (hZ : TendstoInBootstrapProbabilityIndexed μ Pstar Zstar (fun _ => c))
    (hg : ContinuousAt g c) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) (fun _ => g c) :=
  hZ.continuousAt_const_comp hPstar hg

/-- Indexed-space globally Lipschitz mapping bridge for bootstrap convergence
in probability. -/
theorem chapter10_indexed_bootstrap_lipschitz_mapping_probability
    [PseudoMetricSpace E] [PseudoMetricSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zstar : ∀ n, Ω → Ωboot n → E} {Z : Ω → E} {g : E → F} {C : ℝ}
    (hC : 0 < C)
    (hg : ∀ x y, dist (g x) (g y) ≤ C * dist x y)
    (hZ : TendstoInBootstrapProbabilityIndexed μ Pstar Zstar Z) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) (fun ω => g (Z ω)) :=
  hZ.lipschitz_comp hPstar hC hg

/-- Indexed-space bootstrap-probability scalar-multiplication bridge. -/
theorem chapter10_indexed_bootstrap_smul_probability
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (c : ℝ)
    {Zstar : ∀ n, Ω → Ωboot n → E} {Z : Ω → E}
    (hZ : TendstoInBootstrapProbabilityIndexed μ Pstar Zstar Z) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => c • Zstar n ω ωs) (fun ω => c • Z ω) :=
  hZ.smul hPstar c

/-- Indexed-space conditional Markov inequality, stated with a concrete
second moment. -/
theorem bootstrapTailProbIndexed_zero_le_integral_norm_sq_div
    [NormedAddCommGroup E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {η : ℝ} (hη : 0 < η) (n : ℕ) (ω : Ω) :
    bootstrapTailProbIndexed Pstar Zstar (fun _ => 0) η n ω ≤
      (∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω) / η ^ 2 := by
  let Pconst : ℕ → Ω → Measure (Ωboot n) := fun _ _ => Pstar n ω
  let Zconst : ℕ → Ω → Ωboot n → E := fun _ _ ωs => Zstar n ω ωs
  have hPconst : ∀ m ω', IsProbabilityMeasure (Pconst m ω') := fun _ _ => hPstar n ω
  have hZconst : ∀ m ω', MemLp (Zconst m ω') 2 (Pconst m ω') := fun _ _ => hZ n ω
  have htail :=
    bootstrapTailProb_zero_le_integral_norm_sq_div
      (Pstar := Pconst) (Zstar := Zconst) hPconst hZconst hη n ω
  simpa [bootstrapTailProbIndexed, bootstrapTailProb, Pconst, Zconst] using htail

/-- Shifted version of Hansen's Theorem 10.2 second-moment bound.

The ordinary `Fin (n+1)` empirical bootstrap avoids the empty sample-size-zero
case while preserving the same `atTop` asymptotics. -/
theorem bootstrapWLLNSecondMomentBound_succ_tendsto_zero
    [IsFiniteMeasure μ] {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ) {η : ℝ} (hη : 0 < η) :
    TendstoInMeasure μ
      (fun n ω => bootstrapWLLNSecondMomentBound u η (n + 1) ω)
      atTop (fun _ => 0) := by
  have h :=
    bootstrapWLLNSecondMomentBound_tendsto_zero
      (μ := μ) (u := u) (η := η) hu hη
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  simpa using (h ε hε).comp (tendsto_add_atTop_nat 1)

/-- Sample-size-indexed finite-resample norm bound in Hansen's Theorem 10.2
scale.

For sample size `n+1`, the expected squared norm of the centered ordinary
nonparametric-bootstrap mean is bounded by
`(n+1)^{-2} sum_{i<n+1} ||Y_i||^2`, the Marcinkiewicz statistic used in the
asymptotic Theorem 10.2 proof. -/
theorem integral_norm_sq_finSucc_resampleMean_sub_empiricalMean_le_marcinkiewicz
    {k : Type*} [Fintype k]
    (Y : ℕ → Ω → EuclideanSpace ℝ k) (n : ℕ) (ω : Ω) :
    ∫ ωs : Fin (n + 1) → Fin (n + 1),
        ‖empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω)‖ ^ 2
        ∂(ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) ≤
      marcinkiewiczWLLNStatisticNat (fun i ω => ‖Y i ω‖) 2 (n + 1) ω := by
  classical
  have hfinite :=
    integral_norm_sq_resampleMean_sub_empiricalMean_le_secondMoment
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω)
  have hsum :
      (∑ i : Fin (n + 1), ∑ a, Y i.val ω a * Y i.val ω a) =
        ∑ i ∈ Finset.range (n + 1), ‖Y i ω‖ * ‖Y i ω‖ := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl ?_
    intro i _
    simpa [pow_two] using (EuclideanSpace.real_norm_sq_eq (Y i.val ω)).symm
  have hscale :
      (Fintype.card (Fin (n + 1)) : ℝ)⁻¹ *
          (((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal •
            ∑ i : Fin (n + 1), ∑ a, Y i.val ω a ^ 2) =
        marcinkiewiczWLLNStatisticNat (fun i ω => ‖Y i ω‖) 2 (n + 1) ω := by
    have hcard_real : (Fintype.card (Fin (n + 1)) : ℝ) = (n + 1 : ℝ) := by
      simp [Fintype.card_fin]
    have hcard_enn_inv :
        (((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal) =
          ((n + 1 : ℝ)⁻¹) := by
      have htoReal :
          ((Fintype.card (Fin (n + 1)) : ℝ≥0∞).toReal) = (n + 1 : ℝ) := by
        rw [Fintype.card_fin]
        simpa using ENNReal.toReal_natCast (n + 1)
      rw [ENNReal.toReal_inv, htoReal]
    rw [show (∑ i : Fin (n + 1), ∑ a, Y i.val ω a ^ 2) =
        ∑ i : Fin (n + 1), ∑ a, Y i.val ω a * Y i.val ω a by
          simp [pow_two], hsum]
    rw [hcard_real, hcard_enn_inv]
    simp [marcinkiewiczWLLNStatisticNat, pow_two, mul_assoc]
  exact hfinite.trans_eq hscale

/-- Scalar sample-size-indexed finite-resample second-moment bound in Hansen's
Theorem 10.2 scale.

For sample size `n+1`, the expected squared centered ordinary
nonparametric-bootstrap mean is bounded by Hansen's
`(n+1)^{-2} sum_{i<n+1} |Y_i|^2` Marcinkiewicz statistic. -/
theorem integral_sq_finSucc_resampleMean_sub_empiricalMean_le_marcinkiewicz
    (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∫ ωs : Fin (n + 1) → Fin (n + 1),
        (empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω)) ^ 2
        ∂(ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) ≤
      marcinkiewiczWLLNStatisticNat Y 2 (n + 1) ω := by
  classical
  have hfinite :=
    integral_sq_resampleMean_sub_empiricalMean_le_inv_card_mul_secondMoment
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω)
  have hsum :
      (∑ i : Fin (n + 1), (Y i.val ω) ^ 2) =
        ∑ i ∈ Finset.range (n + 1), |Y i ω| ^ 2 := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    simp [sq_abs]
  have hscale :
      (Fintype.card (Fin (n + 1)) : ℝ)⁻¹ *
          (((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal •
            ∑ i : Fin (n + 1), (Y i.val ω) ^ 2) =
        marcinkiewiczWLLNStatisticNat Y 2 (n + 1) ω := by
    have hcard_real : (Fintype.card (Fin (n + 1)) : ℝ) = (n + 1 : ℝ) := by
      simp [Fintype.card_fin]
    have hcard_enn_inv :
        (((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal) =
          ((n + 1 : ℝ)⁻¹) := by
      have htoReal :
          ((Fintype.card (Fin (n + 1)) : ℝ≥0∞).toReal) = (n + 1 : ℝ) := by
        rw [Fintype.card_fin]
        simpa using ENNReal.toReal_natCast (n + 1)
      rw [ENNReal.toReal_inv, htoReal]
    rw [hsum, hcard_real, hcard_enn_inv]
    simp [marcinkiewiczWLLNStatisticNat, pow_two, mul_assoc]
  exact hfinite.trans_eq hscale

/-- Scalar `Fin (n+1)` CLT-scale second-moment identity for the ordinary
nonparametric bootstrap.

For the sample-size-indexed resampling space used later in the chapter,
`sqrt (n+1) (Ybar* - Ybar)` has raw second moment equal to the finite empirical
one-draw variance. -/
theorem integral_sq_normalized_finSucc_resampleMean_sub_empiricalMean_eq_variance
    (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∫ ωs : Fin (n + 1) → Fin (n + 1),
        (Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω))) ^ 2
        ∂(ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) =
      Var[fun i : Fin (n + 1) => Y i.val ω;
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1)))] := by
  simpa [Fintype.card_fin] using
    (integral_sq_normalized_empiricalBootstrapResampleMean_uniformOn_fun_eq_variance
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω))

/-- Scalar `Fin (n+1)` CLT-scale third conditional moment formula for the
ordinary nonparametric bootstrap.

This is the shifted sample-size-indexed face of Hansen equation (10.14) for
the ordinary empirical resampling space. -/
theorem integral_cube_normalized_finSucc_resampleMean_sub_empiricalMean_eq_formula
    (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∫ ωs : Fin (n + 1) → Fin (n + 1),
        (Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω))) ^ 3
        ∂(ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) =
      normalizedBootstrapMeanMoment3Formula (n + 1 : ℝ)
        (fun i : Fin (n + 1) => Y i.val ω) := by
  simpa [Fintype.card_fin] using
    (integral_cube_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_formula
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω))

/-- Scalar `Fin (n+1)` CLT-scale fourth conditional moment formula for the
ordinary nonparametric bootstrap.

This is the shifted sample-size-indexed face of Hansen equation (10.14) used
by the fourth-moment route to uniform square integrability in (10.17). -/
theorem integral_fourth_normalized_finSucc_resampleMean_sub_empiricalMean_eq_formula
    (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∫ ωs : Fin (n + 1) → Fin (n + 1),
        (Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω))) ^ 4
        ∂(ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) =
      normalizedBootstrapMeanMoment4Formula (n + 1 : ℝ)
        (fun i : Fin (n + 1) => Y i.val ω) := by
  simpa [Fintype.card_fin] using
    (integral_fourth_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_formula
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω))

/-- Fourth conditional moment convergence for the ordinary `Fin (n+1)`
bootstrap sample mean from Hansen's cumulant formula.

If the empirical variance converges to `σ2` and the scaled fourth cumulant is
negligible, the exact equation (10.14) formula gives
`E*[(sqrt (n+1) (Ybar* - Ybar))^4] ->p 3 σ2^2`. This is the sample-mean
fourth-moment route behind Hansen equation (10.17). -/
theorem
    integral_fourth_normalized_finSucc_resampleMean_sub_empiricalMean_tendstoInMeasure_of_cumulants
    (Y : ℕ → Ω → ℝ) {σ2 : ℝ}
    (hCumulant2 :
      TendstoInMeasure μ
        (fun n ω =>
          empiricalCumulant2 (fun i : Fin (n + 1) => Y i.val ω))
        atTop (fun _ => σ2))
    (hScaledCumulant4 :
      TendstoInMeasure μ
        (fun n ω =>
          empiricalCumulant4 (fun i : Fin (n + 1) => Y i.val ω) /
            (n + 1 : ℝ))
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        ∫ ωs : Fin (n + 1) → Fin (n + 1),
          (Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω))) ^ 4
          ∂(ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
      atTop (fun _ => 3 * σ2 ^ 2) := by
  have hCumulant2Sq :
      TendstoInMeasure μ
        (fun n ω =>
          empiricalCumulant2 (fun i : Fin (n + 1) => Y i.val ω) *
            empiricalCumulant2 (fun i : Fin (n + 1) => Y i.val ω))
        atTop (fun _ => σ2 * σ2) :=
    TendstoInMeasure.mul_limits_real hCumulant2 hCumulant2
  have hCumulant2Sq0 :
      TendstoInMeasure μ
        (fun n ω =>
          empiricalCumulant2 (fun i : Fin (n + 1) => Y i.val ω) *
            empiricalCumulant2 (fun i : Fin (n + 1) => Y i.val ω) -
              σ2 * σ2)
        atTop (fun _ => 0) :=
    TendstoInMeasure.sub_limit_zero_real hCumulant2Sq
  have hCumulant2SqScaled :
      TendstoInMeasure μ
        (fun n ω =>
          3 *
            (empiricalCumulant2 (fun i : Fin (n + 1) => Y i.val ω) *
              empiricalCumulant2 (fun i : Fin (n + 1) => Y i.val ω) -
                σ2 * σ2))
        atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real 3 hCumulant2Sq0
  have hcenterFormula :
      TendstoInMeasure μ
        (fun n ω =>
          empiricalCumulant4 (fun i : Fin (n + 1) => Y i.val ω) /
              (n + 1 : ℝ) +
            3 *
              (empiricalCumulant2 (fun i : Fin (n + 1) => Y i.val ω) *
                empiricalCumulant2 (fun i : Fin (n + 1) => Y i.val ω) -
                  σ2 * σ2))
        atTop (fun _ => 0) :=
    TendstoInMeasure.add_zero_real hScaledCumulant4 hCumulant2SqScaled
  have hformula0 :
      TendstoInMeasure μ
        (fun (n : ℕ) ω =>
          normalizedBootstrapMeanMoment4Formula (n + 1 : ℝ)
              (fun i : Fin (n + 1) => Y i.val ω) -
            3 * σ2 ^ 2)
        atTop (fun _ => 0) := by
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hcenterFormula
    exact ae_of_all μ fun ω => by
      simp [normalizedBootstrapMeanMoment4Formula, pow_two]
      ring
  have hformula :
      TendstoInMeasure μ
        (fun (n : ℕ) ω =>
          normalizedBootstrapMeanMoment4Formula (n + 1 : ℝ)
            (fun i : Fin (n + 1) => Y i.val ω))
        atTop (fun _ => 3 * σ2 ^ 2) :=
    TendstoInMeasure.of_sub_limit_zero_real hformula0
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hformula
  exact ae_of_all μ fun ω => by
    simpa [Nat.cast_add, Nat.cast_one] using
      (integral_fourth_normalized_finSucc_resampleMean_sub_empiricalMean_eq_formula
        (Y := Y) n ω).symm

/-- Scalar `Fin (n+1)` CLT-scale fifth conditional moment formula for the
ordinary nonparametric bootstrap.

This is the shifted sample-size-indexed face of Hansen equation (10.14) for
the ordinary empirical resampling space. -/
theorem integral_fifth_normalized_finSucc_resampleMean_sub_empiricalMean_eq_formula
    (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∫ ωs : Fin (n + 1) → Fin (n + 1),
        (Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω))) ^ 5
        ∂(ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) =
      normalizedBootstrapMeanMoment5Formula (n + 1 : ℝ)
        (fun i : Fin (n + 1) => Y i.val ω) := by
  simpa [Fintype.card_fin] using
    (integral_fifth_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_formula
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω))

/-- Scalar `Fin (n+1)` CLT-scale sixth conditional moment formula for the
ordinary nonparametric bootstrap.

This is the shifted sample-size-indexed face of Hansen equation (10.14) for
the ordinary empirical resampling space. -/
theorem integral_sixth_normalized_finSucc_resampleMean_sub_empiricalMean_eq_formula
    (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∫ ωs : Fin (n + 1) → Fin (n + 1),
        (Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω))) ^ 6
        ∂(ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) =
      normalizedBootstrapMeanMoment6Formula (n + 1 : ℝ)
        (fun i : Fin (n + 1) => Y i.val ω) := by
  simpa [Fintype.card_fin] using
    (integral_sixth_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_formula
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω))

/-- Scalar `Fin (n+1)` characteristic-function identity for the ordinary
nonparametric-bootstrap CLT statistic.

The conditional characteristic function of
`sqrt (n+1) (Ybar* - Ybar)` is the centered empirical one-draw characteristic
function evaluated at `(sqrt (n+1))⁻¹ t`, raised to `n+1`. -/
theorem charFun_normalized_finSucc_resampleMean_sub_empiricalMean_eq_pow
    (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (u : ℝ) :
    (charFun
        (((ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))).map
          (fun ωs =>
            Real.sqrt (n + 1 : ℝ) *
              (empiricalBootstrapResampleMean
                  (fun i : Fin (n + 1) => Y i.val ω)
                  (fun ωs t => ωs t) ωs -
                empiricalMean (fun i : Fin (n + 1) => Y i.val ω))))) u =
      (charFun
        ((ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1))).map
          (fun i : Fin (n + 1) => Y i.val ω -
            empiricalMean (fun j : Fin (n + 1) => Y j.val ω)))
        ((Real.sqrt (n + 1 : ℝ))⁻¹ * u)) ^ Nat.succ n) := by
  simpa [Fintype.card_fin] using
    (charFun_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_pow
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω) u)

/-- Pathwise characteristic-function convergence for the normalized ordinary
`Fin (n+1)` bootstrap sample mean from the diagonal empirical one-draw bridge.

This composes the finite normalized characteristic-function identity with
`centeredEmpiricalCharFunFinSucc_inv_sqrt_succ_pow_tendsto_of_variance_tendsto`.
It is the pathwise scalar step used before feeding characteristic-function
convergence into the Lévy route for Hansen Theorem 10.4. -/
theorem
    charFun_normalized_finSucc_resampleMean_sub_empiricalMean_tendsto_of_variance_tendsto
    (Y : ℕ → Ω → ℝ) (ω : Ω) {σ2 : ℝ}
    (hvar :
      Tendsto
        (fun n : ℕ => empiricalVarianceFinSucc (fun i => Y i ω) n)
        atTop (𝓝 σ2))
    (u : ℝ)
    (hrem :
      ((fun n : ℕ =>
          centeredEmpiricalCharFunFinSucc (fun i => Y i ω) n
              ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) -
            (1 +
              scalarGaussianCharFunExponent u
                  (empiricalVarianceFinSucc (fun i => Y i ω) n) *
                complexInvNatSucc n)) =o[atTop]
        (fun n : ℕ => complexInvNatSucc n))) :
    Tendsto
      (fun n : ℕ =>
        charFun
          (((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))).map
            (fun ωs =>
              Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))))
          u)
      atTop
      (𝓝 (Complex.exp (scalarGaussianCharFunExponent u σ2))) := by
  have hpow :=
    centeredEmpiricalCharFunFinSucc_inv_sqrt_succ_pow_tendsto_of_variance_tendsto
      (Y := fun i => Y i ω) hvar u hrem
  refine hpow.congr' ?_
  exact Eventually.of_forall fun n => by
    simpa [centeredEmpiricalCharFunFinSucc] using
      (charFun_normalized_finSucc_resampleMean_sub_empiricalMean_eq_pow
        (Y := Y) n ω u).symm

/-- Pathwise characteristic-function convergence for the normalized ordinary
bootstrap sample mean from empirical variance convergence and centered
Lindeberg tails.

This is the scalar pathwise face of Hansen Theorem 10.4 after the diagonal
Taylor remainder has been discharged by
`centeredEmpiricalCharFunFinSucc_remainder_isLittleO_of_variance_tendsto_tail`. -/
theorem
    charFun_normalized_finSucc_resampleMean_sub_empiricalMean_tendsto_of_variance_tendsto_tail
    (Y : ℕ → Ω → ℝ) (ω : Ω) {σ2 : ℝ}
    (hvar :
      Tendsto
        (fun n : ℕ => empiricalVarianceFinSucc (fun i => Y i ω) n)
        atTop (𝓝 σ2))
    (u : ℝ)
    (htail : ∀ δ : ℝ, 0 < δ →
      Tendsto
        (fun n : ℕ =>
          centeredEmpiricalTailSqFinSucc (fun i => Y i ω) n
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * u) δ)
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        charFun
          (((ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))).map
            (fun ωs =>
              Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))))
          u)
      atTop
      (𝓝 (Complex.exp (scalarGaussianCharFunExponent u σ2))) := by
  exact
    charFun_normalized_finSucc_resampleMean_sub_empiricalMean_tendsto_of_variance_tendsto
      (Y := Y) (ω := ω) hvar u
      (centeredEmpiricalCharFunFinSucc_remainder_isLittleO_of_variance_tendsto_tail
        (Y := fun i => Y i ω) hvar u htail)

/-- Characteristic function of a projected centered multivariate Gaussian.

For Hansen Theorem 10.4's Cramér-Wold route, a fixed projection of
`N(0, S)` has characteristic function
`exp (-t² (a' S a) / 2)`. -/
theorem charFun_map_multivariateGaussian_zero_dotProduct_eq_exp
    [Fintype k] [DecidableEq k] {S : Matrix k k ℝ}
    (hS : S.PosSemidef) (a : k → ℝ) (u : ℝ) :
    charFun
        ((multivariateGaussian 0 S).map
          (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a))
        u =
      Complex.exp (scalarGaussianCharFunExponent u (a ⬝ᵥ (S *ᵥ a))) := by
  have hLaw := hasLaw_multivariateGaussian_zero_dotProduct (n := k) hS a
  have hquad_nonneg : 0 ≤ a ⬝ᵥ (S *ᵥ a) := by
    simpa using hS.dotProduct_mulVec_nonneg a
  rw [hLaw.map_eq, charFun_gaussianReal]
  simp [scalarGaussianCharFunExponent, Real.toNNReal_of_nonneg hquad_nonneg]
  ring_nf

/-- Pathwise projected empirical variance convergence from empirical covariance
matrix convergence.

This deterministic bridge turns convergence of the finite empirical covariance
matrix into the projected-variance convergence premise used by the
characteristic-function remainder route for Hansen Theorem 10.4. -/
theorem empiricalVarianceFinSucc_dotProduct_tendsto_of_covMat_tendsto
    [Fintype k]
    (Y : ℕ → k → ℝ) {S : Matrix k k ℝ}
    (hcov :
      Tendsto
        (fun n : ℕ =>
          covMat
            (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))
            (fun i a => Y i.val a))
        atTop (𝓝 S))
    (a : k → ℝ) :
    Tendsto
      (fun n : ℕ => empiricalVarianceFinSucc (fun i => Y i ⬝ᵥ a) n)
      atTop (𝓝 (a ⬝ᵥ (S *ᵥ a))) := by
  have hquad :
      Tendsto
        (fun n : ℕ =>
          a ⬝ᵥ
            ((covMat
              (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                Measure (Fin (n + 1)))
              (fun i a => Y i.val a)) *ᵥ a))
        atTop (𝓝 (a ⬝ᵥ (S *ᵥ a))) := by
    have hcont : Continuous (fun M : Matrix k k ℝ => a ⬝ᵥ (M *ᵥ a)) :=
      continuous_const.dotProduct
        (Continuous.matrix_mulVec continuous_id continuous_const)
    exact (hcont.tendsto S).comp hcov
  refine hquad.congr' ?_
  exact Eventually.of_forall fun n => by
    let P : Measure (Fin (n + 1)) :=
      ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1)))
    have hmem : ∀ j, MemLp (fun i : Fin (n + 1) => Y i.val j) 2 P :=
      fun j => memLp_two_uniformOn_univ (Y := fun i : Fin (n + 1) => Y i.val j)
    simpa [empiricalVarianceFinSucc, P] using
      (variance_dotProduct_eq_dotProduct_covMat_mulVec
        (μ := P) (X := fun i a => Y i.val a) (b := a) hmem).symm

/-- Vector `Fin (n+1)` CLT-scale mean-zero identity for the ordinary
nonparametric bootstrap.

The normalized centered resample mean has exact conditional mean zero in the
indexed resampling space used by Hansen Theorem 10.4. -/
theorem integral_normalized_finSucc_resampleMean_sub_empiricalMean_eq_zero
    {k : Type*} [Fintype k]
    (Y : ℕ → Ω → k → ℝ) (n : ℕ) (ω : Ω) :
    ∫ ωs : Fin (n + 1) → Fin (n + 1),
        Real.sqrt (n + 1 : ℝ) •
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
        ∂(ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) =
      0 := by
  simpa [Fintype.card_fin] using
    (integral_normalized_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_zero
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω))

/-- Coordinate `Fin (n+1)` CLT-scale mean-zero identity for the ordinary
nonparametric bootstrap. -/
theorem integral_normalized_finSucc_resampleMean_sub_empiricalMean_apply_eq_zero
    {k : Type*} [Fintype k]
    (Y : ℕ → Ω → k → ℝ) (n : ℕ) (ω : Ω) (a : k) :
    ∫ ωs : Fin (n + 1) → Fin (n + 1),
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a)
        ∂(ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) =
      0 := by
  simpa [Fintype.card_fin] using
    (integral_normalized_empiricalBootstrapResampleMean_uniformOn_fun_apply_sub_eq_zero
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω) a)

/-- Scalar projection of the normalized ordinary bootstrap mean.

The Cramér-Wold projection of `sqrt (n+1) (Ybar* - Ybar)` is the same
normalized scalar bootstrap mean formed from the projected observations
`Y_i · a`. -/
theorem dotProduct_normalized_finSucc_resampleMean_sub_empiricalMean_eq
    {k : Type*} [Fintype k]
    (Y : ℕ → Ω → k → ℝ) (n : ℕ) (ω : Ω)
    (ωs : Fin (n + 1) → Fin (n + 1)) (a : k → ℝ) :
    (fun b =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs b -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) b)) ⬝ᵥ a =
      Real.sqrt (n + 1 : ℝ) *
        (empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a)
            (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a)) := by
  change
      (Real.sqrt (n + 1 : ℝ) •
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω))) ⬝ᵥ a =
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a)
              (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a))
  rw [smul_dotProduct, sub_dotProduct, empiricalBootstrapResampleMean_dotProduct,
    empiricalMean_dotProduct]
  rfl

/-- Matrix `Fin (n+1)` CLT-scale covariance identity for the ordinary
nonparametric bootstrap.

This is the sample-size-indexed finite-resample covariance normalization used
by the concrete Theorem 10.4 path. -/
theorem covMat_normalized_finSucc_resampleMean_sub_empiricalMean_eq
    {k : Type*} [Fintype k]
    (Y : ℕ → Ω → k → ℝ) (n : ℕ) (ω : Ω) :
    covMat
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1)))
        (fun ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a)) =
      covMat
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1)))
        (fun i a => Y i.val ω a) := by
  simpa [Fintype.card_fin] using
    (covMat_normalized_empiricalBootstrapResampleMean_uniformOn_fun_eq
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω))

/-- Matrix-entry `Fin (n+1)` CLT-scale raw cross-moment identity for the
ordinary nonparametric bootstrap.

Since the normalized centered resample mean has exact conditional mean zero,
its raw cross moments equal the finite empirical one-draw covariance matrix. -/
theorem integral_mul_normalized_finSucc_resampleMean_sub_empiricalMean_eq_covMat
    {k : Type*} [Fintype k]
    (Y : ℕ → Ω → k → ℝ) (n : ℕ) (ω : Ω) (a b : k) :
    ∫ ωs : Fin (n + 1) → Fin (n + 1),
        (Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a)) *
        (Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs b -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) b))
        ∂(ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) =
      covMat
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1)))
        (fun i a => Y i.val ω a) a b := by
  simpa [Fintype.card_fin] using
    (integral_mul_normalized_empiricalBootstrapResampleMean_uniformOn_fun_eq_covMat
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω) a b)

/-- Euclidean `Fin (n+1)` CLT-scale second-moment identity for the ordinary
nonparametric bootstrap.

The conditional expectation of the squared norm of
`sqrt (n+1) (Ybar* - Ybar)` equals the trace of the finite empirical covariance
matrix. -/
theorem integral_norm_sq_normalized_finSucc_resampleMean_sub_empiricalMean_eq_trace_covMat
    {k : Type*} [Fintype k]
    (Y : ℕ → Ω → EuclideanSpace ℝ k) (n : ℕ) (ω : Ω) :
    ∫ ωs : Fin (n + 1) → Fin (n + 1),
        ‖Real.sqrt (n + 1 : ℝ) •
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω))‖ ^ 2
        ∂(ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) =
      Matrix.trace
        (covMat
          (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
            Measure (Fin (n + 1)))
          (fun i a => Y i.val ω a)) := by
  simpa [Fintype.card_fin] using
    (integral_norm_sq_normalized_empiricalBootstrapResampleMean_uniformOn_fun_eq_trace_covMat
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω))

/-- Indexed-space Hansen Theorem 10.2 centered WLLN from a concrete conditional
second-moment bound. -/
theorem chapter10_indexed_bootstrap_wlln_centered_of_integral_norm_sq_bound
    [NormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ∀ n, Ω → Ωboot n → E} {Ybar : ℕ → Ω → E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hbound :
      ∀ n ω,
        (∫ ωs, ‖YbarStar n ω ωs - Ybar n ω‖ ^ 2 ∂Pstar n ω) ≤
          marcinkiewiczWLLNStatisticNat u 2 n ω) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) := by
  refine chapter10_indexed_bootstrap_wlln_centered_of_second_moment_bound
    (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
    (u := u) hu ?_
  intro η hη n ω
  calc
    bootstrapTailProbIndexed Pstar
        (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) η n ω
        ≤ (∫ ωs, ‖YbarStar n ω ωs - Ybar n ω‖ ^ 2 ∂Pstar n ω) / η ^ 2 :=
          bootstrapTailProbIndexed_zero_le_integral_norm_sq_div
            (Pstar := Pstar)
            (Zstar := fun n ω ωs => YbarStar n ω ωs - Ybar n ω)
            hPstar hZ hη n ω
    _ ≤ marcinkiewiczWLLNStatisticNat u 2 n ω / η ^ 2 :=
          div_le_div_of_nonneg_right (hbound n ω) (sq_nonneg η)
    _ = bootstrapWLLNSecondMomentBound u η n ω := by
          rw [bootstrapWLLNSecondMomentBound]
          field_simp [hη.ne']

/-- Indexed-space Hansen Theorem 10.2 level WLLN from the centered conclusion.

This is the indexed analogue of `chapter10_bootstrap_wlln_level_from_centered`:
centered bootstrap convergence on sample-size-dependent resampling spaces plus
ordinary convergence of the sample mean gives the level bootstrap WLLN. -/
theorem chapter10_indexed_bootstrap_wlln_level_from_centered
    [SeminormedAddCommGroup E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ∀ n, Ω → Ωboot n → E} {Ybar : ℕ → Ω → E} {μY : E}
    (hcenter :
      TendstoInBootstrapProbabilityIndexed μ Pstar
        (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0))
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar YbarStar (fun _ => μY) := by
  have hYbar_boot :
      TendstoInBootstrapProbabilityIndexed μ Pstar
        (fun n ω _ => Ybar n ω) (fun _ => μY) :=
    tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure hPstar hYbar
  have hsum :=
    TendstoInBootstrapProbabilityIndexed.add hPstar hcenter hYbar_boot
  exact hsum.congr
    (fun n ω ωs => by simp)
    (fun ω => by simp)

/-- Indexed Hansen Theorem 10.2, level WLLN from Hansen's textbook
second-moment bound.

This is the sample-size-dependent bootstrap-space version of
`chapter10_bootstrap_wlln_level_of_second_moment_bound`. -/
theorem chapter10_indexed_bootstrap_wlln_level_of_second_moment_bound
    [SeminormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ∀ n, Ω → Ωboot n → E} {Ybar : ℕ → Ω → E} {μY : E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hle :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapTailProbIndexed Pstar
          (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0)
          η n ω ≤ bootstrapWLLNSecondMomentBound u η n ω)
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar YbarStar (fun _ => μY) :=
  chapter10_indexed_bootstrap_wlln_level_from_centered
    (μ := μ) hPstar
    (chapter10_indexed_bootstrap_wlln_centered_of_second_moment_bound
      (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
      (u := u) hu hle)
    hYbar

/-- Indexed Hansen Theorem 10.2, vector level WLLN from a bootstrap `L²`
seminorm bound.

This is the sample-size-dependent bootstrap-space version of
`chapter10_bootstrap_wlln_level_of_l2_eLpNorm_bound`. -/
theorem chapter10_indexed_bootstrap_wlln_level_of_l2_eLpNorm_bound
    [NormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ∀ n, Ω → Ωboot n → E} {Ybar : ℕ → Ω → E} {μY : E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hbound :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapL2ENNTailBoundIndexed Pstar
          (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) η n ω ≤
            bootstrapWLLNSecondMomentBound u η n ω)
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar YbarStar (fun _ => μY) :=
  chapter10_indexed_bootstrap_wlln_level_from_centered
    (μ := μ) hPstar
    (chapter10_indexed_bootstrap_wlln_centered_of_l2_eLpNorm_bound
      (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
      (u := u) hu hZ hbound)
    hYbar

/-- Indexed Hansen Theorem 10.2, scalar level WLLN from a conditional
variance bound.

This is the sample-size-dependent bootstrap-space version of
`chapter10_bootstrap_wlln_level_real_of_conditional_variance_bound`. -/
theorem chapter10_indexed_bootstrap_wlln_level_real_of_conditional_variance_bound
    [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ∀ n, Ω → Ωboot n → ℝ} {Ybar : ℕ → Ω → ℝ} {μY : ℝ}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hmean :
      ∀ n ω, (Pstar n ω)[fun ωs => YbarStar n ω ωs - Ybar n ω] = 0)
    (hvar :
      ∀ n ω,
        Var[fun ωs => YbarStar n ω ωs - Ybar n ω; Pstar n ω] ≤
          marcinkiewiczWLLNStatisticNat u 2 n ω)
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar YbarStar (fun _ => μY) :=
  chapter10_indexed_bootstrap_wlln_level_from_centered
    (μ := μ) hPstar
    (chapter10_indexed_bootstrap_wlln_centered_real_of_conditional_variance_bound
      (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
      (u := u) hPstar hu hZ hmean hvar)
    hYbar

/-- Indexed-space Hansen Theorem 10.2 level WLLN from a conditional
second-moment bound.

This is the sample-size-dependent analogue of
`chapter10_bootstrap_wlln_level_of_integral_norm_sq_bound`: a concrete
conditional bound on `E*[‖Ybar* - Ybar‖²]`, Hansen's Marcinkiewicz convergence
for the bound, and the ordinary WLLN for `Ybar` imply the level indexed
bootstrap WLLN. -/
theorem chapter10_indexed_bootstrap_wlln_level_of_integral_norm_sq_bound
    [NormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ∀ n, Ω → Ωboot n → E} {Ybar : ℕ → Ω → E} {μY : E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hbound :
      ∀ n ω,
        (∫ ωs, ‖YbarStar n ω ωs - Ybar n ω‖ ^ 2 ∂Pstar n ω) ≤
          marcinkiewiczWLLNStatisticNat u 2 n ω)
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar YbarStar (fun _ => μY) :=
  chapter10_indexed_bootstrap_wlln_level_of_second_moment_bound
    (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
    (u := u) hPstar hu
    (fun η hη n ω => by
      calc
        bootstrapTailProbIndexed Pstar
            (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) η n ω
            ≤ (∫ ωs, ‖YbarStar n ω ωs - Ybar n ω‖ ^ 2 ∂Pstar n ω) / η ^ 2 :=
              bootstrapTailProbIndexed_zero_le_integral_norm_sq_div
                (Pstar := Pstar)
                (Zstar := fun n ω ωs => YbarStar n ω ωs - Ybar n ω)
                hPstar hZ hη n ω
        _ ≤ marcinkiewiczWLLNStatisticNat u 2 n ω / η ^ 2 :=
              div_le_div_of_nonneg_right (hbound n ω) (sq_nonneg η)
        _ = bootstrapWLLNSecondMomentBound u η n ω := by
              rw [bootstrapWLLNSecondMomentBound]
              field_simp [hη.ne'])
    hYbar

/-- Ordinary finite nonparametric-bootstrap centered WLLN for `Fin (n+1)`
samples, obtained by feeding the finite squared-norm calculation into Hansen's
Theorem 10.2 Marcinkiewicz bound. -/
theorem chapter10_indexed_bootstrap_wlln_centered_finSucc_resampleMean
    [IsFiniteMeasure μ] {k : Type*} [Fintype k]
    (Y : ℕ → Ω → EuclideanSpace ℝ k)
    (hu : UniformIntegrable (fun i ω => ‖Y i ω‖) 1 μ) :
    TendstoInBootstrapProbabilityIndexed (μ := μ)
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
      (fun _ => 0) := by
  refine tendstoInBootstrapProbabilityIndexed_of_tail_bound
    (bound := fun η n ω =>
      bootstrapWLLNSecondMomentBound (fun i ω => ‖Y i ω‖) η (n + 1) ω) ?_ ?_
  · intro η hη
    exact bootstrapWLLNSecondMomentBound_succ_tendsto_zero
      (μ := μ) (u := fun i ω => ‖Y i ω‖) (η := η) hu hη
  · intro η hη n ω
    have hPstar :
        ∀ m (ω : Ω),
          IsProbabilityMeasure
            (ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (m + 1) → Fin (m + 1)))) := by
      intro m ω
      infer_instance
    have hZ :
        ∀ m (ω : Ω),
          MemLp
            (fun ωs : Fin (m + 1) → Fin (m + 1) =>
              empiricalBootstrapResampleMean
                  (fun i : Fin (m + 1) => Y i.val ω)
                  (fun ωs t => ωs t) ωs -
                empiricalMean (fun i : Fin (m + 1) => Y i.val ω))
            2
            (ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (m + 1) → Fin (m + 1)))) := by
      intro m ω
      exact memLp_two_uniformOn_univ
        (Y := fun ωs : Fin (m + 1) → Fin (m + 1) =>
          empiricalBootstrapResampleMean
              (fun i : Fin (m + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (m + 1) => Y i.val ω))
    calc
      bootstrapTailProbIndexed
          (fun n _ =>
            ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
          (fun n ω ωs =>
            empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
          (fun _ => 0) η n ω
          ≤ (∫ ωs : Fin (n + 1) → Fin (n + 1),
              ‖empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω)‖ ^ 2
              ∂(ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1)))) / η ^ 2 :=
            bootstrapTailProbIndexed_zero_le_integral_norm_sq_div
              (Pstar := fun n _ =>
                ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
              (Zstar := fun n ω ωs =>
                empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
              hPstar hZ hη n ω
      _ ≤ marcinkiewiczWLLNStatisticNat (fun i ω => ‖Y i ω‖) 2 (n + 1) ω /
            η ^ 2 :=
            div_le_div_of_nonneg_right
              (integral_norm_sq_finSucc_resampleMean_sub_empiricalMean_le_marcinkiewicz
                (Y := Y) n ω)
              (sq_nonneg η)
      _ = bootstrapWLLNSecondMomentBound (fun i ω => ‖Y i ω‖) η (n + 1) ω := by
            rw [bootstrapWLLNSecondMomentBound]
            field_simp [hη.ne']

/-- Ordinary finite nonparametric-bootstrap level WLLN for `Fin (n+1)` samples.

This packages the concrete centered finite-resample theorem with an ordinary
sample-mean convergence premise, giving Hansen Theorem 10.2's level conclusion
for the indexed ordinary nonparametric bootstrap. -/
theorem chapter10_indexed_bootstrap_wlln_level_finSucc_resampleMean
    [IsFiniteMeasure μ] {k : Type*} [Fintype k]
    (Y : ℕ → Ω → EuclideanSpace ℝ k) {μY : EuclideanSpace ℝ k}
    (hu : UniformIntegrable (fun i ω => ‖Y i ω‖) 1 μ)
    (hYbar :
      TendstoInMeasure μ
        (fun n ω => empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
        atTop (fun _ => μY)) :
    TendstoInBootstrapProbabilityIndexed (μ := μ)
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        empiricalBootstrapResampleMean
          (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs)
      (fun _ => μY) := by
  have hPstar :
      ∀ n (ω : Ω),
        IsProbabilityMeasure
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1)))) := by
    intro n ω
    infer_instance
  exact chapter10_indexed_bootstrap_wlln_level_from_centered
    (μ := μ)
    (Pstar := fun n _ =>
      ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
    hPstar
    (YbarStar := fun n ω ωs =>
      empiricalBootstrapResampleMean
        (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs)
    (Ybar := fun n ω => empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
    (μY := μY)
    (chapter10_indexed_bootstrap_wlln_centered_finSucc_resampleMean
      (μ := μ) Y hu)
    hYbar

/-- Shifted Banach-valued empirical mean WLLN for `Fin (n+1)` empirical
supports.

This rewrites the ordinary WLLN through the canonical `empiricalMean` API used
by the finite ordinary nonparametric-bootstrap statements. -/
theorem empiricalMean_finSucc_tendstoInMeasure_wlln_of_iIndep
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [IsFiniteMeasure μ]
    (Y : ℕ → Ω → E)
    (hint : Integrable (Y 0) μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInMeasure μ
      (fun n ω => empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
      atTop (fun _ => ∫ ω, Y 0 ω ∂μ) := by
  have hpair : Pairwise ((· ⟂ᵢ[μ] ·) on Y) :=
    fun _ _ hij => hindep.indepFun hij
  have hbase :=
    tendstoInMeasure_wlln (μ := μ) Y hint hpair hident
  have hshift :
      TendstoInMeasure μ
        (fun n ω =>
          (((n + 1 : ℕ) : ℝ)⁻¹) •
            ∑ i ∈ Finset.range (n + 1), Y i ω)
        atTop (fun _ => ∫ ω, Y 0 ω ∂μ) := by
    rw [tendstoInMeasure_iff_dist] at hbase ⊢
    intro ε hε
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (hbase ε hε).comp (tendsto_add_atTop_nat 1)
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hshift
  exact ae_of_all μ fun ω => by
    have hcoeff :
        (((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal) =
          ((n + 1 : ℝ)⁻¹) := by
      have htoReal :
          ((Fintype.card (Fin (n + 1)) : ℝ≥0∞).toReal) =
            (n + 1 : ℝ) := by
        rw [Fintype.card_fin]
        simpa using ENNReal.toReal_natCast (n + 1)
      rw [ENNReal.toReal_inv, htoReal]
    have hsum :
        (∑ i : Fin (n + 1), Y i.val ω) =
          ∑ i ∈ Finset.range (n + 1), Y i ω := by
      rw [Finset.sum_range]
    calc
      (((n + 1 : ℕ) : ℝ)⁻¹) •
            ∑ i ∈ Finset.range (n + 1), Y i ω =
          ((n + 1 : ℝ)⁻¹) •
            ∑ i ∈ Finset.range (n + 1), Y i ω := by
            simp [Nat.cast_add, Nat.cast_one]
      _ = ((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal •
            ∑ i : Fin (n + 1), Y i.val ω := by
            rw [hcoeff, hsum]
      _ = empiricalMean (fun i : Fin (n + 1) => Y i.val ω) := rfl

/-- Ordinary finite-dimensional nonparametric-bootstrap centered WLLN from
identical distribution and a finite first moment.

This is the vector counterpart of the scalar iid-integrable wrapper: identical
distribution of the observations transfers to identical distribution of their
norms, and `Y₀ ∈ L¹` supplies the norm uniform-integrability premise in
Hansen's Theorem 10.2 proof. -/
theorem
    chapter10_indexed_bootstrap_wlln_centered_finSucc_resampleMean_of_identDistrib_memLp
    [IsFiniteMeasure μ] {k : Type*} [Fintype k]
    (Y : ℕ → Ω → EuclideanSpace ℝ k)
    (hY : MemLp (Y 0) 1 μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInBootstrapProbabilityIndexed (μ := μ)
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
      (fun _ => 0) := by
  have hnorm_ident :
      ∀ i,
        IdentDistrib (fun ω => ‖Y i ω‖) (fun ω => ‖Y 0 ω‖) μ μ := by
    intro i
    simpa [Function.comp_def] using (hident i).comp continuous_norm.measurable
  exact chapter10_indexed_bootstrap_wlln_centered_finSucc_resampleMean
    (μ := μ) Y
    (uniformIntegrable_one_of_identDistrib_memLp
      (μ := μ) (Z := fun i ω => ‖Y i ω‖) hY.norm hnorm_ident)

/-- Ordinary finite-dimensional nonparametric-bootstrap level WLLN from iid
integrability.

The centered bootstrap conclusion is supplied by identical distribution plus
`Y₀ ∈ L¹`; the ordinary empirical mean convergence is supplied by the shifted
Banach-valued WLLN and the `iIndepFun` independence premise. -/
theorem
    chapter10_indexed_bootstrap_wlln_level_finSucc_resampleMean_of_iid_integrable
    [IsFiniteMeasure μ] {k : Type*} [Fintype k]
    (Y : ℕ → Ω → EuclideanSpace ℝ k)
    (hY : MemLp (Y 0) 1 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInBootstrapProbabilityIndexed (μ := μ)
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        empiricalBootstrapResampleMean
          (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs)
      (fun _ => ∫ ω, Y 0 ω ∂μ) :=
  chapter10_indexed_bootstrap_wlln_level_finSucc_resampleMean
    (μ := μ) Y
    (by
      have hnorm_ident :
          ∀ i,
            IdentDistrib (fun ω => ‖Y i ω‖) (fun ω => ‖Y 0 ω‖) μ μ := by
        intro i
        simpa [Function.comp_def] using (hident i).comp continuous_norm.measurable
      exact uniformIntegrable_one_of_identDistrib_memLp
        (μ := μ) (Z := fun i ω => ‖Y i ω‖) hY.norm hnorm_ident)
    (empiricalMean_finSucc_tendstoInMeasure_wlln_of_iIndep
      (μ := μ) Y (memLp_one_iff_integrable.mp hY) hindep hident)

/-- Ordinary scalar finite nonparametric-bootstrap centered WLLN for
`Fin (n+1)` samples.

This is the one-dimensional counterpart of
`chapter10_indexed_bootstrap_wlln_centered_finSucc_resampleMean`, using the
scalar empirical second-moment identity before applying Hansen's
Marcinkiewicz bound. -/
theorem chapter10_indexed_bootstrap_wlln_centered_real_finSucc_resampleMean
    [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (hu : UniformIntegrable Y 1 μ) :
    TendstoInBootstrapProbabilityIndexed (μ := μ)
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
      (fun _ => 0) := by
  have hPstar :
      ∀ n (ω : Ω),
        IsProbabilityMeasure
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1)))) := by
    intro n ω
    infer_instance
  have hZ :
      ∀ n (ω : Ω),
        MemLp
          (fun ωs : Fin (n + 1) → Fin (n + 1) =>
            empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
          2
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1)))) := by
    intro n ω
    exact memLp_two_uniformOn_univ
      (Y := fun ωs : Fin (n + 1) → Fin (n + 1) =>
        empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω)
            (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
  refine tendstoInBootstrapProbabilityIndexed_of_tail_bound
    (bound := fun η n ω => bootstrapWLLNSecondMomentBound Y η (n + 1) ω) ?_ ?_
  · intro η hη
    exact bootstrapWLLNSecondMomentBound_succ_tendsto_zero
      (μ := μ) (u := Y) (η := η) hu hη
  · intro η hη n ω
    calc
      bootstrapTailProbIndexed
          (fun n _ =>
            ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
          (fun n ω ωs =>
            empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
          (fun _ => 0) η n ω
          ≤ (∫ ωs : Fin (n + 1) → Fin (n + 1),
              ‖empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω)‖ ^ 2
              ∂(ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1)))) / η ^ 2 :=
            bootstrapTailProbIndexed_zero_le_integral_norm_sq_div
              (Pstar := fun n _ =>
                ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
              (Zstar := fun n ω ωs =>
                empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
              hPstar hZ hη n ω
      _ ≤ marcinkiewiczWLLNStatisticNat Y 2 (n + 1) ω / η ^ 2 :=
            div_le_div_of_nonneg_right ?_ (sq_nonneg η)
      _ = bootstrapWLLNSecondMomentBound Y η (n + 1) ω := by
            rw [bootstrapWLLNSecondMomentBound]
            field_simp [hη.ne']
    simpa [Real.norm_eq_abs, sq_abs] using
      integral_sq_finSucc_resampleMean_sub_empiricalMean_le_marcinkiewicz
        (Y := Y) n ω

/-- Ordinary scalar finite nonparametric-bootstrap centered WLLN from identical
distribution and a finite first moment.

This is a textbook-facing wrapper around
`chapter10_indexed_bootstrap_wlln_centered_real_finSucc_resampleMean`: identical
distribution plus `Y₀ ∈ L¹` supplies the uniform-integrability premise used in
Hansen's Theorem 10.2 proof. -/
theorem
    chapter10_indexed_bootstrap_wlln_centered_real_finSucc_resampleMean_of_identDistrib_memLp
    [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hY : MemLp (Y 0) 1 μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInBootstrapProbabilityIndexed (μ := μ)
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
      (fun _ => 0) :=
  chapter10_indexed_bootstrap_wlln_centered_real_finSucc_resampleMean
    (μ := μ) Y
    (uniformIntegrable_one_of_identDistrib_memLp
      (μ := μ) (Z := Y) hY hident)

/-- Shifted scalar empirical mean WLLN for `Fin (n+1)` empirical supports.

This rewrites the shifted empirical-uniform integral WLLN through the canonical
`empiricalMean` API used by the ordinary nonparametric-bootstrap statements. -/
theorem empiricalMean_finSucc_tendstoInMeasure_wlln_real_of_iIndep
    [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hY : MemLp (Y 0) 1 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInMeasure μ
      (fun n ω => empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
      atTop (fun _ => ∫ ω, Y 0 ω ∂μ) :=
  empiricalMean_finSucc_tendstoInMeasure_wlln_of_iIndep
    (μ := μ) Y (memLp_one_iff_integrable.mp hY) hindep hident

/-- Ordinary scalar finite nonparametric-bootstrap level WLLN for `Fin (n+1)`
samples.

This packages the concrete centered scalar finite-resample theorem with an
ordinary sample-mean convergence premise, giving Hansen Theorem 10.2's level
conclusion for the one-dimensional indexed ordinary nonparametric bootstrap. -/
theorem chapter10_indexed_bootstrap_wlln_level_real_finSucc_resampleMean
    [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) {μY : ℝ}
    (hu : UniformIntegrable Y 1 μ)
    (hYbar :
      TendstoInMeasure μ
        (fun n ω => empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
        atTop (fun _ => μY)) :
    TendstoInBootstrapProbabilityIndexed (μ := μ)
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        empiricalBootstrapResampleMean
          (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs)
      (fun _ => μY) := by
  have hPstar :
      ∀ n (ω : Ω),
        IsProbabilityMeasure
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1)))) := by
    intro n ω
    infer_instance
  exact chapter10_indexed_bootstrap_wlln_level_from_centered
    (μ := μ)
    (Pstar := fun n _ =>
      ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
    hPstar
    (YbarStar := fun n ω ωs =>
      empiricalBootstrapResampleMean
        (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs)
    (Ybar := fun n ω => empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
    (μY := μY)
    (chapter10_indexed_bootstrap_wlln_centered_real_finSucc_resampleMean
      (μ := μ) Y hu)
    hYbar

/-- Ordinary scalar finite nonparametric-bootstrap level WLLN from iid
integrability.

The centered bootstrap conclusion is supplied by identical distribution plus
`Y₀ ∈ L¹`; the ordinary empirical mean convergence is supplied by the shifted
WLLN and the `iIndepFun` independence premise. -/
theorem
    chapter10_indexed_bootstrap_wlln_level_real_finSucc_resampleMean_of_iid_integrable
    [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hY : MemLp (Y 0) 1 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInBootstrapProbabilityIndexed (μ := μ)
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        empiricalBootstrapResampleMean
          (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs)
      (fun _ => ∫ ω, Y 0 ω ∂μ) :=
  chapter10_indexed_bootstrap_wlln_level_real_finSucc_resampleMean
    (μ := μ) Y
    (uniformIntegrable_one_of_identDistrib_memLp
      (μ := μ) (Z := Y) hY hident)
    (empiricalMean_finSucc_tendstoInMeasure_wlln_real_of_iIndep
      (μ := μ) Y hY hindep hident)

end IndexedBootstrapWLLN

end HansenEconometrics
