import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.UniformOn
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.AsymptoticUtils.MaxBounds
import HansenEconometrics.BootstrapUtils
import HansenEconometrics.ProbabilityUtils

/-!
# Chapter 10 — Resampling Methods

This module starts the theorem-facing Chapter 10 API for Hansen's resampling
methods.  The initial public surface covers the bootstrap convergence notions
used throughout the chapter:

* `chapter10_bootstrap_convergence_in_probability_of_convergence_in_probability`
  is Hansen Theorem 10.1.
* `chapter10_bootstrap_continuous_mapping_probability` is Hansen Theorem 10.3.
* `chapter10_bootstrap_wlln_centered_of_tail_bound` is the reusable
  conditional-Markov bridge for the centered conclusion of Hansen Theorem 10.2.
* `chapter10_bootstrap_wlln_level_from_centered` is the Slutsky/addition step
  in Hansen Theorem 10.2: centered bootstrap WLLN plus the ordinary WLLN gives
  bootstrap convergence of the sample mean to the population mean.
* `chapter10_bootstrap_wlln_centered_of_second_moment_bound` is the
  Chebyshev/Marcinkiewicz bridge that turns Hansen's empirical second-moment
  bound into the centered conclusion of Theorem 10.2.
* `TendstoInBootstrapDistribution` is Hansen Definition 10.2 for
  finite-dimensional random vectors, stated in the chapter-facing CDF form.
* `integral_uniformOn_univ_eq_card_inv_smul_sum` is the finite empirical mean
  identity behind equations (10.10) and (10.12).
* `variance_uniformOn_univ_eq_card_inv_smul_sum_sq_centered` is the scalar
  finite empirical variance identity behind equation (10.11).
* `covMat_uniformOn_univ_eq_card_inv_smul_sum_centered` is the
  finite-dimensional empirical covariance matrix identity behind (10.11).
* `chapter10_marcinkiewicz_wlln_natPower_of_uniformIntegrable` is the
  natural-power face of Hansen Theorem 10.20.

The concrete nonparametric-bootstrap sample-mean, CLT, variance, percentile,
and regression results are built on top of this two-probability-space layer.
Detailed theorem-by-theorem status lives in `inventory/ch10-inventory.md`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

section EmpiricalDistribution

variable {ι : Type*} [MeasurableSpace ι] [Fintype ι]

/-- Uniform sampling from a finite empirical support is normalized counting
measure. -/
theorem uniformOn_univ_eq_inv_card_smul_count :
    (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
      ((Fintype.card ι : ℝ≥0∞)⁻¹) • Measure.count := by
  ext s hs
  rw [ProbabilityTheory.uniformOn_univ, Measure.smul_apply]
  simp [ENNReal.div_eq_inv_mul]

variable [MeasurableSingletonClass ι]

/-- Empirical mean identity for one bootstrap draw.

For any finite empirical support, integrating a statistic under the uniform
resampling law equals the finite-sample average.  This is the measure-theoretic
form of Hansen's equations (10.10) and (10.12). -/
theorem integral_uniformOn_univ_eq_card_inv_smul_sum
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : ι → E) :
    ∫ i, Y i ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, Y i := by
  rw [uniformOn_univ_eq_inv_card_smul_count, integral_smul_measure, integral_count]

/-- Scalar empirical variance identity for one bootstrap draw.

This is the scalar version of Hansen's exact bootstrap covariance formula
(10.11): under uniform resampling from a finite empirical support, the
variance is the average squared deviation from the empirical mean. -/
theorem variance_uniformOn_univ_eq_card_inv_smul_sum_sq_centered
    (Y : ι → ℝ) :
    Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)] =
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal •
        ∑ i, (Y i -
          ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j) ^ 2 := by
  have hmean :
      ∫ i, Y i ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j :=
    integral_uniformOn_univ_eq_card_inv_smul_sum Y
  rw [ProbabilityTheory.variance_eq_integral (measurable_of_finite Y).aemeasurable, hmean]
  exact integral_uniformOn_univ_eq_card_inv_smul_sum
    (fun i => (Y i - ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j) ^ 2)

/-- Finite-dimensional empirical covariance identity for one bootstrap draw.

This is the matrix form of Hansen's exact bootstrap covariance formula
(10.11): under uniform resampling from a finite empirical support, the
covariance matrix is the average outer product of deviations from the empirical
mean. -/
theorem covMat_uniformOn_univ_eq_card_inv_smul_sum_centered
    {k : Type*} (Y : ι → k → ℝ) :
    covMat (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) Y =
      fun a b =>
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal •
          ∑ i, (Y i a -
              ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j a) *
            (Y i b -
              ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j b) := by
  ext a b
  have hmean_a :
      ∫ i, Y i a ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j a :=
    integral_uniformOn_univ_eq_card_inv_smul_sum (fun i => Y i a)
  have hmean_b :
      ∫ i, Y i b ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j b :=
    integral_uniformOn_univ_eq_card_inv_smul_sum (fun i => Y i b)
  simp [covMat, ProbabilityTheory.covariance, hmean_a, hmean_b,
    integral_uniformOn_univ_eq_card_inv_smul_sum]

end EmpiricalDistribution

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

section BootstrapDistribution

/-- Coordinatewise lower-tail relation for finite-dimensional CDFs. -/
def coordinateLE (x y : k → ℝ) : Prop :=
  ∀ i, x i ≤ y i

/-- Conditional bootstrap CDF `Gₙ*(x) = P*[Zₙ* ≤ x]` for a finite-dimensional
random vector. -/
noncomputable def bootstrapVectorCDF
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → k → ℝ)
    (x : k → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((Pstar n ω) {ωs | coordinateLE (Zstar n ω ωs) x}).toReal

/-- Limit CDF `G(x) = P[Z ≤ x]` for a finite-dimensional random vector. -/
noncomputable def vectorCDF
    (ν : Measure Ωlim) (Z : Ωlim → k → ℝ) (x : k → ℝ) : ℝ :=
  (ν {ω | coordinateLE (Z ω) x}).toReal

/-- Hansen Definition 10.2: convergence in bootstrap distribution.

The conditional CDF of `Zstar n` converges in ordinary probability, under the
original-sample law `μ`, to the limit CDF at every continuity point of the
limit CDF. -/
def TendstoInBootstrapDistribution
    (μ : Measure Ω) (Pstar : ℕ → Ω → Measure Ωs)
    (Zstar : ℕ → Ω → Ωs → k → ℝ)
    (ν : Measure Ωlim) (Z : Ωlim → k → ℝ) : Prop :=
  ∀ x : k → ℝ,
    ContinuousAt (fun y => vectorCDF ν Z y) x →
      TendstoInMeasure μ (fun n ω => bootstrapVectorCDF Pstar Zstar x n ω)
        atTop (fun _ => vectorCDF ν Z x)

/-- The CDF-convergence projection built into Hansen Definition 10.2. -/
theorem TendstoInBootstrapDistribution.tendsto_cdf
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hZ : TendstoInBootstrapDistribution μ Pstar Zstar ν Z)
    {x : k → ℝ} (hx : ContinuousAt (fun y => vectorCDF ν Z y) x) :
    TendstoInMeasure μ (fun n ω => bootstrapVectorCDF Pstar Zstar x n ω)
      atTop (fun _ => vectorCDF ν Z x) :=
  hZ x hx

end BootstrapDistribution

end HansenEconometrics
