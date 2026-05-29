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
* `chapter10_bootstrap_lipschitz_mapping_probability` is the reusable
  Lipschitz mapping bridge used by Slutsky and Delta-method theorem wrappers.
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
* `TendstoInBootstrapDistribution.of_tendsto_cdf` and congruence lemmas expose
  the reusable CDF bridge needed by later bootstrap CLT and delta-method
  wrappers.
* `TendstoInBootstrapWeakDistribution` is a bounded-continuous-test-function
  backend for bootstrap distributional convergence, used by the distributional
  continuous-mapping theorem.
* `TendstoInBootstrapWeakDistribution.congr` gives pointwise congruence for
  that weak backend.
* `chapter10_bootstrap_continuous_mapping_distribution` is the globally
  continuous face of Hansen Theorem 10.5.
* `chapter10_bootstrap_delta_method_linear` and
  `chapter10_bootstrap_delta_method_gaussian` are the linear-image and
  Gaussian covariance faces of Hansen Theorem 10.6.
* `integral_uniformOn_univ_eq_card_inv_smul_sum` is the finite empirical mean
  identity behind equations (10.10) and (10.12).
* `variance_uniformOn_univ_eq_card_inv_smul_sum_sq_centered` is the scalar
  finite empirical variance identity behind equation (10.11).
* `covMat_uniformOn_univ_eq_card_inv_smul_sum_centered` is the
  finite-dimensional empirical covariance matrix identity behind (10.11).
* `chapter10_marcinkiewicz_wlln_natPower_of_uniformIntegrable` is the
  natural-power face of Hansen Theorem 10.20.
* `chapter10_marcinkiewicz_wlln_rpow_of_uniformIntegrable` is Hansen Theorem
  10.20 in its real-exponent `r > 1` form.
* `chapter10_bootstrap_smooth_variance_consistency` is the plug-in covariance
  continuous-mapping bridge behind Hansen Theorem 10.8.
* `chapter10_bootstrap_smooth_variance_consistency_of_components` derives the
  Theorem 10.8 bridge from separate bootstrap convergence of the plug-in
  Jacobian and covariance inputs.
* `chapter10_bootstrap_variance_consistency_of_moment_convergence` is the
  moment-convergence bridge behind Hansen Theorem 10.9.
* `chapter10_trimmedBootstrapVariance_tendsto_of_moments` is the trimmed
  conditional covariance bridge behind Hansen Theorem 10.12.
* `chapter10_finiteReplicationVariance_tendsto_of_moments` is the
  finite-replication variance moment bridge behind Hansen Theorem 10.11.
* `chapter10_finiteReplicationCovarianceMat_tendsto_of_moments` is the
  finite-dimensional covariance-matrix bridge behind Hansen Theorem 10.11.
* `chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_moments` is the
  textbook-centered finite-replication covariance-matrix bridge for Theorem
  10.11.
* `chapter10_percentileCI_coverage_tendsto_of_joint_quantile_limit` is the
  coverage bridge behind Hansen Theorem 10.13.
* `chapter10_percentileCI_coverage_tendsto` is the calibrated percentile
  coverage wrapper.
* `chapter10_percentileTCI_coverage_tendsto_of_joint_quantile_limit` is the
  percentile-`t` coverage bridge behind Hansen Theorem 10.14.
* `chapter10_bootstrap_abs_test_rejectionProb_tendsto_of_joint_critical_value_limit`
  is the bootstrap-test critical-value bridge behind Hansen Theorem 10.16.

The concrete nonparametric-bootstrap sample-mean, CLT, variance, percentile,
and regression results are built on top of this two-probability-space layer.
Detailed theorem-by-theorem status lives in `inventory/ch10-inventory.md`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix Matrix.Norms.Elementwise

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

/-- Constructor for Hansen Definition 10.2 from pointwise conditional-CDF
convergence. -/
theorem TendstoInBootstrapDistribution.of_tendsto_cdf
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hZ :
      ∀ x : k → ℝ,
        ContinuousAt (fun y => vectorCDF ν Z y) x →
          TendstoInMeasure μ (fun n ω => bootstrapVectorCDF Pstar Zstar x n ω)
            atTop (fun _ => vectorCDF ν Z x)) :
    TendstoInBootstrapDistribution μ Pstar Zstar ν Z :=
  hZ

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

/-- Bootstrap-distribution convergence is invariant under pointwise equality of
the bootstrap statistic. -/
theorem TendstoInBootstrapDistribution.congr_bootstrap
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hZ : TendstoInBootstrapDistribution μ Pstar Zstar ν Z) :
    TendstoInBootstrapDistribution μ Pstar Zstar' ν Z := by
  intro x hx
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl (hZ.tendsto_cdf hx)
  refine ae_of_all μ fun ω => ?_
  have hset :
      {ωs : Ωs | coordinateLE (Zstar' n ω ωs) x} =
        {ωs : Ωs | coordinateLE (Zstar n ω ωs) x} := by
    ext ωs
    simp [coordinateLE, hstar n ω ωs]
  simp [bootstrapVectorCDF, hset]

/-- Bootstrap-distribution convergence is invariant under pointwise equality of
the limiting statistic. -/
theorem TendstoInBootstrapDistribution.congr_limit
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z Z' : Ωlim → k → ℝ}
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapDistribution μ Pstar Zstar ν Z) :
    TendstoInBootstrapDistribution μ Pstar Zstar ν Z' := by
  intro x hx
  have hcdf_fun :
      (fun y => vectorCDF ν Z y) = fun y => vectorCDF ν Z' y := by
    funext y
    simp [vectorCDF, hlim]
  have hx_old : ContinuousAt (fun y => vectorCDF ν Z y) x := by
    simpa [hcdf_fun] using hx
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_
    (hZ.tendsto_cdf hx_old)
  refine ae_of_all μ fun _ => ?_
  simp [hcdf_fun]

/-- Pointwise congruence for bootstrap convergence in distribution. -/
theorem TendstoInBootstrapDistribution.congr
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → k → ℝ}
    {Z Z' : Ωlim → k → ℝ}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapDistribution μ Pstar Zstar ν Z) :
    TendstoInBootstrapDistribution μ Pstar Zstar' ν Z' :=
  (hZ.congr_bootstrap hstar).congr_limit hlim

end BootstrapDistribution

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

end BootstrapWeakDistribution

section BootstrapDeltaMethod

/-- Hansen Theorem 10.6, linearized bootstrap Delta-method bridge.

Once the nonlinear estimator has been reduced to its derivative-linearized
statistic, bootstrap weak convergence is preserved by the continuous linear
derivative map.  The deterministic differentiability remainder supplies the
separate `oₚ*` step in the full Delta-method proof. -/
theorem chapter10_bootstrap_delta_method_linear
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → E}
    {ξ : Ωlim → E} (G : E →L[ℝ] F)
    (hT : TendstoInBootstrapWeakDistribution μ Pstar Tstar ν ξ) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => G (Tstar n ω ωs)) ν (fun ω => G (ξ ω)) :=
  chapter10_bootstrap_continuous_mapping_distribution hT G.continuous

/-- Matrix-linear form of the bootstrap Delta-method bridge. -/
theorem chapter10_bootstrap_delta_method_matrix_linear
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {ξ : Ωlim → EuclideanSpace ℝ d} (G : Matrix r d ℝ)
    (hT : TendstoInBootstrapWeakDistribution μ Pstar Tstar ν ξ) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      ν (fun ω => matrixContinuousLinearMap G (ξ ω)) :=
  chapter10_bootstrap_delta_method_linear (matrixContinuousLinearMap G) hT

/-- Hansen Theorem 10.6, Gaussian covariance specialization.

If the bootstrap linearized statistic converges weakly to `N(0, V)`, then its
matrix-derivative image converges weakly to `N(0, G V G')`, matching the
textbook covariance formula. -/
theorem chapter10_bootstrap_delta_method_gaussian
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) := by
  intro f
  have hlinear :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => matrixContinuousLinearMap G z) :=
    chapter10_bootstrap_delta_method_matrix_linear (G := G) hT
  have hmap :
      (multivariateGaussian (0 : EuclideanSpace ℝ d) V).map
          (matrixContinuousLinearMap G) =
        multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (map_matrix_multivariateGaussian
        (μ := (0 : EuclideanSpace ℝ d)) hV G)
  have htarget :
      ∫ z, f z ∂(multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) =
        ∫ z, f (matrixContinuousLinearMap G z)
          ∂(multivariateGaussian (0 : EuclideanSpace ℝ d) V) := by
    rw [← hmap]
    exact integral_map (matrixContinuousLinearMap G).continuous.aemeasurable
      f.continuous.aestronglyMeasurable
  simpa [htarget] using hlinear.tendsto_integral f

end BootstrapDeltaMethod

section SmoothFunctionBootstrapVariance

/-- Smooth-function plug-in covariance functional `Gᵀ V G`.

This is the covariance map in Hansen's smooth-function bootstrap delta-method
results, with `G` the Jacobian and `V` the covariance matrix of the underlying
moment/statistic. -/
noncomputable def smoothFunctionVarianceFunctional
    {d r : Type*} [Fintype d] [Fintype r]
    (G : Matrix d r ℝ) (V : Matrix d d ℝ) : Matrix r r ℝ :=
  Gᵀ * V * G

/-- The smooth-function plug-in covariance map is continuous in its Jacobian
and covariance inputs. -/
theorem smoothFunctionVarianceFunctional_continuous
    {d r : Type*} [Fintype d] [Fintype r] :
    Continuous (fun p : Matrix d r ℝ × Matrix d d ℝ =>
      smoothFunctionVarianceFunctional p.1 p.2) := by
  unfold smoothFunctionVarianceFunctional
  exact ((continuous_fst.matrix_transpose).matrix_mul continuous_snd).matrix_mul
    continuous_fst

/-- Hansen Theorem 10.8, plug-in covariance continuous-mapping bridge.

If the bootstrap Jacobian/covariance pair converges in bootstrap probability to
the population pair, then the smooth-function covariance plug-in
`Gstarᵀ Vstar Gstar` converges in bootstrap probability to `Gᵀ V G`.  The
concrete Theorem 10.8 constructors provide the joint bootstrap-probability
premise from the smooth-function model and the bootstrap WLLN/CLT layer. -/
theorem chapter10_bootstrap_smooth_variance_consistency
    {d r : Type*} [Fintype d] [Fintype r]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Gstar : ℕ → Ω → Ωs → Matrix d r ℝ}
    {Vstar : ℕ → Ω → Ωs → Matrix d d ℝ}
    {G : Matrix d r ℝ} {V : Matrix d d ℝ}
    (hGV :
      TendstoInBootstrapProbability μ Pstar
        (fun n ω ωs => (Gstar n ω ωs, Vstar n ω ωs))
        (fun _ => (G, V))) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gstar n ω ωs) (Vstar n ω ωs))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  TendstoInBootstrapProbability.continuousAt_const_comp
    (E := Matrix d r ℝ × Matrix d d ℝ)
    (F := Matrix r r ℝ)
    (Pstar := Pstar)
    (Zstar := fun n ω ωs => (Gstar n ω ωs, Vstar n ω ωs))
    (c := (G, V))
    (g := fun p => smoothFunctionVarianceFunctional p.1 p.2)
    hPstar hGV smoothFunctionVarianceFunctional_continuous.continuousAt

/-- Hansen Theorem 10.8, componentwise plug-in covariance bridge.

This wrapper packages the usual proof shape: establish separate bootstrap
convergence of the plug-in Jacobian and covariance inputs, combine them into a
joint convergence statement, then apply the smooth covariance CMT. -/
theorem chapter10_bootstrap_smooth_variance_consistency_of_components
    {d r : Type*} [Fintype d] [Fintype r]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Gstar : ℕ → Ω → Ωs → Matrix d r ℝ}
    {Vstar : ℕ → Ω → Ωs → Matrix d d ℝ}
    {G : Matrix d r ℝ} {V : Matrix d d ℝ}
    (hG :
      TendstoInBootstrapProbability μ Pstar Gstar (fun _ => G))
    (hV :
      TendstoInBootstrapProbability μ Pstar Vstar (fun _ => V)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gstar n ω ωs) (Vstar n ω ωs))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_bootstrap_smooth_variance_consistency hPstar
    (TendstoInBootstrapProbability.prodMk hPstar hG hV)

end SmoothFunctionBootstrapVariance

section BootstrapVariance

/-- Conditional bootstrap mean of a real statistic. -/
noncomputable def bootstrapMeanReal
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  (Pstar n ω)[Zstar n ω]

/-- Conditional bootstrap second moment of a real statistic. -/
noncomputable def bootstrapSecondMomentReal
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  (Pstar n ω)[(Zstar n ω) ^ 2]

/-- Conditional bootstrap variance of a real statistic. -/
noncomputable def bootstrapVarianceReal
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  Var[Zstar n ω; Pstar n ω]

/-- Conditional variance equals second moment minus squared conditional mean. -/
theorem bootstrapVarianceReal_eq_secondMoment_sub_mean_sq
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (n : ℕ) (ω : Ω) :
    bootstrapVarianceReal Pstar Zstar n ω =
      bootstrapSecondMomentReal Pstar Zstar n ω -
        (bootstrapMeanReal Pstar Zstar n ω) ^ 2 := by
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  simpa [bootstrapVarianceReal, bootstrapSecondMomentReal, bootstrapMeanReal]
    using (ProbabilityTheory.variance_eq_sub (μ := Pstar n ω) (X := Zstar n ω)
      (hZ n ω))

/-- Hansen Theorem 10.9, variance-consistency moment bridge.

If the conditional bootstrap first and second moments of a real statistic
converge in ordinary probability to the corresponding limit moments, then the
conditional bootstrap variance converges in probability to the variance
functional `m₂ - m²`.  The remaining Theorem 10.9 constructors show how
bootstrap distribution plus uniform square integrability imply these moment
premises, and how finite bootstrap replications estimate this conditional
variance. -/
theorem chapter10_bootstrap_variance_consistency_of_moment_convergence
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {m m₂ : ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanReal Pstar Zstar) atTop (fun _ => m))
    (hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentReal Pstar Zstar) atTop
        (fun _ => m₂)) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
      (fun _ => m₂ - m ^ 2) := by
  have hmean_sq :
      TendstoInMeasure μ
        (fun n ω => bootstrapMeanReal Pstar Zstar n ω *
          bootstrapMeanReal Pstar Zstar n ω)
        atTop (fun _ => m * m) :=
    TendstoInMeasure.mul_limits_real hmean hmean
  have hsecond0 := TendstoInMeasure.sub_limit_zero_real hsecond
  have hmean_sq0 := TendstoInMeasure.sub_limit_zero_real hmean_sq
  have hdiff0 :
      TendstoInMeasure μ
        (fun n ω =>
          (bootstrapSecondMomentReal Pstar Zstar n ω -
            bootstrapMeanReal Pstar Zstar n ω *
              bootstrapMeanReal Pstar Zstar n ω) -
            (m₂ - m * m))
        atTop (fun _ => 0) := by
    have hsub := TendstoInMeasure.sub_zero_real hsecond0 hmean_sq0
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hsub
    refine ae_of_all μ fun ω => ?_
    ring
  have hdiff :
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapSecondMomentReal Pstar Zstar n ω -
            bootstrapMeanReal Pstar Zstar n ω *
              bootstrapMeanReal Pstar Zstar n ω)
        atTop (fun _ => m₂ - m * m) :=
    TendstoInMeasure.of_sub_limit_zero_real hdiff0
  have hvar :
      TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
        (fun _ => m₂ - m * m) := by
    refine TendstoInMeasure.congr
      (f := fun n ω =>
        bootstrapSecondMomentReal Pstar Zstar n ω -
          bootstrapMeanReal Pstar Zstar n ω *
            bootstrapMeanReal Pstar Zstar n ω)
      (f' := bootstrapVarianceReal Pstar Zstar)
      (g := fun _ : Ω => m₂ - m * m)
      (g' := fun _ : Ω => m₂ - m * m)
      (fun n => ?_) EventuallyEq.rfl hdiff
    refine ae_of_all μ fun ω => ?_
    rw [bootstrapVarianceReal_eq_secondMoment_sub_mean_sq hPstar hZ]
    ring
  simpa [pow_two] using hvar

end BootstrapVariance

section BootstrapCovariance

/-- Conditional bootstrap mean vector of a finite-dimensional statistic. -/
noncomputable def bootstrapMeanVec
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → k → ℝ)
    (n : ℕ) (ω : Ω) : k → ℝ :=
  fun a => (Pstar n ω)[fun ωs => Zstar n ω ωs a]

/-- Conditional bootstrap cross-moment matrix of a finite-dimensional statistic. -/
noncomputable def bootstrapCrossMomentMat
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → k → ℝ)
    (n : ℕ) (ω : Ω) : Matrix k k ℝ :=
  fun a c => (Pstar n ω)[fun ωs => Zstar n ω ωs a * Zstar n ω ωs c]

/-- Moment-form conditional bootstrap covariance matrix. -/
noncomputable def bootstrapCovarianceMomentMat
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → k → ℝ)
    (n : ℕ) (ω : Ω) : Matrix k k ℝ :=
  fun a c =>
    bootstrapCrossMomentMat Pstar Zstar n ω a c -
      bootstrapMeanVec Pstar Zstar n ω a * bootstrapMeanVec Pstar Zstar n ω c

/-- Conditional bootstrap covariance matrix, stated directly with `cov`. -/
noncomputable def bootstrapCovarianceMat
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → k → ℝ)
    (n : ℕ) (ω : Ω) : Matrix k k ℝ :=
  fun a c => cov[fun ωs => Zstar n ω ωs a,
    fun ωs => Zstar n ω ωs c; Pstar n ω]

/-- Conditional covariance equals the moment-form covariance matrix. -/
theorem bootstrapCovarianceMat_eq_momentMat
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (n : ℕ) (ω : Ω) :
    bootstrapCovarianceMat Pstar Zstar n ω =
      bootstrapCovarianceMomentMat Pstar Zstar n ω := by
  ext a c
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  simpa [bootstrapCovarianceMat, bootstrapCovarianceMomentMat, bootstrapCrossMomentMat,
    bootstrapMeanVec, Pi.mul_apply] using
    (ProbabilityTheory.covariance_eq_sub (hZ n ω a) (hZ n ω c))

/-- Conditional bootstrap covariance moment bridge for two real coordinates. -/
theorem chapter10_bootstrap_covarianceReal_tendsto_of_moments
    {Pstar : ℕ → Ω → Measure Ωs} {Xstar Ystar : ℕ → Ω → Ωs → ℝ}
    {mX mY mXY : ℝ}
    (hmeanX :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[Xstar n ω])
        atTop (fun _ => mX))
    (hmeanY :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[Ystar n ω])
        atTop (fun _ => mY))
    (hcross :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs])
        atTop (fun _ => mXY)) :
    TendstoInMeasure μ
      (fun n ω =>
        (Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs] -
          (Pstar n ω)[Xstar n ω] * (Pstar n ω)[Ystar n ω])
      atTop (fun _ => mXY - mX * mY) := by
  have hmean_prod :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω)[Xstar n ω] * (Pstar n ω)[Ystar n ω])
        atTop (fun _ => mX * mY) :=
    TendstoInMeasure.mul_limits_real hmeanX hmeanY
  have hcross0 := TendstoInMeasure.sub_limit_zero_real hcross
  have hmean_prod0 := TendstoInMeasure.sub_limit_zero_real hmean_prod
  have hdiff0 :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs] -
            (Pstar n ω)[Xstar n ω] * (Pstar n ω)[Ystar n ω]) -
            (mXY - mX * mY))
        atTop (fun _ => 0) := by
    have hsub := TendstoInMeasure.sub_zero_real hcross0 hmean_prod0
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hsub
    exact ae_of_all μ fun ω => by ring
  exact TendstoInMeasure.of_sub_limit_zero_real hdiff0

/-- Conditional bootstrap covariance-matrix bridge from mean-vector and
cross-moment convergence. -/
theorem chapter10_bootstrap_covarianceMomentMat_tendsto_of_moments
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanVec Pstar Zstar) atTop (fun _ => m))
    (hcross :
      TendstoInMeasure μ (bootstrapCrossMomentMat Pstar Zstar) atTop
        (fun _ => M₂)) :
    TendstoInMeasure μ (bootstrapCovarianceMomentMat Pstar Zstar) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) := by
  refine tendstoInMeasure_pi (fun a => ?_)
  refine tendstoInMeasure_pi (fun c => ?_)
  have hentry :=
    chapter10_bootstrap_covarianceReal_tendsto_of_moments
      (μ := μ)
      (Pstar := Pstar)
      (Xstar := fun n ω ωs => Zstar n ω ωs a)
      (Ystar := fun n ω ωs => Zstar n ω ωs c)
      (mX := m a) (mY := m c) (mXY := M₂ a c)
      (by
        simpa [bootstrapMeanVec] using
          TendstoInMeasure.pi_apply hmean a)
      (by
        simpa [bootstrapMeanVec] using
          TendstoInMeasure.pi_apply hmean c)
      (by
        simpa [bootstrapCrossMomentMat] using
          TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hcross a) c)
  simpa [bootstrapCovarianceMomentMat, bootstrapMeanVec, bootstrapCrossMomentMat]
    using hentry

/-- Conditional bootstrap covariance matrix bridge, stated for `cov`. -/
theorem chapter10_bootstrap_covarianceMat_tendsto_of_moments
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanVec Pstar Zstar) atTop (fun _ => m))
    (hcross :
      TendstoInMeasure μ (bootstrapCrossMomentMat Pstar Zstar) atTop
        (fun _ => M₂)) :
    TendstoInMeasure μ (bootstrapCovarianceMat Pstar Zstar) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) := by
  have hmoment :=
    chapter10_bootstrap_covarianceMomentMat_tendsto_of_moments
      (μ := μ) hmean hcross
  refine TendstoInMeasure.congr
    (f := bootstrapCovarianceMomentMat Pstar Zstar)
    (f' := bootstrapCovarianceMat Pstar Zstar)
    (g := fun _ : Ω => fun a c => M₂ a c - m a * m c)
    (g' := fun _ : Ω => fun a c => M₂ a c - m a * m c)
    (fun n => ?_) EventuallyEq.rfl hmoment
  exact ae_of_all μ fun ω =>
    (bootstrapCovarianceMat_eq_momentMat
      (Pstar := Pstar) (Zstar := Zstar) hPstar hZ n ω).symm

/-- Hansen's trimmed bootstrap statistic `Z** = Z* 1{‖Z*‖ ≤ τ}`. -/
noncomputable def trimmedBootstrapStatistic
    {k : Type*} [Fintype k]
    (Zstar : ℕ → Ω → Ωs → k → ℝ) (τ : ℕ → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Ωs) : k → ℝ :=
  if ‖Zstar n ω ωs‖ ≤ τ n then Zstar n ω ωs else 0

/-- Conditional covariance matrix of Hansen's trimmed bootstrap statistic. -/
noncomputable def trimmedBootstrapCovarianceMat
    {k : Type*} [Fintype k]
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → k → ℝ)
    (τ : ℕ → ℝ) (n : ℕ) (ω : Ω) : Matrix k k ℝ :=
  bootstrapCovarianceMat Pstar (trimmedBootstrapStatistic Zstar τ) n ω

/-- Hansen Theorem 10.12, trimmed conditional covariance moment bridge.

For the trimmed statistic `Z** = Z* 1{‖Z*‖ ≤ τ}`, convergence of its conditional
mean vector and cross-moment matrix implies convergence of its conditional
covariance matrix.  The smooth-model proof of Theorem 10.12 supplies these
moment premises by showing the trimming is asymptotically negligible and the
trimmed sequence is uniformly square integrable. -/
theorem chapter10_trimmedBootstrapVariance_tendsto_of_moments
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {τ : ℕ → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ :
      ∀ n ω a,
        MemLp (fun ωs => trimmedBootstrapStatistic Zstar τ n ω ωs a) 2
          (Pstar n ω))
    {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ
        (bootstrapMeanVec Pstar (trimmedBootstrapStatistic Zstar τ))
        atTop (fun _ => m))
    (hcross :
      TendstoInMeasure μ
        (bootstrapCrossMomentMat Pstar (trimmedBootstrapStatistic Zstar τ))
        atTop (fun _ => M₂)) :
    TendstoInMeasure μ (trimmedBootstrapCovarianceMat Pstar Zstar τ) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) := by
  simpa [trimmedBootstrapCovarianceMat] using
    chapter10_bootstrap_covarianceMat_tendsto_of_moments
      (μ := μ) (Pstar := Pstar)
      (Zstar := trimmedBootstrapStatistic Zstar τ)
      hPstar hZ hmean hcross

/-- Theorem 10.12 zero-mean covariance specialization.

In the asymptotically centered case, if the trimmed conditional mean converges
to zero and the trimmed conditional cross moment converges to `V`, then the
trimmed conditional covariance converges to `V`. -/
theorem chapter10_trimmedBootstrapVariance_tendsto
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {τ : ℕ → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ :
      ∀ n ω a,
        MemLp (fun ωs => trimmedBootstrapStatistic Zstar τ n ω ωs a) 2
          (Pstar n ω))
    {V : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ
        (bootstrapMeanVec Pstar (trimmedBootstrapStatistic Zstar τ))
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ
        (bootstrapCrossMomentMat Pstar (trimmedBootstrapStatistic Zstar τ))
        atTop (fun _ => V)) :
    TendstoInMeasure μ (trimmedBootstrapCovarianceMat Pstar Zstar τ) atTop
      (fun _ => V) := by
  have h :=
    chapter10_trimmedBootstrapVariance_tendsto_of_moments
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
      hPstar hZ hmean hcross
  simpa using h

end BootstrapCovariance

section FiniteReplicationVariance

/-- Mean across `B` finite bootstrap replications of a real statistic. -/
noncomputable def finiteReplicationMeanReal
    (Z : ℕ → ℕ → Ω → ℝ) (B : ℕ) (ω : Ω) : ℝ :=
  (B : ℝ)⁻¹ * ∑ b ∈ Finset.range B, Z B b ω

/-- Second moment across `B` finite bootstrap replications of a real statistic. -/
noncomputable def finiteReplicationSecondMomentReal
    (Z : ℕ → ℕ → Ω → ℝ) (B : ℕ) (ω : Ω) : ℝ :=
  (B : ℝ)⁻¹ * ∑ b ∈ Finset.range B, (Z B b ω) ^ 2

/-- Cross moment across `B` finite bootstrap replications of two real statistics. -/
noncomputable def finiteReplicationCrossMomentReal
    (X Y : ℕ → ℕ → Ω → ℝ) (B : ℕ) (ω : Ω) : ℝ :=
  (B : ℝ)⁻¹ * ∑ b ∈ Finset.range B, X B b ω * Y B b ω

/-- Finite-sample degrees-of-freedom correction `B / (B - 1)`. -/
noncomputable def finiteReplicationVarianceCorrection (B : ℕ) : ℝ :=
  (B : ℝ) / ((B : ℝ) - 1)

/-- Moment-form finite-replication variance estimator for a real statistic. -/
noncomputable def finiteReplicationVarianceMomentReal
    (Z : ℕ → ℕ → Ω → ℝ) (B : ℕ) (ω : Ω) : ℝ :=
  finiteReplicationVarianceCorrection B *
    (finiteReplicationSecondMomentReal Z B ω -
      (finiteReplicationMeanReal Z B ω) ^ 2)

/-- Moment-form finite-replication covariance estimator for two real statistics. -/
noncomputable def finiteReplicationCovarianceMomentReal
    (X Y : ℕ → ℕ → Ω → ℝ) (B : ℕ) (ω : Ω) : ℝ :=
  finiteReplicationVarianceCorrection B *
    (finiteReplicationCrossMomentReal X Y B ω -
      finiteReplicationMeanReal X B ω * finiteReplicationMeanReal Y B ω)

/-- Centered finite-replication covariance estimator for two real statistics. -/
noncomputable def finiteReplicationCovarianceCenteredReal
    (X Y : ℕ → ℕ → Ω → ℝ) (B : ℕ) (ω : Ω) : ℝ :=
  (((B : ℝ) - 1)⁻¹) *
    ∑ b ∈ Finset.range B,
      (X B b ω - finiteReplicationMeanReal X B ω) *
        (Y B b ω - finiteReplicationMeanReal Y B ω)

/-- Mean vector across `B` finite bootstrap replications. -/
noncomputable def finiteReplicationMeanVec
    (Z : ℕ → ℕ → Ω → k → ℝ) (B : ℕ) (ω : Ω) : k → ℝ :=
  fun a => (B : ℝ)⁻¹ * ∑ b ∈ Finset.range B, Z B b ω a

/-- Cross-moment matrix across `B` finite bootstrap replications. -/
noncomputable def finiteReplicationCrossMomentMat
    (Z : ℕ → ℕ → Ω → k → ℝ) (B : ℕ) (ω : Ω) : Matrix k k ℝ :=
  fun a c => (B : ℝ)⁻¹ * ∑ b ∈ Finset.range B, Z B b ω a * Z B b ω c

/-- Moment-form finite-replication covariance matrix estimator. -/
noncomputable def finiteReplicationCovarianceMomentMat
    (Z : ℕ → ℕ → Ω → k → ℝ) (B : ℕ) (ω : Ω) : Matrix k k ℝ :=
  fun a c =>
    finiteReplicationVarianceCorrection B *
      (finiteReplicationCrossMomentMat Z B ω a c -
        finiteReplicationMeanVec Z B ω a * finiteReplicationMeanVec Z B ω c)

/-- Centered finite-replication covariance matrix estimator. -/
noncomputable def finiteReplicationCovarianceCenteredMat
    (Z : ℕ → ℕ → Ω → k → ℝ) (B : ℕ) (ω : Ω) : Matrix k k ℝ :=
  fun a c =>
    (((B : ℝ) - 1)⁻¹) *
      ∑ b ∈ Finset.range B,
        (Z B b ω a - finiteReplicationMeanVec Z B ω a) *
          (Z B b ω c - finiteReplicationMeanVec Z B ω c)

/-- The finite-replication degrees-of-freedom correction `B / (B - 1)`
tends to `1`. -/
theorem finiteReplicationVarianceCorrection_tendsto_one :
    Tendsto finiteReplicationVarianceCorrection atTop (𝓝 1) := by
  let r : ℕ → ℝ := finiteReplicationVarianceCorrection
  have hB : Tendsto (fun B : ℕ => (B : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun B : ℕ => (B : ℝ) - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(1 : ℝ)) hB
  have hrSub : Tendsto (fun B => r B - 1) atTop (𝓝 0) := by
    have hsmall : Tendsto (fun B : ℕ => (1 : ℝ) / ((B : ℝ) - 1))
        atTop (𝓝 0) :=
      hden.const_div_atTop (1 : ℝ)
    have heq : (fun B => r B - 1) =ᶠ[atTop]
        (fun B : ℕ => (1 : ℝ) / ((B : ℝ) - 1)) := by
      filter_upwards [eventually_gt_atTop 1] with B hB_gt
      have hden_ne : (B : ℝ) - 1 ≠ 0 := by
        have hgt : (1 : ℝ) < (B : ℝ) := by
          exact_mod_cast hB_gt
        linarith
      dsimp [r, finiteReplicationVarianceCorrection]
      field_simp [hden_ne]
      ring
    rw [tendsto_congr' heq]
    exact hsmall
  have hadd := hrSub.add_const 1
  simpa [r, finiteReplicationVarianceCorrection, sub_eq_add_neg, add_assoc,
    add_comm, add_left_comm] using hadd

/-- The centered finite-replication covariance formula equals its moment form
whenever the number of replications is greater than one. -/
theorem finiteReplicationCovarianceCenteredReal_eq_momentReal
    {X Y : ℕ → ℕ → Ω → ℝ} {B : ℕ} (hB : 1 < B) (ω : Ω) :
    finiteReplicationCovarianceCenteredReal X Y B ω =
      finiteReplicationCovarianceMomentReal X Y B ω := by
  have hB0_nat : B ≠ 0 := Nat.ne_of_gt (lt_trans zero_lt_one hB)
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB0_nat
  have hden_ne : (B : ℝ) - 1 ≠ 0 := by
    have hgt : (1 : ℝ) < (B : ℝ) := by exact_mod_cast hB
    linarith
  have hsumX :
      ∑ b ∈ Finset.range B, X B b ω =
        (B : ℝ) * finiteReplicationMeanReal X B ω := by
    unfold finiteReplicationMeanReal
    field_simp [hB0]
  have hsumY :
      ∑ b ∈ Finset.range B, Y B b ω =
        (B : ℝ) * finiteReplicationMeanReal Y B ω := by
    unfold finiteReplicationMeanReal
    field_simp [hB0]
  have hcenter_sum :
      ∑ b ∈ Finset.range B,
          (X B b ω - finiteReplicationMeanReal X B ω) *
            (Y B b ω - finiteReplicationMeanReal Y B ω) =
        ∑ b ∈ Finset.range B, X B b ω * Y B b ω -
          (B : ℝ) * finiteReplicationMeanReal X B ω *
            finiteReplicationMeanReal Y B ω := by
    calc
      ∑ b ∈ Finset.range B,
          (X B b ω - finiteReplicationMeanReal X B ω) *
            (Y B b ω - finiteReplicationMeanReal Y B ω)
          =
        ∑ b ∈ Finset.range B,
          (X B b ω * Y B b ω -
            X B b ω * finiteReplicationMeanReal Y B ω -
            finiteReplicationMeanReal X B ω * Y B b ω +
            finiteReplicationMeanReal X B ω *
              finiteReplicationMeanReal Y B ω) := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          ring
      _ =
        ∑ b ∈ Finset.range B, X B b ω * Y B b ω -
          (∑ b ∈ Finset.range B, X B b ω) *
            finiteReplicationMeanReal Y B ω -
          finiteReplicationMeanReal X B ω *
            (∑ b ∈ Finset.range B, Y B b ω) +
          (B : ℝ) * finiteReplicationMeanReal X B ω *
            finiteReplicationMeanReal Y B ω := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_mul, Finset.mul_sum, mul_assoc]
      _ =
        ∑ b ∈ Finset.range B, X B b ω * Y B b ω -
          (B : ℝ) * finiteReplicationMeanReal X B ω *
            finiteReplicationMeanReal Y B ω := by
          rw [hsumX, hsumY]
          ring
  unfold finiteReplicationCovarianceCenteredReal
  unfold finiteReplicationCovarianceMomentReal
  unfold finiteReplicationCrossMomentReal
  unfold finiteReplicationVarianceCorrection
  rw [hcenter_sum]
  field_simp [hB0, hden_ne]

/-- Matrix form of `finiteReplicationCovarianceCenteredReal_eq_momentReal`. -/
theorem finiteReplicationCovarianceCenteredMat_eq_momentMat
    {k : Type*} {Z : ℕ → ℕ → Ω → k → ℝ} {B : ℕ}
    (hB : 1 < B) (ω : Ω) :
    finiteReplicationCovarianceCenteredMat Z B ω =
      finiteReplicationCovarianceMomentMat Z B ω := by
  ext a c
  simpa [finiteReplicationCovarianceCenteredMat, finiteReplicationCovarianceMomentMat,
    finiteReplicationMeanVec, finiteReplicationCrossMomentMat,
    finiteReplicationMeanReal, finiteReplicationCrossMomentReal] using
    finiteReplicationCovarianceCenteredReal_eq_momentReal
      (X := fun B b ω => Z B b ω a)
      (Y := fun B b ω => Z B b ω c) hB ω

/-- Hansen Theorem 10.11, finite-replication variance moment bridge.

If the finite-`B` replication mean and second moment converge in probability to
their conditional limits, then the moment-form finite-replication variance
converges in probability to `m₂ - m²`.  In applications, the moment premises are
the bootstrap WLLN for bounded trimmed replications. -/
theorem chapter10_finiteReplicationVariance_tendsto_of_moments
    {Z : ℕ → ℕ → Ω → ℝ} {m m₂ : ℝ}
    (hmean :
      TendstoInMeasure μ (finiteReplicationMeanReal Z) atTop (fun _ => m))
    (hsecond :
      TendstoInMeasure μ (finiteReplicationSecondMomentReal Z) atTop
        (fun _ => m₂)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Z) atTop
      (fun _ => m₂ - m ^ 2) := by
  have hmean_sq :
      TendstoInMeasure μ
        (fun B ω => finiteReplicationMeanReal Z B ω *
          finiteReplicationMeanReal Z B ω)
        atTop (fun _ => m * m) :=
    TendstoInMeasure.mul_limits_real hmean hmean
  have hsecond0 := TendstoInMeasure.sub_limit_zero_real hsecond
  have hmean_sq0 := TendstoInMeasure.sub_limit_zero_real hmean_sq
  have hdiff0 :
      TendstoInMeasure μ
        (fun B ω =>
          (finiteReplicationSecondMomentReal Z B ω -
            finiteReplicationMeanReal Z B ω *
              finiteReplicationMeanReal Z B ω) -
            (m₂ - m * m))
        atTop (fun _ => 0) := by
    have hsub := TendstoInMeasure.sub_zero_real hsecond0 hmean_sq0
    refine TendstoInMeasure.congr (fun B => ?_) EventuallyEq.rfl hsub
    refine ae_of_all μ fun ω => ?_
    ring
  have hdiff :
      TendstoInMeasure μ
        (fun B ω =>
          finiteReplicationSecondMomentReal Z B ω -
            finiteReplicationMeanReal Z B ω *
              finiteReplicationMeanReal Z B ω)
        atTop (fun _ => m₂ - m * m) :=
    TendstoInMeasure.of_sub_limit_zero_real hdiff0
  have hfactor :
      TendstoInMeasure μ
        (fun B (_ : Ω) => finiteReplicationVarianceCorrection B)
        atTop (fun _ => 1) :=
    tendstoInMeasure_const_real (μ := μ)
      finiteReplicationVarianceCorrection_tendsto_one
  have hprod :
      TendstoInMeasure μ
        (fun B ω =>
          finiteReplicationVarianceCorrection B *
            (finiteReplicationSecondMomentReal Z B ω -
              (finiteReplicationMeanReal Z B ω) ^ 2))
        atTop (fun _ => 1 * (m₂ - m * m)) := by
    simpa [pow_two] using TendstoInMeasure.mul_limits_real hfactor hdiff
  refine TendstoInMeasure.congr
    (f := fun B ω =>
      finiteReplicationVarianceCorrection B *
        (finiteReplicationSecondMomentReal Z B ω -
          (finiteReplicationMeanReal Z B ω) ^ 2))
    (f' := finiteReplicationVarianceMomentReal Z)
    (g := fun _ : Ω => 1 * (m₂ - m * m))
    (g' := fun _ : Ω => m₂ - m ^ 2)
    (fun B => ?_) ?_ hprod
  · exact ae_of_all μ fun ω => by
      simp [finiteReplicationVarianceMomentReal]
  · exact ae_of_all μ fun _ => by ring

/-- Finite-replication covariance moment bridge for two real statistics.

If the finite-`B` replication means of `X` and `Y` and their cross moment
converge in probability, then the moment-form finite-replication covariance
converges in probability to `mXY - mX * mY`. -/
theorem chapter10_finiteReplicationCovarianceReal_tendsto_of_moments
    {X Y : ℕ → ℕ → Ω → ℝ} {mX mY mXY : ℝ}
    (hmeanX :
      TendstoInMeasure μ (finiteReplicationMeanReal X) atTop (fun _ => mX))
    (hmeanY :
      TendstoInMeasure μ (finiteReplicationMeanReal Y) atTop (fun _ => mY))
    (hcross :
      TendstoInMeasure μ (finiteReplicationCrossMomentReal X Y) atTop
        (fun _ => mXY)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentReal X Y) atTop
      (fun _ => mXY - mX * mY) := by
  have hmean_prod :
      TendstoInMeasure μ
        (fun B ω => finiteReplicationMeanReal X B ω *
          finiteReplicationMeanReal Y B ω)
        atTop (fun _ => mX * mY) :=
    TendstoInMeasure.mul_limits_real hmeanX hmeanY
  have hcross0 := TendstoInMeasure.sub_limit_zero_real hcross
  have hmean_prod0 := TendstoInMeasure.sub_limit_zero_real hmean_prod
  have hdiff0 :
      TendstoInMeasure μ
        (fun B ω =>
          (finiteReplicationCrossMomentReal X Y B ω -
            finiteReplicationMeanReal X B ω *
              finiteReplicationMeanReal Y B ω) -
            (mXY - mX * mY))
        atTop (fun _ => 0) := by
    have hsub := TendstoInMeasure.sub_zero_real hcross0 hmean_prod0
    refine TendstoInMeasure.congr (fun B => ?_) EventuallyEq.rfl hsub
    exact ae_of_all μ fun ω => by ring
  have hdiff :
      TendstoInMeasure μ
        (fun B ω =>
          finiteReplicationCrossMomentReal X Y B ω -
            finiteReplicationMeanReal X B ω *
              finiteReplicationMeanReal Y B ω)
        atTop (fun _ => mXY - mX * mY) :=
    TendstoInMeasure.of_sub_limit_zero_real hdiff0
  have hfactor :
      TendstoInMeasure μ
        (fun B (_ : Ω) => finiteReplicationVarianceCorrection B)
        atTop (fun _ => 1) :=
    tendstoInMeasure_const_real (μ := μ)
      finiteReplicationVarianceCorrection_tendsto_one
  have hprod :
      TendstoInMeasure μ
        (fun B ω =>
          finiteReplicationVarianceCorrection B *
            (finiteReplicationCrossMomentReal X Y B ω -
              finiteReplicationMeanReal X B ω *
                finiteReplicationMeanReal Y B ω))
        atTop (fun _ => 1 * (mXY - mX * mY)) :=
    TendstoInMeasure.mul_limits_real hfactor hdiff
  simpa [finiteReplicationCovarianceMomentReal] using hprod

/-- Hansen Theorem 10.11, finite-dimensional covariance-matrix moment bridge.

If the finite-`B` replication mean vector and cross-moment matrix converge in
probability, then the moment-form finite-replication covariance matrix
converges in probability to the corresponding covariance matrix `M₂ - mm'`.
The bounded-trimmed bootstrap WLLN supplies these moment premises in the
textbook application. -/
theorem chapter10_finiteReplicationCovarianceMat_tendsto_of_moments
    {k : Type*} [Fintype k]
    {Z : ℕ → ℕ → Ω → k → ℝ} {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ (finiteReplicationMeanVec Z) atTop (fun _ => m))
    (hcross :
      TendstoInMeasure μ (finiteReplicationCrossMomentMat Z) atTop
        (fun _ => M₂)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Z) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) := by
  refine tendstoInMeasure_pi (fun a => ?_)
  refine tendstoInMeasure_pi (fun c => ?_)
  have hentry :=
    chapter10_finiteReplicationCovarianceReal_tendsto_of_moments
      (μ := μ)
      (X := fun B b ω => Z B b ω a)
      (Y := fun B b ω => Z B b ω c)
      (mX := m a) (mY := m c) (mXY := M₂ a c)
      (by
        simpa [finiteReplicationMeanVec, finiteReplicationMeanReal] using
          TendstoInMeasure.pi_apply hmean a)
      (by
        simpa [finiteReplicationMeanVec, finiteReplicationMeanReal] using
          TendstoInMeasure.pi_apply hmean c)
      (by
        simpa [finiteReplicationCrossMomentMat,
          finiteReplicationCrossMomentReal] using
          TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hcross a) c)
  simpa [finiteReplicationCovarianceMomentMat, finiteReplicationMeanVec,
    finiteReplicationCrossMomentMat, finiteReplicationCovarianceMomentReal,
    finiteReplicationMeanReal, finiteReplicationCrossMomentReal] using hentry

/-- Textbook-centered finite-replication covariance bridge for two real
statistics.

This is the same convergence result as
`chapter10_finiteReplicationCovarianceReal_tendsto_of_moments`, but stated for
the centered `1 / (B - 1) ∑ (X_b - Xbar)(Y_b - Ybar)` estimator. -/
theorem chapter10_finiteReplicationCovarianceCenteredReal_tendsto_of_moments
    {X Y : ℕ → ℕ → Ω → ℝ} {mX mY mXY : ℝ}
    (hmeanX :
      TendstoInMeasure μ (finiteReplicationMeanReal X) atTop (fun _ => mX))
    (hmeanY :
      TendstoInMeasure μ (finiteReplicationMeanReal Y) atTop (fun _ => mY))
    (hcross :
      TendstoInMeasure μ (finiteReplicationCrossMomentReal X Y) atTop
        (fun _ => mXY)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredReal X Y) atTop
      (fun _ => mXY - mX * mY) := by
  have hmoment :=
    chapter10_finiteReplicationCovarianceReal_tendsto_of_moments
      (μ := μ) hmeanX hmeanY hcross
  refine TendstoInMeasure.congr'
    (f := finiteReplicationCovarianceMomentReal X Y)
    (f' := finiteReplicationCovarianceCenteredReal X Y)
    (g := fun _ : Ω => mXY - mX * mY)
    (g' := fun _ : Ω => mXY - mX * mY)
    ?_ EventuallyEq.rfl hmoment
  filter_upwards [eventually_gt_atTop 1] with B hB
  exact ae_of_all μ fun ω =>
    (finiteReplicationCovarianceCenteredReal_eq_momentReal
      (X := X) (Y := Y) hB ω).symm

/-- Hansen Theorem 10.11, textbook-centered finite-dimensional covariance
bridge.

This wrapper states the finite-replication covariance convergence for Hansen's
centered estimator `1 / (B - 1) ∑ (Z_b - Zbar)(Z_b - Zbar)'`, using the exact
centered/moment-form identity and the finite-dimensional moment bridge. -/
theorem chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_moments
    {k : Type*} [Fintype k]
    {Z : ℕ → ℕ → Ω → k → ℝ} {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ (finiteReplicationMeanVec Z) atTop (fun _ => m))
    (hcross :
      TendstoInMeasure μ (finiteReplicationCrossMomentMat Z) atTop
        (fun _ => M₂)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Z) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) := by
  have hmoment :=
    chapter10_finiteReplicationCovarianceMat_tendsto_of_moments
      (μ := μ) hmean hcross
  refine TendstoInMeasure.congr'
    (f := finiteReplicationCovarianceMomentMat Z)
    (f' := finiteReplicationCovarianceCenteredMat Z)
    (g := fun _ : Ω => fun a c => M₂ a c - m a * m c)
    (g' := fun _ : Ω => fun a c => M₂ a c - m a * m c)
    ?_ EventuallyEq.rfl hmoment
  filter_upwards [eventually_gt_atTop 1] with B hB
  exact ae_of_all μ fun ω =>
    (finiteReplicationCovarianceCenteredMat_eq_momentMat
      (Z := Z) hB ω).symm

end FiniteReplicationVariance

section PercentileIntervals

/-- Hansen percentile confidence interval event, `qLower <= θ <= qUpper`. -/
def percentileCIEvent (θ qLower qUpper : ℝ) : Prop :=
  qLower ≤ θ ∧ θ ≤ qUpper

/-- Three-coordinate statistic used in the percentile-interval coverage proof:

* coordinate `0`: `aₙ(θhatₙ - θ)`;
* coordinate `1`: `aₙ(q*_{α/2,n} - θhatₙ)`;
* coordinate `2`: `aₙ(q*_{1-α/2,n} - θhatₙ)`.

The confidence event is the lower/upper half-space intersection encoded by
`percentileCoverageSet`. -/
noncomputable def percentileCoverageVector
    (a : ℕ → ℝ) (θ : ℝ) (θhat qLower qUpper : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then a n * (θhat n ω - θ)
    else if i = 1 then a n * (qLower n ω - θhat n ω)
    else a n * (qUpper n ω - θhat n ω)

/-- Limit vector for the percentile-interval coverage proof. -/
noncomputable def percentileCoverageLimitVector
    (ξ : Ωlim → ℝ) (qLower qUpper : ℝ) (ω : Ωlim) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then ξ ω
    else if i = 1 then qLower
    else qUpper

/-- Limit event corresponding to percentile-interval coverage:
`qLower <= -ξ <= qUpper`. -/
def percentileCoverageSet : Set (Fin 3 → ℝ) :=
  {z | z 1 ≤ -z 0 ∧ -z 0 ≤ z 2}

theorem isClosed_percentileCoverageSet : IsClosed percentileCoverageSet := by
  have hleft : IsClosed {z : Fin 3 → ℝ | z 1 ≤ -z 0} :=
    isClosed_le (continuous_apply 1) ((continuous_apply 0).neg)
  have hright : IsClosed {z : Fin 3 → ℝ | -z 0 ≤ z 2} :=
    isClosed_le ((continuous_apply 0).neg) (continuous_apply 2)
  simpa [percentileCoverageSet] using hleft.inter hright

theorem percentileCoverageVector_mem_set_iff
    {a : ℕ → ℝ} {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {n : ℕ} {ω : Ω} (ha : 0 < a n) :
    percentileCoverageVector a θ θhat qLower qUpper n ω ∈ percentileCoverageSet ↔
      percentileCIEvent θ (qLower n ω) (qUpper n ω) := by
  change
    (a n * (qLower n ω - θhat n ω) ≤ -(a n * (θhat n ω - θ)) ∧
        -(a n * (θhat n ω - θ)) ≤ a n * (qUpper n ω - θhat n ω)) ↔
      qLower n ω ≤ θ ∧ θ ≤ qUpper n ω
  constructor
  · intro h
    constructor <;> nlinarith [ha, h.1, h.2]
  · intro h
    constructor <;> nlinarith [ha, h.1, h.2]

/-- Hansen Theorem 10.13, percentile-interval coverage bridge.

If the scaled estimator error and the scaled bootstrap percentile endpoints
jointly converge to `(ξ, qL, qU)`, and the limiting coverage boundary has zero
probability, then the percentile interval coverage converges to
`P[qL <= -ξ <= qU]`.  Hansen's symmetric continuous-limit conclusion
`1 - α` is obtained by instantiating this bridge with the appropriate
bootstrap quantile limits and symmetry identity for the limit law. -/
theorem chapter10_percentileCI_coverage_tendsto_of_joint_quantile_limit
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ}
    (hjoint :
      TendstoInDistribution
        (percentileCoverageVector a θ θhat qLower qUpper)
        atTop
        (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (percentileCoverageLimitVector ξ qLowerLim qUpperLim))
        (frontier percentileCoverageSet) = 0) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop
      (𝓝 ((ν.map (percentileCoverageLimitVector ξ qLowerLim qUpperLim))
        percentileCoverageSet)) := by
  have hset_meas : MeasurableSet percentileCoverageSet :=
    isClosed_percentileCoverageSet.measurableSet
  have hcoverage :=
    TendstoInDistribution.tendsto_measure_preimage_of_null_frontier
      (h := hjoint) hset_meas hfrontier
  have hseq_eq :
      (fun n =>
        μ {ω | percentileCoverageVector a θ θhat qLower qUpper n ω ∈
          percentileCoverageSet}) =
        fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)} := by
    funext n
    congr 1
    ext ω
    exact percentileCoverageVector_mem_set_iff (Ω := Ω) (ha n)
  simpa [hseq_eq] using hcoverage

/-- Calibrated percentile-interval coverage bridge. -/
theorem chapter10_percentileCI_coverage_tendsto
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (percentileCoverageVector a θ θhat qLower qUpper)
        atTop
        (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (percentileCoverageLimitVector ξ qLowerLim qUpperLim))
        (frontier percentileCoverageSet) = 0)
    (hcoverage :
      (ν.map (percentileCoverageLimitVector ξ qLowerLim qUpperLim))
        percentileCoverageSet = coverage) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  simpa [hcoverage] using
    chapter10_percentileCI_coverage_tendsto_of_joint_quantile_limit
      (μ := μ) (ν := ν) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      hjoint hfrontier

end PercentileIntervals

section PercentileTIntervals

/-- Percentile-`t` statistic `T = (θhat - θ) / se`. -/
noncomputable def percentileTStatistic (θ θhat se : ℝ) : ℝ :=
  (θhat - θ) / se

/-- Hansen percentile-`t` confidence interval event:
`θhat - se * qUpper <= θ <= θhat - se * qLower`. -/
def percentileTCIEvent (θ θhat se qLower qUpper : ℝ) : Prop :=
  θhat - se * qUpper ≤ θ ∧ θ ≤ θhat - se * qLower

/-- Three-coordinate statistic used in the percentile-`t` coverage proof:

* coordinate `0`: sample t-ratio `Tₙ`;
* coordinate `1`: lower bootstrap t-ratio quantile `q*_{α/2,n}`;
* coordinate `2`: upper bootstrap t-ratio quantile `q*_{1-α/2,n}`. -/
noncomputable def percentileTCoverageVector
    (θ : ℝ) (θhat se qLower qUpper : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then percentileTStatistic θ (θhat n ω) (se n ω)
    else if i = 1 then qLower n ω
    else qUpper n ω

/-- Limit vector for the percentile-`t` coverage proof. -/
noncomputable def percentileTCoverageLimitVector
    (ξ : Ωlim → ℝ) (qLower qUpper : ℝ) (ω : Ωlim) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then ξ ω
    else if i = 1 then qLower
    else qUpper

/-- Limit event corresponding to percentile-`t` coverage:
`qLower <= ξ <= qUpper`. -/
def percentileTCoverageSet : Set (Fin 3 → ℝ) :=
  {z | z 1 ≤ z 0 ∧ z 0 ≤ z 2}

theorem isClosed_percentileTCoverageSet : IsClosed percentileTCoverageSet := by
  have hleft : IsClosed {z : Fin 3 → ℝ | z 1 ≤ z 0} :=
    isClosed_le (continuous_apply 1) (continuous_apply 0)
  have hright : IsClosed {z : Fin 3 → ℝ | z 0 ≤ z 2} :=
    isClosed_le (continuous_apply 0) (continuous_apply 2)
  simpa [percentileTCoverageSet] using hleft.inter hright

/-- Positive standard errors turn Hansen's percentile-`t` interval event into
the t-ratio event `qLower <= T <= qUpper`. -/
theorem percentileTCIEvent_iff_tstat_between
    {θ θhat se qLower qUpper : ℝ} (hse : 0 < se) :
    percentileTCIEvent θ θhat se qLower qUpper ↔
      qLower ≤ percentileTStatistic θ θhat se ∧
        percentileTStatistic θ θhat se ≤ qUpper := by
  constructor
  · intro h
    constructor
    · have hmul : qLower * se ≤ θhat - θ := by nlinarith [h.2]
      exact (le_div_iff₀ hse).2 (by simpa [mul_comm] using hmul)
    · have hmul : θhat - θ ≤ qUpper * se := by nlinarith [h.1]
      exact (div_le_iff₀ hse).2 (by simpa [mul_comm] using hmul)
  · intro h
    constructor
    · have hmul : θhat - θ ≤ qUpper * se := by
        simpa [percentileTStatistic, mul_comm] using (div_le_iff₀ hse).1 h.2
      nlinarith
    · have hmul : qLower * se ≤ θhat - θ := by
        simpa [percentileTStatistic, mul_comm] using (le_div_iff₀ hse).1 h.1
      nlinarith

theorem percentileTCoverageVector_mem_set_iff
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {n : ℕ} {ω : Ω} (hse : 0 < se n ω) :
    percentileTCoverageVector θ θhat se qLower qUpper n ω ∈
        percentileTCoverageSet ↔
      percentileTCIEvent θ (θhat n ω) (se n ω) (qLower n ω) (qUpper n ω) := by
  change
    (qLower n ω ≤ percentileTStatistic θ (θhat n ω) (se n ω) ∧
        percentileTStatistic θ (θhat n ω) (se n ω) ≤ qUpper n ω) ↔
      percentileTCIEvent θ (θhat n ω) (se n ω) (qLower n ω) (qUpper n ω)
  exact (percentileTCIEvent_iff_tstat_between hse).symm

/-- Hansen Theorem 10.14, percentile-`t` interval coverage bridge.

If the sample t-ratio and bootstrap percentile-`t` critical values jointly
converge to `(ξ, qL, qU)`, and the limiting coverage boundary has zero
probability, then percentile-`t` interval coverage converges to
`P[qL <= ξ <= qU]`. Hansen's first-order validity conclusion `1 - α` is
obtained by instantiating this bridge with the bootstrap quantile limits from
(10.31). -/
theorem chapter10_percentileTCI_coverage_tendsto_of_joint_quantile_limit
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (hjoint :
      TendstoInDistribution
        (percentileTCoverageVector θ θhat se qLower qUpper)
        atTop
        (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (percentileTCoverageLimitVector ξ qLowerLim qUpperLim))
        (frontier percentileTCoverageSet) = 0) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop
      (𝓝 ((ν.map (percentileTCoverageLimitVector ξ qLowerLim qUpperLim))
        percentileTCoverageSet)) := by
  have hset_meas : MeasurableSet percentileTCoverageSet :=
    isClosed_percentileTCoverageSet.measurableSet
  have hcoverage :=
    TendstoInDistribution.tendsto_measure_preimage_of_null_frontier
      (h := hjoint) hset_meas hfrontier
  have hseq_eq :
      (fun n =>
        μ {ω | percentileTCoverageVector θ θhat se qLower qUpper n ω ∈
          percentileTCoverageSet}) =
        fun n =>
          μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
            (qLower n ω) (qUpper n ω)} := by
    funext n
    congr 1
    ext ω
    exact percentileTCoverageVector_mem_set_iff (Ω := Ω) (hse n ω)
  simpa [hseq_eq] using hcoverage

/-- Calibrated percentile-`t` coverage bridge. -/
theorem chapter10_percentileTCI_coverage_tendsto
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hse : ∀ n ω, 0 < se n ω)
    (hjoint :
      TendstoInDistribution
        (percentileTCoverageVector θ θhat se qLower qUpper)
        atTop
        (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (percentileTCoverageLimitVector ξ qLowerLim qUpperLim))
        (frontier percentileTCoverageSet) = 0)
    (hcoverage :
      (ν.map (percentileTCoverageLimitVector ξ qLowerLim qUpperLim))
        percentileTCoverageSet = coverage) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  simpa [hcoverage] using
    chapter10_percentileTCI_coverage_tendsto_of_joint_quantile_limit
      (μ := μ) (ν := ν) (θ := θ) (θhat := θhat) (se := se)
      (qLower := qLower) (qUpper := qUpper) (ξ := ξ)
      (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      hse hjoint hfrontier

end PercentileTIntervals

section BootstrapTests

/-- Two-sided bootstrap-test rejection event: reject when `crit < |T|`. -/
def bootstrapAbsTestReject (T crit : ℝ) : Prop :=
  crit < |T|

/-- Two-coordinate statistic for a two-sided bootstrap critical-value test:
coordinate `0` is the test statistic and coordinate `1` is the bootstrap
critical value. -/
noncomputable def bootstrapAbsTestVector
    (T crit : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Fin 2 → ℝ :=
  fun i => if i = 0 then T n ω else crit n ω

/-- Limit vector for the two-sided bootstrap critical-value test. -/
noncomputable def bootstrapAbsTestLimitVector
    (ξ : Ωlim → ℝ) (crit : ℝ) (ω : Ωlim) : Fin 2 → ℝ :=
  fun i => if i = 0 then ξ ω else crit

/-- Rejection region for the two-sided bootstrap critical-value test. -/
def bootstrapAbsRejectionSet : Set (Fin 2 → ℝ) :=
  {z | z 1 < |z 0|}

theorem isOpen_bootstrapAbsRejectionSet : IsOpen bootstrapAbsRejectionSet := by
  simpa [bootstrapAbsRejectionSet] using
    isOpen_lt (continuous_apply 1) ((continuous_apply 0).abs)

theorem bootstrapAbsTestVector_mem_rejectionSet_iff
    {T crit : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω} :
    bootstrapAbsTestVector T crit n ω ∈ bootstrapAbsRejectionSet ↔
      bootstrapAbsTestReject (T n ω) (crit n ω) := by
  change crit n ω < |T n ω| ↔ crit n ω < |T n ω|
  rfl

/-- Hansen Theorem 10.16, bootstrap critical-value rejection-probability bridge.

If the test statistic and bootstrap critical value jointly converge to
`(ξ, q)`, and the rejection boundary has zero limit mass, then the rejection
probability converges to `P[q < |ξ|]`. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_of_joint_critical_value_limit
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim : ℝ}
    (hjoint :
      TendstoInDistribution
        (bootstrapAbsTestVector T crit)
        atTop
        (bootstrapAbsTestLimitVector ξ critLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (bootstrapAbsTestLimitVector ξ critLim))
        (frontier bootstrapAbsRejectionSet) = 0) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop
      (𝓝 ((ν.map (bootstrapAbsTestLimitVector ξ critLim)) bootstrapAbsRejectionSet)) := by
  have hset_meas : MeasurableSet bootstrapAbsRejectionSet :=
    isOpen_bootstrapAbsRejectionSet.measurableSet
  have hrejection :=
    TendstoInDistribution.tendsto_measure_preimage_of_null_frontier
      (h := hjoint) hset_meas hfrontier
  have hseq_eq :
      (fun n =>
        μ {ω | bootstrapAbsTestVector T crit n ω ∈ bootstrapAbsRejectionSet}) =
        fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)} := by
    funext n
    rfl
  simpa [hseq_eq] using hrejection

/-- Calibrated form of the bootstrap critical-value bridge.

When the limiting rejection probability equals `α`, the bootstrap critical
value test has asymptotic size `α`. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim : ℝ} {α : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (bootstrapAbsTestVector T crit)
        atTop
        (bootstrapAbsTestLimitVector ξ critLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (bootstrapAbsTestLimitVector ξ critLim))
        (frontier bootstrapAbsRejectionSet) = 0)
    (halpha :
      (ν.map (bootstrapAbsTestLimitVector ξ critLim)) bootstrapAbsRejectionSet = α) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop (𝓝 α) := by
  simpa [halpha] using
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_of_joint_critical_value_limit
      (μ := μ) (ν := ν) (T := T) (crit := crit) (ξ := ξ) (critLim := critLim)
      hjoint hfrontier

end BootstrapTests

end HansenEconometrics
