import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Bootstrap convergence utilities

This file contains the reusable two-probability-space interface for Hansen's
bootstrap convergence in probability.  A bootstrap statistic depends on the
original sample point `ω` and on a resampling point `ωs`; the bootstrap law
`Pstar n ω` is therefore allowed to vary with the realized sample.

The public surface starts with:

* `TendstoInBootstrapProbability` — Hansen Definition 10.1, expressed as
  convergence in probability of the conditional tail probability.
* `tendstoInBootstrapProbability_of_tendstoInMeasure` — Hansen Theorem 10.1:
  ordinary convergence in probability implies bootstrap convergence in
  probability when the statistic is non-random under the bootstrap law.
* `TendstoInBootstrapProbability.continuousAt_const_comp` — Hansen Theorem
  10.3, the continuous-mapping theorem for bootstrap convergence in
  probability to a constant.

The bootstrap-distribution interface is kept out of this first layer so that
the Chapter 10 module can introduce it with the exact theorem-facing
quantile/CDF surface used later in the chapter.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Ω Ωs E F : Type*} {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
  {μ : Measure Ω}

/-- Conditional bootstrap tail probability for Hansen Definition 10.1.

For a fixed original sample point `ω`, the bootstrap statistic `Zstar n ω` is a
random variable on the bootstrap space `Ωs`, with conditional law
`Pstar n ω`.  This definition is real-valued because Hansen's convergence
statement treats the conditional probability itself as a random scalar on the
original sample space. -/
noncomputable def bootstrapTailProb [PseudoMetricSpace E]
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → E) (Z : Ω → E)
    (η : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((Pstar n ω) {ωs | η ≤ dist (Zstar n ω ωs) (Z ω)}).toReal

/-- Hansen Definition 10.1: convergence in bootstrap probability.

`Zstar n ->p* Z` means that for every positive tolerance `η`, the conditional
tail probability `Pstar[dist (Zstar n) Z ≥ η]` converges to zero in ordinary
probability under the original-sample law `μ`.

The inequality is written with `≤` to match Mathlib's `TendstoInMeasure`
convention; this is the usual harmless closed-tail version of convergence in
probability. -/
def TendstoInBootstrapProbability [PseudoMetricSpace E]
    (μ : Measure Ω) (Pstar : ℕ → Ω → Measure Ωs)
    (Zstar : ℕ → Ω → Ωs → E) (Z : Ω → E) : Prop :=
  ∀ η : ℝ, 0 < η →
    TendstoInMeasure μ (fun n ω => bootstrapTailProb Pstar Zstar Z η n ω)
      atTop (fun _ => 0)

private theorem tendstoInMeasure_zero_of_nonneg_le
    {f g : ℕ → Ω → ℝ}
    (hf_nonneg : ∀ n ω, 0 ≤ f n ω)
    (hfg : ∀ n ω, f n ω ≤ g n ω)
    (hg : TendstoInMeasure μ g atTop (fun _ => 0)) :
    TendstoInMeasure μ f atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hg ⊢
  intro ε hε
  specialize hg ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg
    (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  have hω_le : ε ≤ dist (f n ω) 0 := hω
  have hf_abs : dist (f n ω) 0 = f n ω := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf_nonneg n ω)]
  have hg_nonneg : 0 ≤ g n ω := le_trans (hf_nonneg n ω) (hfg n ω)
  have hg_abs : dist (g n ω) 0 = g n ω := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hg_nonneg]
  rw [hf_abs] at hω_le
  change ε ≤ dist (g n ω) 0
  rw [hg_abs]
  exact hω_le.trans (hfg n ω)

private theorem tendstoInMeasure_add_nonneg_zero
    {f g : ℕ → Ω → ℝ}
    (hf_nonneg : ∀ n ω, 0 ≤ f n ω)
    (hg_nonneg : ∀ n ω, 0 ≤ g n ω)
    (hf : TendstoInMeasure μ f atTop (fun _ => 0))
    (hg : TendstoInMeasure μ g atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => f n ω + g n ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hf hg ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hfhalf := hf (ε / 2) hhalf
  have hghalf := hg (ε / 2) hhalf
  have hsum : Tendsto
      (fun n =>
        μ {ω | ε / 2 ≤ dist (f n ω) 0} +
          μ {ω | ε / 2 ≤ dist (g n ω) 0})
      atTop (𝓝 0) := by
    simpa using hfhalf.add hghalf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le _) ?_
  intro n
  calc
    μ {ω | ε ≤ dist (f n ω + g n ω) 0}
        ≤ μ ({ω | ε / 2 ≤ dist (f n ω) 0} ∪
            {ω | ε / 2 ≤ dist (g n ω) 0}) := by
          refine measure_mono ?_
          intro ω hω
          by_cases hf_tail : ε / 2 ≤ dist (f n ω) 0
          · exact Or.inl hf_tail
          · right
            by_contra hg_tail
            have hf_abs : dist (f n ω) 0 = f n ω := by
              rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf_nonneg n ω)]
            have hg_abs : dist (g n ω) 0 = g n ω := by
              rw [Real.dist_eq, sub_zero, abs_of_nonneg (hg_nonneg n ω)]
            have hsum_nonneg : 0 ≤ f n ω + g n ω :=
              add_nonneg (hf_nonneg n ω) (hg_nonneg n ω)
            have hsum_abs : |f n ω + g n ω| = f n ω + g n ω :=
              abs_of_nonneg hsum_nonneg
            have hf_lt : f n ω < ε / 2 := by
              rw [← hf_abs]
              exact lt_of_not_ge hf_tail
            have hg_lt : g n ω < ε / 2 := by
              rw [← hg_abs]
              exact lt_of_not_ge hg_tail
            have hω_le : ε ≤ f n ω + g n ω := by
              simpa [Real.dist_eq, sub_zero, hsum_abs] using hω
            linarith
    _ ≤ μ {ω | ε / 2 ≤ dist (f n ω) 0} +
        μ {ω | ε / 2 ≤ dist (g n ω) 0} :=
          measure_union_le _ _

private theorem tendstoInMeasure_indicator_zero_of_tendsto_measure
    {A : ℕ → Set Ω}
    [∀ n, DecidablePred (fun ω => ω ∈ A n)]
    (hA : Tendsto (fun n => μ (A n)) atTop (𝓝 0)) :
    TendstoInMeasure μ (fun n ω => if ω ∈ A n then (1 : ℝ) else 0)
      atTop (fun _ => 0) := by
  classical
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hA
    (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  have hω_le : ε ≤ dist (if ω ∈ A n then (1 : ℝ) else 0) 0 := hω
  by_contra hnot
  have hzero : (if ω ∈ A n then (1 : ℝ) else 0) = 0 := by simp [hnot]
  have hle_zero : ε ≤ (0 : ℝ) := by simpa [hzero] using hω_le
  exact (lt_irrefl (0 : ℝ)) (hε.trans_le hle_zero)

/-- Hansen Theorem 10.1.

If `Zₙ ->p Z` under the original-sample law, then the same statistic, viewed as
constant under every bootstrap law `Pstar n ω`, converges to `Z` in bootstrap
probability. -/
theorem tendstoInBootstrapProbability_of_tendstoInMeasure [PseudoMetricSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zseq : ℕ → Ω → E} {Z : Ω → E}
    (hZ : TendstoInMeasure μ Zseq atTop Z) :
    TendstoInBootstrapProbability μ Pstar (fun n ω _ => Zseq n ω) Z := by
  classical
  intro η hη
  let A : ℕ → Set Ω := fun n => {ω | η ≤ dist (Zseq n ω) (Z ω)}
  have hA : Tendsto (fun n => μ (A n)) atTop (𝓝 0) := by
    exact (tendstoInMeasure_iff_dist.mp hZ) η hη
  have hindicator :
      TendstoInMeasure μ (fun n ω => if ω ∈ A n then (1 : ℝ) else 0)
        atTop (fun _ => 0) :=
    tendstoInMeasure_indicator_zero_of_tendsto_measure (μ := μ) hA
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hindicator
  refine Filter.Eventually.of_forall ?_
  intro ω
  by_cases hω : ω ∈ A n
  · have hset :
        {ωs : Ωs | η ≤ dist (Zseq n ω) (Z ω)} = Set.univ := by
      have htail : η ≤ dist (Zseq n ω) (Z ω) := by simpa [A] using hω
      ext ωs
      simp [htail]
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    simp [bootstrapTailProb, A, hω, hset]
  · have hset :
        {ωs : Ωs | η ≤ dist (Zseq n ω) (Z ω)} = ∅ := by
      have htail : ¬ η ≤ dist (Zseq n ω) (Z ω) := by simpa [A] using hω
      ext ωs
      simp [htail]
    simp [bootstrapTailProb, A, hω, hset]

/-- Bootstrap convergence in probability from a conditional tail-probability
bound.

This is the reusable Markov/Chebyshev bridge behind Hansen's centered
bootstrap WLLN proof: once each conditional tail probability is bounded by a
random scalar that converges to zero in ordinary probability, the bootstrap
statistic converges in bootstrap probability. -/
theorem tendstoInBootstrapProbability_of_tail_bound [PseudoMetricSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E} {Z : Ω → E}
    {bound : ℝ → ℕ → Ω → ℝ}
    (hbound :
      ∀ η : ℝ, 0 < η →
        TendstoInMeasure μ (fun n ω => bound η n ω) atTop (fun _ => 0))
    (hle :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapTailProb Pstar Zstar Z η n ω ≤ bound η n ω) :
    TendstoInBootstrapProbability μ Pstar Zstar Z := by
  intro η hη
  exact tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω => bootstrapTailProb Pstar Zstar Z η n ω)
    (g := fun n ω => bound η n ω)
    (fun _ _ => ENNReal.toReal_nonneg)
    (hle η hη)
    (hbound η hη)

namespace TendstoInBootstrapProbability

/-- Pointwise congruence for bootstrap convergence in probability. -/
theorem congr [PseudoMetricSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → E} {Z Z' : Ω → E}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapProbability μ Pstar Zstar Z) :
    TendstoInBootstrapProbability μ Pstar Zstar' Z' := by
  intro η hη
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl (hZ η hη)
  refine Filter.Eventually.of_forall ?_
  intro ω
  simp [bootstrapTailProb, hstar, hlim]

/-- Hansen Theorem 10.3, bootstrap continuous-mapping theorem in probability.

If `Zₙ* ->p* c` and `g` is continuous at `c`, then `g(Zₙ*) ->p* g(c)`. -/
theorem continuousAt_const_comp [PseudoMetricSpace E] [PseudoMetricSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zstar : ℕ → Ω → Ωs → E} {c : E} {g : E → F}
    (hZ : TendstoInBootstrapProbability μ Pstar Zstar (fun _ => c))
    (hg : ContinuousAt g c) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) (fun _ => g c) := by
  intro η hη
  obtain ⟨δ, hδ, hδ_eventually⟩ := (Metric.continuousAt_iff.mp hg) η hη
  refine tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω =>
      bootstrapTailProb Pstar (fun n ω ωs => g (Zstar n ω ωs)) (fun _ => g c) η n ω)
    (g := fun n ω => bootstrapTailProb Pstar Zstar (fun _ => c) δ n ω)
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

set_option maxHeartbeats 400000 in
-- The proof expands the bootstrap union-bound event and a finite-measure `toReal`
-- comparison; the extra heartbeat budget avoids fragile elaboration timeouts.
/-- Bootstrap convergence in probability is closed under addition.

This is the bootstrap-probability analogue of the elementary Slutsky/addition
step used after Hansen Theorem 10.2: if `Xₙ* ->p* X` and `Yₙ* ->p* Y`, then
`Xₙ* + Yₙ* ->p* X + Y`. -/
theorem add [SeminormedAddCommGroup E]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Xstar Ystar : ℕ → Ω → Ωs → E} {X Y : Ω → E}
    (hX : TendstoInBootstrapProbability μ Pstar Xstar X)
    (hY : TendstoInBootstrapProbability μ Pstar Ystar Y) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => Xstar n ω ωs + Ystar n ω ωs)
      (fun ω => X ω + Y ω) := by
  intro η hη
  have hhalf : 0 < η / 2 := by linarith
  refine tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω =>
      bootstrapTailProb Pstar
        (fun n ω ωs => Xstar n ω ωs + Ystar n ω ωs)
        (fun ω => X ω + Y ω) η n ω)
    (g := fun n ω =>
      bootstrapTailProb Pstar Xstar X (η / 2) n ω +
        bootstrapTailProb Pstar Ystar Y (η / 2) n ω)
    ?_ ?_
    (tendstoInMeasure_add_nonneg_zero
      (μ := μ)
      (f := fun n ω => bootstrapTailProb Pstar Xstar X (η / 2) n ω)
      (g := fun n ω => bootstrapTailProb Pstar Ystar Y (η / 2) n ω)
      (fun _ _ => ENNReal.toReal_nonneg)
      (fun _ _ => ENNReal.toReal_nonneg)
      (hX (η / 2) hhalf) (hY (η / 2) hhalf))
  · intro n ω
    exact ENNReal.toReal_nonneg
  · intro n ω
    let C : Set Ωs :=
      {ωs | η ≤ dist (Xstar n ω ωs + Ystar n ω ωs) (X ω + Y ω)}
    let A : Set Ωs := {ωs | η / 2 ≤ dist (Xstar n ω ωs) (X ω)}
    let B : Set Ωs := {ωs | η / 2 ≤ dist (Ystar n ω ωs) (Y ω)}
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
      bootstrapTailProb Pstar
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
      _ = bootstrapTailProb Pstar Xstar X (η / 2) n ω +
          bootstrapTailProb Pstar Ystar Y (η / 2) n ω := rfl

end TendstoInBootstrapProbability

end HansenEconometrics
