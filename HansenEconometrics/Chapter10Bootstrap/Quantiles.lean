import Mathlib.Probability.CDF
import HansenEconometrics.Chapter10Bootstrap.Distribution
import HansenEconometrics.ProbabilityUtils

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Elementwise Function

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

section QuantileConvergence

/-- Bracketing property for a lower quantile selected from a random CDF.

For each sample point, values whose CDF is still below `p` must lie below the
selected quantile, and values whose CDF is already above `p` must lie above it.
This is the theorem-facing condition supplied by concrete bootstrap quantile
definitions such as the generalized inverse of a conditional bootstrap CDF. -/
structure CDFQuantileBracket
    (Gseq : ℕ → Ω → ℝ → ℝ) (p : ℝ) (qseq : ℕ → Ω → ℝ) : Prop where
  lower : ∀ n ω x, Gseq n ω x < p → x < qseq n ω
  upper : ∀ n ω x, p < Gseq n ω x → qseq n ω ≤ x

/-- Lower generalized inverse of a real CDF-like function. -/
noncomputable def lowerCDFQuantile (G : ℝ → ℝ) (p : ℝ) : ℝ :=
  sInf {x : ℝ | p ≤ G x}

/-- A point where the CDF-like function has reached level `p` lies weakly above
the lower generalized inverse. -/
theorem lowerCDFQuantile_le
    {G : ℝ → ℝ} {p x : ℝ}
    (hbdd : BddBelow {y : ℝ | p ≤ G y})
    (hx : p ≤ G x) :
    lowerCDFQuantile G p ≤ x := by
  simpa [lowerCDFQuantile] using
    (csInf_le (s := {y : ℝ | p ≤ G y}) hbdd hx)

/-- If a monotone CDF-like function remains below `p` just to the right of
`x`, then `x` lies strictly below the lower generalized inverse. -/
theorem lt_lowerCDFQuantile_of_exists_right_lt
    {G : ℝ → ℝ} {p x : ℝ}
    (hmono : Monotone G)
    (hne : ({y : ℝ | p ≤ G y} : Set ℝ).Nonempty)
    (hlocal : ∃ δ : ℝ, 0 < δ ∧ G (x + δ) < p) :
    x < lowerCDFQuantile G p := by
  obtain ⟨δ, hδ_pos, hxδ⟩ := hlocal
  have hbound : ∀ y ∈ ({y : ℝ | p ≤ G y} : Set ℝ), x + δ ≤ y := by
    intro y hy
    by_contra hnot
    have hylt : y < x + δ := lt_of_not_ge hnot
    have hGy_le : G y ≤ G (x + δ) := hmono hylt.le
    have hy_le : p ≤ G y := hy
    linarith
  have hle : x + δ ≤ lowerCDFQuantile G p := by
    simpa [lowerCDFQuantile] using
      (le_csInf (s := {y : ℝ | p ≤ G y}) hne hbound)
  linarith

/-- Lower generalized inverses bracket their CDF levels when the random CDFs
are monotone and locally stay below `p` immediately to the right of any point
where they are below `p`. -/
theorem lowerCDFQuantile_bracket_of_local_right_lt
    {Gseq : ℕ → Ω → ℝ → ℝ} {p : ℝ}
    (hmono : ∀ n ω, Monotone (Gseq n ω))
    (hne : ∀ n ω, ({x : ℝ | p ≤ Gseq n ω x} : Set ℝ).Nonempty)
    (hbdd : ∀ n ω, BddBelow {x : ℝ | p ≤ Gseq n ω x})
    (hlocal :
      ∀ n ω x, Gseq n ω x < p →
        ∃ δ : ℝ, 0 < δ ∧ Gseq n ω (x + δ) < p) :
    CDFQuantileBracket Gseq p
      (fun n ω => lowerCDFQuantile (Gseq n ω) p) := by
  constructor
  · intro n ω x hx
    exact lt_lowerCDFQuantile_of_exists_right_lt
      (hmono n ω) (hne n ω) (hlocal n ω x hx)
  · intro n ω x hx
    exact lowerCDFQuantile_le (hbdd n ω) (le_of_lt hx)

private theorem stieltjesFunction_exists_right_lt_of_lt
    (G : StieltjesFunction ℝ) {p x : ℝ} (hx : G x < p) :
    ∃ δ : ℝ, 0 < δ ∧ G (x + δ) < p := by
  have hcont := Metric.continuousWithinAt_iff.mp (G.right_continuous x)
  obtain ⟨δ, hδ_pos, hδ⟩ := hcont (p - G x) (sub_pos.mpr hx)
  refine ⟨δ / 2, by positivity, ?_⟩
  have hx_mem : x + δ / 2 ∈ Set.Ici x := by
    dsimp
    exact le_add_of_nonneg_right (by positivity : 0 ≤ δ / 2)
  have hdist : dist (x + δ / 2) x < δ := by
    rw [Real.dist_eq]
    have habs : |x + δ / 2 - x| = δ / 2 := by
      have hnonneg : 0 ≤ x + δ / 2 - x := by
        rwa [sub_nonneg]
      rw [abs_of_nonneg hnonneg]
      ring
    rw [habs]
    linarith
  have hdistG := hδ hx_mem hdist
  rw [Real.dist_eq] at hdistG
  have hlt := (abs_lt.mp hdistG).2
  linarith

/-- Stieltjes-function CDFs supply the right-local persistence premise for the
lower generalized inverse through right-continuity. -/
theorem lowerCDFQuantile_bracket_of_stieltjesFunction
    {Gseq : ℕ → Ω → StieltjesFunction ℝ} {p : ℝ}
    (hne :
      ∀ n ω, ({x : ℝ | p ≤ Gseq n ω x} : Set ℝ).Nonempty)
    (hbdd : ∀ n ω, BddBelow {x : ℝ | p ≤ Gseq n ω x}) :
    CDFQuantileBracket (fun n ω x => Gseq n ω x) p
      (fun n ω => lowerCDFQuantile (fun x => Gseq n ω x) p) :=
  lowerCDFQuantile_bracket_of_local_right_lt
    (hmono := fun n ω => (Gseq n ω).mono)
    hne hbdd
    (fun n ω x hx => stieltjesFunction_exists_right_lt_of_lt (Gseq n ω) (x := x) hx)

/-- Quantile convergence from pointwise CDF convergence at strict bracketing
points.

If the random CDFs `Gseq n` converge in probability to `G` at every fixed
point, the target `q` is strictly bracketed by the limiting CDF around level
`p`, and `qseq` is a lower-quantile selection for each random CDF, then
`qseq ->p q`.  This is the reusable quantile-convergence constructor behind
the percentile, percentile-`t`, and bootstrap critical-value endpoints in
Hansen Theorems 10.13, 10.14, and 10.16. -/
theorem tendstoInMeasure_quantile_of_cdf_brackets
    {Gseq : ℕ → Ω → ℝ → ℝ} {G : ℝ → ℝ} {p q : ℝ}
    {qseq : ℕ → Ω → ℝ}
    (hbracket : CDFQuantileBracket Gseq p qseq)
    (hleft : ∀ ε : ℝ, 0 < ε → G (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < G (q + ε))
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ (fun n ω => Gseq n ω x) atTop (fun _ => G x)) :
    TendstoInMeasure μ qseq atTop (fun _ => q) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ_pos : 0 < δ := by positivity
  have hδ_lt : δ < ε := by
    dsimp [δ]
    linarith
  let xL : ℝ := q - δ
  let xU : ℝ := q + δ
  let gapL : ℝ := p - G xL
  let gapU : ℝ := G xU - p
  have hgapL_pos : 0 < gapL := by
    dsimp [gapL, xL]
    exact sub_pos.mpr (hleft δ hδ_pos)
  have hgapU_pos : 0 < gapU := by
    dsimp [gapU, xU]
    exact sub_pos.mpr (hright δ hδ_pos)
  have hleft_tendsto := (tendstoInMeasure_iff_dist.mp (hG xL)) gapL hgapL_pos
  have hright_tendsto := (tendstoInMeasure_iff_dist.mp (hG xU)) gapU hgapU_pos
  have hsum :
      Tendsto
        (fun n =>
          μ {ω | gapL ≤ dist (Gseq n ω xL) (G xL)} +
            μ {ω | gapU ≤ dist (Gseq n ω xU) (G xU)})
        atTop (𝓝 0) := by
    simpa using hleft_tendsto.add hright_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le _) ?_
  intro n
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_union, Set.mem_setOf_eq] at hω ⊢
  by_cases hleft_bad : gapL ≤ dist (Gseq n ω xL) (G xL)
  · exact Or.inl hleft_bad
  · right
    by_contra hright_not_bad
    have hleft_close : dist (Gseq n ω xL) (G xL) < gapL := not_le.mp hleft_bad
    have hright_close : dist (Gseq n ω xU) (G xU) < gapU := not_le.mp hright_not_bad
    have hleft_abs : |Gseq n ω xL - G xL| < gapL := by
      simpa [Real.dist_eq] using hleft_close
    have hright_abs : |Gseq n ω xU - G xU| < gapU := by
      simpa [Real.dist_eq] using hright_close
    have hG_left_lt : Gseq n ω xL < p := by
      have hlt := (abs_lt.mp hleft_abs).2
      dsimp [gapL] at hlt
      linarith
    have hG_right_gt : p < Gseq n ω xU := by
      have hlt := (abs_lt.mp hright_abs).1
      dsimp [gapU] at hlt
      linarith
    have hq_lower : q - δ < qseq n ω := by
      simpa [xL] using hbracket.lower n ω xL hG_left_lt
    have hq_upper : qseq n ω ≤ q + δ := by
      simpa [xU] using hbracket.upper n ω xU hG_right_gt
    have hdist_lt : dist (qseq n ω) q < ε := by
      rw [Real.dist_eq]
      exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
    exact (not_le_of_gt hdist_lt) hω

/-- A strictly increasing limit CDF brackets its quantile level on both sides. -/
theorem strictMono_cdf_brackets
    {G : ℝ → ℝ} {p q : ℝ}
    (hstrict : StrictMono G) (hq : G q = p) :
    (∀ ε : ℝ, 0 < ε → G (q - ε) < p) ∧
      (∀ ε : ℝ, 0 < ε → p < G (q + ε)) := by
  constructor
  · intro ε hε
    rw [← hq]
    exact hstrict (by linarith)
  · intro ε hε
    rw [← hq]
    exact hstrict (by linarith)

/-- Quantile convergence from pointwise CDF convergence and a strictly
increasing limiting CDF.

This is the common calibrated-quantile specialization of
`tendstoInMeasure_quantile_of_cdf_brackets`: the strict bracketing premises are
derived from `G(q) = p` and strict monotonicity of the limiting CDF. -/
theorem tendstoInMeasure_quantile_of_strictMono_cdf
    {Gseq : ℕ → Ω → ℝ → ℝ} {G : ℝ → ℝ} {p q : ℝ}
    {qseq : ℕ → Ω → ℝ}
    (hbracket : CDFQuantileBracket Gseq p qseq)
    (hstrict : StrictMono G)
    (hq : G q = p)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ (fun n ω => Gseq n ω x) atTop (fun _ => G x)) :
    TendstoInMeasure μ qseq atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact tendstoInMeasure_quantile_of_cdf_brackets
    (μ := μ) hbracket hleft hright hG

/-- Quantile convergence for lower generalized inverses under explicit
monotonicity and right-local CDF bracketing assumptions. -/
theorem lowerCDFQuantile_tendstoInMeasure_of_cdf_brackets
    {Gseq : ℕ → Ω → ℝ → ℝ} {G : ℝ → ℝ} {p q : ℝ}
    (hmono : ∀ n ω, Monotone (Gseq n ω))
    (hne : ∀ n ω, ({x : ℝ | p ≤ Gseq n ω x} : Set ℝ).Nonempty)
    (hbdd : ∀ n ω, BddBelow {x : ℝ | p ≤ Gseq n ω x})
    (hlocal :
      ∀ n ω x, Gseq n ω x < p →
        ∃ δ : ℝ, 0 < δ ∧ Gseq n ω (x + δ) < p)
    (hleft : ∀ ε : ℝ, 0 < ε → G (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < G (q + ε))
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ (fun n ω => Gseq n ω x) atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (fun n ω => lowerCDFQuantile (Gseq n ω) p) atTop (fun _ => q) :=
  tendstoInMeasure_quantile_of_cdf_brackets
    (μ := μ)
    (hbracket := lowerCDFQuantile_bracket_of_local_right_lt
      hmono hne hbdd hlocal)
    hleft hright hG

/-- Strict-limit-CDF specialization of lower generalized-inverse convergence. -/
theorem lowerCDFQuantile_tendstoInMeasure_of_strictMono_cdf
    {Gseq : ℕ → Ω → ℝ → ℝ} {G : ℝ → ℝ} {p q : ℝ}
    (hmono : ∀ n ω, Monotone (Gseq n ω))
    (hne : ∀ n ω, ({x : ℝ | p ≤ Gseq n ω x} : Set ℝ).Nonempty)
    (hbdd : ∀ n ω, BddBelow {x : ℝ | p ≤ Gseq n ω x})
    (hlocal :
      ∀ n ω x, Gseq n ω x < p →
        ∃ δ : ℝ, 0 < δ ∧ Gseq n ω (x + δ) < p)
    (hstrict : StrictMono G)
    (hq : G q = p)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ (fun n ω => Gseq n ω x) atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (fun n ω => lowerCDFQuantile (Gseq n ω) p) atTop (fun _ => q) :=
  tendstoInMeasure_quantile_of_strictMono_cdf
    (μ := μ)
    (hbracket := lowerCDFQuantile_bracket_of_local_right_lt
      hmono hne hbdd hlocal)
    hstrict hq hG

/-- Lower generalized-inverse convergence for random Stieltjes-function CDFs. -/
theorem lowerCDFQuantile_tendstoInMeasure_of_stieltjesFunction
    {Gseq : ℕ → Ω → StieltjesFunction ℝ} {G : ℝ → ℝ} {p q : ℝ}
    (hne :
      ∀ n ω, ({x : ℝ | p ≤ Gseq n ω x} : Set ℝ).Nonempty)
    (hbdd : ∀ n ω, BddBelow {x : ℝ | p ≤ Gseq n ω x})
    (hleft : ∀ ε : ℝ, 0 < ε → G (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < G (q + ε))
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ (fun n ω => Gseq n ω x) atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (fun n ω => lowerCDFQuantile (fun x => Gseq n ω x) p)
      atTop (fun _ => q) :=
  tendstoInMeasure_quantile_of_cdf_brackets
    (μ := μ)
    (hbracket := lowerCDFQuantile_bracket_of_stieltjesFunction hne hbdd)
    hleft hright hG

/-- Strict-limit-CDF specialization for random Stieltjes-function lower
generalized inverses. -/
theorem lowerCDFQuantile_tendstoInMeasure_of_stieltjesFunction_strictMono
    {Gseq : ℕ → Ω → StieltjesFunction ℝ} {G : ℝ → ℝ} {p q : ℝ}
    (hne :
      ∀ n ω, ({x : ℝ | p ≤ Gseq n ω x} : Set ℝ).Nonempty)
    (hbdd : ∀ n ω, BddBelow {x : ℝ | p ≤ Gseq n ω x})
    (hstrict : StrictMono G)
    (hq : G q = p)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ (fun n ω => Gseq n ω x) atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (fun n ω => lowerCDFQuantile (fun x => Gseq n ω x) p)
      atTop (fun _ => q) :=
  tendstoInMeasure_quantile_of_strictMono_cdf
    (μ := μ)
    (hbracket := lowerCDFQuantile_bracket_of_stieltjesFunction hne hbdd)
    hstrict hq hG

/-- Limit scalar CDF `G(x) = P[Z ≤ x]`. -/
noncomputable def scalarCDF
    (ν : Measure Ωlim) (Z : Ωlim → ℝ) (x : ℝ) : ℝ :=
  (ν {ωlim | Z ωlim ≤ x}).toReal

/-- Limit scalar CDFs are monotone under finite limit measures. -/
theorem scalarCDF_mono
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} [IsFiniteMeasure ν] :
    Monotone (scalarCDF ν Z) := by
  intro x y hxy
  refine ENNReal.toReal_mono (measure_ne_top ν {ωlim | Z ωlim ≤ y}) ?_
  exact measure_mono fun ωlim hωlim => le_trans hωlim hxy

/-- The scalar-CDF bridge agrees with Mathlib's real-law CDF for the identity
statistic. -/
@[simp]
theorem scalarCDF_id_eq_cdf
    (η : Measure ℝ) [IsProbabilityMeasure η] :
    scalarCDF η (fun x : ℝ => x) = fun x => cdf η x := by
  funext x
  simpa [scalarCDF, Set.Iic, Measure.real] using
    (ProbabilityTheory.cdf_eq_real η x).symm

/-- A non-atomic real probability measure has a continuous CDF.

The proof uses Mathlib's Stieltjes-function representation of CDFs: right
continuity is part of the structure, while no atoms kill the jump
`cdf η x - leftLim (cdf η) x`. -/
theorem continuousAt_cdf_of_noAtoms
    (η : Measure ℝ) [IsProbabilityMeasure η] [NoAtoms η] (x : ℝ) :
    ContinuousAt (fun y : ℝ => cdf η y) x := by
  have hleftLim : Function.leftLim (fun y : ℝ => cdf η y) x = cdf η x := by
    have hzero :
        ENNReal.ofReal (cdf η x - Function.leftLim (fun y : ℝ => cdf η y) x) = 0 := by
      calc
        ENNReal.ofReal (cdf η x - Function.leftLim (fun y : ℝ => cdf η y) x)
            = (cdf η).measure {x} := by
              rw [StieltjesFunction.measure_singleton]
        _ = 0 := by
              rw [measure_cdf η]
              simp
    have hle :
        cdf η x - Function.leftLim (fun y : ℝ => cdf η y) x ≤ 0 := by
      simpa [ENNReal.ofReal_eq_zero] using hzero
    have hnonneg :
        0 ≤ cdf η x - Function.leftLim (fun y : ℝ => cdf η y) x := by
      exact sub_nonneg.mpr ((cdf η).mono.leftLim_le le_rfl)
    have hdiff :
        cdf η x - Function.leftLim (fun y : ℝ => cdf η y) x = 0 :=
      le_antisymm hle hnonneg
    linarith
  have hleft :
      ContinuousWithinAt (fun y : ℝ => cdf η y) (Set.Iic x) x := by
    rw [← continuousWithinAt_Iio_iff_Iic]
    exact (Monotone.continuousWithinAt_Iio_iff_leftLim_eq (monotone_cdf η)).2 hleftLim
  have hright :
      ContinuousWithinAt (fun y : ℝ => cdf η y) (Set.Ici x) x :=
    (cdf η).right_continuous x
  exact continuousAt_iff_continuous_left_right.2 ⟨hleft, hright⟩

/-- Gaussian real laws with nonzero variance have continuous CDFs. -/
theorem continuousAt_cdf_gaussianReal
    {m : ℝ} {v : NNReal} (hv : v ≠ 0) (x : ℝ) :
    ContinuousAt (fun y : ℝ => cdf (gaussianReal m v) y) x := by
  haveI : NoAtoms (gaussianReal m v) := noAtoms_gaussianReal hv
  exact continuousAt_cdf_of_noAtoms (gaussianReal m v) x

/-- The standard-normal CDF is continuous. -/
theorem continuousAt_cdf_standardNormal (x : ℝ) :
    ContinuousAt (fun y : ℝ => cdf (gaussianReal 0 1) y) x :=
  continuousAt_cdf_gaussianReal (m := 0) (v := 1) (by norm_num) x

/-- Mapping a non-atomic real law through absolute value remains non-atomic. -/
theorem noAtoms_map_abs_of_noAtoms (η : Measure ℝ) [NoAtoms η] :
    NoAtoms (η.map (fun x : ℝ => |x|)) := by
  refine ⟨?_⟩
  intro y
  rw [Measure.map_apply continuous_abs.measurable (measurableSet_singleton y)]
  have hpre_subset :
      (fun x : ℝ => |x|) ⁻¹' ({y} : Set ℝ) ⊆
        ({y} ∪ {-y} : Set ℝ) := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp only [Set.mem_union, Set.mem_singleton_iff]
    by_cases hx_nonneg : 0 ≤ x
    · left
      simpa [abs_of_nonneg hx_nonneg] using hx
    · right
      have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
      have hneg : -x = y := by
        simpa [abs_of_neg hx_neg] using hx
      linarith
  exact measure_mono_null hpre_subset
    (measure_union_null (measure_singleton y) (measure_singleton (-y)))

/-- The absolute-standard-normal CDF is continuous. -/
theorem continuousAt_cdf_standardNormalAbs (x : ℝ) :
    ContinuousAt
      (fun y : ℝ => cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) y) x := by
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  haveI : IsProbabilityMeasure ((gaussianReal 0 1).map (fun z : ℝ => |z|)) :=
    Measure.isProbabilityMeasure_map continuous_abs.aemeasurable
  haveI : NoAtoms ((gaussianReal 0 1).map (fun z : ℝ => |z|)) :=
    noAtoms_map_abs_of_noAtoms (gaussianReal 0 1)
  exact continuousAt_cdf_of_noAtoms
    ((gaussianReal 0 1).map (fun z : ℝ => |z|)) x

/-- The absolute-standard-normal CDF is zero on negative arguments. -/
theorem cdf_standardNormalAbs_eq_zero_of_neg {x : ℝ} (hx : x < 0) :
    cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) x = 0 := by
  haveI : IsProbabilityMeasure ((gaussianReal 0 1).map (fun z : ℝ => |z|)) :=
    Measure.isProbabilityMeasure_map continuous_abs.aemeasurable
  rw [ProbabilityTheory.cdf_eq_real]
  rw [Measure.real]
  rw [Measure.map_apply continuous_abs.measurable measurableSet_Iic]
  have hpre :
      (fun z : ℝ => |z|) ⁻¹' Set.Iic x = (∅ : Set ℝ) := by
    ext z
    constructor
    · intro hz
      have hz_le : |z| ≤ x := hz
      exact False.elim (not_le_of_gt hx (le_trans (abs_nonneg z) hz_le))
    · intro hz
      exact False.elim hz
  rw [hpre, measure_empty]
  norm_num

/-- On nonnegative arguments, the absolute-standard-normal CDF is the central
standard-normal CDF increment. -/
theorem cdf_standardNormalAbs_eq_sub_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) x =
      cdf (gaussianReal 0 1) x - cdf (gaussianReal 0 1) (-x) := by
  haveI : IsProbabilityMeasure ((gaussianReal 0 1).map (fun z : ℝ => |z|)) :=
    Measure.isProbabilityMeasure_map continuous_abs.aemeasurable
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  rw [ProbabilityTheory.cdf_eq_real]
  rw [Measure.real]
  rw [Measure.map_apply continuous_abs.measurable measurableSet_Iic]
  have hpre :
      (fun z : ℝ => |z|) ⁻¹' Set.Iic x = Set.Icc (-x) x := by
    ext z
    constructor
    · intro hz
      exact (abs_le).1 hz
    · intro hz
      exact (abs_le).2 hz
  rw [hpre, ← Measure.real]
  exact measureReal_Icc_eq_cdf_sub_of_noAtoms
    (ν := gaussianReal 0 1) (a := -x) (b := x) (by linarith)

/-- Endpoint standard-normal calibration strictly brackets the
absolute-standard-normal critical-value CDF at level `1 - α`.

The absolute-standard-normal CDF is not globally strictly monotone on `ℝ`, but
standard-normal strict monotonicity plus the usual symmetric endpoint
calibration gives the local bracketing needed by the lower-critical-value
constructor. -/
theorem standardNormalAbs_cdf_brackets_of_standardNormal_endpoints
    {critLim α : ℝ}
    (hstrict : StrictMono (fun x => cdf (gaussianReal 0 1) x))
    (hα_lt_one : α < 1)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf (gaussianReal 0 1) (-critLim) = α / 2)
    (hcdfUpper : cdf (gaussianReal 0 1) critLim = 1 - α / 2) :
    (∀ ε : ℝ, 0 < ε →
        cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim - ε) <
          1 - α) ∧
      (∀ ε : ℝ, 0 < ε →
        1 - α <
          cdf ((gaussianReal 0 1).map (fun z : ℝ => |z|)) (critLim + ε)) := by
  let F : ℝ → ℝ := fun x => cdf (gaussianReal 0 1) x
  have htarget : F critLim - F (-critLim) = 1 - α := by
    dsimp [F]
    rw [hcdfLower, hcdfUpper]
    ring
  constructor
  · intro ε hε
    by_cases hq_nonneg : 0 ≤ critLim - ε
    · rw [cdf_standardNormalAbs_eq_sub_of_nonneg hq_nonneg]
      rw [← htarget]
      have hupper_lt : F (critLim - ε) < F critLim :=
        hstrict (by linarith)
      have hlower_lt : F (-critLim) < F (-(critLim - ε)) :=
        hstrict (by linarith)
      dsimp [F] at hupper_lt hlower_lt ⊢
      linarith
    · have hq_neg : critLim - ε < 0 := lt_of_not_ge hq_nonneg
      rw [cdf_standardNormalAbs_eq_zero_of_neg hq_neg]
      linarith
  · intro ε hε
    have hq_nonneg : 0 ≤ critLim + ε := by linarith
    rw [cdf_standardNormalAbs_eq_sub_of_nonneg hq_nonneg]
    rw [← htarget]
    have hupper_lt : F critLim < F (critLim + ε) :=
      hstrict (by linarith)
    have hlower_lt : F (-(critLim + ε)) < F (-critLim) :=
      hstrict (by linarith)
    dsimp [F] at hupper_lt hlower_lt ⊢
    linarith

/-- A scalar limit statistic with law `η` has scalar CDF equal to the CDF of
`η`.

This lets one-dimensional bootstrap quantile arguments consume limits stated on
an auxiliary probability space, such as a coordinate projection of a
finite-dimensional Gaussian vector. -/
theorem scalarCDF_eq_cdf_of_hasLaw
    {ν : Measure Ωlim} {η : Measure ℝ} [IsProbabilityMeasure η]
    {Z : Ωlim → ℝ} (hZ : HasLaw Z η ν) :
    scalarCDF ν Z = fun x => cdf η x := by
  funext x
  rw [ProbabilityTheory.cdf_eq_real]
  rw [Measure.real]
  rw [← hZ.map_eq]
  rw [Measure.map_apply_of_aemeasurable hZ.aemeasurable measurableSet_Iic]
  simp [scalarCDF, Set.Iic]

/-- Scalar CDF continuity gives continuity of the one-dimensional vector-CDF
view used by Hansen Definition 10.2. -/
theorem continuousAt_vectorCDF_unit_of_scalarCDF
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {x : ℝ}
    (hx : ContinuousAt (scalarCDF ν Z) x) :
    ContinuousAt
      (fun y : Unit → ℝ =>
        vectorCDF ν (fun ωlim (_ : Unit) => Z ωlim) y)
      (fun _ : Unit => x) := by
  have hcomp :
      ContinuousAt ((scalarCDF ν Z) ∘ (fun y : Unit → ℝ => y ()))
        (fun _ : Unit => x) := by
    exact hx.comp (continuous_apply ()).continuousAt
  have hfun :
      (fun y : Unit → ℝ =>
        vectorCDF ν (fun ωlim (_ : Unit) => Z ωlim) y) =
        (scalarCDF ν Z) ∘ (fun y : Unit → ℝ => y ()) := by
    funext y
    have hset :
        {ωlim | coordinateLE (fun _ : Unit => Z ωlim) y} =
          {ωlim | Z ωlim ≤ y ()} := by
      ext ωlim
      constructor
      · intro h
        exact h ()
      · intro h i
        simpa [Subsingleton.elim i ()] using h
    simp [scalarCDF, vectorCDF, hset]
  rw [hfun]
  exact hcomp

/-- Scalar conditional bootstrap CDF `P*[Zₙ* ≤ x]`. -/
noncomputable def bootstrapScalarCDF
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → ℝ)
    (x : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((Pstar n ω) {ωs | Zstar n ω ωs ≤ x}).toReal

/-- Conditional bootstrap scalar CDFs are monotone under finite conditional
bootstrap measures. -/
theorem bootstrapScalarCDF_mono
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {n : ℕ} {ω : Ω} [IsFiniteMeasure (Pstar n ω)] :
    Monotone (fun x => bootstrapScalarCDF Pstar Zstar x n ω) := by
  intro x y hxy
  refine ENNReal.toReal_mono
    (measure_ne_top (Pstar n ω) {ωs | Zstar n ω ωs ≤ y}) ?_
  exact measure_mono fun ωs hωs => le_trans hωs hxy

/-- Conditional bootstrap scalar CDF as Mathlib's CDF of the push-forward law. -/
theorem bootstrapScalarCDF_eq_cdf_map
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {n : ℕ} {ω : Ω}
    (hPstar : IsProbabilityMeasure (Pstar n ω))
    (hZ : AEMeasurable (Zstar n ω) (Pstar n ω)) (x : ℝ) :
    bootstrapScalarCDF Pstar Zstar x n ω =
      cdf ((Pstar n ω).map (Zstar n ω)) x := by
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar
  haveI : IsProbabilityMeasure ((Pstar n ω).map (Zstar n ω)) :=
    Measure.isProbabilityMeasure_map hZ
  rw [ProbabilityTheory.cdf_eq_real]
  rw [Measure.real]
  rw [Measure.map_apply_of_aemeasurable hZ measurableSet_Iic]
  simp [bootstrapScalarCDF, Set.Iic]

/-- Scalar conditional bootstrap CDFs remain below a level just to the right
of any point where they are strictly below it.

This is the standard right-continuity bracketing premise for lower generalized
inverse arguments, derived from Mathlib's CDF of the push-forward law. -/
theorem bootstrapScalarCDF_exists_right_lt_of_lt
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {n : ℕ} {ω : Ω}
    (hPstar : IsProbabilityMeasure (Pstar n ω))
    (hZ : AEMeasurable (Zstar n ω) (Pstar n ω))
    {p x : ℝ}
    (hx : bootstrapScalarCDF Pstar Zstar x n ω < p) :
    ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p := by
  let η : Measure ℝ := (Pstar n ω).map (Zstar n ω)
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar
  haveI : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map hZ
  have hcdf_eq :
      ∀ y : ℝ, bootstrapScalarCDF Pstar Zstar y n ω = cdf η y := by
    intro y
    exact bootstrapScalarCDF_eq_cdf_map
      (Pstar := Pstar) (Zstar := Zstar) (n := n) (ω := ω) hPstar hZ y
  have hx_cdf : cdf η x < p := by
    simpa [hcdf_eq x] using hx
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    stieltjesFunction_exists_right_lt_of_lt (cdf η) (x := x) hx_cdf
  exact ⟨δ, hδ_pos, by simpa [hcdf_eq (x + δ)] using hδ⟩

/-- A pointwise a.e.-measurability package for the local-right bracketing
premise of scalar conditional bootstrap CDFs. -/
theorem bootstrapScalarCDF_local_right_lt_of_aemeasurable
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    {p : ℝ} :
    ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
      ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p :=
  fun n ω x hx =>
    bootstrapScalarCDF_exists_right_lt_of_lt
      (Pstar := Pstar) (Zstar := Zstar) (n := n) (ω := ω)
      (x := x) (hPstar n ω) (hZ n ω) hx

/-- For a scalar conditional bootstrap CDF, every level below one is reached
somewhere. -/
theorem bootstrapScalarCDF_level_nonempty_of_aemeasurable
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    {p : ℝ} (hp : p < 1) :
    ∀ n ω,
      ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} :
        Set ℝ).Nonempty := by
  intro n ω
  let η : Measure ℝ := (Pstar n ω).map (Zstar n ω)
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  haveI : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map (hZ n ω)
  have hEventually :
      ∀ᶠ x in atTop, p < cdf η x :=
    (ProbabilityTheory.tendsto_cdf_atTop η).eventually_const_lt hp
  obtain ⟨x, hx⟩ := hEventually.exists
  refine ⟨x, ?_⟩
  have hcdf_eq :
      bootstrapScalarCDF Pstar Zstar x n ω = cdf η x :=
    bootstrapScalarCDF_eq_cdf_map
      (Pstar := Pstar) (Zstar := Zstar) (n := n) (ω := ω)
      (hPstar n ω) (hZ n ω) x
  change p ≤ bootstrapScalarCDF Pstar Zstar x n ω
  rw [hcdf_eq]
  exact le_of_lt hx

/-- For a scalar conditional bootstrap CDF, every strictly positive level has
a lower-bounded generalized-inverse set. -/
theorem bootstrapScalarCDF_level_bddBelow_of_aemeasurable
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    {p : ℝ} (hp : 0 < p) :
    ∀ n ω, BddBelow
      {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} := by
  intro n ω
  let η : Measure ℝ := (Pstar n ω).map (Zstar n ω)
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  haveI : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map (hZ n ω)
  have hEventually :
      ∀ᶠ x in atBot, cdf η x < p :=
    (ProbabilityTheory.tendsto_cdf_atBot η).eventually_lt_const hp
  obtain ⟨M, hM⟩ := eventually_atBot.mp hEventually
  refine ⟨M, ?_⟩
  intro x hx
  by_contra hnot
  have hx_le : x ≤ M := le_of_not_ge hnot
  have hcdf_lt : cdf η x < p := hM x hx_le
  have hboot_lt : bootstrapScalarCDF Pstar Zstar x n ω < p := by
    have hcdf_eq :
        bootstrapScalarCDF Pstar Zstar x n ω = cdf η x :=
      bootstrapScalarCDF_eq_cdf_map
        (Pstar := Pstar) (Zstar := Zstar) (n := n) (ω := ω)
        (hPstar n ω) (hZ n ω) x
    simpa [hcdf_eq] using hcdf_lt
  exact not_lt_of_ge hx hboot_lt

/-- Scalar CDF convergence extracted from Hansen Definition 10.2 in one
dimension.

This bridge lets scalar quantile arguments consume a one-dimensional
bootstrap-distribution convergence theorem stated in the finite-dimensional
`Unit → ℝ` API. -/
theorem TendstoInBootstrapDistribution.bootstrapScalarCDF_tendsto_unit
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    {x : ℝ}
    (hx :
      ContinuousAt
        (fun y : Unit → ℝ =>
          vectorCDF ν (fun ωlim (_ : Unit) => Z ωlim) y)
        (fun _ : Unit => x)) :
    TendstoInMeasure μ (fun n ω => bootstrapScalarCDF Pstar Zstar x n ω)
      atTop (fun _ => scalarCDF ν Z x) := by
  have hunit :=
    hZ.tendsto_cdf (x := fun _ : Unit => x) hx
  refine TendstoInMeasure.congr (fun n => ?_) ?_ hunit
  · exact ae_of_all μ fun ω => by
      simp [bootstrapScalarCDF, bootstrapVectorCDF, coordinateLE]
  · exact ae_of_all μ fun _ => by
      simp [scalarCDF, vectorCDF, coordinateLE]

/-- Scalar CDF convergence extracted from one-dimensional Hansen Definition
10.2, with continuity stated for the scalar CDF. -/
theorem TendstoInBootstrapDistribution.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    {x : ℝ}
    (hx : ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ (fun n ω => bootstrapScalarCDF Pstar Zstar x n ω)
      atTop (fun _ => scalarCDF ν Z x) :=
  hZ.bootstrapScalarCDF_tendsto_unit (x := x)
    (continuousAt_vectorCDF_unit_of_scalarCDF hx)

/-- Scalar CDF convergence from one-dimensional Hansen Definition 10.2 when
the limiting statistic is the identity under a scalar probability law. -/
theorem TendstoInBootstrapDistribution.bootstrapScalarCDF_tendsto_unit_id_cdf
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η]
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    {x : ℝ}
    (hx : ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ (fun n ω => bootstrapScalarCDF Pstar Zstar x n ω)
      atTop (fun _ => cdf η x) := by
  simpa using
    (TendstoInBootstrapDistribution.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := η)
      (Z := fun x : ℝ => x) hZ (by simpa using hx))

/-- Scalar conditional-bootstrap CDF convergence from a one-dimensional
Definition 10.2 limit whose scalar statistic has law `η`.

This is the law-facing counterpart of
`bootstrapScalarCDF_tendsto_unit_id_cdf`: the limiting probability space may be
an auxiliary one, while `HasLaw` identifies the scalar CDF used by the
quantile layer. -/
theorem TendstoInBootstrapDistribution.bootstrapScalarCDF_tendsto_unit_law_cdf
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η]
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hZlaw : HasLaw Z η ν)
    {x : ℝ}
    (hx : ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ (fun n ω => bootstrapScalarCDF Pstar Zstar x n ω)
      atTop (fun _ => cdf η x) := by
  have hscalar : scalarCDF ν Z = fun y => cdf η y :=
    scalarCDF_eq_cdf_of_hasLaw hZlaw
  have hxscalar : ContinuousAt (scalarCDF ν Z) x := by
    simpa [hscalar] using hx
  have h :=
    TendstoInBootstrapDistribution.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν)
      (Z := Z) hZ hxscalar
  simpa [hscalar] using h

/-- Bootstrap scalar quantile convergence from pointwise conditional-CDF
convergence.

This is the bootstrap-specialized face of
`tendstoInMeasure_quantile_of_cdf_brackets`, stated with the scalar
conditional CDF `bootstrapScalarCDF`. -/
theorem bootstrapScalarQuantile_tendsto_of_cdf_brackets
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {G : ℝ → ℝ} {p q : ℝ} {qseq : ℕ → Ω → ℝ}
    (hbracket :
      CDFQuantileBracket
        (fun n ω x => bootstrapScalarCDF Pstar Zstar x n ω) p qseq)
    (hleft : ∀ ε : ℝ, 0 < ε → G (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < G (q + ε))
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Zstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ qseq atTop (fun _ => q) :=
  tendstoInMeasure_quantile_of_cdf_brackets
    (μ := μ) (Gseq := fun n ω x => bootstrapScalarCDF Pstar Zstar x n ω)
    hbracket hleft hright hG

/-- Bootstrap scalar quantile convergence with a strictly increasing limiting
CDF. -/
theorem bootstrapScalarQuantile_tendsto_of_strictMono_cdf
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {G : ℝ → ℝ} {p q : ℝ} {qseq : ℕ → Ω → ℝ}
    (hbracket :
      CDFQuantileBracket
        (fun n ω x => bootstrapScalarCDF Pstar Zstar x n ω) p qseq)
    (hstrict : StrictMono G)
    (hq : G q = p)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Zstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ qseq atTop (fun _ => q) :=
  tendstoInMeasure_quantile_of_strictMono_cdf
    (μ := μ) (Gseq := fun n ω x => bootstrapScalarCDF Pstar Zstar x n ω)
    hbracket hstrict hq hG

/-- Bootstrap scalar quantile convergence from one-dimensional Hansen
Definition 10.2.

This composes the one-dimensional Definition 10.2-to-scalar-CDF bridge with
the pointwise-CDF quantile constructor. -/
theorem bootstrapScalarQuantile_tendsto_of_bootstrapDistribution_unit
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    {qseq : ℕ → Ω → ℝ}
    (hbracket :
      CDFQuantileBracket
        (fun n ω x => bootstrapScalarCDF Pstar Zstar x n ω) p qseq)
    (hleft : ∀ ε : ℝ, 0 < ε → scalarCDF ν Z (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < scalarCDF ν Z (q + ε))
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ qseq atTop (fun _ => q) :=
  bootstrapScalarQuantile_tendsto_of_cdf_brackets
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (G := scalarCDF ν Z)
    hbracket hleft hright
    (fun x =>
      TendstoInBootstrapDistribution.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
        hZ (hcont x))

/-- Strict-limit-CDF specialization of scalar quantile convergence from
one-dimensional Hansen Definition 10.2. -/
theorem bootstrapScalarQuantile_tendsto_of_bootstrapDistribution_unit_strictMono
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    {qseq : ℕ → Ω → ℝ}
    (hbracket :
      CDFQuantileBracket
        (fun n ω x => bootstrapScalarCDF Pstar Zstar x n ω) p qseq)
    (hstrict : StrictMono (scalarCDF ν Z))
    (hq : scalarCDF ν Z q = p)
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ qseq atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarQuantile_tendsto_of_bootstrapDistribution_unit
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      hbracket hleft hright hZ hcont

/-- Lower generalized inverse of the scalar conditional bootstrap CDF. -/
noncomputable def bootstrapScalarLowerQuantile
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → ℝ)
    (p : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  lowerCDFQuantile (fun x => bootstrapScalarCDF Pstar Zstar x n ω) p

/-- Bootstrap scalar lower-quantile convergence from pointwise CDF convergence
and concrete generalized-inverse bracketing assumptions. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_cdf_brackets
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {G : ℝ → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Zstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p)
    (hleft : ∀ ε : ℝ, 0 < ε → G (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < G (q + ε))
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Zstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) :=
  lowerCDFQuantile_tendstoInMeasure_of_cdf_brackets
    (μ := μ) (Gseq := fun n ω x => bootstrapScalarCDF Pstar Zstar x n ω)
    hmono hne hbdd hlocal hleft hright hG

/-- Bootstrap scalar lower-quantile convergence with a strictly increasing
limiting CDF. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_strictMono_cdf
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {G : ℝ → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Zstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p)
    (hstrict : StrictMono G)
    (hq : G q = p)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Zstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) :=
  lowerCDFQuantile_tendstoInMeasure_of_strictMono_cdf
    (μ := μ) (Gseq := fun n ω x => bootstrapScalarCDF Pstar Zstar x n ω)
    hmono hne hbdd hlocal hstrict hq hG

/-- Bootstrap scalar lower-quantile convergence from one-dimensional Hansen
Definition 10.2.

This is the concrete generalized-inverse version of
`bootstrapScalarQuantile_tendsto_of_bootstrapDistribution_unit`. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Zstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p)
    (hleft : ∀ ε : ℝ, 0 < ε → scalarCDF ν Z (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < scalarCDF ν Z (q + ε))
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) :=
  bootstrapScalarLowerQuantile_tendsto_of_cdf_brackets
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (G := scalarCDF ν Z)
    hmono hne hbdd hlocal hleft hright
    (fun x =>
      TendstoInBootstrapDistribution.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
        hZ (hcont x))

/-- Strict-limit-CDF specialization of scalar lower-quantile convergence from
one-dimensional Hansen Definition 10.2. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_strictMono
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Zstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p)
    (hstrict : StrictMono (scalarCDF ν Z))
    (hq : scalarCDF ν Z q = p)
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      hmono hne hbdd hlocal hleft hright hZ hcont

/-- Finite conditional bootstrap measures supply the scalar-CDF monotonicity
premise in the lower-quantile Definition 10.2 wrapper. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_finite
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p)
    (hleft : ∀ ε : ℝ, 0 < ε → scalarCDF ν Z (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < scalarCDF ν Z (q + ε))
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) :=
  bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (fun n ω => by
      haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
      exact bootstrapScalarCDF_mono (Pstar := Pstar) (Zstar := Zstar)
        (n := n) (ω := ω))
    hne hbdd hlocal hleft hright hZ hcont

/-- Strict-limit-CDF specialization of the finite-measure scalar
lower-quantile Definition 10.2 wrapper. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_strictMono_finite
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p)
    (hstrict : StrictMono (scalarCDF ν Z))
    (hq : scalarCDF ν Z q = p)
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_finite
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      hPstar hne hbdd hlocal hleft hright hZ hcont

/-- Law-CDF specialization of the finite-measure scalar lower-quantile
Definition 10.2 wrapper.

The limiting one-dimensional statistic is the identity under the scalar law
`η`, so the limiting CDF is Mathlib's `cdf η`. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_id_cdf_finite
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p)
    (hleft : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < cdf η (q + ε))
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) := by
  exact
    bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_finite
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := η)
      (Z := fun x : ℝ => x) hPstar hne hbdd hlocal
      (by simpa using hleft) (by simpa using hright) hZ
      (by simpa using hcont)

/-- Strict law-CDF specialization of the finite-measure scalar lower-quantile
Definition 10.2 wrapper. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_strictMono_id_cdf_finite
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p)
    (hstrict : StrictMono (fun x => cdf η x))
    (hq : cdf η q = p)
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) := by
  exact
    bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_strictMono_finite
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := η)
      (Z := fun x : ℝ => x) hPstar hne hbdd hlocal
      (by simpa using hstrict) (by simpa using hq) hZ (by simpa using hcont)

/-- Law-CDF scalar lower-quantile wrapper with the local-right CDF bracketing
premise discharged from pointwise a.e. measurability of the bootstrap statistic. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_id_cdf_aemeasurable
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hleft : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < cdf η (q + ε))
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_id_cdf_finite
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η) (p := p)
      (q := q) hPstarFinite hne hbdd
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas)
      hleft hright hZ hcont

/-- Strict law-CDF scalar lower-quantile wrapper with the local-right CDF
bracketing premise discharged from pointwise a.e. measurability. -/
theorem
bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_strictMono_id_cdf_aemeasurable
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hstrict : StrictMono (fun x => cdf η x))
    (hq : cdf η q = p)
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_id_cdf_aemeasurable
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η)
      hPstar hZmeas hne hbdd hleft hright hZ hcont

/-- Law-CDF scalar lower-quantile wrapper for probability-valued conditional
bootstrap CDFs at levels `0 < p < 1`.

The probability and a.e.-measurability assumptions discharge monotonicity,
right-local persistence, nonemptiness, and bounded-below bracketing for the
lower generalized inverse. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_id_cdf_probability
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hleft : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < cdf η (q + ε))
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) :=
  bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_id_cdf_aemeasurable
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η)
    hPstar hZmeas
    (bootstrapScalarCDF_level_nonempty_of_aemeasurable
      (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas hp_lt_one)
    (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
      (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas hp_pos)
    hleft hright hZ hcont

/-- Law-CDF scalar lower-quantile wrapper for probability-valued conditional
bootstrap CDFs at levels `0 < p < 1`.

The limiting one-dimensional statistic may live on an auxiliary probability
space; `HasLaw Z η ν` identifies its scalar CDF with the CDF of `η`. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_law_cdf_probability
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hleft : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < cdf η (q + ε))
    (hT :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hZlaw : HasLaw Z η ν)
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    bootstrapScalarLowerQuantile_tendsto_of_cdf_brackets
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
      (G := fun x => cdf η x) (p := p) (q := q)
      (fun n ω => by
        haveI : IsFiniteMeasure (Pstar n ω) := hPstarFinite n ω
        exact bootstrapScalarCDF_mono (Pstar := Pstar) (Zstar := Zstar)
          (n := n) (ω := ω))
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas hp_lt_one)
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas hp_pos)
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas)
      hleft hright
      (fun x =>
        TendstoInBootstrapDistribution.bootstrapScalarCDF_tendsto_unit_law_cdf
          (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
          (ν := ν) (Z := Z) (η := η) hT hZlaw (hcont x))

/-- Strict law-CDF scalar lower-quantile wrapper for probability-valued
conditional bootstrap CDFs at levels `0 < p < 1`. -/
theorem
bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_strictMono_id_cdf_probability
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hq : cdf η q = p)
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_id_cdf_probability
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η)
      hPstar hZmeas hp_pos hp_lt_one hleft hright hZ hcont

variable {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]

/-- Scalar conditional bootstrap CDF for sample-size-dependent bootstrap
spaces. -/
noncomputable def bootstrapScalarCDFIndexed
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → ℝ)
    (x : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((Pstar n ω) {ωs | Zstar n ω ωs ≤ x}).toReal

/-- Indexed scalar conditional bootstrap CDF as Mathlib's CDF of the
push-forward law. -/
theorem bootstrapScalarCDFIndexed_eq_cdf_map
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {n : ℕ} {ω : Ω}
    (hPstar : IsProbabilityMeasure (Pstar n ω))
    (hZ : AEMeasurable (Zstar n ω) (Pstar n ω)) (x : ℝ) :
    bootstrapScalarCDFIndexed Pstar Zstar x n ω =
      cdf ((Pstar n ω).map (Zstar n ω)) x := by
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar
  haveI : IsProbabilityMeasure ((Pstar n ω).map (Zstar n ω)) :=
    Measure.isProbabilityMeasure_map hZ
  rw [ProbabilityTheory.cdf_eq_real]
  rw [Measure.real]
  rw [Measure.map_apply_of_aemeasurable hZ measurableSet_Iic]
  simp [bootstrapScalarCDFIndexed, Set.Iic]

/-- Indexed scalar conditional bootstrap CDFs are monotone under finite
conditional bootstrap measures. -/
theorem bootstrapScalarCDFIndexed_mono
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {n : ℕ} {ω : Ω} [IsFiniteMeasure (Pstar n ω)] :
    Monotone (fun x => bootstrapScalarCDFIndexed Pstar Zstar x n ω) := by
  intro x y hxy
  refine ENNReal.toReal_mono
    (measure_ne_top (Pstar n ω) {ωs | Zstar n ω ωs ≤ y}) ?_
  exact measure_mono fun ωs hωs => le_trans hωs hxy

/-- Indexed scalar conditional bootstrap CDFs remain below a level just to the
right of any point where they are strictly below it. -/
theorem bootstrapScalarCDFIndexed_exists_right_lt_of_lt
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {n : ℕ} {ω : Ω}
    (hPstar : IsProbabilityMeasure (Pstar n ω))
    (hZ : AEMeasurable (Zstar n ω) (Pstar n ω))
    {p x : ℝ}
    (hx : bootstrapScalarCDFIndexed Pstar Zstar x n ω < p) :
    ∃ δ : ℝ, 0 < δ ∧
      bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p := by
  let η : Measure ℝ := (Pstar n ω).map (Zstar n ω)
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar
  haveI : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map hZ
  have hcdf_eq :
      ∀ y : ℝ, bootstrapScalarCDFIndexed Pstar Zstar y n ω = cdf η y := by
    intro y
    exact bootstrapScalarCDFIndexed_eq_cdf_map
      (Pstar := Pstar) (Zstar := Zstar) (n := n) (ω := ω) hPstar hZ y
  have hx_cdf : cdf η x < p := by
    simpa [hcdf_eq x] using hx
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    stieltjesFunction_exists_right_lt_of_lt (cdf η) (x := x) hx_cdf
  exact ⟨δ, hδ_pos, by simpa [hcdf_eq (x + δ)] using hδ⟩

/-- Pointwise a.e.-measurability package for indexed scalar conditional CDF
local-right bracketing. -/
theorem bootstrapScalarCDFIndexed_local_right_lt_of_aemeasurable
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    {p : ℝ} :
    ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
      ∃ δ : ℝ, 0 < δ ∧
        bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p :=
  fun n ω x hx =>
    bootstrapScalarCDFIndexed_exists_right_lt_of_lt
      (Pstar := Pstar) (Zstar := Zstar) (n := n) (ω := ω)
      (x := x) (hPstar n ω) (hZ n ω) hx

/-- For an indexed scalar conditional bootstrap CDF, every level below one is
reached somewhere. -/
theorem bootstrapScalarCDFIndexed_level_nonempty_of_aemeasurable
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    {p : ℝ} (hp : p < 1) :
    ∀ n ω,
      ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
        Set ℝ).Nonempty := by
  intro n ω
  let η : Measure ℝ := (Pstar n ω).map (Zstar n ω)
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  haveI : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map (hZ n ω)
  have hEventually :
      ∀ᶠ x in atTop, p < cdf η x :=
    (ProbabilityTheory.tendsto_cdf_atTop η).eventually_const_lt hp
  obtain ⟨x, hx⟩ := hEventually.exists
  refine ⟨x, ?_⟩
  have hcdf_eq :
      bootstrapScalarCDFIndexed Pstar Zstar x n ω = cdf η x :=
    bootstrapScalarCDFIndexed_eq_cdf_map
      (Pstar := Pstar) (Zstar := Zstar) (n := n) (ω := ω)
      (hPstar n ω) (hZ n ω) x
  change p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω
  rw [hcdf_eq]
  exact le_of_lt hx

/-- For an indexed scalar conditional bootstrap CDF, every strictly positive
level has a lower-bounded generalized-inverse set. -/
theorem bootstrapScalarCDFIndexed_level_bddBelow_of_aemeasurable
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    {p : ℝ} (hp : 0 < p) :
    ∀ n ω, BddBelow
      {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} := by
  intro n ω
  let η : Measure ℝ := (Pstar n ω).map (Zstar n ω)
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  haveI : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map (hZ n ω)
  have hEventually :
      ∀ᶠ x in atBot, cdf η x < p :=
    (ProbabilityTheory.tendsto_cdf_atBot η).eventually_lt_const hp
  obtain ⟨M, hM⟩ := eventually_atBot.mp hEventually
  refine ⟨M, ?_⟩
  intro x hx
  by_contra hnot
  have hx_le : x ≤ M := le_of_not_ge hnot
  have hcdf_lt : cdf η x < p := hM x hx_le
  have hboot_lt : bootstrapScalarCDFIndexed Pstar Zstar x n ω < p := by
    have hcdf_eq :
        bootstrapScalarCDFIndexed Pstar Zstar x n ω = cdf η x :=
      bootstrapScalarCDFIndexed_eq_cdf_map
        (Pstar := Pstar) (Zstar := Zstar) (n := n) (ω := ω)
        (hPstar n ω) (hZ n ω) x
    simpa [hcdf_eq] using hcdf_lt
  exact not_lt_of_ge hx hboot_lt

/-- Scalar CDF convergence extracted from indexed one-dimensional Hansen
Definition 10.2. -/
theorem TendstoInBootstrapDistributionIndexed.bootstrapScalarCDF_tendsto_unit
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    {x : ℝ}
    (hx :
      ContinuousAt
        (fun y : Unit → ℝ =>
          vectorCDF ν (fun ωlim (_ : Unit) => Z ωlim) y)
        (fun _ : Unit => x)) :
    TendstoInMeasure μ
      (fun n ω => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
      atTop (fun _ => scalarCDF ν Z x) := by
  have hunit :=
    hZ.tendsto_cdf (x := fun _ : Unit => x) hx
  refine TendstoInMeasure.congr (fun n => ?_) ?_ hunit
  · exact ae_of_all μ fun ω => by
      simp [bootstrapScalarCDFIndexed, bootstrapVectorCDFIndexed, coordinateLE]
  · exact ae_of_all μ fun _ => by
      simp [scalarCDF, vectorCDF, coordinateLE]

/-- Scalar CDF convergence extracted from indexed one-dimensional Hansen
Definition 10.2, with continuity stated for the scalar CDF. -/
theorem
TendstoInBootstrapDistributionIndexed.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    {x : ℝ}
    (hx : ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (fun n ω => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
      atTop (fun _ => scalarCDF ν Z x) :=
  hZ.bootstrapScalarCDF_tendsto_unit (x := x)
    (continuousAt_vectorCDF_unit_of_scalarCDF hx)

/-- Indexed scalar CDF convergence when the limiting statistic is the identity
under a scalar probability law. -/
theorem TendstoInBootstrapDistributionIndexed.bootstrapScalarCDF_tendsto_unit_id_cdf
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η]
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    {x : ℝ}
    (hx : ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (fun n ω => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
      atTop (fun _ => cdf η x) := by
  simpa using
    (TendstoInBootstrapDistributionIndexed.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := η)
      (Z := fun x : ℝ => x) hZ (by simpa using hx))

/-- Indexed scalar conditional-bootstrap CDF convergence from a
one-dimensional Definition 10.2 limit whose scalar statistic has law `η`. -/
theorem TendstoInBootstrapDistributionIndexed.bootstrapScalarCDF_tendsto_unit_law_cdf
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η]
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hZlaw : HasLaw Z η ν)
    {x : ℝ}
    (hx : ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (fun n ω => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
      atTop (fun _ => cdf η x) := by
  have hscalar : scalarCDF ν Z = fun y => cdf η y :=
    scalarCDF_eq_cdf_of_hasLaw hZlaw
  have hxscalar : ContinuousAt (scalarCDF ν Z) x := by
    simpa [hscalar] using hx
  have h :=
    TendstoInBootstrapDistributionIndexed.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν)
      (Z := Z) hZ hxscalar
  simpa [hscalar] using h

/-- Indexed bootstrap scalar quantile convergence from pointwise conditional-CDF
convergence. -/
theorem bootstrapScalarQuantileIndexed_tendsto_of_cdf_brackets
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {G : ℝ → ℝ} {p q : ℝ} {qseq : ℕ → Ω → ℝ}
    (hbracket :
      CDFQuantileBracket
        (fun n ω x => bootstrapScalarCDFIndexed Pstar Zstar x n ω) p qseq)
    (hleft : ∀ ε : ℝ, 0 < ε → G (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < G (q + ε))
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ qseq atTop (fun _ => q) :=
  tendstoInMeasure_quantile_of_cdf_brackets
    (μ := μ)
    (Gseq := fun n ω x => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
    hbracket hleft hright hG

/-- Indexed bootstrap scalar quantile convergence with a strictly increasing
limiting CDF. -/
theorem bootstrapScalarQuantileIndexed_tendsto_of_strictMono_cdf
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {G : ℝ → ℝ} {p q : ℝ} {qseq : ℕ → Ω → ℝ}
    (hbracket :
      CDFQuantileBracket
        (fun n ω x => bootstrapScalarCDFIndexed Pstar Zstar x n ω) p qseq)
    (hstrict : StrictMono G)
    (hq : G q = p)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ qseq atTop (fun _ => q) :=
  tendstoInMeasure_quantile_of_strictMono_cdf
    (μ := μ)
    (Gseq := fun n ω x => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
    hbracket hstrict hq hG

/-- Indexed bootstrap scalar quantile convergence from one-dimensional indexed
Hansen Definition 10.2. -/
theorem bootstrapScalarQuantileIndexed_tendsto_of_bootstrapDistribution_unit
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    {qseq : ℕ → Ω → ℝ}
    (hbracket :
      CDFQuantileBracket
        (fun n ω x => bootstrapScalarCDFIndexed Pstar Zstar x n ω) p qseq)
    (hleft : ∀ ε : ℝ, 0 < ε → scalarCDF ν Z (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < scalarCDF ν Z (q + ε))
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ qseq atTop (fun _ => q) :=
  bootstrapScalarQuantileIndexed_tendsto_of_cdf_brackets
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (G := scalarCDF ν Z)
    hbracket hleft hright
    (fun x =>
      TendstoInBootstrapDistributionIndexed.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
        hZ (hcont x))

/-- Strict-limit-CDF specialization of indexed scalar quantile convergence from
one-dimensional indexed Hansen Definition 10.2. -/
theorem
bootstrapScalarQuantileIndexed_tendsto_of_bootstrapDistribution_unit_strictMono
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    {qseq : ℕ → Ω → ℝ}
    (hbracket :
      CDFQuantileBracket
        (fun n ω x => bootstrapScalarCDFIndexed Pstar Zstar x n ω) p qseq)
    (hstrict : StrictMono (scalarCDF ν Z))
    (hq : scalarCDF ν Z q = p)
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ qseq atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarQuantileIndexed_tendsto_of_bootstrapDistribution_unit
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      hbracket hleft hright hZ hcont

/-- Lower generalized inverse of an indexed scalar conditional bootstrap CDF. -/
noncomputable def bootstrapScalarLowerQuantileIndexed
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → ℝ)
    (p : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  lowerCDFQuantile (fun x => bootstrapScalarCDFIndexed Pstar Zstar x n ω) p

/-- Indexed scalar lower-quantile convergence from pointwise CDF convergence
and concrete generalized-inverse bracketing assumptions. -/
theorem bootstrapScalarLowerQuantileIndexed_tendsto_of_cdf_brackets
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {G : ℝ → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x =>
        bootstrapScalarCDFIndexed Pstar Zstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧
          bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p)
    (hleft : ∀ ε : ℝ, 0 < ε → G (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < G (q + ε))
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) :=
  lowerCDFQuantile_tendstoInMeasure_of_cdf_brackets
    (μ := μ)
    (Gseq := fun n ω x => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
    hmono hne hbdd hlocal hleft hright hG

/-- Indexed scalar lower-quantile convergence with a strictly increasing
limiting CDF. -/
theorem bootstrapScalarLowerQuantileIndexed_tendsto_of_strictMono_cdf
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {G : ℝ → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x =>
        bootstrapScalarCDFIndexed Pstar Zstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧
          bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p)
    (hstrict : StrictMono G)
    (hq : G q = p)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) :=
  lowerCDFQuantile_tendstoInMeasure_of_strictMono_cdf
    (μ := μ)
    (Gseq := fun n ω x => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
    hmono hne hbdd hlocal hstrict hq hG

/-- Indexed scalar lower-quantile convergence from one-dimensional indexed
Hansen Definition 10.2. -/
theorem bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x =>
        bootstrapScalarCDFIndexed Pstar Zstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧
          bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p)
    (hleft : ∀ ε : ℝ, 0 < ε → scalarCDF ν Z (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < scalarCDF ν Z (q + ε))
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) :=
  bootstrapScalarLowerQuantileIndexed_tendsto_of_cdf_brackets
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (G := scalarCDF ν Z)
    hmono hne hbdd hlocal hleft hright
    (fun x =>
      TendstoInBootstrapDistributionIndexed.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
        hZ (hcont x))

/-- Strict-limit-CDF specialization of indexed scalar lower-quantile
convergence from one-dimensional indexed Hansen Definition 10.2. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_strictMono
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x =>
        bootstrapScalarCDFIndexed Pstar Zstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧
          bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p)
    (hstrict : StrictMono (scalarCDF ν Z))
    (hq : scalarCDF ν Z q = p)
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      hmono hne hbdd hlocal hleft hright hZ hcont

/-- Finite-measure indexed scalar lower-quantile convergence from
one-dimensional indexed Hansen Definition 10.2. -/
theorem bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_finite
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧
          bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p)
    (hleft : ∀ ε : ℝ, 0 < ε → scalarCDF ν Z (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < scalarCDF ν Z (q + ε))
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  have hmono :
      ∀ n ω, Monotone (fun x =>
        bootstrapScalarCDFIndexed Pstar Zstar x n ω) := by
    intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact bootstrapScalarCDFIndexed_mono (Pstar := Pstar) (Zstar := Zstar)
      (n := n) (ω := ω)
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      hmono hne hbdd hlocal hleft hright hZ hcont

/-- Strict finite-measure indexed scalar lower-quantile convergence from
one-dimensional indexed Hansen Definition 10.2. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_strictMono_finite
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧
          bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p)
    (hstrict : StrictMono (scalarCDF ν Z))
    (hq : scalarCDF ν Z q = p)
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_finite
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      hPstar hne hbdd hlocal hleft hright hZ hcont

/-- Law-CDF specialization of indexed scalar lower-quantile convergence from
one-dimensional indexed Hansen Definition 10.2. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_finite
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧
          bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p)
    (hleft : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < cdf η (q + ε))
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  have hmono :
      ∀ n ω, Monotone (fun x =>
        bootstrapScalarCDFIndexed Pstar Zstar x n ω) := by
    intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact bootstrapScalarCDFIndexed_mono (Pstar := Pstar) (Zstar := Zstar)
      (n := n) (ω := ω)
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_cdf_brackets
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
      (G := fun x => cdf η x) hmono hne hbdd hlocal
      hleft hright
      (fun x =>
        hZ.bootstrapScalarCDF_tendsto_unit_id_cdf
          (Pstar := Pstar) (Zstar := Zstar) (x := x) (hcont x))

/-- Strict law-CDF specialization of indexed scalar lower-quantile
convergence. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_strictMono_id_cdf_finite
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧
          bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p)
    (hstrict : StrictMono (fun x => cdf η x))
    (hq : cdf η q = p)
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_finite
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η)
      hPstar hne hbdd hlocal hleft hright hZ hcont

/-- Indexed law-CDF scalar lower-quantile wrapper with the local-right CDF
bracketing premise discharged from pointwise a.e. measurability. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_aemeasurable
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hleft : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < cdf η (q + ε))
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_finite
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η) (p := p)
      (q := q) hPstarFinite hne hbdd
      (bootstrapScalarCDFIndexed_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas)
      hleft hright hZ hcont

/-- Strict indexed law-CDF scalar lower-quantile wrapper with the local-right
CDF bracketing premise discharged from pointwise a.e. measurability. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_strictMono_id_cdf_aemeasurable
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hstrict : StrictMono (fun x => cdf η x))
    (hq : cdf η q = p)
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_aemeasurable
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η)
      hPstar hZmeas hne hbdd hleft hright hZ hcont

/-- Indexed law-CDF scalar lower-quantile wrapper for probability-valued
conditional bootstrap CDFs at levels `0 < p < 1`. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_probability
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hleft : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < cdf η (q + ε))
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_aemeasurable
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η) (p := p)
      (q := q) hPstar hZmeas
      (bootstrapScalarCDFIndexed_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas hp_lt_one)
      (bootstrapScalarCDFIndexed_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas hp_pos)
      hleft hright hZ hcont

/-- Indexed law-CDF scalar lower-quantile wrapper for probability-valued
conditional bootstrap CDFs at levels `0 < p < 1`.

This is the sample-size-dependent counterpart of
`bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_law_cdf_probability`. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_law_cdf_probability
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hleft : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < cdf η (q + ε))
    (hT :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hZlaw : HasLaw Z η ν)
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_cdf_brackets
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
      (G := fun x => cdf η x) (p := p) (q := q)
      (fun n ω => by
        haveI : IsFiniteMeasure (Pstar n ω) := hPstarFinite n ω
        exact bootstrapScalarCDFIndexed_mono (Pstar := Pstar) (Zstar := Zstar)
          (n := n) (ω := ω))
      (bootstrapScalarCDFIndexed_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas hp_lt_one)
      (bootstrapScalarCDFIndexed_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas hp_pos)
      (bootstrapScalarCDFIndexed_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas)
      hleft hright
      (fun x =>
        TendstoInBootstrapDistributionIndexed.bootstrapScalarCDF_tendsto_unit_law_cdf
          (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
          (ν := ν) (Z := Z) (η := η) hT hZlaw (hcont x))

/-- Strict indexed law-CDF scalar lower-quantile wrapper for
probability-valued conditional bootstrap CDFs at levels `0 < p < 1`. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_strictMono_id_cdf_probability
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hq : cdf η q = p)
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_probability
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η)
      hPstar hZmeas hp_pos hp_lt_one hleft hright hZ hcont

end QuantileConvergence

end HansenEconometrics
