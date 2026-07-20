import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Function

/-!
# The Koopman operator and the von Neumann mean ergodic theorem

This file constructs the Koopman operator on `L²` associated with a measure-preserving map and
instantiates the von Neumann mean ergodic theorem for it. It is the Hilbert-space core underlying
Hansen's *Econometrics* §14.6 ergodic theorem (Theorems 14.7–14.9): the `L²`-norm convergence of
Birkhoff averages to a conditional-mean limit.

## Main declarations

* `ProbabilityTheory.koopmanL2` — for a measure-preserving map `f : α → α`, the **Koopman
  operator** `g ↦ g ∘ f` as a continuous linear self-map of `Lp ℝ 2 μ`, built from
  `MeasureTheory.Lp.compMeasurePreserving`.
* `ProbabilityTheory.koopmanL2_norm_le_one` — the Koopman operator is a contraction (it is in fact
  an isometry), so its operator norm is at most one.
* `ProbabilityTheory.mem_eqLocus_koopmanL2_iff` — a function lies in the fixed subspace
  `LinearMap.eqLocus (koopmanL2 hf) 1` of the Koopman operator iff it is a.e. invariant under `f`.
* `ProbabilityTheory.MeasurePreserving.tendsto_birkhoffAverage_L2` — the **von Neumann mean
  ergodic theorem** for the Koopman operator: the Birkhoff averages of `g` under `koopmanL2 hf`
  converge in `L²` to the orthogonal projection of `g` onto the fixed subspace.
* `ProbabilityTheory.Ergodic.mem_eqLocus_koopmanL2_iff` — for an ergodic map on a probability
  space, the Koopman fixed subspace is exactly the a.e.-constant functions.
* `ProbabilityTheory.Ergodic.tendsto_birkhoffAverage_integral_L2` — the endpoint consumed by the
  chapter: for an ergodic map on a probability space and `g ∈ L²`, the (pointwise) Birkhoff
  averages of `g` converge in `L²` to the constant `∫ g`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace ProbabilityTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α}

/-- **Koopman operator.** For a measure-preserving map `f : α → α`, composition with `f`,
`g ↦ g ∘ f`, is a continuous linear self-map of `Lp ℝ 2 μ`. It is realized here via
`MeasureTheory.Lp.compMeasurePreserving` and is an isometry (see `koopmanL2_norm_le_one`). -/
noncomputable def koopmanL2 (hf : MeasurePreserving f μ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ f hf).toContinuousLinearMap

theorem koopmanL2_apply (hf : MeasurePreserving f μ μ) (g : Lp ℝ 2 μ) :
    koopmanL2 hf g = Lp.compMeasurePreserving f hf g := by
  rw [koopmanL2, LinearIsometry.coe_toContinuousLinearMap, ← LinearIsometry.coe_toLinearMap]
  change (Lp.compMeasurePreservingₗ ℝ f hf) g = _
  rw [Lp.compMeasurePreservingₗ_apply]
  rfl

/-- The Koopman operator is a contraction: `‖koopmanL2 hf‖ ≤ 1`. It is in fact an isometry, but the
contraction bound is what the mean ergodic theorem requires. -/
theorem koopmanL2_norm_le_one (hf : MeasurePreserving f μ μ) : ‖koopmanL2 hf‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => ?_
  simp [koopmanL2_apply, Lp.norm_compMeasurePreserving]

theorem koopmanL2_coeFn (hf : MeasurePreserving f μ μ) (g : Lp ℝ 2 μ) :
    ⇑(koopmanL2 hf g) =ᵐ[μ] ⇑g ∘ f :=
  Lp.coeFn_compMeasurePreserving g hf

/-- A function is fixed by the Koopman operator iff it is a.e. invariant under `f`: membership in
the fixed subspace `LinearMap.eqLocus (koopmanL2 hf) 1` is exactly a.e. `f`-invariance. This is the
fixed-space interface consumed by the mean ergodic theorem. -/
theorem mem_eqLocus_koopmanL2_iff (hf : MeasurePreserving f μ μ) (g : Lp ℝ 2 μ) :
    g ∈ LinearMap.eqLocus (koopmanL2 hf) 1 ↔ ⇑g ∘ f =ᵐ[μ] ⇑g := by
  rw [LinearMap.mem_eqLocus, ContinuousLinearMap.one_apply, Lp.ext_iff]
  exact ⟨fun h => (koopmanL2_coeFn hf g).symm.trans h, fun h => (koopmanL2_coeFn hf g).trans h⟩

/-- The `k`-th Koopman iterate of `g` is a.e. equal to `g ∘ f^[k]`. -/
private theorem koopmanL2_iterate_coeFn (hf : MeasurePreserving f μ μ) (g : Lp ℝ 2 μ) (k : ℕ) :
    ⇑((⇑(koopmanL2 hf))^[k] g) =ᵐ[μ] ⇑g ∘ f^[k] := by
  have h1 : (⇑(koopmanL2 hf))^[k] = ⇑(Lp.compMeasurePreserving f^[k] (hf.iterate k)) := by
    rw [show ⇑(koopmanL2 hf) = ⇑(Lp.compMeasurePreserving f hf) from funext (koopmanL2_apply hf)]
    exact Lp.compMeasurePreserving_iterate hf k
  rw [h1]
  exact Lp.coeFn_compMeasurePreserving g (hf.iterate k)

/-- The coercion of the operator Birkhoff sum `birkhoffSum (koopmanL2 hf) id n g` agrees a.e. with
the pointwise Birkhoff sum `birkhoffSum f (⇑g) n`. This identifies the Hilbert-space iteration with
the dynamical average. -/
private theorem koopmanL2_birkhoffSum_coeFn (hf : MeasurePreserving f μ μ) (g : Lp ℝ 2 μ) (n : ℕ) :
    ⇑(birkhoffSum (koopmanL2 hf) id n g) =ᵐ[μ] birkhoffSum f (⇑g) n := by
  induction n with
  | zero =>
    rw [birkhoffSum_zero, birkhoffSum_zero']
    exact Lp.coeFn_zero ℝ 2 μ
  | succ n ih =>
    have hstep : birkhoffSum (koopmanL2 hf) id (n + 1) g
        = birkhoffSum (koopmanL2 hf) id n g + (⇑(koopmanL2 hf))^[n] g := by
      rw [birkhoffSum_succ]; rfl
    rw [hstep]
    filter_upwards [Lp.coeFn_add (birkhoffSum (koopmanL2 hf) id n g) ((⇑(koopmanL2 hf))^[n] g),
      ih, koopmanL2_iterate_coeFn hf g n] with x hadd hih hiter
    rw [birkhoffSum_succ, hadd, Pi.add_apply, hih, hiter]
    rfl

/-- The coercion of the operator Birkhoff average `birkhoffAverage ℝ (koopmanL2 hf) id n g` agrees
a.e. with the pointwise Birkhoff average `birkhoffAverage ℝ f (⇑g) n`. -/
theorem koopmanL2_birkhoffAverage_coeFn (hf : MeasurePreserving f μ μ) (g : Lp ℝ 2 μ) (n : ℕ) :
    ⇑(birkhoffAverage ℝ (koopmanL2 hf) id n g) =ᵐ[μ] birkhoffAverage ℝ f (⇑g) n := by
  have hL : birkhoffAverage ℝ (koopmanL2 hf) id n g
      = (n : ℝ)⁻¹ • birkhoffSum (koopmanL2 hf) id n g := rfl
  have hR : birkhoffAverage ℝ f (⇑g) n = (n : ℝ)⁻¹ • birkhoffSum f (⇑g) n := rfl
  rw [hL, hR]
  filter_upwards [Lp.coeFn_smul (n : ℝ)⁻¹ (birkhoffSum (koopmanL2 hf) id n g),
    koopmanL2_birkhoffSum_coeFn hf g n] with x hsmul hsum
  rw [hsmul, Pi.smul_apply, Pi.smul_apply, hsum]

/-- **Von Neumann mean ergodic theorem for a measure-preserving map.** For `g ∈ L²`, the Birkhoff
averages of `g` under the Koopman operator converge in `L²` to the orthogonal projection of `g` onto
the subspace of Koopman-fixed functions. This is
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection` instantiated at the Koopman
operator. -/
theorem MeasurePreserving.tendsto_birkhoffAverage_L2 (hf : MeasurePreserving f μ μ) (g : Lp ℝ 2 μ) :
    Tendsto (fun n => birkhoffAverage ℝ (koopmanL2 hf) id n g) atTop
      (𝓝 ((LinearMap.eqLocus (koopmanL2 hf) 1).orthogonalProjection g)) :=
  ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection (koopmanL2 hf)
    (koopmanL2_norm_le_one hf) g

section Constants

variable [IsProbabilityMeasure μ]

/-- The constant function `1` as an element of `L²` of a probability measure, realized as the
`indicatorConstLp` of the whole space. On an ergodic system it spans the fixed subspace of the
Koopman operator. -/
private noncomputable def constOneL2 (μ : Measure α) [IsProbabilityMeasure μ] : Lp ℝ 2 μ :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ Set.univ) (1 : ℝ)

private theorem constOneL2_coeFn : ⇑(constOneL2 μ) =ᵐ[μ] Function.const α (1 : ℝ) := by
  unfold constOneL2
  filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := MeasurableSet.univ)
    (hμs := measure_ne_top μ Set.univ) (c := (1 : ℝ))] with x hx
  rw [hx, Set.indicator_univ]; rfl

private theorem norm_constOneL2 : ‖constOneL2 μ‖ = 1 := by
  unfold constOneL2
  rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp

private theorem inner_constOneL2 (g : Lp ℝ 2 μ) :
    (inner ℝ (constOneL2 μ) g : ℝ) = ∫ x, g x ∂μ := by
  unfold constOneL2
  rw [← setIntegral_univ]
  exact L2.inner_indicatorConstLp_one MeasurableSet.univ (measure_ne_top μ Set.univ) g

private theorem koopmanL2_constOneL2 (hf : MeasurePreserving f μ μ) :
    koopmanL2 hf (constOneL2 μ) = constOneL2 μ := by
  unfold constOneL2
  rw [koopmanL2_apply, Lp.indicatorConstLp_compMeasurePreserving]
  simp only [Set.preimage_univ]

/-- On an ergodic probability space the Koopman fixed subspace is the line spanned by the constant
`1`. Kept internal (its statement mentions the private constant `constOneL2`); the consumable
characterization is `Ergodic.mem_eqLocus_koopmanL2_iff`. -/
private theorem eqLocus_koopmanL2_eq_span_one (hf : Ergodic f μ) :
    LinearMap.eqLocus (koopmanL2 hf.toMeasurePreserving) 1 = ℝ ∙ constOneL2 μ := by
  refine le_antisymm (fun g hg => ?_) ?_
  · rw [mem_eqLocus_koopmanL2_iff] at hg
    obtain ⟨c, hc⟩ := hf.ae_eq_const_of_ae_eq_comp_ae (Lp.aestronglyMeasurable g) hg
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [Lp.ext_iff]
    filter_upwards [Lp.coeFn_smul c (constOneL2 μ), constOneL2_coeFn (μ := μ), hc]
      with x h1 h2 h3
    rw [h1, Pi.smul_apply, h2]
    simp [h3]
  · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_eqLocus, ContinuousLinearMap.one_apply]
    exact koopmanL2_constOneL2 hf.toMeasurePreserving

/-- **Fixed subspace of the Koopman operator on an ergodic system.** For an ergodic map on a
probability space, the functions fixed by the Koopman operator are exactly the a.e.-constant
functions: `g` lies in the fixed subspace `LinearMap.eqLocus (koopmanL2 hf.toMeasurePreserving) 1`
iff `g` is a.e. equal to a constant. This is the ergodic sharpening of
`mem_eqLocus_koopmanL2_iff`. -/
theorem Ergodic.mem_eqLocus_koopmanL2_iff (hf : Ergodic f μ) (g : Lp ℝ 2 μ) :
    g ∈ LinearMap.eqLocus (koopmanL2 hf.toMeasurePreserving) 1
      ↔ ∃ c : ℝ, ⇑g =ᵐ[μ] Function.const α c := by
  refine ⟨fun hg => ?_, fun ⟨c, hc⟩ => ?_⟩
  · rw [ProbabilityTheory.mem_eqLocus_koopmanL2_iff] at hg
    exact hf.ae_eq_const_of_ae_eq_comp_ae (Lp.aestronglyMeasurable g) hg
  · rw [eqLocus_koopmanL2_eq_span_one hf, Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [Lp.ext_iff]
    filter_upwards [Lp.coeFn_smul c (constOneL2 μ), constOneL2_coeFn (μ := μ), hc]
      with x h1 h2 h3
    rw [h1, Pi.smul_apply, h2]
    simp [h3]

/-- **Ergodic theorem in `L²` (map form).** For an ergodic map on a probability space and a
square-integrable `g`, the pointwise Birkhoff averages of `g` converge in `L²` to the constant
`∫ g`. This is the endpoint consumed by the chapter's ergodic theorem. -/
theorem Ergodic.tendsto_birkhoffAverage_integral_L2 (hf : Ergodic f μ) {g : α → ℝ}
    (hg : MemLp g 2 μ) :
    Tendsto (fun n => eLpNorm (fun x => birkhoffAverage ℝ f g n x - ∫ y, g y ∂μ) 2 μ) atTop
      (𝓝 0) := by
  have hvn := MeasurePreserving.tendsto_birkhoffAverage_L2 hf.toMeasurePreserving (hg.toLp g)
  have hlim : (↑((LinearMap.eqLocus (koopmanL2 hf.toMeasurePreserving) 1).orthogonalProjection
      (hg.toLp g)) : Lp ℝ 2 μ) = (∫ x, ⇑(hg.toLp g) x ∂μ) • constOneL2 μ := by
    rw [← Submodule.starProjection_apply]
    simp only [eqLocus_koopmanL2_eq_span_one hf]
    rw [Submodule.starProjection_unit_singleton ℝ norm_constOneL2, inner_constOneL2]
  rw [hlim, Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hvn
  have hint : (∫ x, ⇑(hg.toLp g) x ∂μ) = ∫ y, g y ∂μ := integral_congr_ae hg.coeFn_toLp
  refine hvn.congr fun n => ?_
  apply eLpNorm_congr_ae
  filter_upwards [koopmanL2_birkhoffAverage_coeFn hf.toMeasurePreserving (hg.toLp g) n,
    hf.toMeasurePreserving.quasiMeasurePreserving.birkhoffAverage_ae_eq_of_ae_eq ℝ hg.coeFn_toLp n,
    Lp.coeFn_smul (∫ x, ⇑(hg.toLp g) x ∂μ) (constOneL2 μ), constOneL2_coeFn (μ := μ)]
    with x hbA hbAg hsmul honex
  rw [Pi.sub_apply, hbA, hbAg, hsmul, Pi.smul_apply, honex]
  simp only [Function.const_apply, smul_eq_mul, mul_one]
  rw [hint]

end Constants

end ProbabilityTheory
