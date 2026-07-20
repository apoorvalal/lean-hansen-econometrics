import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import HansenEconometrics.Chapter14TimeSeries

/-!
# Chapter 14: Ergodic theory — the path-space shift bridge

This file builds the bridge between a discrete-time stochastic process `X : ℤ → Ω → E` and
the theory of measure-preserving / ergodic dynamical systems, by transporting the process to
its *path law* on sequence space `ℤ → E` and letting the coordinate shift act there. It is the
foundational module for Hansen §14 ergodic theory (Theorems 14.4–14.9): everything downstream
is phrased as a statement about the shift `pathShift E` acting on `pathLaw X P`.

## Main declarations

* `ProbabilityTheory.pathShift E` — the two-sided coordinate shift on `ℤ → E`,
  `(pathShift E x) t = x (t + 1)`, together with `ProbabilityTheory.measurable_pathShift`,
  the measurable equivalence `ProbabilityTheory.pathShiftEquiv`, and the iterate formula
  `ProbabilityTheory.pathShift_iterate : (pathShift E)^[n] x t = x (t + n)`.
* `ProbabilityTheory.pathLaw X P` — the law of the whole path `fun ω t => X t ω` on `ℤ → E`,
  i.e. `P.map (fun ω t => X t ω)`, with `ProbabilityTheory.isProbabilityMeasure_pathLaw` and
  the shift characterization `ProbabilityTheory.pathLaw_map_pathShift`.
* `ProbabilityTheory.IsStrictlyStationary.measurePreserving_pathShift` — a strictly stationary
  process makes the shift measure-preserving for its path law. This is the dynamical-systems
  reading of strict stationarity, obtained from
  `ProbabilityTheory.IsStrictlyStationary.identDistrib_path`.
* `ProbabilityTheory.IsErgodicProcess X P` — the process `X` is *ergodic* under `P` if the
  shift `pathShift E` is `Ergodic` for `pathLaw X P`. `ProbabilityTheory.IsErgodicProcess.congr_ae`
  records invariance under an a.e. modification of each coordinate.
* `ProbabilityTheory.IsErgodicProcess.comp_shiftEquivariant` — **Hansen Theorem 14.5**: a
  measurable functional of the whole shifted path of an ergodic process is again ergodic. This
  is the ergodic companion of `ProbabilityTheory.IsStrictlyStationary.comp_shiftEquivariant`
  (the strict-stationarity half, Hansen Theorem 14.2).

* `ProbabilityTheory.ergodic_pathShift_infinitePi` — **Bernoulli-shift ergodicity**: the coordinate
  shift `pathShift E` is `Ergodic` for the countable product `Measure.infinitePi (fun _ : ℤ => μ)`
  of a probability measure `μ`. This is the reusable analytic core (the classical
  cylinder-approximation / asymptotic-independence argument), of independent interest.
* `ProbabilityTheory.ergodic_pathShift_of_pathLaw_eq_infinitePi` — the bridge from "the path law is
  an i.i.d. product" to ergodicity of the process; the reusable engine behind Theorems 14.4/14.14.
* `ProbabilityTheory.IsErgodicProcess.of_iid` — **Hansen Theorem 14.4**: an i.i.d. process is
  ergodic. This is the ergodic companion of `ProbabilityTheory.IsStrictlyStationary.of_iid`
  (Hansen Theorem 14.1, the strict-stationarity half): the path law is the product of the common
  one-dimensional law, so `ergodic_pathShift_infinitePi` applies.
-/

open MeasureTheory

open scoped symmDiff ENNReal

namespace ProbabilityTheory

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- The two-sided **path shift** on sequence space `ℤ → E`: `(pathShift E x) t = x (t + 1)`.
This is the map whose measure-preserving / ergodic behaviour under a path law encodes the
stationarity and ergodicity of the underlying process. -/
def pathShift (E : Type*) : (ℤ → E) → (ℤ → E) := fun x t => x (t + 1)

/-- The path shift is measurable. -/
theorem measurable_pathShift : Measurable (pathShift E) :=
  measurable_pi_iff.mpr fun t => measurable_pi_apply (t + 1)

/-- The path shift as a measurable equivalence of `ℤ → E`, with measurable inverse
`fun x t => x (t - 1)`. Provided directly (rather than via `MeasurableEquiv.piCongrLeft`) since
the coordinate type is constant; the forward map is definitionally `pathShift E`. -/
def pathShiftEquiv (E : Type*) [MeasurableSpace E] : (ℤ → E) ≃ᵐ (ℤ → E) where
  toFun := pathShift E
  invFun := fun x t => x (t - 1)
  left_inv := fun x => funext fun t => congrArg x (show t - 1 + 1 = t by ring)
  right_inv := fun x => funext fun t => congrArg x (show t + 1 - 1 = t by ring)
  measurable_toFun := measurable_pathShift
  measurable_invFun := measurable_pi_iff.mpr fun t => measurable_pi_apply (t - 1)

@[simp] theorem coe_pathShiftEquiv : ⇑(pathShiftEquiv E) = pathShift E := rfl

omit [MeasurableSpace E] in
/-- Iterating the path shift `n` times advances the index by `n`:
`(pathShift E)^[n] x t = x (t + n)`. -/
theorem pathShift_iterate (n : ℕ) (x : ℤ → E) (t : ℤ) :
    (pathShift E)^[n] x t = x (t + (n : ℤ)) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply,
      show pathShift E ((pathShift E)^[n] x) t = (pathShift E)^[n] x (t + 1) from rfl, ih (t + 1)]
    congr 1
    push_cast
    ring

variable {X Y : ℤ → Ω → E} {P : Measure Ω}

/-- The **path law** of a process `X : ℤ → Ω → E` under `P`: the law on sequence space `ℤ → E`
of the whole path `fun ω t => X t ω`. All ergodic-theoretic statements about `X` are phrased as
statements about `pathShift E` acting on `pathLaw X P`. -/
noncomputable def pathLaw (X : ℤ → Ω → E) (P : Measure Ω) : Measure (ℤ → E) :=
  P.map (fun ω t => X t ω)

/-- The path law of a process under a probability measure is a probability measure, whenever
each coordinate `X t` is `AEMeasurable`. -/
theorem isProbabilityMeasure_pathLaw [IsProbabilityMeasure P]
    (hX : ∀ t, AEMeasurable (X t) P) : IsProbabilityMeasure (pathLaw X P) :=
  Measure.isProbabilityMeasure_map (aemeasurable_pi_iff.mpr hX)

/-- Pushing the path law of `X` forward by the shift gives the path law of the shifted process
`fun t => X (t + 1)`. -/
theorem pathLaw_map_pathShift (hX : ∀ t, AEMeasurable (X t) P) :
    (pathLaw X P).map (pathShift E) = pathLaw (fun t => X (t + 1)) P := by
  simp only [pathLaw]
  rw [AEMeasurable.map_map_of_aemeasurable measurable_pathShift.aemeasurable
    (aemeasurable_pi_iff.mpr hX)]
  rfl

/-- **Strict stationarity as measure preservation.** For a strictly stationary, `AEMeasurable`
process over a finite measure, the path shift preserves the path law. This is the
dynamical-systems reading of strict stationarity and the entry point to Hansen's ergodic
theory; it is obtained from `IsStrictlyStationary.identDistrib_path` (the full-path
shift-invariance bridge). -/
theorem IsStrictlyStationary.measurePreserving_pathShift [IsFiniteMeasure P]
    (hX : IsStrictlyStationary X P) (hmeas : ∀ t, AEMeasurable (X t) P) :
    MeasurePreserving (pathShift E) (pathLaw X P) (pathLaw X P) := by
  refine ⟨measurable_pathShift, ?_⟩
  rw [pathLaw_map_pathShift hmeas]
  exact (hX.identDistrib_path hmeas 1).map_eq

/-- **Ergodic process.** `X : ℤ → Ω → E` is *ergodic* under `P` if the path shift `pathShift E`
is `Ergodic` for the path law `pathLaw X P`. Combined with
`IsStrictlyStationary.measurePreserving_pathShift`, this places Hansen's notion of an ergodic
stationary process squarely inside Mathlib's `Ergodic` dynamical-systems API. -/
def IsErgodicProcess (X : ℤ → Ω → E) (P : Measure Ω) : Prop :=
  Ergodic (pathShift E) (pathLaw X P)

/-- An a.e. modification of each coordinate leaves the path law unchanged (using that `ℤ` is
countable, so the coordinatewise a.e. equalities combine). Kept private; the public face is
`IsErgodicProcess.congr_ae`. -/
private theorem pathLaw_congr (h : ∀ t, X t =ᵐ[P] Y t) : pathLaw X P = pathLaw Y P := by
  simp only [pathLaw]
  refine Measure.map_congr ?_
  filter_upwards [ae_all_iff.mpr h] with ω hω
  exact funext hω

/-- Ergodicity of a process is invariant under an a.e. modification of each coordinate. -/
theorem IsErgodicProcess.congr_ae (h : ∀ t, X t =ᵐ[P] Y t) (hX : IsErgodicProcess X P) :
    IsErgodicProcess Y P := by
  change Ergodic (pathShift E) (pathLaw Y P)
  rw [← pathLaw_congr h]
  exact hX

/-- **Hansen Theorem 14.5.** A measurable functional `φ` of the whole shifted path
`fun j => Y (t + j)` of an ergodic process `Y` is again ergodic. This is the ergodic companion
of `IsStrictlyStationary.comp_shiftEquivariant` (Hansen Theorem 14.2, the strict-stationarity
half): Hansen's causal function of the history `(Yₜ, Yₜ₋₁, …)` is the special case where `φ`
ignores the strictly positive coordinates.

The proof transports ergodicity along the shift-equivariant factor map
`Φ y = fun t => φ (fun j => y (t + j))`, which is measure-preserving from `pathLaw Y P` to the
path law of the transformed process and semiconjugates the two shifts; the conclusion is then
`MeasureTheory.MeasurePreserving.ergodic_of_ergodic_semiconj`. Unlike Hansen's statement, only
ergodicity of `Y` (not separately strict stationarity, nor a probability-measure hypothesis) is
needed for the ergodic conclusion. -/
theorem IsErgodicProcess.comp_shiftEquivariant {F : Type*} [MeasurableSpace F]
    {φ : (ℤ → E) → F} (hφ : Measurable φ)
    (hYe : IsErgodicProcess Y P) (hY_meas : ∀ t, AEMeasurable (Y t) P) :
    IsErgodicProcess (fun t ω => φ (fun j => Y (t + j) ω)) P := by
  have hYe' : Ergodic (pathShift E) (pathLaw Y P) := hYe
  have hΦ : Measurable (fun (y : ℤ → E) t => φ (fun j => y (t + j))) :=
    measurable_pi_iff.mpr fun t =>
      hφ.comp (measurable_pi_iff.mpr fun j => measurable_pi_apply (t + j))
  have hmp : MeasurePreserving (fun (y : ℤ → E) t => φ (fun j => y (t + j)))
      (pathLaw Y P) (pathLaw (fun t ω => φ (fun j => Y (t + j) ω)) P) := by
    refine ⟨hΦ, ?_⟩
    simp only [pathLaw]
    rw [AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable (aemeasurable_pi_iff.mpr hY_meas)]
    rfl
  have hsemiconj : Function.Semiconj (fun (y : ℤ → E) t => φ (fun j => y (t + j)))
      (pathShift E) (pathShift F) := by
    intro y
    funext t
    exact congrArg φ (funext fun j => congrArg y (add_right_comm t j 1))
  exact hmp.ergodic_of_ergodic_semiconj hYe' measurable_pathShift hsemiconj

/-- For a finite set `I` of integers there is a natural-number shift `n` moving every element of
`I` off `I`; used to make a cylinder and its `n`-shift depend on disjoint coordinate blocks. -/
private theorem exists_shift_disjoint (I : Finset ℤ) : ∃ n : ℕ, ∀ i ∈ I, i + (n : ℤ) ∉ I := by
  classical
  rcases I.eq_empty_or_nonempty with rfl | hI
  · exact ⟨1, by simp⟩
  · refine ⟨(I.max' hI - I.min' hI).toNat + 1, fun i hi hmem => ?_⟩
    have hMm : I.min' hI ≤ I.max' hI := I.min'_le _ (I.max'_mem hI)
    have hcast : ((I.max' hI - I.min' hI).toNat : ℤ) = I.max' hI - I.min' hI :=
      Int.toNat_of_nonneg (by linarith)
    have hi_min : I.min' hI ≤ i := I.min'_le i hi
    have hmem_max : i + ((I.max' hI - I.min' hI).toNat + 1 : ℕ) ≤ I.max' hI := I.le_max' _ hmem
    push_cast at hmem_max
    rw [hcast] at hmem_max
    linarith

/-- The `n`-th shift preimage of a measurable cylinder on coordinate block `I` is again a measurable
cylinder, on the shifted block `I + n`. This is the relabeling step in the Bernoulli-shift
ergodicity argument: it exhibits the concrete disjoint-block cylinder `cylinder J B` equal to
`(pathShift E)^[n] ⁻¹' cylinder I S`. -/
private theorem exists_cylinder_iterate_preimage {E : Type*} [MeasurableSpace E]
    (I : Finset ℤ) (S : Set (∀ _ : I, E)) (hS : MeasurableSet S) (n : ℕ) :
    ∃ (J : Finset ℤ) (B : Set (∀ _ : J, E)), MeasurableSet B ∧
      J = I.map (Equiv.addRight (n : ℤ)).toEmbedding ∧
      (pathShift E)^[n] ⁻¹' cylinder I S = cylinder J B := by
  classical
  have hmemJ : ∀ i : I, ((i : ℤ) + n) ∈ I.map (Equiv.addRight (n : ℤ)).toEmbedding := by
    intro i
    rw [Finset.mem_map]
    exact ⟨(i : ℤ), i.2, by simp [Equiv.coe_addRight]⟩
  refine ⟨I.map (Equiv.addRight (n : ℤ)).toEmbedding,
    (fun (g : ∀ j : (I.map (Equiv.addRight (n : ℤ)).toEmbedding), E) (i : I) =>
        g ⟨(i : ℤ) + n, hmemJ i⟩) ⁻¹' S,
    (measurable_pi_iff.mpr fun i => measurable_pi_apply _) hS, rfl, ?_⟩
  ext x
  simp only [Set.mem_preimage, mem_cylinder]
  have hfun : I.restrict ((pathShift E)^[n] x)
      = fun (i : I) => (Finset.restrict _ x) ⟨(i : ℤ) + n, hmemJ i⟩ := by
    funext i
    change (pathShift E)^[n] x (i : ℤ) = x ((i : ℤ) + n)
    rw [pathShift_iterate]
  rw [hfun]

/-- **Bernoulli-shift ergodicity.** The two-sided coordinate shift `pathShift E` is `Ergodic` for
the countable product measure `Measure.infinitePi (fun _ : ℤ => μ)` of a probability measure `μ`.
This is the reusable analytic core of Hansen's ergodic theory: an i.i.d. process has this product
as its path law, so `IsErgodicProcess.of_iid` (Hansen Theorem 14.4) follows at once.

The proof is the classical cylinder-approximation argument. Measure preservation of the shift comes
from `Measure.infinitePi_map_piCongrLeft` with the reindexing `Equiv.addRight (-1)`. For ergodicity,
a measurable shift-invariant set `s` is approximated in symmetric difference by a cylinder `t`
depending on finitely many coordinates `I`; the `n`-shift of `t` (for `n` large) depends on
coordinates disjoint from `I`, hence is independent of `t` under the product measure
(`iIndepFun.indepFun_finset`), while invariance keeps `s` close to that shift. The resulting
estimate forces `μ(s) = μ(s)²`, so `μ(s) ∈ {0, 1}`. -/
theorem ergodic_pathShift_infinitePi {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] :
    Ergodic (pathShift E) (Measure.infinitePi fun _ : ℤ => μ) := by
  set ν : Measure (ℤ → E) := Measure.infinitePi (fun _ : ℤ => μ) with hν
  haveI : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  -- Measure preservation of the shift, via `piCongrLeft` with the reindexing `t ↦ t - 1`.
  set e : ℤ ≃ ℤ := Equiv.addRight (-1 : ℤ) with he
  have hcoe : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ℤ => E) e) = pathShift E := by
    rw [MeasurableEquiv.coe_piCongrLeft]
    funext x b
    obtain ⟨a, rfl⟩ := e.surjective b
    rw [Equiv.piCongrLeft_apply_apply]
    change x a = x (e a + 1)
    congr 1
    rw [he]
    simp only [Equiv.coe_addRight]
    ring
  have hmp : MeasurePreserving (pathShift E) ν ν := by
    rw [hν]
    refine ⟨measurable_pathShift, ?_⟩
    have hmap := Measure.infinitePi_map_piCongrLeft (μ := fun _ : ℤ => μ) e
    rw [hcoe] at hmap
    exact hmap
  refine ⟨hmp, ⟨fun s hs hs' => ?_⟩⟩
  -- coordinate projections are independent under the product measure
  have hcoord : iIndepFun (fun (i : ℤ) (x : ℤ → E) => x i) ν := by
    rw [hν]
    exact iIndepFun_infinitePi (Ω := fun _ : ℤ => E) (P := fun _ : ℤ => μ)
      (X := fun _ => (id : E → E)) (fun _ => measurable_id)
  set a : ℝ := ν.real s with ha_def
  have ha0 : 0 ≤ a := measureReal_nonneg
  have ha1 : a ≤ 1 := measureReal_le_one
  -- The core estimate: for every `ε > 0`, `|ν s − (ν s)²| ≤ 4ε`.
  have key : ∀ ε : ℝ, 0 < ε → |a - a ^ 2| ≤ 4 * ε := by
    intro ε hε
    -- approximate `s` by a measurable cylinder `t`
    obtain ⟨t, htC, hct⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := ν) isSetRing_measurableCylinders
      ⟨{Set.univ}, Set.countable_singleton _,
        Set.singleton_subset_iff.mpr (univ_mem_measurableCylinders _), by simp⟩
      (generateFrom_measurableCylinders (α := fun _ : ℤ => E)).symm hs
      (ENNReal.ofReal_pos.mpr hε)
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders t).mp htC
    set p : ℝ := ν.real (cylinder I S) with hp_def
    have hp0 : 0 ≤ p := measureReal_nonneg
    have hp1 : p ≤ 1 := measureReal_le_one
    -- shift the cylinder off its own coordinate block
    obtain ⟨n, hn⟩ := exists_shift_disjoint I
    obtain ⟨J, B, hB, hJeq, hpre⟩ := exists_cylinder_iterate_preimage I S hS n
    have hdisj : Disjoint I J := by
      rw [Finset.disjoint_left]
      intro c hcI hcJ
      rw [hJeq, Finset.mem_map] at hcJ
      obtain ⟨i, hiI, hic⟩ := hcJ
      simp only [Equiv.coe_toEmbedding, Equiv.coe_addRight] at hic
      rw [← hic] at hcI
      exact hn i hiI hcI
    have hIF : IndepFun (fun (x : ℤ → E) (i : I) => x i) (fun (x : ℤ → E) (j : J) => x j) ν :=
      hcoord.indepFun_finset I J hdisj fun i => measurable_pi_apply i
    set u : Set (ℤ → E) := (pathShift E)^[n] ⁻¹' cylinder I S with hu_def
    have hu_cyl : u = cylinder J B := hu_def.trans hpre
    have ht_meas : MeasurableSet (cylinder I S) :=
      MeasurableSet.cylinder (α := fun _ : ℤ => E) I hS
    have hu_meas : MeasurableSet u := (hmp.iterate n).measurable ht_meas
    have hpres : ν.real u = p := (hmp.iterate n).measureReal_preimage ht_meas.nullMeasurableSet
    -- independence of the two disjoint-block cylinders gives `ν(t ∩ Tⁿt) = (ν t)²`
    have hkey : ν (cylinder I S ∩ cylinder J B) = ν (cylinder I S) * ν (cylinder J B) :=
      hIF.measure_inter_preimage_eq_mul S B hS hB
    have hprodR : ν.real (cylinder I S ∩ cylinder J B)
        = ν.real (cylinder I S) * ν.real (cylinder J B) := by
      rw [measureReal_def, measureReal_def, measureReal_def, hkey, ENNReal.toReal_mul]
    have hinter : ν.real (cylinder I S ∩ u) = p * p := by
      rw [hu_cyl, hprodR, ← hp_def, ← hu_cyl, hpres]
    -- symmetric-difference control
    have hst : ν.real (s ∆ cylinder I S) < ε := by
      rw [symmDiff_comm, measureReal_def]
      calc (ν (cylinder I S ∆ s)).toReal
          < (ENNReal.ofReal ε).toReal :=
            (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hct
        _ = ε := ENNReal.toReal_ofReal hε.le
    have hap : |a - p| < ε :=
      lt_of_le_of_lt
        (abs_measureReal_sub_le_measureReal_symmDiff hs.nullMeasurableSet
          ht_meas.nullMeasurableSet) hst
    -- invariance of `s` transports the symmetric difference under the shift
    have hinv_n : (pathShift E)^[n] ⁻¹' s = s := Function.IsFixedPt.preimage_iterate hs' n
    have hsu : ν.real (s ∆ u) = ν.real (s ∆ cylinder I S) := by
      have hpre_symm : (pathShift E)^[n] ⁻¹' (s ∆ cylinder I S) = s ∆ u := by
        rw [Set.preimage_symmDiff, hinv_n]
      rw [← hpre_symm,
        (hmp.iterate n).measureReal_preimage (hs.symmDiff ht_meas).nullMeasurableSet]
    have hsub : s ∆ (cylinder I S ∩ u) ⊆ (s ∆ cylinder I S) ∪ (s ∆ u) := by
      intro y hy
      simp only [Set.mem_symmDiff, Set.mem_union, Set.mem_inter_iff] at hy ⊢
      tauto
    have hinter_symm : ν.real (s ∆ (cylinder I S ∩ u)) < 2 * ε := by
      calc ν.real (s ∆ (cylinder I S ∩ u))
          ≤ ν.real ((s ∆ cylinder I S) ∪ (s ∆ u)) := measureReal_mono hsub
        _ ≤ ν.real (s ∆ cylinder I S) + ν.real (s ∆ u) := measureReal_union_le _ _
        _ < ε + ε := by rw [hsu]; exact add_lt_add hst hst
        _ = 2 * ε := by ring
    have hai : |a - ν.real (cylinder I S ∩ u)| < 2 * ε :=
      lt_of_le_of_lt
        (abs_measureReal_sub_le_measureReal_symmDiff hs.nullMeasurableSet
          (ht_meas.inter hu_meas).nullMeasurableSet) hinter_symm
    have hp2 : ν.real (cylinder I S ∩ u) = p ^ 2 := by rw [hinter]; ring
    have hpa2 : |p ^ 2 - a ^ 2| < 2 * ε := by
      have hfac : p ^ 2 - a ^ 2 = (p - a) * (p + a) := by ring
      rw [hfac, abs_mul]
      have h1 : |p - a| < ε := by rw [abs_sub_comm]; exact hap
      have h2 : |p + a| ≤ 2 := by rw [abs_of_nonneg (by linarith)]; linarith
      calc |p - a| * |p + a| ≤ |p - a| * 2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ < ε * 2 := mul_lt_mul_of_pos_right h1 (by norm_num)
        _ = 2 * ε := by ring
    have hbound : |a - a ^ 2| < 4 * ε :=
      lt_of_le_of_lt (abs_sub_le a (p ^ 2) (a ^ 2))
        (by calc |a - p ^ 2| + |p ^ 2 - a ^ 2|
                < 2 * ε + 2 * ε := add_lt_add (hp2 ▸ hai) hpa2
              _ = 4 * ε := by ring)
    exact le_of_lt hbound
  -- the estimate forces `a = a²`, hence `ν s ∈ {0, 1}`
  have haa : a - a ^ 2 = 0 := by
    have h0 : |a - a ^ 2| ≤ 0 := by
      by_contra hpos
      rw [not_le] at hpos
      have hk := key (|a - a ^ 2| / 8) (by linarith)
      linarith
    exact abs_nonpos_iff.mp h0
  have hfin : ν s ≠ ∞ := measure_ne_top ν s
  have hnu : ν s = ENNReal.ofReal a := by
    rw [ha_def, measureReal_def, ENNReal.ofReal_toReal hfin]
  have hdich : ν s = 0 ∨ ν s = 1 := by
    have hfac : a * (1 - a) = 0 := by linear_combination haa
    rcases mul_eq_zero.mp hfac with h | h
    · refine Or.inl ?_
      rw [hnu, h]; simp
    · refine Or.inr ?_
      have ha1' : a = 1 := by linarith
      rw [hnu, ha1']; simp
  rw [Filter.eventuallyConst_set']
  rcases hdich with h0 | h1
  · exact Or.inl (ae_eq_empty.mpr h0)
  · exact Or.inr (ae_eq_univ.mpr (by
      rw [measure_compl hs hfin, measure_univ, h1, tsub_self]))

/-- If the path law of a process `X` is a countable i.i.d. product `Measure.infinitePi ν`, then `X`
is ergodic. This is the process-level packaging of `ergodic_pathShift_infinitePi` and the reusable
engine behind Hansen Theorems 14.4 (`IsErgodicProcess.of_iid`) and 14.14 (the i.i.d. ⇒ mixing
bridge, via its ergodic clause). -/
theorem ergodic_pathShift_of_pathLaw_eq_infinitePi {ν : Measure E} [IsProbabilityMeasure ν]
    (h : pathLaw X P = Measure.infinitePi fun _ : ℤ => ν) : IsErgodicProcess X P := by
  change Ergodic (pathShift E) (pathLaw X P)
  rw [h]
  exact ergodic_pathShift_infinitePi ν

/-- **Hansen Theorem 14.4.** An i.i.d. process is ergodic. Independence is `iIndepFun` and identical
distribution is `IdentDistrib (Y t) (Y s) P P` for all `t, s`, matching the hypothesis style of
`IsStrictlyStationary.of_iid` (the strict-stationarity half, Hansen Theorem 14.1). The path law is
the countable product of the common one-dimensional law `P.map (Y 0)`, so Bernoulli-shift ergodicity
(`ergodic_pathShift_infinitePi`) applies. -/
theorem IsErgodicProcess.of_iid [IsProbabilityMeasure P] (h_indep : iIndepFun Y P)
    (h_ident : ∀ t s, IdentDistrib (Y t) (Y s) P P) (h_meas : ∀ t, AEMeasurable (Y t) P) :
    IsErgodicProcess Y P := by
  haveI : IsProbabilityMeasure (P.map (Y 0)) := Measure.isProbabilityMeasure_map (h_meas 0)
  refine ergodic_pathShift_of_pathLaw_eq_infinitePi (ν := P.map (Y 0)) ?_
  have hfam : (fun i => P.map (Y i)) = fun _ : ℤ => P.map (Y 0) :=
    funext fun i => (h_ident i 0).map_eq
  simp only [pathLaw]
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map₀' h_meas).mp h_indep, hfam]

end ProbabilityTheory


