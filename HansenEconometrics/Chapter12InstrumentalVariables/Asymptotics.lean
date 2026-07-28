import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.Chapter7Asymptotics.Consistency
import HansenEconometrics.Chapter7Asymptotics.Normality
import HansenEconometrics.Chapter12InstrumentalVariables.Basic

/-!
# Chapter 12 — asymptotic instrumental-variables interfaces

This file contains the Chapter 12 2SLS convergence interfaces. The public
structures keep Hansen's rectangular IV moment matrices explicit:
`Q_XZ`, `Q_ZZ`, `Q_ZX`, the instrument-error score `n^{-1}Z'e`, and the robust
middle `n^{-1}∑ Z_i Z_i' ê_i²`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Function Topology MeasureTheory
  ProbabilityTheory ENNReal

namespace HansenEconometrics

@[reducible]
private noncomputable def matrixBorelMeasurableSpaceInst
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurableSpace (Matrix ι κ ℝ) :=
  matrixBorelMeasurableSpace ι κ

private lemma matrixBorelSpaceInst
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    @BorelSpace (Matrix ι κ ℝ) _ (matrixBorelMeasurableSpaceInst (ι := ι) (κ := κ)) :=
  matrixBorelSpace ι κ

attribute [local instance] matrixBorelMeasurableSpaceInst matrixBorelSpaceInst

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {k l : Type*} [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]

section IidGramWLLN

variable {q : Type*} [Fintype q] [DecidableEq q]

omit [DecidableEq q] in
private lemma measurable_vecMulVec_self :
    Measurable (fun x : q → ℝ => Matrix.vecMulVec x x) :=
  (Continuous.matrix_vecMulVec continuous_id continuous_id).measurable

omit [DecidableEq q] [IsProbabilityMeasure μ] in
private theorem integrable_vecMulVec_of_integrable_norm_sq
    {X : ℕ → Ω → q → ℝ}
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (hNormSq : Integrable (fun ω => ‖X 0 ω‖ ^ 2) μ) :
    Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ := by
  classical
  refine Integrable.of_eval ?_
  intro a
  refine Integrable.of_eval ?_
  intro b
  have hXa : AEStronglyMeasurable (fun ω => X 0 ω a) μ :=
    (continuous_apply a).comp_aestronglyMeasurable hX0
  have hXb : AEStronglyMeasurable (fun ω => X 0 ω b) μ :=
    (continuous_apply b).comp_aestronglyMeasurable hX0
  refine hNormSq.mono' (hXa.mul hXb) (ae_of_all μ fun ω => ?_)
  have hxa : |X 0 ω a| ≤ ‖X 0 ω‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (X 0 ω) a
  have hxb : |X 0 ω b| ≤ ‖X 0 ω‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (X 0 ω) b
  calc
    ‖Matrix.vecMulVec (X 0 ω) (X 0 ω) a b‖
        = |X 0 ω a| * |X 0 ω b| := by
          simp [Matrix.vecMulVec_apply, Real.norm_eq_abs]
    _ ≤ ‖X 0 ω‖ * ‖X 0 ω‖ := by gcongr
    _ = ‖X 0 ω‖ ^ 2 := by ring

omit [DecidableEq q] in
/-- IID finite-second-moment rows supply the Gram-only WLLN package used by
Hansen Assumption 12.1. -/
theorem SampleGramWLLNConditions.of_iid_finite_second
    {X : ℕ → Ω → q → ℝ}
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hNormSq : Integrable (fun ω => ‖X 0 ω‖ ^ 2) μ) :
    SampleGramWLLNConditions μ X where
  indep_outer := by
    have hout : iIndepFun (fun i ω => Matrix.vecMulVec (X i ω) (X i ω)) μ := by
      simpa [Function.comp] using
        hindep.comp (fun _ x => Matrix.vecMulVec x x)
          (fun _ => measurable_vecMulVec_self (q := q))
    intro i j hij
    exact hout.indepFun hij
  ident_outer := by
    intro i
    have hi := (hident i).comp (measurable_vecMulVec_self (q := q))
    simpa [Function.comp] using hi
  int_outer :=
    integrable_vecMulVec_of_integrable_norm_sq
      (μ := μ) (X := X) (hX 0) hNormSq

omit [DecidableEq q] in
private lemma measurable_pair_outer_fst :
    Measurable (fun z : (q → ℝ) × ℝ => Matrix.vecMulVec z.1 z.1) :=
  (measurable_vecMulVec_self (q := q)).comp measurable_fst

omit [Fintype q] [DecidableEq q] in
private lemma measurable_pair_cross :
    Measurable (fun z : (q → ℝ) × ℝ => z.2 • z.1) := by
  rw [measurable_pi_iff]
  intro i
  simpa using measurable_snd.mul ((measurable_pi_apply i).comp measurable_fst)

omit [DecidableEq q] in
private lemma measurable_pair_score_outer :
    Measurable (fun z : (q → ℝ) × ℝ =>
      Matrix.vecMulVec (z.2 • z.1) (z.2 • z.1)) := by
  have hscore : Continuous (fun z : (q → ℝ) × ℝ => z.2 • z.1) :=
    continuous_snd.smul continuous_fst
  exact (Continuous.matrix_vecMulVec hscore hscore).measurable

/-- IID finite-moment joint observations supply Chapter 7's
`SampleMomentAssumption71` package. This is the reusable iid constructor used by
the Hansen Chapter 12 primitive assumption layer. -/
theorem sampleMomentAssumption71_of_iid_moments
    {X : ℕ → Ω → q → ℝ} {e : ℕ → Ω → ℝ}
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (hjoint : iIndepFun (fun i ω => (X i ω, e i ω)) μ)
    (hident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω))
        (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (hNormSq : Integrable (fun ω => ‖X 0 ω‖ ^ 2) μ)
    (hCross : Integrable (fun ω => e 0 ω • X 0 ω) μ)
    (hQ : IsUnit (popGram μ X).det)
    (hortho : μ[fun ω => e 0 ω • X 0 ω] = 0) :
    SampleMomentAssumption71 μ X e where
  indep_outer := by
    have hout : iIndepFun
        (fun i ω => Matrix.vecMulVec (X i ω) (X i ω)) μ := by
      simpa [Function.comp] using
        hjoint.comp (fun _ z => Matrix.vecMulVec z.1 z.1)
          (fun _ => measurable_pair_outer_fst (q := q))
    intro i j hij
    exact hout.indepFun hij
  indep_cross := by
    have hcross_indep : iIndepFun (fun i ω => e i ω • X i ω) μ := by
      simpa [Function.comp] using
        hjoint.comp (fun _ z => z.2 • z.1)
          (fun _ => measurable_pair_cross (q := q))
    intro i j hij
    exact hcross_indep.indepFun hij
  ident_outer := by
    intro i
    have hi := (hident i).comp (measurable_pair_outer_fst (q := q))
    simpa [Function.comp] using hi
  ident_cross := by
    intro i
    have hi := (hident i).comp (measurable_pair_cross (q := q))
    simpa [Function.comp] using hi
  int_outer :=
    integrable_vecMulVec_of_integrable_norm_sq
      (μ := μ) (X := X) hX0 hNormSq
  int_cross := hCross
  Q_nonsing := hQ
  orthogonality := hortho

omit [DecidableEq q] [IsProbabilityMeasure μ] in
private theorem scoreCoordinate_memLp_two_of_integrable_score_outer
    {X : ℕ → Ω → q → ℝ} {e : ℕ → Ω → ℝ}
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (he0 : AEStronglyMeasurable (e 0) μ)
    (hScoreOuter :
      Integrable (fun ω => Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω)) μ)
    (j : q) :
    MemLp (fun ω => (e 0 ω • X 0 ω) j) 2 μ := by
  have hsq_entry :
      Integrable
        (fun ω => Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω) j j) μ :=
    Integrable.eval (Integrable.eval hScoreOuter j) j
  have hsq : Integrable (fun ω => ((e 0 ω • X 0 ω) j) ^ 2) μ := by
    simpa [Matrix.vecMulVec_apply, pow_two] using hsq_entry
  exact (memLp_two_iff_integrable_sq
    ((continuous_apply j).comp_aestronglyMeasurable (he0.smul hX0))).2 hsq

omit [DecidableEq q] [IsProbabilityMeasure μ] in
private theorem memLp_score_projection_of_integrable_score_outer
    {X : ℕ → Ω → q → ℝ} {e : ℕ → Ω → ℝ}
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (he0 : AEStronglyMeasurable (e 0) μ)
    (hScoreOuter :
      Integrable (fun ω => Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω)) μ)
    (a : q → ℝ) :
    MemLp (fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a) 2 μ := by
  classical
  convert (memLp_finset_sum' (s := Finset.univ)
    (f := fun j ω => (e 0 ω • X 0 ω) j * a j)
    (fun j _ =>
      (scoreCoordinate_memLp_two_of_integrable_score_outer
        (μ := μ) (X := X) (e := e) hX0 he0 hScoreOuter j).mul_const (a j)))
    using 1
  ext ω
  simp [dotProduct]

omit [Fintype q] [DecidableEq q] [IsProbabilityMeasure μ] in
private theorem memLp_four_of_integrable_fourth
    {f : Ω → ℝ}
    (hf_meas : AEStronglyMeasurable f μ)
    (hf_four : Integrable (fun ω => f ω ^ 4) μ) :
    MemLp f 4 μ := by
  rw [← integrable_norm_rpow_iff (μ := μ) hf_meas (by norm_num) (by norm_num)]
  convert hf_four using 1
  ext ω
  simpa [Real.norm_eq_abs] using (show Even (4 : ℕ) by decide).pow_abs (f ω)

omit [DecidableEq q] [IsProbabilityMeasure μ] in
private theorem coordinate_memLp_four_of_norm_fourth
    {X : ℕ → Ω → q → ℝ}
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (hXNorm4 : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ)
    (j : q) :
    MemLp (fun ω => X 0 ω j) 4 μ := by
  have hXj : AEStronglyMeasurable (fun ω => X 0 ω j) μ :=
    (continuous_apply j).comp_aestronglyMeasurable hX0
  refine memLp_four_of_integrable_fourth hXj ?_
  refine hXNorm4.mono' (hXj.aemeasurable.pow_const 4).aestronglyMeasurable
    (ae_of_all μ fun ω => ?_)
  have hxj : |X 0 ω j| ≤ ‖X 0 ω‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (X 0 ω) j
  calc
    ‖X 0 ω j ^ 4‖ = |X 0 ω j| ^ 4 := by
      simp [Real.norm_eq_abs]
    _ ≤ ‖X 0 ω‖ ^ 4 := by
      gcongr

omit [DecidableEq q] [IsProbabilityMeasure μ] in
private theorem linearIndex_memLp_four_of_norm_fourth
    {X : ℕ → Ω → q → ℝ}
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (hXNorm4 : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ)
    (β : q → ℝ) :
    MemLp (fun ω => (X 0 ω) ⬝ᵥ β) 4 μ := by
  classical
  convert (memLp_finset_sum' (s := Finset.univ)
    (f := fun j ω => X 0 ω j * β j)
    (fun j _ =>
      (coordinate_memLp_four_of_norm_fourth
        (μ := μ) (X := X) hX0 hXNorm4 j).mul_const (β j))) using 1
  ext ω
  simp [dotProduct]

omit [DecidableEq q] [IsProbabilityMeasure μ] in
private theorem error_memLp_four_of_response_regressor_fourth
    {X : ℕ → Ω → q → ℝ} {e Y : ℕ → Ω → ℝ} {β : q → ℝ}
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (hY0 : AEStronglyMeasurable (Y 0) μ)
    (hmodel0 : ∀ ω, Y 0 ω = (X 0 ω) ⬝ᵥ β + e 0 ω)
    (hYFourth : Integrable (fun ω => Y 0 ω ^ 4) μ)
    (hXNorm4 : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ) :
    MemLp (fun ω => e 0 ω) 4 μ := by
  have hYmem : MemLp (fun ω => Y 0 ω) 4 μ :=
    memLp_four_of_integrable_fourth hY0 hYFourth
  have hFitMem : MemLp (fun ω => (X 0 ω) ⬝ᵥ β) 4 μ :=
    linearIndex_memLp_four_of_norm_fourth (μ := μ) (X := X) hX0 hXNorm4 β
  have hdiff : MemLp (fun ω => Y 0 ω - (X 0 ω) ⬝ᵥ β) 4 μ :=
    hYmem.sub hFitMem
  convert hdiff using 1
  ext ω
  rw [hmodel0 ω]
  ring

omit [Fintype q] [DecidableEq q] [IsProbabilityMeasure μ] in
private theorem memLp_two_of_integrable_sq
    {f : Ω → ℝ}
    (hf_meas : AEStronglyMeasurable f μ)
    (hf_sq : Integrable (fun ω => f ω ^ 2) μ) :
    MemLp f 2 μ :=
  (memLp_two_iff_integrable_sq hf_meas).2 hf_sq

omit [Fintype q] [DecidableEq q] in
private theorem integrable_sq_of_integrable_fourth
    {f : Ω → ℝ}
    (hf_meas : AEStronglyMeasurable f μ)
    (hf_four : Integrable (fun ω => f ω ^ 4) μ) :
    Integrable (fun ω => f ω ^ 2) μ := by
  have hf4 : MemLp f 4 μ :=
    memLp_four_of_integrable_fourth hf_meas hf_four
  have hf2 : MemLp f 2 μ :=
    hf4.mono_exponent (by norm_num)
  exact (memLp_two_iff_integrable_sq hf_meas).1 hf2

omit [DecidableEq q] [IsProbabilityMeasure μ] in
private theorem coordinate_memLp_two_of_norm_sq
    {X : ℕ → Ω → q → ℝ}
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (hXNorm2 : Integrable (fun ω => ‖X 0 ω‖ ^ 2) μ)
    (j : q) :
    MemLp (fun ω => X 0 ω j) 2 μ := by
  have hXj : AEStronglyMeasurable (fun ω => X 0 ω j) μ :=
    (continuous_apply j).comp_aestronglyMeasurable hX0
  refine memLp_two_of_integrable_sq hXj ?_
  refine hXNorm2.mono' (hXj.aemeasurable.pow_const 2).aestronglyMeasurable
    (ae_of_all μ fun ω => ?_)
  have hxj : |X 0 ω j| ≤ ‖X 0 ω‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (X 0 ω) j
  calc
    ‖X 0 ω j ^ 2‖ = |X 0 ω j| ^ 2 := by
      simp [Real.norm_eq_abs]
    _ ≤ ‖X 0 ω‖ ^ 2 := by
      gcongr

omit [DecidableEq q] [IsProbabilityMeasure μ] in
private theorem linearIndex_memLp_two_of_norm_sq
    {X : ℕ → Ω → q → ℝ}
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (hXNorm2 : Integrable (fun ω => ‖X 0 ω‖ ^ 2) μ)
    (β : q → ℝ) :
    MemLp (fun ω => (X 0 ω) ⬝ᵥ β) 2 μ := by
  classical
  convert (memLp_finset_sum' (s := Finset.univ)
    (f := fun j ω => X 0 ω j * β j)
    (fun j _ =>
      (coordinate_memLp_two_of_norm_sq
        (μ := μ) (X := X) hX0 hXNorm2 j).mul_const (β j))) using 1
  ext ω
  simp [dotProduct]

omit [DecidableEq q] [IsProbabilityMeasure μ] in
private theorem error_memLp_two_of_response_regressor_second
    {X : ℕ → Ω → q → ℝ} {e Y : ℕ → Ω → ℝ} {β : q → ℝ}
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (hY0 : AEStronglyMeasurable (Y 0) μ)
    (hmodel0 : ∀ ω, Y 0 ω = (X 0 ω) ⬝ᵥ β + e 0 ω)
    (hYSq : Integrable (fun ω => Y 0 ω ^ 2) μ)
    (hXNorm2 : Integrable (fun ω => ‖X 0 ω‖ ^ 2) μ) :
    MemLp (fun ω => e 0 ω) 2 μ := by
  have hYmem : MemLp (fun ω => Y 0 ω) 2 μ :=
    memLp_two_of_integrable_sq hY0 hYSq
  have hFitMem : MemLp (fun ω => (X 0 ω) ⬝ᵥ β) 2 μ :=
    linearIndex_memLp_two_of_norm_sq (μ := μ) (X := X) hX0 hXNorm2 β
  have hdiff : MemLp (fun ω => Y 0 ω - (X 0 ω) ⬝ᵥ β) 2 μ :=
    hYmem.sub hFitMem
  convert hdiff using 1
  ext ω
  rw [hmodel0 ω]
  ring

omit [Fintype q] [DecidableEq q] [IsProbabilityMeasure μ] in
private theorem integrable_mul_of_memLp_two
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun ω => f ω * g ω) μ := by
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) (1 : ℝ≥0∞) := by
    have hreal : Real.HolderTriple (2 : ℝ) (2 : ℝ) (1 : ℝ) := by
      refine ⟨?_, by norm_num, by norm_num⟩
      norm_num [inv_eq_one_div]
    simpa using (Real.HolderTriple.ennrealOfReal hreal)
  simpa [Pi.mul_apply] using hf.integrable_mul hg

omit [DecidableEq q] [IsProbabilityMeasure μ] in
private theorem instrument_cross_integrable_of_memLp_two
    {Z : ℕ → Ω → q → ℝ} {e : ℕ → Ω → ℝ}
    (hZ0 : AEStronglyMeasurable (Z 0) μ)
    (he2 : MemLp (fun ω => e 0 ω) 2 μ)
    (hZNorm2 : Integrable (fun ω => ‖Z 0 ω‖ ^ 2) μ) :
    Integrable (fun ω => e 0 ω • Z 0 ω) μ := by
  refine Integrable.of_eval ?_
  intro a
  have hZa : MemLp (fun ω => Z 0 ω a) 2 μ :=
    coordinate_memLp_two_of_norm_sq (μ := μ) (X := Z) hZ0 hZNorm2 a
  simpa [Pi.smul_apply] using integrable_mul_of_memLp_two (μ := μ) he2 hZa

omit [Fintype q] [DecidableEq q] [IsProbabilityMeasure μ] in
private theorem memLp_mul_two_of_memLp_four
    {f g : Ω → ℝ} (hf : MemLp f 4 μ) (hg : MemLp g 4 μ) :
    MemLp (fun ω => f ω * g ω) 2 μ := by
  haveI : ENNReal.HolderTriple (4 : ℝ≥0∞) (4 : ℝ≥0∞) (2 : ℝ≥0∞) := by
    have hreal : Real.HolderTriple (4 : ℝ) (4 : ℝ) (2 : ℝ) := by
      refine ⟨?_, by norm_num, by norm_num⟩
      norm_num [inv_eq_one_div]
    simpa using (Real.HolderTriple.ennrealOfReal hreal)
  simpa [Pi.mul_apply, mul_comm] using hf.mul hg

omit [Fintype q] [DecidableEq q] in
private theorem integrable_of_memLp_two
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    Integrable f μ :=
  memLp_one_iff_integrable.mp (hf.mono_exponent one_le_two)

omit [DecidableEq q] [IsProbabilityMeasure μ] in
private theorem score_outer_integrable_of_memLp_four
    {Z : ℕ → Ω → q → ℝ} {e : ℕ → Ω → ℝ}
    (he4 : MemLp (fun ω => e 0 ω) 4 μ)
    (hZ4 : ∀ a : q, MemLp (fun ω => Z 0 ω a) 4 μ) :
    Integrable (fun ω => Matrix.vecMulVec (e 0 ω • Z 0 ω) (e 0 ω • Z 0 ω)) μ := by
  classical
  refine Integrable.of_eval ?_
  intro a
  refine Integrable.of_eval ?_
  intro b
  have ha : MemLp (fun ω => e 0 ω * Z 0 ω a) 2 μ :=
    memLp_mul_two_of_memLp_four (μ := μ) he4 (hZ4 a)
  have hb : MemLp (fun ω => e 0 ω * Z 0 ω b) 2 μ :=
    memLp_mul_two_of_memLp_four (μ := μ) he4 (hZ4 b)
  have hprod : Integrable
      (fun ω => (e 0 ω * Z 0 ω a) * (e 0 ω * Z 0 ω b)) μ :=
    ha.integrable_mul hb
  convert hprod using 1

omit [Fintype q] [DecidableEq q] in
private theorem error_sq_integrable_of_memLp_four
    {e : ℕ → Ω → ℝ}
    (he4 : MemLp (fun ω => e 0 ω) 4 μ) :
    Integrable (fun ω => e 0 ω ^ 2) μ := by
  have he2 : MemLp (fun ω => e 0 ω) 2 μ :=
    he4.mono_exponent (by norm_num)
  have hnorm2 : Integrable (fun ω => ‖e 0 ω‖ ^ 2) μ :=
    he2.integrable_norm_pow' (p := 2)
  convert hnorm2 using 1
  ext ω
  simp [Real.norm_eq_abs]

omit [Fintype q] [DecidableEq q] in
private theorem sigma_cross_integrable_of_memLp_four
    {X : ℕ → Ω → q → ℝ} {e : ℕ → Ω → ℝ}
    (he4 : MemLp (fun ω => e 0 ω) 4 μ)
    (hX4 : ∀ j : q, MemLp (fun ω => X 0 ω j) 4 μ)
    (j : q) :
    Integrable (fun ω => e 0 ω * X 0 ω j) μ :=
  integrable_of_memLp_two (μ := μ)
    (memLp_mul_two_of_memLp_four (μ := μ) he4 (hX4 j))

omit [Fintype q] [DecidableEq q] [Fintype l] [DecidableEq l] [IsProbabilityMeasure μ] in
private theorem omega_cross_integrable_of_memLp_four
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → q → ℝ} {e : ℕ → Ω → ℝ}
    (he4 : MemLp (fun ω => e 0 ω) 4 μ)
    (hX4 : ∀ j : q, MemLp (fun ω => X 0 ω j) 4 μ)
    (hZ4 : ∀ a : l, MemLp (fun ω => Z 0 ω a) 4 μ)
    (a b : l) (j : q) :
    Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ := by
  have heX : MemLp (fun ω => e 0 ω * X 0 ω j) 2 μ :=
    memLp_mul_two_of_memLp_four (μ := μ) he4 (hX4 j)
  have hZZ : MemLp (fun ω => Z 0 ω a * Z 0 ω b) 2 μ :=
    memLp_mul_two_of_memLp_four (μ := μ) (hZ4 a) (hZ4 b)
  have hprod : Integrable
      (fun ω => (e 0 ω * X 0 ω j) * (Z 0 ω a * Z 0 ω b)) μ :=
    heX.integrable_mul hZZ
  convert hprod using 1
  ext ω
  ring

omit [Fintype q] [DecidableEq q] [Fintype l] [DecidableEq l] [IsProbabilityMeasure μ] in
private theorem omega_quadratic_integrable_of_memLp_four
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → q → ℝ}
    (hX4 : ∀ j : q, MemLp (fun ω => X 0 ω j) 4 μ)
    (hZ4 : ∀ a : l, MemLp (fun ω => Z 0 ω a) 4 μ)
    (a b : l) (j m : q) :
    Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ := by
  have hXX : MemLp (fun ω => X 0 ω j * X 0 ω m) 2 μ :=
    memLp_mul_two_of_memLp_four (μ := μ) (hX4 j) (hX4 m)
  have hZZ : MemLp (fun ω => Z 0 ω a * Z 0 ω b) 2 μ :=
    memLp_mul_two_of_memLp_four (μ := μ) (hZ4 a) (hZ4 b)
  have hprod : Integrable
      (fun ω => (X 0 ω j * X 0 ω m) * (Z 0 ω a * Z 0 ω b)) μ :=
    hXX.integrable_mul hZZ
  convert hprod using 1
  ext ω
  ring

/-- IID joint observations with a finite score second moment supply the Chapter
7 score-CLT package used in Hansen Assumption 12.2. -/
theorem scoreCLTConditions_of_iid_score_outer
    {X : ℕ → Ω → q → ℝ} {e : ℕ → Ω → ℝ}
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (he0 : AEStronglyMeasurable (e 0) μ)
    (hjoint : iIndepFun (fun i ω => (X i ω, e i ω)) μ)
    (hident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω))
        (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (hNormSq : Integrable (fun ω => ‖X 0 ω‖ ^ 2) μ)
    (hCross : Integrable (fun ω => e 0 ω • X 0 ω) μ)
    (hScoreOuter :
      Integrable (fun ω => Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω)) μ)
    (hQ : IsUnit (popGram μ X).det)
    (hortho : μ[fun ω => e 0 ω • X 0 ω] = 0) :
    ScoreCLTConditions μ X e where
  toLeastSquaresConsistencyConditions :=
    sampleMomentAssumption71_of_iid_moments
      (μ := μ) (X := X) (e := e) hX0 hjoint hident hNormSq hCross hQ hortho
  iIndep_cross := by
    simpa [Function.comp] using
      hjoint.comp (fun _ z => z.2 • z.1)
        (fun _ => measurable_pair_cross (q := q))
  memLp_cross_projection :=
    memLp_score_projection_of_integrable_score_outer
      (μ := μ) (X := X) (e := e) hX0 he0 hScoreOuter

end IidGramWLLN

section FiniteSampleMeasurability

variable {q : Type*} [Fintype q]

omit [IsProbabilityMeasure μ] [Fintype q] in
theorem stackMatrix_aestronglyMeasurable
    [Finite q] {n : ℕ} {X : ℕ → Ω → q → ℝ}
    (hX : ∀ i, AEStronglyMeasurable (X i) μ) :
    AEStronglyMeasurable
      (fun ω => (fun i : Fin n => X i.val ω : Matrix (Fin n) q ℝ)) μ := by
  classical
  letI := Fintype.ofFinite q
  rw [aestronglyMeasurable_iff_aemeasurable]
  rw [aemeasurable_pi_iff]
  intro i
  rw [aemeasurable_pi_iff]
  intro j
  exact ((continuous_apply j).comp_aestronglyMeasurable (hX i.val)).aemeasurable

omit [IsProbabilityMeasure μ] in
/-- Row measurability implies measurability of the corresponding finite scalar
stack. -/
theorem stackScalar_aestronglyMeasurable
    {n : ℕ} {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ) :
    AEStronglyMeasurable (fun ω => (fun i : Fin n => Y i.val ω)) μ := by
  rw [aestronglyMeasurable_iff_aemeasurable]
  rw [aemeasurable_pi_iff]
  intro i
  exact (hY i.val).aemeasurable

end FiniteSampleMeasurability

omit [IsProbabilityMeasure μ] [DecidableEq k] in
/-- Row measurability of the structural equation implies row measurability of
the observed outcome. -/
theorem outcome_aestronglyMeasurable_of_linear_model
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ} (β : k → ℝ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    ∀ i, AEStronglyMeasurable (Y i) μ := by
  intro i
  have hdot : AEStronglyMeasurable (fun ω => (X i ω) ⬝ᵥ β) μ := by
    classical
    convert Finset.aestronglyMeasurable_fun_sum Finset.univ
      (fun j _ =>
        ((continuous_apply j).comp_aestronglyMeasurable (hX i)).mul_const (β j))
      using 1
  exact (hdot.add (he i)).congr (ae_of_all μ fun ω => (hmodel i ω).symm)

set_option maxHeartbeats 800000 in
-- Expanding finite-sample Star 2SLS measurability unfolds nested matrix
-- inverses, matrix products, and finite function spaces.
omit [IsProbabilityMeasure μ] in
/-- Finite-sample 2SLS Star estimator measurability from row measurability. -/
theorem twoSLSBetaStar_aestronglyMeasurable_of_rows
    {n : ℕ} {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ) :
    AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω)) μ := by
  let Zmat : Ω → Matrix (Fin n) l ℝ := fun ω => fun i => Z i.val ω
  let Xmat : Ω → Matrix (Fin n) k ℝ := fun ω => fun i => X i.val ω
  let yvec : Ω → Fin n → ℝ := fun ω => fun i => Y i.val ω
  have hZmat : AEStronglyMeasurable Zmat μ :=
    stackMatrix_aestronglyMeasurable (μ := μ) hZ
  have hXmat : AEStronglyMeasurable Xmat μ :=
    stackMatrix_aestronglyMeasurable (μ := μ) hX
  have hyvec : AEStronglyMeasurable yvec μ :=
    stackScalar_aestronglyMeasurable (μ := μ) hY
  have hZt : AEStronglyMeasurable (fun ω => (Zmat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hZmat
  have hZZ : AEStronglyMeasurable (fun ω => (Zmat ω)ᵀ * Zmat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hZt.prodMk hZmat)
  have hZZinv : AEStronglyMeasurable (fun ω => ((Zmat ω)ᵀ * Zmat ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hZZ
  have hP_left :
      AEStronglyMeasurable (fun ω => Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hZmat.prodMk hZZinv)
  have hP : AEStronglyMeasurable
      (fun ω => Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹ * (Zmat ω)ᵀ) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hP_left.prodMk hZt)
  have hXt : AEStronglyMeasurable (fun ω => (Xmat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hXmat
  have hXtP : AEStronglyMeasurable
      (fun ω => (Xmat ω)ᵀ *
        (Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹ * (Zmat ω)ᵀ)) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXt.prodMk hP)
  have hM : AEStronglyMeasurable
      (fun ω => (Xmat ω)ᵀ *
        (Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹ * (Zmat ω)ᵀ) * Xmat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXtP.prodMk hXmat)
  have hMinv : AEStronglyMeasurable
      (fun ω => ((Xmat ω)ᵀ *
        (Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹ * (Zmat ω)ᵀ) * Xmat ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hM
  have hv : AEStronglyMeasurable
      (fun ω => ((Xmat ω)ᵀ *
        (Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹ * (Zmat ω)ᵀ)) *ᵥ yvec ω) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXtP.prodMk hyvec)
  have hbeta : AEStronglyMeasurable
      (fun ω => ((Xmat ω)ᵀ *
          (Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹ * (Zmat ω)ᵀ) * Xmat ω)⁻¹ *ᵥ
        (((Xmat ω)ᵀ *
          (Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹ * (Zmat ω)ᵀ)) *ᵥ yvec ω)) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hMinv.prodMk hv)
  simpa [Zmat, Xmat, yvec, twoSLSBetaStar, twoSLSMomentMatrixStar,
    twoSLSMomentVectorStar, instrumentProjectionStar, Matrix.mul_assoc] using hbeta

omit [Fintype k] [DecidableEq k] [IsProbabilityMeasure μ] in
/-- Finite-sample fitted first-stage regressors measurability from row
measurability. -/
theorem fittedRegressorsStar_aestronglyMeasurable_of_rows
    [Finite k]
    {n : ℕ} {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ) :
    AEStronglyMeasurable
      (fun ω =>
        fittedRegressorsStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)) μ := by
  letI : Fintype k := Fintype.ofFinite k
  let Zmat : Ω → Matrix (Fin n) l ℝ := fun ω => fun i => Z i.val ω
  let Xmat : Ω → Matrix (Fin n) k ℝ := fun ω => fun i => X i.val ω
  have hZmat : AEStronglyMeasurable Zmat μ :=
    stackMatrix_aestronglyMeasurable (μ := μ) hZ
  have hXmat : AEStronglyMeasurable Xmat μ :=
    stackMatrix_aestronglyMeasurable (μ := μ) hX
  have hZt : AEStronglyMeasurable (fun ω => (Zmat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hZmat
  have hZZ : AEStronglyMeasurable (fun ω => (Zmat ω)ᵀ * Zmat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hZt.prodMk hZmat)
  have hZZinv : AEStronglyMeasurable (fun ω => ((Zmat ω)ᵀ * Zmat ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hZZ
  have hP_left :
      AEStronglyMeasurable (fun ω => Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hZmat.prodMk hZZinv)
  have hP : AEStronglyMeasurable
      (fun ω => Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹ * (Zmat ω)ᵀ) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hP_left.prodMk hZt)
  have hfit : AEStronglyMeasurable
      (fun ω => (Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹ * (Zmat ω)ᵀ) * Xmat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hP.prodMk hXmat)
  simpa [Zmat, Xmat, fittedRegressorsStar, instrumentProjectionStar, Matrix.mul_assoc]
    using hfit

omit [IsProbabilityMeasure μ] in
/-- Finite-sample textbook-facing 2SLS estimator measurability from row
measurability. -/
theorem twoSLSBetaOrZero_aestronglyMeasurable_of_rows
    {n : ℕ} {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ) :
    AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaOrZero
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω)) μ := by
  simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using
    twoSLSBetaStar_aestronglyMeasurable_of_rows
      (μ := μ) (Z := Z) (X := X) (Y := Y) hZ hX hY

omit [IsProbabilityMeasure μ] in
/-- Scaled and centered finite-sample 2SLS Star estimator measurability from row
measurability. -/
theorem twoSLSBetaStar_scaled_centered_aemeasurable_of_rows
    {n : ℕ} {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ) (β : k → ℝ) :
    AEMeasurable
      (fun ω =>
        Real.sqrt (n : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω) - β)) μ :=
  (((twoSLSBetaStar_aestronglyMeasurable_of_rows
      (μ := μ) (Z := Z) (X := X) (Y := Y) hZ hX hY).sub
    aestronglyMeasurable_const).const_smul (Real.sqrt (n : ℝ))).aemeasurable

omit [IsProbabilityMeasure μ] in
/-- Scaled and centered textbook-facing finite-sample 2SLS estimator
measurability from row measurability. -/
theorem twoSLSBetaOrZero_scaled_centered_aemeasurable_of_rows
    {n : ℕ} {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ) (β : k → ℝ) :
    AEMeasurable
      (fun ω =>
        Real.sqrt (n : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω) - β)) μ := by
  simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using
    twoSLSBetaStar_scaled_centered_aemeasurable_of_rows
      (μ := μ) (Z := Z) (X := X) (Y := Y) hZ hX hY β

omit [IsProbabilityMeasure μ] in
/-- Finite-sample 2SLS Star residual measurability from row measurability. -/
theorem twoSLSResidualStar_aestronglyMeasurable_of_rows
    {n : ℕ} {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ) :
    AEStronglyMeasurable
      (fun ω =>
        twoSLSResidualStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω)) μ := by
  let Xmat : Ω → Matrix (Fin n) k ℝ := fun ω => fun i => X i.val ω
  let yvec : Ω → Fin n → ℝ := fun ω => fun i => Y i.val ω
  let beta : Ω → k → ℝ := fun ω =>
    twoSLSBetaStar
      (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
      (fun i : Fin n => Y i.val ω)
  have hXmat : AEStronglyMeasurable Xmat μ :=
    stackMatrix_aestronglyMeasurable (μ := μ) hX
  have hyvec : AEStronglyMeasurable yvec μ :=
    stackScalar_aestronglyMeasurable (μ := μ) hY
  have hbeta : AEStronglyMeasurable beta μ :=
    twoSLSBetaStar_aestronglyMeasurable_of_rows
      (μ := μ) (Z := Z) (X := X) (Y := Y) hZ hX hY
  have hfit : AEStronglyMeasurable (fun ω => Xmat ω *ᵥ beta ω) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXmat.prodMk hbeta)
  simpa [twoSLSResidualStar, Xmat, yvec, beta] using hyvec.sub hfit

omit [IsProbabilityMeasure μ] in
/-- Feasible robust 2SLS middle measurability from row measurability. -/
private theorem twoSLSOmegaHatStar_aestronglyMeasurable_of_rows
    {n : ℕ} {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ) :
    AEStronglyMeasurable
      (fun ω =>
        twoSLSOmegaHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω)) μ := by
  let Zmat : Ω → Matrix (Fin n) l ℝ := fun ω => fun i => Z i.val ω
  let Xmat : Ω → Matrix (Fin n) k ℝ := fun ω => fun i => X i.val ω
  let yvec : Ω → Fin n → ℝ := fun ω => fun i => Y i.val ω
  let res : Ω → Fin n → ℝ := fun ω =>
    twoSLSResidualStar (Zmat ω) (Xmat ω) (yvec ω)
  have hZmat : AEStronglyMeasurable Zmat μ :=
    stackMatrix_aestronglyMeasurable (μ := μ) hZ
  have hres : AEStronglyMeasurable res μ := by
    simpa [res, Zmat, Xmat, yvec] using
      twoSLSResidualStar_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y) hZ hX hY
  have hterm : ∀ i : Fin n, AEStronglyMeasurable
      (fun ω => (res ω i) ^ 2 • Matrix.vecMulVec (Zmat ω i) (Zmat ω i)) μ := by
    intro i
    have hres_i : AEStronglyMeasurable (fun ω => res ω i) μ :=
      (continuous_apply i).comp_aestronglyMeasurable hres
    have hZ_i : AEStronglyMeasurable (fun ω => Zmat ω i) μ :=
      (continuous_apply i).comp_aestronglyMeasurable hZmat
    have hres_sq : AEStronglyMeasurable (fun ω => (res ω i) ^ 2) μ :=
      by simpa [pow_two] using hres_i.mul hres_i
    have houter_cont : Continuous (fun z : l → ℝ => Matrix.vecMulVec z z) := by
      refine continuous_pi (fun a => ?_)
      refine continuous_pi (fun b => ?_)
      simpa [Matrix.vecMulVec_apply] using
        (continuous_apply a).mul (continuous_apply b)
    exact hres_sq.smul (houter_cont.comp_aestronglyMeasurable hZ_i)
  have hsum : AEStronglyMeasurable
      (fun ω => ∑ i : Fin n,
        (res ω i) ^ 2 • Matrix.vecMulVec (Zmat ω i) (Zmat ω i)) μ := by
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => hterm i)
  simpa [twoSLSOmegaHatStar, res, Zmat, Xmat, yvec] using
    AEStronglyMeasurable.const_smul hsum ((Fintype.card (Fin n) : ℝ)⁻¹)

omit [IsProbabilityMeasure μ] in
/-- Feasible homoskedastic 2SLS residual-variance measurability from row
measurability. -/
theorem twoSLSSigmaSqHatStar_aestronglyMeasurable_of_rows
    {n : ℕ} {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ) :
    AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω)) μ := by
  let res : Ω → Fin n → ℝ := fun ω =>
    twoSLSResidualStar
      (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
      (fun i : Fin n => Y i.val ω)
  have hres : AEStronglyMeasurable res μ :=
    twoSLSResidualStar_aestronglyMeasurable_of_rows
      (μ := μ) (Z := Z) (X := X) (Y := Y) hZ hX hY
  have hdot_cont : Continuous (fun r : Fin n → ℝ => r ⬝ᵥ r) := by
    simpa [dotProduct] using
      continuous_finset_sum Finset.univ
        (fun i _ => (continuous_apply i).mul (continuous_apply i))
  have hdot : AEStronglyMeasurable (fun ω => res ω ⬝ᵥ res ω) μ :=
    hdot_cont.comp_aestronglyMeasurable hres
  simpa [twoSLSSigmaSqHatStar, sampleErrorSecondMoment, res] using
    hdot.const_mul ((Fintype.card (Fin n) : ℝ)⁻¹)

set_option maxHeartbeats 800000 in
-- Expanding finite-sample robust 2SLS covariance measurability unfolds nested
-- matrix inverses/products and residualized middle terms.
omit [IsProbabilityMeasure μ] in
/-- Feasible robust 2SLS covariance-estimator measurability from row
measurability. -/
theorem twoSLSVHatStar_aestronglyMeasurable_of_rows
    {n : ℕ} {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ) :
    AEStronglyMeasurable
      (fun ω =>
        twoSLSVHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω)) μ := by
  let Zmat : Ω → Matrix (Fin n) l ℝ := fun ω => fun i => Z i.val ω
  let Xmat : Ω → Matrix (Fin n) k ℝ := fun ω => fun i => X i.val ω
  let yvec : Ω → Fin n → ℝ := fun ω => fun i => Y i.val ω
  have hZmat : AEStronglyMeasurable Zmat μ :=
    stackMatrix_aestronglyMeasurable (μ := μ) hZ
  have hXmat : AEStronglyMeasurable Xmat μ :=
    stackMatrix_aestronglyMeasurable (μ := μ) hX
  have hZt : AEStronglyMeasurable (fun ω => (Zmat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hZmat
  let QZZhat : Ω → Matrix l l ℝ := fun ω => sampleQZZ (Zmat ω)
  let QZXhat : Ω → Matrix l k ℝ := fun ω => sampleQZX (Zmat ω) (Xmat ω)
  let QXZhat : Ω → Matrix k l ℝ := fun ω => sampleQXZ (Zmat ω) (Xmat ω)
  let Omegahat : Ω → Matrix l l ℝ := fun ω =>
    twoSLSOmegaHatStar (Zmat ω) (Xmat ω) (yvec ω)
  let Breadhat : Ω → Matrix k k ℝ := fun ω =>
    twoSLSBread (QXZhat ω) (QZZhat ω) (QZXhat ω)
  let Middlehat : Ω → Matrix k k ℝ := fun ω =>
    QXZhat ω * (QZZhat ω)⁻¹ * Omegahat ω * (QZZhat ω)⁻¹ * QZXhat ω
  have hQZZ : AEStronglyMeasurable QZZhat μ := by
    have hZZ : AEStronglyMeasurable (fun ω => (Zmat ω)ᵀ * Zmat ω) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hZt.prodMk hZmat)
    simpa [QZZhat, sampleQZZ, sampleGram, Zmat] using
      hZZ.const_smul ((Fintype.card (Fin n) : ℝ)⁻¹)
  have hQZX : AEStronglyMeasurable QZXhat μ := by
    have hZX : AEStronglyMeasurable (fun ω => (Zmat ω)ᵀ * Xmat ω) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hZt.prodMk hXmat)
    simpa [QZXhat, sampleQZX, Zmat, Xmat] using
      hZX.const_smul ((Fintype.card (Fin n) : ℝ)⁻¹)
  have hQXZ : AEStronglyMeasurable QXZhat μ := by
    simpa [QXZhat, QZXhat, sampleQXZ, Zmat, Xmat] using
      (continuous_id.matrix_transpose).comp_aestronglyMeasurable hQZX
  have hOmega : AEStronglyMeasurable Omegahat μ := by
    simpa [Omegahat, Zmat, Xmat, yvec] using
      twoSLSOmegaHatStar_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y) hZ hX hY
  have hQZZinv : AEStronglyMeasurable (fun ω => (QZZhat ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hQZZ
  have hbread : AEStronglyMeasurable Breadhat μ := by
    have hleft : AEStronglyMeasurable (fun ω => QXZhat ω * (QZZhat ω)⁻¹) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hQXZ.prodMk hQZZinv)
    have hprod : AEStronglyMeasurable (fun ω => (QXZhat ω * (QZZhat ω)⁻¹) *
        QZXhat ω) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hleft.prodMk hQZX)
    simpa [Breadhat, twoSLSBread, Matrix.mul_assoc] using hprod
  have hbreadInv : AEStronglyMeasurable (fun ω => (Breadhat ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hbread
  have hmiddle : AEStronglyMeasurable Middlehat μ := by
    have h1 : AEStronglyMeasurable (fun ω => QXZhat ω * (QZZhat ω)⁻¹) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hQXZ.prodMk hQZZinv)
    have h2 : AEStronglyMeasurable (fun ω => (QXZhat ω * (QZZhat ω)⁻¹) *
        Omegahat ω) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (h1.prodMk hOmega)
    have h3 : AEStronglyMeasurable
        (fun ω => ((QXZhat ω * (QZZhat ω)⁻¹) * Omegahat ω) *
          (QZZhat ω)⁻¹) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (h2.prodMk hQZZinv)
    have h4 : AEStronglyMeasurable
        (fun ω => (((QXZhat ω * (QZZhat ω)⁻¹) * Omegahat ω) *
          (QZZhat ω)⁻¹) * QZXhat ω) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (h3.prodMk hQZX)
    simpa [Middlehat, Matrix.mul_assoc] using h4
  have hleft : AEStronglyMeasurable
      (fun ω => (Breadhat ω)⁻¹ * Middlehat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hbreadInv.prodMk hmiddle)
  have hall : AEStronglyMeasurable
      (fun ω => ((Breadhat ω)⁻¹ * Middlehat ω) * (Breadhat ω)⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hleft.prodMk hbreadInv)
  simpa [twoSLSVHatStar, twoSLSAsymptoticVariance, Breadhat, Middlehat, QXZhat,
    QZZhat, QZXhat, Omegahat, Matrix.mul_assoc, Zmat, Xmat, yvec]
    using hall

/-- The combined instrument-regressor vector `[Z_i, X_i]`, used to reuse Chapter
7's sample-Gram WLLN for Hansen Chapter 12 IV moments. -/
def twoSLSCombinedRegressors
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) :
    ℕ → Ω → (l ⊕ k → ℝ) :=
  fun i ω => Sum.elim (Z i ω) (X i ω)

/-- Sample-moment convergence package for Hansen Theorem 12.1.

This is one step closer to Hansen Assumption 12.1 than
`TwoSLSConsistencyConditions`: it records the WLLN/CMT outputs for the three
sample IV moment matrices and the orthogonality score `n^{-1}Z'e`, together
with the population nonsingularity conditions needed for the continuous mapping
through matrix inversion.  The remaining primitive step is deriving these
fields from iid finite-second-moment assumptions. -/
structure TwoSLSSampleMomentConvergenceConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (QXZ : Matrix k l ℝ) (QZZ : Matrix l l ℝ) (QZX : Matrix l k ℝ) : Prop where
  qxz_meas : ∀ n,
    AEStronglyMeasurable
      (fun ω => sampleQXZ (fun i : Fin n => Z i.val ω)
        (fun i : Fin n => X i.val ω)) μ
  qzz_meas : ∀ n,
    AEStronglyMeasurable
      (fun ω => sampleQZZ (fun i : Fin n => Z i.val ω)) μ
  qzx_meas : ∀ n,
    AEStronglyMeasurable
      (fun ω => sampleQZX (fun i : Fin n => Z i.val ω)
        (fun i : Fin n => X i.val ω)) μ
  qxz_tendsto : TendstoInMeasure μ
    (fun n ω => sampleQXZ (fun i : Fin n => Z i.val ω)
      (fun i : Fin n => X i.val ω))
    atTop (fun _ => QXZ)
  qzz_tendsto : TendstoInMeasure μ
    (fun n ω => sampleQZZ (fun i : Fin n => Z i.val ω))
    atTop (fun _ => QZZ)
  qzx_tendsto : TendstoInMeasure μ
    (fun n ω => sampleQZX (fun i : Fin n => Z i.val ω)
      (fun i : Fin n => X i.val ω))
    atTop (fun _ => QZX)
  qzz_nonsing : IsUnit QZZ.det
  bread_nonsing : IsUnit (twoSLSBread QXZ QZZ QZX).det
  linearization_meas : ∀ n,
    AEStronglyMeasurable
      (fun ω =>
        twoSLSLinearizationMatrix
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)) μ
  score_meas : ∀ n,
    AEStronglyMeasurable
      (fun ω => sampleCrossMoment (fun i : Fin n => Z i.val ω)
        (fun i : Fin n => e i.val ω)) μ
  score_tendsto_zero : TendstoInMeasure μ
    (fun n ω => sampleCrossMoment (fun i : Fin n => Z i.val ω)
      (fun i : Fin n => e i.val ω))
    atTop (fun _ => 0)

set_option maxHeartbeats 1200000 in
-- The expanded matrix measurability proof composes several continuous matrix maps.
omit [IsProbabilityMeasure μ] in
private theorem twoSLSLinearizationMatrix_aestronglyMeasurable_of_combined_sampleGram
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {n : ℕ}
    (h_meas : AEStronglyMeasurable
      (fun ω =>
        sampleGram
          (Matrix.fromCols (fun i : Fin n => Z i.val ω)
            (fun i : Fin n => X i.val ω))) μ) :
    AEStronglyMeasurable
      (fun ω =>
        twoSLSLinearizationMatrix
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)) μ := by
  let QXZhat : Ω → Matrix k l ℝ := fun ω =>
    sampleQXZ (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
  let QZZhat : Ω → Matrix l l ℝ := fun ω =>
    sampleQZZ (fun i : Fin n => Z i.val ω)
  let QZXhat : Ω → Matrix l k ℝ := fun ω =>
    sampleQZX (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
  have hQXZ_meas : AEStronglyMeasurable QXZhat μ := by
    simpa [QXZhat] using
      (continuous_id.matrix_submatrix Sum.inr Sum.inl).comp_aestronglyMeasurable h_meas
  have hQZZ_meas : AEStronglyMeasurable QZZhat μ := by
    simpa [QZZhat] using
      (continuous_id.matrix_submatrix Sum.inl Sum.inl).comp_aestronglyMeasurable h_meas
  have hQZX_meas : AEStronglyMeasurable QZXhat μ := by
    simpa [QZXhat] using
      (continuous_id.matrix_submatrix Sum.inl Sum.inr).comp_aestronglyMeasurable h_meas
  have hQZZinv_meas : AEStronglyMeasurable (fun ω => (QZZhat ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hQZZ_meas
  have hQXZ_QZZinv_meas :
      AEStronglyMeasurable (fun ω => QXZhat ω * (QZZhat ω)⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hQXZ_meas.prodMk hQZZinv_meas)
  have hbread_meas :
      AEStronglyMeasurable (fun ω => QXZhat ω * (QZZhat ω)⁻¹ * QZXhat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hQXZ_QZZinv_meas.prodMk hQZX_meas)
  have hbread_inv_meas :
      AEStronglyMeasurable (fun ω => (QXZhat ω * (QZZhat ω)⁻¹ * QZXhat ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hbread_meas
  have hleft_meas :
      AEStronglyMeasurable
        (fun ω => (QXZhat ω * (QZZhat ω)⁻¹ * QZXhat ω)⁻¹ * QXZhat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hbread_inv_meas.prodMk hQXZ_meas)
  have hlin_meas :
      AEStronglyMeasurable
        (fun ω => (QXZhat ω * (QZZhat ω)⁻¹ * QZXhat ω)⁻¹ *
          QXZhat ω * (QZZhat ω)⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hleft_meas.prodMk hQZZinv_meas)
  simpa [QXZhat, QZZhat, QZXhat, twoSLSLinearizationMatrix, twoSLSBread, Matrix.mul_assoc]
    using hlin_meas

omit [DecidableEq k] [DecidableEq l] in
/-- Reuse bridge for Hansen Theorem 12.1: convergence of the combined sample
Gram for `[Z X]` implies convergence of the instrument Gram block `Q̂_ZZ`. -/
theorem sampleQZZ_tendstoInMeasure_of_combined_sampleGram
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Q : Matrix (l ⊕ k) (l ⊕ k) ℝ}
    (h_meas : ∀ n, AEStronglyMeasurable
      (fun ω =>
        sampleGram
          (Matrix.fromCols (fun i : Fin n => Z i.val ω)
            (fun i : Fin n => X i.val ω))) μ)
    (h_tendsto : TendstoInMeasure μ
      (fun n ω =>
        sampleGram
          (Matrix.fromCols (fun i : Fin n => Z i.val ω)
            (fun i : Fin n => X i.val ω)))
      atTop (fun _ => Q)) :
    TendstoInMeasure μ
      (fun n ω => sampleQZZ (fun i : Fin n => Z i.val ω))
      atTop (fun _ => Q.submatrix Sum.inl Sum.inl) := by
  have hblock :=
    tendstoInMeasure_continuous_comp h_meas h_tendsto
      (continuous_id.matrix_submatrix Sum.inl Sum.inl)
  simpa using hblock

omit [DecidableEq k] [DecidableEq l] in
/-- Reuse bridge for Hansen Theorem 12.1: convergence of the combined sample
Gram for `[Z X]` implies convergence of the cross block `Q̂_ZX`. -/
theorem sampleQZX_tendstoInMeasure_of_combined_sampleGram
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Q : Matrix (l ⊕ k) (l ⊕ k) ℝ}
    (h_meas : ∀ n, AEStronglyMeasurable
      (fun ω =>
        sampleGram
          (Matrix.fromCols (fun i : Fin n => Z i.val ω)
            (fun i : Fin n => X i.val ω))) μ)
    (h_tendsto : TendstoInMeasure μ
      (fun n ω =>
        sampleGram
          (Matrix.fromCols (fun i : Fin n => Z i.val ω)
            (fun i : Fin n => X i.val ω)))
      atTop (fun _ => Q)) :
    TendstoInMeasure μ
      (fun n ω => sampleQZX (fun i : Fin n => Z i.val ω)
        (fun i : Fin n => X i.val ω))
      atTop (fun _ => Q.submatrix Sum.inl Sum.inr) := by
  have hblock :=
    tendstoInMeasure_continuous_comp h_meas h_tendsto
      (continuous_id.matrix_submatrix Sum.inl Sum.inr)
  simpa using hblock

omit [DecidableEq k] [DecidableEq l] in
/-- Reuse bridge for Hansen Theorem 12.1: convergence of the combined sample
Gram for `[Z X]` implies convergence of the transposed cross block `Q̂_XZ`. -/
theorem sampleQXZ_tendstoInMeasure_of_combined_sampleGram
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Q : Matrix (l ⊕ k) (l ⊕ k) ℝ}
    (h_meas : ∀ n, AEStronglyMeasurable
      (fun ω =>
        sampleGram
          (Matrix.fromCols (fun i : Fin n => Z i.val ω)
            (fun i : Fin n => X i.val ω))) μ)
    (h_tendsto : TendstoInMeasure μ
      (fun n ω =>
        sampleGram
          (Matrix.fromCols (fun i : Fin n => Z i.val ω)
            (fun i : Fin n => X i.val ω)))
      atTop (fun _ => Q)) :
    TendstoInMeasure μ
      (fun n ω => sampleQXZ (fun i : Fin n => Z i.val ω)
        (fun i : Fin n => X i.val ω))
      atTop (fun _ => Q.submatrix Sum.inr Sum.inl) := by
  have hblock :=
    tendstoInMeasure_continuous_comp h_meas h_tendsto
      (continuous_id.matrix_submatrix Sum.inr Sum.inl)
  simpa using hblock

omit [DecidableEq k] [DecidableEq l] in
/-- Reuse bridge for Hansen Theorem 12.3: convergence of the combined sample
Gram for `[Z X]` implies convergence of the regressor Gram block `Q̂_XX`. -/
theorem sampleGramX_tendstoInMeasure_of_combined_sampleGram
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Q : Matrix (l ⊕ k) (l ⊕ k) ℝ}
    (h_meas : ∀ n, AEStronglyMeasurable
      (fun ω =>
        sampleGram
          (Matrix.fromCols (fun i : Fin n => Z i.val ω)
            (fun i : Fin n => X i.val ω))) μ)
    (h_tendsto : TendstoInMeasure μ
      (fun n ω =>
        sampleGram
          (Matrix.fromCols (fun i : Fin n => Z i.val ω)
            (fun i : Fin n => X i.val ω)))
      atTop (fun _ => Q)) :
    TendstoInMeasure μ
      (fun n ω => sampleGram (fun i : Fin n => X i.val ω))
      atTop (fun _ => Q.submatrix Sum.inr Sum.inr) := by
  have hblock :=
    tendstoInMeasure_continuous_comp h_meas h_tendsto
      (continuous_id.matrix_submatrix Sum.inr Sum.inr)
  simpa using hblock

omit [DecidableEq k] [DecidableEq l] in
/-- Population `Q_ZZ` block extracted from the combined second moment of
`[Z X]`. -/
noncomputable def twoSLSCombinedQZZ
    (Q : Matrix (l ⊕ k) (l ⊕ k) ℝ) : Matrix l l ℝ :=
  Q.submatrix Sum.inl Sum.inl

omit [DecidableEq k] [DecidableEq l] in
/-- Population `Q_ZX` block extracted from the combined second moment of
`[Z X]`. -/
noncomputable def twoSLSCombinedQZX
    (Q : Matrix (l ⊕ k) (l ⊕ k) ℝ) : Matrix l k ℝ :=
  Q.submatrix Sum.inl Sum.inr

omit [DecidableEq k] [DecidableEq l] in
/-- Population `Q_XZ` block extracted from the combined second moment of
`[Z X]`. -/
noncomputable def twoSLSCombinedQXZ
    (Q : Matrix (l ⊕ k) (l ⊕ k) ℝ) : Matrix k l ℝ :=
  Q.submatrix Sum.inr Sum.inl

omit [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
/-- The `Q_ZZ` block of the combined population Gram is the ordinary
instrument population Gram. -/
theorem popGram_eq_twoSLSCombinedQZZ_popGram
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    (hZ : Integrable (fun ω => Matrix.vecMulVec (Z 0 ω) (Z 0 ω)) μ)
    (hCombined : Integrable
      (fun ω =>
        Matrix.vecMulVec (twoSLSCombinedRegressors Z X 0 ω)
          (twoSLSCombinedRegressors Z X 0 ω)) μ) :
    popGram μ Z =
      twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)) := by
  ext i j
  rw [popGram, twoSLSCombinedQZZ, popGram]
  change (∫ x, Matrix.vecMulVec (Z 0 x) (Z 0 x) ∂μ) i j =
    (∫ x, Matrix.vecMulVec (twoSLSCombinedRegressors Z X 0 x)
      (twoSLSCombinedRegressors Z X 0 x) ∂μ) (Sum.inl i) (Sum.inl j)
  calc
    (∫ x, Matrix.vecMulVec (Z 0 x) (Z 0 x) ∂μ) i j
        = ∫ x, Matrix.vecMulVec (Z 0 x) (Z 0 x) i j ∂μ := by
          exact integral_apply_apply hZ i j
    _ = ∫ x, Matrix.vecMulVec (twoSLSCombinedRegressors Z X 0 x)
          (twoSLSCombinedRegressors Z X 0 x) (Sum.inl i) (Sum.inl j) ∂μ := by
          simp [twoSLSCombinedRegressors, Matrix.vecMulVec_apply]
    _ = (∫ x, Matrix.vecMulVec (twoSLSCombinedRegressors Z X 0 x)
          (twoSLSCombinedRegressors Z X 0 x) ∂μ) (Sum.inl i) (Sum.inl j) := by
          exact (integral_apply_apply hCombined (Sum.inl i) (Sum.inl j)).symm

omit [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
/-- The population first-stage normal equation follows from the reduced-form
model `X = A'Z + u` and `E[Zu'] = 0`. -/
theorem twoSLSCombinedQZX_eq_qzz_mul_of_firstStage_ae
    {Z : ℕ → Ω → l → ℝ} {X u : ℕ → Ω → k → ℝ}
    (A : Matrix l k ℝ)
    (hCombined : Integrable
      (fun ω => Matrix.vecMulVec (twoSLSCombinedRegressors Z X 0 ω)
        (twoSLSCombinedRegressors Z X 0 ω)) μ)
    (hZU : Integrable (fun ω => Matrix.vecMulVec (Z 0 ω) (u 0 ω)) μ)
    (hmodel : (fun ω => X 0 ω) =ᵐ[μ] fun ω => Aᵀ *ᵥ Z 0 ω + u 0 ω)
    (horth : (∫ ω, Matrix.vecMulVec (Z 0 ω) (u 0 ω) ∂μ) = 0) :
    twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)) =
      twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)) * A := by
  classical
  ext a j
  rw [twoSLSCombinedQZX, twoSLSCombinedQZZ, popGram]
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  let M : Ω → Matrix (l ⊕ k) (l ⊕ k) ℝ := fun ω =>
    Matrix.vecMulVec (twoSLSCombinedRegressors Z X 0 ω)
      (twoSLSCombinedRegressors Z X 0 ω)
  change (∫ ω, M ω ∂μ) (Sum.inl a) (Sum.inr j) =
    ∑ b, (∫ ω, M ω ∂μ) (Sum.inl a) (Sum.inl b) * A b j
  have hZZ : ∀ b : l, Integrable (fun ω => Z 0 ω a * Z 0 ω b) μ := by
    intro b
    simpa [twoSLSCombinedRegressors, Matrix.vecMulVec_apply] using
      Integrable.eval (Integrable.eval hCombined (Sum.inl a)) (Sum.inl b)
  have hZUaj : Integrable (fun ω => Z 0 ω a * u 0 ω j) μ := by
    simpa [Matrix.vecMulVec_apply] using Integrable.eval (Integrable.eval hZU a) j
  have hZUzero : (∫ ω, Z 0 ω a * u 0 ω j ∂μ) = 0 := by
    calc
      (∫ ω, Z 0 ω a * u 0 ω j ∂μ) =
          (∫ ω, Matrix.vecMulVec (Z 0 ω) (u 0 ω) ∂μ) a j := by
            exact (integral_apply_apply hZU a j).symm
      _ = 0 := by rw [horth]; rfl
  calc
    (∫ ω, M ω ∂μ) (Sum.inl a) (Sum.inr j) =
        ∫ ω, M ω (Sum.inl a) (Sum.inr j) ∂μ :=
          integral_apply_apply hCombined (Sum.inl a) (Sum.inr j)
    _ = ∫ ω, Z 0 ω a * X 0 ω j ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          rfl
    _ =
        ∫ ω, Z 0 ω a * ((Aᵀ *ᵥ Z 0 ω + u 0 ω) j) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hmodel] with ω hω
          rw [hω]
    _ = ∫ ω,
        (∑ b, (Z 0 ω a * Z 0 ω b) * A b j) + Z 0 ω a * u 0 ω j ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
          rw [mul_add, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro b _
          ring
    _ = (∑ b, (∫ ω, Z 0 ω a * Z 0 ω b ∂μ) * A b j) +
          ∫ ω, Z 0 ω a * u 0 ω j ∂μ := by
          rw [integral_add]
          · rw [integral_finset_sum]
            · congr 1
              apply Finset.sum_congr rfl
              intro b _
              rw [integral_mul_const]
            · intro b _
              exact (hZZ b).mul_const (A b j)
          · exact integrable_finset_sum _ (fun b _ => (hZZ b).mul_const (A b j))
          · exact hZUaj
    _ = ∑ b, (∫ ω, Z 0 ω a * Z 0 ω b ∂μ) * A b j := by rw [hZUzero, add_zero]
    _ = ∑ b, (∫ ω, M ω ∂μ) (Sum.inl a) (Sum.inl b) * A b j := by
          apply Finset.sum_congr rfl
          intro b _
          congr 1
          calc
            (∫ ω, Z 0 ω a * Z 0 ω b ∂μ) =
                ∫ ω, M ω (Sum.inl a) (Sum.inl b) ∂μ := by
                  apply integral_congr_ae
                  filter_upwards with ω
                  rfl
            _ = (∫ ω, M ω ∂μ) (Sum.inl a) (Sum.inl b) :=
              (integral_apply_apply hCombined (Sum.inl a) (Sum.inl b)).symm

/-- Combined-moment version of Hansen Assumption 12.1's WLLN surface.

Instead of assuming convergence of `Q̂_ZZ`, `Q̂_ZX`, and `Q̂_XZ` separately,
this package records convergence of the single combined sample Gram for
`[Z X]`; the converter below recovers the three Hansen moment limits by
submatrix CMT. -/
structure TwoSLSCombinedSampleMomentConvergenceConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (Q : Matrix (l ⊕ k) (l ⊕ k) ℝ) : Prop where
  combined_meas : ∀ n,
    AEStronglyMeasurable
      (fun ω =>
        sampleGram
          (Matrix.fromCols (fun i : Fin n => Z i.val ω)
            (fun i : Fin n => X i.val ω))) μ
  combined_tendsto : TendstoInMeasure μ
    (fun n ω =>
      sampleGram
        (Matrix.fromCols (fun i : Fin n => Z i.val ω)
          (fun i : Fin n => X i.val ω)))
    atTop (fun _ => Q)
  qzz_nonsing : IsUnit (twoSLSCombinedQZZ Q).det
  bread_nonsing : IsUnit
    (twoSLSBread (twoSLSCombinedQXZ Q) (twoSLSCombinedQZZ Q)
      (twoSLSCombinedQZX Q)).det
  linearization_meas : ∀ n,
    AEStronglyMeasurable
      (fun ω =>
        twoSLSLinearizationMatrix
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)) μ
  score_meas : ∀ n,
    AEStronglyMeasurable
      (fun ω => sampleCrossMoment (fun i : Fin n => Z i.val ω)
        (fun i : Fin n => e i.val ω)) μ
  score_tendsto_zero : TendstoInMeasure μ
    (fun n ω => sampleCrossMoment (fun i : Fin n => Z i.val ω)
      (fun i : Fin n => e i.val ω))
    atTop (fun _ => 0)

/-- Convert the combined `[Z X]` sample-Gram WLLN surface into the Hansen
`Q_XZ`, `Q_ZZ`, `Q_ZX` sample-moment convergence package. -/
theorem TwoSLSCombinedSampleMomentConvergenceConditions.toSampleMomentConvergenceConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {Q : Matrix (l ⊕ k) (l ⊕ k) ℝ}
    (h : TwoSLSCombinedSampleMomentConvergenceConditions μ Z X e Q) :
    TwoSLSSampleMomentConvergenceConditions μ Z X e
      (twoSLSCombinedQXZ Q) (twoSLSCombinedQZZ Q) (twoSLSCombinedQZX Q) where
  qxz_meas := by
    intro n
    simpa using
      (continuous_id.matrix_submatrix Sum.inr Sum.inl).comp_aestronglyMeasurable
        (h.combined_meas n)
  qzz_meas := by
    intro n
    simpa using
      (continuous_id.matrix_submatrix Sum.inl Sum.inl).comp_aestronglyMeasurable
        (h.combined_meas n)
  qzx_meas := by
    intro n
    simpa using
      (continuous_id.matrix_submatrix Sum.inl Sum.inr).comp_aestronglyMeasurable
        (h.combined_meas n)
  qxz_tendsto := by
    simpa [twoSLSCombinedQXZ] using
      sampleQXZ_tendstoInMeasure_of_combined_sampleGram
        (μ := μ) (Z := Z) (X := X) h.combined_meas h.combined_tendsto
  qzz_tendsto := by
    simpa [twoSLSCombinedQZZ] using
      sampleQZZ_tendstoInMeasure_of_combined_sampleGram
        (μ := μ) (Z := Z) (X := X) h.combined_meas h.combined_tendsto
  qzx_tendsto := by
    simpa [twoSLSCombinedQZX] using
      sampleQZX_tendstoInMeasure_of_combined_sampleGram
        (μ := μ) (Z := Z) (X := X) h.combined_meas h.combined_tendsto
  qzz_nonsing := h.qzz_nonsing
  bread_nonsing := h.bread_nonsing
  linearization_meas := h.linearization_meas
  score_meas := h.score_meas
  score_tendsto_zero := h.score_tendsto_zero

/-- Hansen-facing Assumption 12.1 constructor surface.

The combined `[Z X]` sample-Gram WLLN is supplied by Chapter 7's
`SampleMomentAssumption71` applied to `twoSLSCombinedRegressors Z X`, so callers
do not re-assume separate limits for `Q̂_XZ`, `Q̂_ZZ`, and `Q̂_ZX`. The
instrument orthogonality WLLN is supplied by Chapter 7's same package applied to
`Z` and `e`; the converter below extracts the exact lower-level Chapter 12 proof
package. -/
structure TwoSLSCombinedSampleMomentRankConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ) : Prop where
  combined_moments :
    ∃ u : ℕ → Ω → ℝ, SampleMomentAssumption71 μ (twoSLSCombinedRegressors Z X) u
  instrument_moments : SampleMomentAssumption71 μ Z e
  qzz_nonsing :
    IsUnit (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X))).det
  bread_nonsing : IsUnit
    (twoSLSBread
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))).det

namespace TwoSLSCombinedSampleMomentRankConditions

/-- Constructor for the Assumption 12.1 proof package from Hansen's population
rank conditions.

This replaces the direct 2SLS-bread nonsingularity field by the textbook
conditions `Q_ZZ` positive definite and `Q_ZX` full column rank, with
`Q_XZ = Q_ZX'`. The combined `[Z X]` and instrument-score WLLN packages remain
the current proof-facing inputs. -/
theorem of_qzz_posDef_qzx_rank
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (combined_moments :
      ∃ u : ℕ → Ω → ℝ, SampleMomentAssumption71 μ (twoSLSCombinedRegressors Z X) u)
    (instrument_moments : SampleMomentAssumption71 μ Z e)
    (hQXZ :
      twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)) =
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))ᵀ)
    (hQZZ :
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X))).PosDef)
    (hQZX :
      Function.Injective
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))).mulVec) :
    TwoSLSCombinedSampleMomentRankConditions μ Z X e where
  combined_moments := combined_moments
  instrument_moments := instrument_moments
  qzz_nonsing := (Matrix.isUnit_iff_isUnit_det _).mp hQZZ.isUnit
  bread_nonsing :=
    isUnit_twoSLSBread_det_of_qzz_posDef_rank hQXZ hQZZ hQZX

/-- A Hansen Assumption 12.1 package supplies the combined `[Z X]` sample-Gram
surface used by the lower-level Chapter 12 moment converter. -/
theorem toCombinedSampleMomentConvergenceConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSCombinedSampleMomentRankConditions μ Z X e) :
    TwoSLSCombinedSampleMomentConvergenceConditions μ Z X e
      (popGram μ (twoSLSCombinedRegressors Z X)) where
  combined_meas := by
    rcases h.combined_moments with ⟨u, hCombined⟩
    intro n
    simpa [twoSLSCombinedRegressors, stackRegressors] using
      sampleGram_stackRegressors_aestronglyMeasurable
        (μ := μ) (X := twoSLSCombinedRegressors Z X) (e := u) hCombined n
  combined_tendsto := by
    rcases h.combined_moments with ⟨u, hCombined⟩
    simpa [twoSLSCombinedRegressors, stackRegressors] using
      sampleGram_stackRegressors_tendstoInMeasure_popGram
        (μ := μ) (X := twoSLSCombinedRegressors Z X) (e := u) hCombined
  qzz_nonsing := h.qzz_nonsing
  bread_nonsing := h.bread_nonsing
  linearization_meas := by
    rcases h.combined_moments with ⟨u, hCombined⟩
    intro n
    have hCombinedMeas : AEStronglyMeasurable
        (fun ω =>
          sampleGram
            (Matrix.fromCols (fun i : Fin n => Z i.val ω)
              (fun i : Fin n => X i.val ω))) μ := by
      simpa [twoSLSCombinedRegressors, stackRegressors] using
        sampleGram_stackRegressors_aestronglyMeasurable
          (μ := μ) (X := twoSLSCombinedRegressors Z X) (e := u) hCombined n
    exact twoSLSLinearizationMatrix_aestronglyMeasurable_of_combined_sampleGram
      (μ := μ) (Z := Z) (X := X) (n := n) hCombinedMeas
  score_meas := by
    intro n
    simpa [stackRegressors, stackErrors] using
      sampleCrossMoment_stack_aestronglyMeasurable
        (μ := μ) (X := Z) (e := e) h.instrument_moments n
  score_tendsto_zero := by
    simpa [stackRegressors, stackErrors] using
      sampleCrossMoment_stack_tendstoInMeasure_zero
        (μ := μ) (X := Z) (e := e) h.instrument_moments

/-- A Hansen Assumption 12.1 package supplies the lower-level Chapter 12 sample
moment convergence package, with the population blocks extracted from the
combined `[Z X]` population Gram. -/
theorem toSampleMomentConvergenceConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSCombinedSampleMomentRankConditions μ Z X e) :
    TwoSLSSampleMomentConvergenceConditions μ Z X e
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) :=
  h.toCombinedSampleMomentConvergenceConditions.toSampleMomentConvergenceConditions

end TwoSLSCombinedSampleMomentRankConditions

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] in
private theorem twoSLSCombinedQZZ_transpose_eq_of_symm
    (Q : Matrix (l ⊕ k) (l ⊕ k) ℝ) (hQ : Qᵀ = Q) :
    (twoSLSCombinedQZZ Q)ᵀ = twoSLSCombinedQZZ Q := by
  ext i j
  have hij := congrFun (congrFun hQ (Sum.inl i)) (Sum.inl j)
  simpa [twoSLSCombinedQZZ, Matrix.transpose_apply] using hij

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] in
private theorem twoSLSCombinedQZX_eq_transpose_of_symm
    (Q : Matrix (l ⊕ k) (l ⊕ k) ℝ) (hQ : Qᵀ = Q) :
    twoSLSCombinedQZX Q = (twoSLSCombinedQXZ Q)ᵀ := by
  ext i j
  have hij := congrFun (congrFun hQ (Sum.inl i)) (Sum.inr j)
  simpa [twoSLSCombinedQZX, twoSLSCombinedQXZ, Matrix.transpose_apply] using hij.symm

omit [DecidableEq k] [DecidableEq l] in
/-- The combined `[Z X]` population Gram supplies Hansen's block symmetry
`Q_ZX = Q_XZ'`.

This is the Chapter 12 bridge that reuses Chapter 7's symmetry theorem for
`popGram`; callers proving Assumption 12.1/12.2 from Hansen's rank conditions do
not need to assume the cross-block transpose relation separately. -/
theorem twoSLSCombinedQZX_eq_transpose_QXZ_of_popGram_wlln
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    (hCombined : SampleGramWLLNConditions μ (twoSLSCombinedRegressors Z X)) :
    twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)) =
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))ᵀ := by
  have hQsymm :
      (popGram μ (twoSLSCombinedRegressors Z X))ᵀ =
        popGram μ (twoSLSCombinedRegressors Z X) :=
    (popGram_isSymm (μ := μ) (X := twoSLSCombinedRegressors Z X)
      hCombined.int_outer).eq
  exact twoSLSCombinedQZX_eq_transpose_of_symm _ hQsymm

omit [DecidableEq k] [DecidableEq l] in
/-- The combined `[Z X]` population Gram supplies Hansen's block symmetry
`Q_XZ = Q_ZX'` under the Gram-only WLLN package. -/
theorem twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    (hCombined : SampleGramWLLNConditions μ (twoSLSCombinedRegressors Z X)) :
    twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)) =
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))ᵀ := by
  rw [twoSLSCombinedQZX_eq_transpose_QXZ_of_popGram_wlln (hCombined := hCombined)]
  simp

/-- The combined `[Z X]` population Gram supplies Hansen's block symmetry
`Q_ZX = Q_XZ'`.

Compatibility wrapper for callers that still use the full Chapter 7 sample
moment package. -/
theorem twoSLSCombinedQZX_eq_transpose_QXZ_of_popGram
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {u : ℕ → Ω → ℝ}
    (hCombined : SampleMomentAssumption71 μ (twoSLSCombinedRegressors Z X) u) :
    twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)) =
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))ᵀ :=
  twoSLSCombinedQZX_eq_transpose_QXZ_of_popGram_wlln
    (hCombined := SampleGramWLLNConditions.ofSampleMoment hCombined)

/-- The combined `[Z X]` population Gram supplies Hansen's block symmetry
`Q_XZ = Q_ZX'`.

Compatibility wrapper for callers that still use the full Chapter 7 sample
moment package. -/
theorem twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {u : ℕ → Ω → ℝ}
    (hCombined : SampleMomentAssumption71 μ (twoSLSCombinedRegressors Z X) u) :
    twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)) =
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))ᵀ :=
  twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
    (hCombined := SampleGramWLLNConditions.ofSampleMoment hCombined)

namespace TwoSLSCombinedSampleMomentRankConditions

/-- Constructor for the Assumption 12.1 proof package from Hansen's population
rank conditions, deriving `Q_XZ = Q_ZX'` from the combined population Gram. -/
theorem of_qzz_posDef_qzx_rank_popGram
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (combined_moments :
      ∃ u : ℕ → Ω → ℝ, SampleMomentAssumption71 μ (twoSLSCombinedRegressors Z X) u)
    (instrument_moments : SampleMomentAssumption71 μ Z e)
    (hQZZ :
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X))).PosDef)
    (hQZX :
      Function.Injective
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))).mulVec) :
    TwoSLSCombinedSampleMomentRankConditions μ Z X e := by
  rcases combined_moments with ⟨u, hCombined⟩
  exact of_qzz_posDef_qzx_rank
    (combined_moments := ⟨u, hCombined⟩)
    (instrument_moments := instrument_moments)
    (hQXZ := twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram
      (μ := μ) (Z := Z) (X := X) (hCombined := hCombined))
    (hQZZ := hQZZ) (hQZX := hQZX)

end TwoSLSCombinedSampleMomentRankConditions

/-- Hansen-facing Assumption 12.2 constructor surface.

This extends the Assumption 12.1 sample-moment constructor with Chapter 7's
instrument-score CLT. The converter derives the lower-level formula-facing
normality package, including the population `Q_ZZ` symmetry and
`Q_ZX = Q_XZᵀ` facts from the combined population Gram. -/
structure TwoSLSCombinedSampleMomentScoreCLTPositiveCovarianceConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    : Prop extends TwoSLSCombinedSampleMomentRankConditions μ Z X e where
  score_clt : ScoreCLTConditions μ Z e
  omega_posDef : (scoreCovMat μ Z e).PosDef

namespace TwoSLSCombinedSampleMomentScoreCLTPositiveCovarianceConditions

/-- Constructor for the Assumption 12.2 proof package from Hansen's population
rank conditions and Chapter 7's instrument-score CLT, deriving
`Q_XZ = Q_ZX'` from the combined population Gram. -/
theorem of_qzz_posDef_qzx_rank_popGram
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (combined_moments :
      ∃ u : ℕ → Ω → ℝ, SampleMomentAssumption71 μ (twoSLSCombinedRegressors Z X) u)
    (instrument_moments : SampleMomentAssumption71 μ Z e)
    (score_clt : ScoreCLTConditions μ Z e)
    (omega_posDef : (scoreCovMat μ Z e).PosDef)
    (hQZZ :
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X))).PosDef)
    (hQZX :
      Function.Injective
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))).mulVec) :
    TwoSLSCombinedSampleMomentScoreCLTPositiveCovarianceConditions μ Z X e where
  toTwoSLSCombinedSampleMomentRankConditions :=
    TwoSLSCombinedSampleMomentRankConditions.of_qzz_posDef_qzx_rank_popGram
      (combined_moments := combined_moments)
      (instrument_moments := instrument_moments)
      (hQZZ := hQZZ) (hQZX := hQZX)
  score_clt := score_clt
  omega_posDef := omega_posDef

end TwoSLSCombinedSampleMomentScoreCLTPositiveCovarianceConditions

/-- Hansen-facing Assumption 12.1 surface using only the primitive sample-Gram
WLLN for `[Z_i, X_i]`.

Compared with `TwoSLSCombinedSampleMomentRankConditions`, this package no longer asks for
a dummy regression error attached to the combined regressor.  It records exactly
the combined second-moment WLLN, the instrument-error orthogonality WLLN, and
Hansen's population rank conditions used to derive nonsingularity of the 2SLS
bread. -/
structure TwoSLSGramInstrumentMomentRankConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ) : Prop where
  combined_gram :
    SampleGramWLLNConditions μ (twoSLSCombinedRegressors Z X)
  instrument_moments : SampleMomentAssumption71 μ Z e
  qzz_posDef :
    (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X))).PosDef
  qzx_rank :
    Function.Injective
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))).mulVec

namespace TwoSLSGramInstrumentMomentRankConditions

/-- The primitive Assumption 12.1 Gram package supplies the lower-level combined
sample-moment convergence package used by the 2SLS CMT layer. -/
theorem toCombinedSampleMomentConvergenceConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSGramInstrumentMomentRankConditions μ Z X e) :
    TwoSLSCombinedSampleMomentConvergenceConditions μ Z X e
      (popGram μ (twoSLSCombinedRegressors Z X)) where
  combined_meas := by
    intro n
    simpa [twoSLSCombinedRegressors, stackRegressors] using
      sampleGram_stackRegressors_aestronglyMeasurable_of_wlln
        (μ := μ) (X := twoSLSCombinedRegressors Z X) h.combined_gram n
  combined_tendsto := by
    simpa [twoSLSCombinedRegressors, stackRegressors] using
      sampleGram_stackRegressors_tendstoInMeasure_popGram_of_wlln
        (μ := μ) (X := twoSLSCombinedRegressors Z X) h.combined_gram
  qzz_nonsing := (Matrix.isUnit_iff_isUnit_det _).mp h.qzz_posDef.isUnit
  bread_nonsing :=
    isUnit_twoSLSBread_det_of_qzz_posDef_rank
      (twoSLSCombinedQXZ_eq_transpose_QZX_of_popGram_wlln
        (μ := μ) (Z := Z) (X := X) h.combined_gram)
      h.qzz_posDef h.qzx_rank
  linearization_meas := by
    intro n
    have hCombinedMeas : AEStronglyMeasurable
        (fun ω =>
          sampleGram
            (Matrix.fromCols (fun i : Fin n => Z i.val ω)
              (fun i : Fin n => X i.val ω))) μ := by
      simpa [twoSLSCombinedRegressors, stackRegressors] using
        sampleGram_stackRegressors_aestronglyMeasurable_of_wlln
          (μ := μ) (X := twoSLSCombinedRegressors Z X) h.combined_gram n
    exact twoSLSLinearizationMatrix_aestronglyMeasurable_of_combined_sampleGram
      (μ := μ) (Z := Z) (X := X) (n := n) hCombinedMeas
  score_meas := by
    intro n
    simpa [stackRegressors, stackErrors] using
      sampleCrossMoment_stack_aestronglyMeasurable
        (μ := μ) (X := Z) (e := e) h.instrument_moments n
  score_tendsto_zero := by
    simpa [stackRegressors, stackErrors] using
      sampleCrossMoment_stack_tendstoInMeasure_zero
        (μ := μ) (X := Z) (e := e) h.instrument_moments

/-- The primitive Assumption 12.1 Gram package supplies the lower-level Hansen
sample-moment convergence package. -/
theorem toSampleMomentConvergenceConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSGramInstrumentMomentRankConditions μ Z X e) :
    TwoSLSSampleMomentConvergenceConditions μ Z X e
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) :=
  h.toCombinedSampleMomentConvergenceConditions.toSampleMomentConvergenceConditions

/-- Compatibility constructor from the older proof-facing package when callers
already have a full combined-regression Chapter 7 moment bundle. -/
theorem ofAssumption12_1Conditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSCombinedSampleMomentRankConditions μ Z X e)
    (hQZZ :
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X))).PosDef)
    (hQZX :
      Function.Injective
        (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))).mulVec) :
    TwoSLSGramInstrumentMomentRankConditions μ Z X e := by
  rcases h.combined_moments with ⟨u, hCombined⟩
  exact
    { combined_gram := SampleGramWLLNConditions.ofSampleMoment hCombined
      instrument_moments := h.instrument_moments
      qzz_posDef := hQZZ
      qzx_rank := hQZX }

end TwoSLSGramInstrumentMomentRankConditions

/-- IID finite-second-moment sufficient condition package for Hansen
Assumption 12.1.

This is the primitive row-level surface for Theorem 12.1: iid combined
instrument/regressor rows `[Z_i, X_i]`, iid instrument-error rows `(Z_i,e_i)`,
finite second moments, orthogonality, and Hansen's population rank conditions. -/
structure TwoSLSSplitIidSecondMomentRankConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ) : Prop where
  combined_aestronglyMeasurable :
    ∀ i, AEStronglyMeasurable (twoSLSCombinedRegressors Z X i) μ
  combined_iIndep : iIndepFun (twoSLSCombinedRegressors Z X) μ
  combined_identDistrib : ∀ i,
    IdentDistrib (twoSLSCombinedRegressors Z X i)
      (twoSLSCombinedRegressors Z X 0) μ μ
  combined_norm_sq_integrable :
    Integrable (fun ω => ‖twoSLSCombinedRegressors Z X 0 ω‖ ^ 2) μ
  z_aestronglyMeasurable : ∀ i, AEStronglyMeasurable (Z i) μ
  x_aestronglyMeasurable : ∀ i, AEStronglyMeasurable (X i) μ
  e_aestronglyMeasurable : ∀ i, AEStronglyMeasurable (e i) μ
  instrument_joint_iIndep : iIndepFun (fun i ω => (Z i ω, e i ω)) μ
  instrument_joint_identDistrib : ∀ i,
    IdentDistrib (fun ω => (Z i ω, e i ω))
      (fun ω => (Z 0 ω, e 0 ω)) μ μ
  instrument_norm_sq_integrable : Integrable (fun ω => ‖Z 0 ω‖ ^ 2) μ
  instrument_cross_integrable : Integrable (fun ω => e 0 ω • Z 0 ω) μ
  orthogonality : μ[fun ω => e 0 ω • Z 0 ω] = 0
  qzz_posDef :
    (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X))).PosDef
  qzx_rank :
    Function.Injective
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))).mulVec

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
private lemma measurable_joint_observation_combined [Finite k] [Finite l] :
    Measurable (fun row : ((l → ℝ) × (k → ℝ)) × ℝ =>
      (Sum.elim row.1.1 row.1.2 : l ⊕ k → ℝ)) := by
  classical
  letI := Fintype.ofFinite k
  letI := Fintype.ofFinite l
  rw [measurable_pi_iff]
  intro s
  cases s with
  | inl a =>
      exact (measurable_pi_apply a).comp (measurable_fst.comp measurable_fst)
  | inr j =>
      exact (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
private lemma measurable_joint_observation_instrument_error :
    Measurable (fun row : ((l → ℝ) × (k → ℝ)) × ℝ => (row.1.1, row.2)) :=
  (measurable_fst.comp measurable_fst).prodMk measurable_snd

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
private theorem twoSLSCombinedRegressors_aestronglyMeasurable_of_rows
    [Finite k] [Finite l]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ) :
    ∀ i, AEStronglyMeasurable (twoSLSCombinedRegressors Z X i) μ := by
  classical
  letI := Fintype.ofFinite k
  letI := Fintype.ofFinite l
  intro i
  rw [aestronglyMeasurable_iff_aemeasurable]
  rw [aemeasurable_pi_iff]
  intro s
  cases s with
  | inl a =>
      exact ((continuous_apply a).comp_aestronglyMeasurable (hZ i)).aemeasurable
  | inr j =>
      exact ((continuous_apply j).comp_aestronglyMeasurable (hX i)).aemeasurable

omit [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
/-- Separate finite second moments of `Z` and `X` imply a finite second moment
for the combined IV row `[Z,X]`. -/
private theorem twoSLSCombinedRegressors_norm_sq_integrable_of_rows
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    (hZ0 : AEStronglyMeasurable (Z 0) μ)
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (hZNorm2 : Integrable (fun ω => ‖Z 0 ω‖ ^ 2) μ)
    (hXNorm2 : Integrable (fun ω => ‖X 0 ω‖ ^ 2) μ) :
    Integrable (fun ω => ‖twoSLSCombinedRegressors Z X 0 ω‖ ^ 2) μ := by
  classical
  have hcombined0 :
      AEStronglyMeasurable (twoSLSCombinedRegressors Z X 0) μ := by
    rw [aestronglyMeasurable_iff_aemeasurable]
    rw [aemeasurable_pi_iff]
    intro s
    cases s with
    | inl a =>
        exact ((continuous_apply a).comp_aestronglyMeasurable hZ0).aemeasurable
    | inr j =>
        exact ((continuous_apply j).comp_aestronglyMeasurable hX0).aemeasurable
  have hcombined_meas :
      AEStronglyMeasurable
        (fun ω => ‖twoSLSCombinedRegressors Z X 0 ω‖ ^ 2) μ := by
    exact ((continuous_norm.comp_aestronglyMeasurable hcombined0).aemeasurable
      |>.pow_const 2).aestronglyMeasurable
  have hdom : Integrable
      (fun ω => 2 * ‖Z 0 ω‖ ^ 2 + 2 * ‖X 0 ω‖ ^ 2) μ := by
    simpa [Pi.add_apply] using
      (hZNorm2.const_mul (2 : ℝ)).add (hXNorm2.const_mul (2 : ℝ))
  refine hdom.mono' hcombined_meas (ae_of_all μ fun ω => ?_)
  have hnorm :
      ‖twoSLSCombinedRegressors Z X 0 ω‖ ≤ ‖Z 0 ω‖ + ‖X 0 ω‖ := by
    refine (pi_norm_le_iff_of_nonneg ?_).2 ?_
    · positivity
    · intro s
      cases s with
      | inl a =>
          calc
            ‖twoSLSCombinedRegressors Z X 0 ω (Sum.inl a)‖ = ‖Z 0 ω a‖ := by
              simp [twoSLSCombinedRegressors]
            _ ≤ ‖Z 0 ω‖ := norm_le_pi_norm (Z 0 ω) a
            _ ≤ ‖Z 0 ω‖ + ‖X 0 ω‖ :=
              le_add_of_nonneg_right (norm_nonneg (X 0 ω))
      | inr j =>
          calc
            ‖twoSLSCombinedRegressors Z X 0 ω (Sum.inr j)‖ = ‖X 0 ω j‖ := by
              simp [twoSLSCombinedRegressors]
            _ ≤ ‖X 0 ω‖ := norm_le_pi_norm (X 0 ω) j
            _ ≤ ‖Z 0 ω‖ + ‖X 0 ω‖ :=
              le_add_of_nonneg_left (norm_nonneg (Z 0 ω))
  have hsq1 :
      ‖twoSLSCombinedRegressors Z X 0 ω‖ ^ 2 ≤
        (‖Z 0 ω‖ + ‖X 0 ω‖) ^ 2 := by
    nlinarith [hnorm, norm_nonneg (twoSLSCombinedRegressors Z X 0 ω)]
  have hsq2 :
      (‖Z 0 ω‖ + ‖X 0 ω‖) ^ 2 ≤
        2 * ‖Z 0 ω‖ ^ 2 + 2 * ‖X 0 ω‖ ^ 2 := by
    nlinarith [sq_nonneg (‖Z 0 ω‖ - ‖X 0 ω‖)]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hsq1.trans hsq2

omit [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
/-- Separate finite second moments of `Z` and `X` make the combined-row outer
product integrable. -/
theorem twoSLSCombinedRegressors_outer_integrable_of_rows
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    (hZ0 : AEStronglyMeasurable (Z 0) μ)
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (hZNorm2 : Integrable (fun ω => ‖Z 0 ω‖ ^ 2) μ)
    (hXNorm2 : Integrable (fun ω => ‖X 0 ω‖ ^ 2) μ) :
    Integrable (fun ω =>
      Matrix.vecMulVec (twoSLSCombinedRegressors Z X 0 ω)
        (twoSLSCombinedRegressors Z X 0 ω)) μ := by
  have hCombinedMeas : AEStronglyMeasurable
      (twoSLSCombinedRegressors Z X 0) μ := by
    rw [aestronglyMeasurable_iff_aemeasurable, aemeasurable_pi_iff]
    intro s
    cases s with
    | inl a => exact ((continuous_apply a).comp_aestronglyMeasurable hZ0).aemeasurable
    | inr j => exact ((continuous_apply j).comp_aestronglyMeasurable hX0).aemeasurable
  exact integrable_vecMulVec_of_integrable_norm_sq
    (μ := μ) hCombinedMeas
    (twoSLSCombinedRegressors_norm_sq_integrable_of_rows
      (μ := μ) (Z := Z) (X := X) hZ0 hX0 hZNorm2 hXNorm2)

/-- Hansen-facing single-row iid Assumption 12.1 surface.

This packages the iid hypothesis on the observed structural row
`((Z_i, X_i), e_i)` and derives the older split iid fields for `[Z_i, X_i]` and
`(Z_i,e_i)` by measurable projections. -/
structure TwoSLSResidualJointIidSecondMomentRankConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ) : Prop where
  joint_aestronglyMeasurable :
    ∀ i, AEStronglyMeasurable (fun ω => ((Z i ω, X i ω), e i ω)) μ
  joint_iIndep : iIndepFun (fun i ω => ((Z i ω, X i ω), e i ω)) μ
  joint_identDistrib : ∀ i,
    IdentDistrib (fun ω => ((Z i ω, X i ω), e i ω))
      (fun ω => ((Z 0 ω, X 0 ω), e 0 ω)) μ μ
  combined_norm_sq_integrable :
    Integrable (fun ω => ‖twoSLSCombinedRegressors Z X 0 ω‖ ^ 2) μ
  instrument_norm_sq_integrable : Integrable (fun ω => ‖Z 0 ω‖ ^ 2) μ
  instrument_cross_integrable : Integrable (fun ω => e 0 ω • Z 0 ω) μ
  orthogonality : μ[fun ω => e 0 ω • Z 0 ω] = 0
  qzz_posDef :
    (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X))).PosDef
  qzx_rank :
    Function.Injective
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))).mulVec

namespace TwoSLSResidualJointIidSecondMomentRankConditions

omit [DecidableEq k] [DecidableEq l] in
/-- Row measurability for `Z` from the single joint-row measurability field. -/
theorem z_aestronglyMeasurable
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidSecondMomentRankConditions μ Z X e) :
    ∀ i, AEStronglyMeasurable (Z i) μ :=
  fun i =>
    (continuous_fst.comp continuous_fst).comp_aestronglyMeasurable
      (h.joint_aestronglyMeasurable i)

omit [DecidableEq k] [DecidableEq l] in
/-- Row measurability for `X` from the single joint-row measurability field. -/
theorem x_aestronglyMeasurable
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidSecondMomentRankConditions μ Z X e) :
    ∀ i, AEStronglyMeasurable (X i) μ :=
  fun i =>
    (continuous_snd.comp continuous_fst).comp_aestronglyMeasurable
      (h.joint_aestronglyMeasurable i)

omit [DecidableEq k] [DecidableEq l] in
/-- Row measurability for `e` from the single joint-row measurability field. -/
theorem e_aestronglyMeasurable
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidSecondMomentRankConditions μ Z X e) :
    ∀ i, AEStronglyMeasurable (e i) μ :=
  fun i => continuous_snd.comp_aestronglyMeasurable
    (h.joint_aestronglyMeasurable i)

omit [DecidableEq k] [DecidableEq l] in
/-- Convert the single-row iid Assumption 12.1 package into the existing
split-row iid package used by the proof engine. -/
theorem toIidConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidSecondMomentRankConditions μ Z X e) :
    TwoSLSSplitIidSecondMomentRankConditions μ Z X e where
  combined_aestronglyMeasurable :=
    twoSLSCombinedRegressors_aestronglyMeasurable_of_rows
      (μ := μ) (Z := Z) (X := X)
      h.z_aestronglyMeasurable h.x_aestronglyMeasurable
  combined_iIndep := by
    simpa [Function.comp_def, twoSLSCombinedRegressors] using
      h.joint_iIndep.comp
        (fun _ => fun row : ((l → ℝ) × (k → ℝ)) × ℝ =>
          (Sum.elim row.1.1 row.1.2 : l ⊕ k → ℝ))
        (fun _ => measurable_joint_observation_combined (l := l) (k := k))
  combined_identDistrib := by
    intro i
    have hi := (h.joint_identDistrib i).comp
      (measurable_joint_observation_combined (l := l) (k := k))
    simpa [Function.comp_def, twoSLSCombinedRegressors] using hi
  combined_norm_sq_integrable := h.combined_norm_sq_integrable
  z_aestronglyMeasurable := h.z_aestronglyMeasurable
  x_aestronglyMeasurable := h.x_aestronglyMeasurable
  e_aestronglyMeasurable := h.e_aestronglyMeasurable
  instrument_joint_iIndep := by
    simpa [Function.comp_def] using
      h.joint_iIndep.comp
        (fun _ => fun row : ((l → ℝ) × (k → ℝ)) × ℝ => (row.1.1, row.2))
        (fun _ => measurable_joint_observation_instrument_error (l := l) (k := k))
  instrument_joint_identDistrib := by
    intro i
    have hi := (h.joint_identDistrib i).comp
      (measurable_joint_observation_instrument_error (l := l) (k := k))
    simpa [Function.comp_def] using hi
  instrument_norm_sq_integrable := h.instrument_norm_sq_integrable
  instrument_cross_integrable := h.instrument_cross_integrable
  orthogonality := h.orthogonality
  qzz_posDef := h.qzz_posDef
  qzx_rank := h.qzx_rank

end TwoSLSResidualJointIidSecondMomentRankConditions

omit [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
private def twoSLSObservedToResidualRow
    (β0 : k → ℝ)
    (row : ((l → ℝ) × (k → ℝ)) × ℝ) :
    ((l → ℝ) × (k → ℝ)) × ℝ :=
  (row.1, row.2 - row.1.2 ⬝ᵥ β0)

omit [Fintype l] [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
private theorem continuous_twoSLSObservedToResidualRow
    (β0 : k → ℝ) :
    Continuous (twoSLSObservedToResidualRow (l := l) β0) := by
  have hdot : Continuous
      (fun row : ((l → ℝ) × (k → ℝ)) × ℝ => row.1.2 ⬝ᵥ β0) :=
    (continuous_snd.comp continuous_fst).dotProduct continuous_const
  exact continuous_fst.prodMk (continuous_snd.sub hdot)

/-- Literal observed-row finite-second-moment surface for Hansen Assumption 12.1.

The iid condition is stated on Hansen's observed row `((Z_i, X_i), Y_i)`.
The structural equation converts this to the residual-row package used by the
proof engine, while the displayed second moments imply the `[Z,X]` Gram moment
and the `E[Z_i e_i]` integrability fields. -/
structure TwoSLSObservedIidSecondMomentRankConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e Y : ℕ → Ω → ℝ)
    (β0 : k → ℝ) : Prop where
  observed_aestronglyMeasurable :
    ∀ i, AEStronglyMeasurable (fun ω => ((Z i ω, X i ω), Y i ω)) μ
  observed_iIndep : iIndepFun (fun i ω => ((Z i ω, X i ω), Y i ω)) μ
  observed_identDistrib : ∀ i,
    IdentDistrib (fun ω => ((Z i ω, X i ω), Y i ω))
      (fun ω => ((Z 0 ω, X 0 ω), Y 0 ω)) μ μ
  model : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω
  response_sq_integrable : Integrable (fun ω => Y 0 ω ^ 2) μ
  regressor_norm_sq_integrable : Integrable (fun ω => ‖X 0 ω‖ ^ 2) μ
  instrument_norm_sq_integrable : Integrable (fun ω => ‖Z 0 ω‖ ^ 2) μ
  orthogonality : μ[fun ω => e 0 ω • Z 0 ω] = 0
  qzz_posDef :
    (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X))).PosDef
  qzx_rank :
    Function.Injective
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))).mulVec

namespace TwoSLSObservedIidSecondMomentRankConditions

omit [DecidableEq k] [DecidableEq l] in
/-- Row measurability for `Z` from the observed-row iid package. -/
theorem z_aestronglyMeasurable
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidSecondMomentRankConditions μ Z X e Y β0) :
    ∀ i, AEStronglyMeasurable (Z i) μ :=
  fun i =>
    (continuous_fst.comp continuous_fst).comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable i)

omit [DecidableEq k] [DecidableEq l] in
/-- Row measurability for `X` from the observed-row iid package. -/
theorem x_aestronglyMeasurable
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidSecondMomentRankConditions μ Z X e Y β0) :
    ∀ i, AEStronglyMeasurable (X i) μ :=
  fun i =>
    (continuous_snd.comp continuous_fst).comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable i)

omit [DecidableEq k] [DecidableEq l] in
/-- Row measurability for `Y` from the observed-row iid package. -/
theorem y_aestronglyMeasurable
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidSecondMomentRankConditions μ Z X e Y β0) :
    ∀ i, AEStronglyMeasurable (Y i) μ :=
  fun i => continuous_snd.comp_aestronglyMeasurable
    (h.observed_aestronglyMeasurable i)

omit [DecidableEq k] [DecidableEq l] in
/-- Hansen's response and regressor second moments imply a structural-error
second moment through the linear model. -/
private theorem error_memLp_two
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidSecondMomentRankConditions μ Z X e Y β0) :
    MemLp (fun ω => e 0 ω) 2 μ :=
  error_memLp_two_of_response_regressor_second
    (μ := μ) (X := X) (e := e) (Y := Y) (β := β0)
    (h.x_aestronglyMeasurable 0) (h.y_aestronglyMeasurable 0)
    (h.model 0) h.response_sq_integrable h.regressor_norm_sq_integrable

omit [DecidableEq k] [DecidableEq l] in
/-- Convert the observed-row Hansen Assumption 12.1 package into the residual-row
package used by the existing 2SLS consistency proof. -/
theorem toJointIidConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidSecondMomentRankConditions μ Z X e Y β0) :
    TwoSLSResidualJointIidSecondMomentRankConditions μ Z X e := by
  have hrows :
      (fun i ω =>
        twoSLSObservedToResidualRow (l := l) β0 ((Z i ω, X i ω), Y i ω)) =
      (fun i ω => ((Z i ω, X i ω), e i ω)) := by
    funext i ω
    simp [twoSLSObservedToResidualRow, h.model i ω]
  refine
    { joint_aestronglyMeasurable := ?_
      joint_iIndep := ?_
      joint_identDistrib := ?_
      combined_norm_sq_integrable := ?_
      instrument_norm_sq_integrable := h.instrument_norm_sq_integrable
      instrument_cross_integrable := ?_
      orthogonality := h.orthogonality
      qzz_posDef := h.qzz_posDef
      qzx_rank := h.qzx_rank }
  · intro i
    have hres :=
      (continuous_twoSLSObservedToResidualRow (l := l) β0).comp_aestronglyMeasurable
        (h.observed_aestronglyMeasurable i)
    have hrow :
        (fun ω =>
          twoSLSObservedToResidualRow (l := l) β0 ((Z i ω, X i ω), Y i ω)) =
        (fun ω => ((Z i ω, X i ω), e i ω)) :=
      congrFun hrows i
    rw [hrow] at hres
    exact hres
  · have hindep := h.observed_iIndep.comp
      (fun _ => twoSLSObservedToResidualRow (l := l) β0)
      (fun _ => (continuous_twoSLSObservedToResidualRow (l := l) β0).measurable)
    simpa [Function.comp_def, hrows] using hindep
  · intro i
    have hi := (h.observed_identDistrib i).comp
      (continuous_twoSLSObservedToResidualRow (l := l) β0).measurable
    have hrowi :
        (fun ω =>
          twoSLSObservedToResidualRow (l := l) β0 ((Z i ω, X i ω), Y i ω)) =
        (fun ω => ((Z i ω, X i ω), e i ω)) := by
      funext ω
      simp [twoSLSObservedToResidualRow, h.model i ω]
    have hrow0 :
        (fun ω =>
          twoSLSObservedToResidualRow (l := l) β0 ((Z 0 ω, X 0 ω), Y 0 ω)) =
        (fun ω => ((Z 0 ω, X 0 ω), e 0 ω)) := by
      funext ω
      simp [twoSLSObservedToResidualRow, h.model 0 ω]
    simpa [Function.comp_def, hrowi, hrow0] using hi
  · exact twoSLSCombinedRegressors_norm_sq_integrable_of_rows
      (μ := μ) (Z := Z) (X := X)
      (h.z_aestronglyMeasurable 0) (h.x_aestronglyMeasurable 0)
      h.instrument_norm_sq_integrable h.regressor_norm_sq_integrable
  · exact instrument_cross_integrable_of_memLp_two
      (μ := μ) (Z := Z) (e := e)
      (h.z_aestronglyMeasurable 0) h.error_memLp_two
      h.instrument_norm_sq_integrable

end TwoSLSObservedIidSecondMomentRankConditions

namespace TwoSLSSplitIidSecondMomentRankConditions

omit [DecidableEq k] in
/-- Hansen's `Q_ZZ > 0` condition supplies the nonsingularity field required by
Chapter 7's instrument-score moment package. -/
theorem instrument_popGram_nonsing
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidSecondMomentRankConditions μ Z X e) :
    IsUnit (popGram μ Z).det := by
  have hZint : Integrable (fun ω => Matrix.vecMulVec (Z 0 ω) (Z 0 ω)) μ :=
    integrable_vecMulVec_of_integrable_norm_sq
      (μ := μ) (X := Z) (h.z_aestronglyMeasurable 0) h.instrument_norm_sq_integrable
  have hCombinedInt :
      Integrable
        (fun ω =>
          Matrix.vecMulVec (twoSLSCombinedRegressors Z X 0 ω)
            (twoSLSCombinedRegressors Z X 0 ω)) μ :=
    integrable_vecMulVec_of_integrable_norm_sq
      (μ := μ) (X := twoSLSCombinedRegressors Z X)
      (h.combined_aestronglyMeasurable 0) h.combined_norm_sq_integrable
  rw [popGram_eq_twoSLSCombinedQZZ_popGram
    (μ := μ) (Z := Z) (X := X) hZint hCombinedInt]
  exact (Matrix.isUnit_iff_isUnit_det _).mp h.qzz_posDef.isUnit

omit [DecidableEq k] in
/-- The iid finite-second Assumption 12.1 package supplies the existing
Gram/WLLN package used by the 2SLS consistency theorem. -/
theorem toGramConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidSecondMomentRankConditions μ Z X e) :
    TwoSLSGramInstrumentMomentRankConditions μ Z X e where
  combined_gram :=
    SampleGramWLLNConditions.of_iid_finite_second
      (μ := μ) (X := twoSLSCombinedRegressors Z X)
      h.combined_aestronglyMeasurable h.combined_iIndep
      h.combined_identDistrib h.combined_norm_sq_integrable
  instrument_moments :=
    sampleMomentAssumption71_of_iid_moments
      (μ := μ) (X := Z) (e := e)
      (h.z_aestronglyMeasurable 0) h.instrument_joint_iIndep
      h.instrument_joint_identDistrib h.instrument_norm_sq_integrable
      h.instrument_cross_integrable h.instrument_popGram_nonsing h.orthogonality
  qzz_posDef := h.qzz_posDef
  qzx_rank := h.qzx_rank

end TwoSLSSplitIidSecondMomentRankConditions

/-- Proof-facing Gram and score-CLT surface for 2SLS coefficient normality.

Unlike Hansen Assumption 12.2, this reusable engine permits a singular score
covariance and therefore a degenerate Gaussian coefficient limit. -/
structure TwoSLSGramScoreCLTConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    : Prop extends TwoSLSGramInstrumentMomentRankConditions μ Z X e where
  score_clt : ScoreCLTConditions μ Z e

/-- Hansen-facing Assumption 12.2 surface using the primitive sample-Gram WLLN
for `[Z_i, X_i]`, the instrument-score moment WLLN, and the score CLT. -/
structure TwoSLSGramScoreCLTPositiveCovarianceConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    : Prop extends TwoSLSGramInstrumentMomentRankConditions μ Z X e where
  score_clt : ScoreCLTConditions μ Z e
  omega_posDef : (scoreCovMat μ Z e).PosDef

/-- IID finite-fourth-moment sufficient condition package for Hansen
Assumption 12.2.

The finite fourth-moment content is represented by integrability of the
instrument-error score outer product, which is the exact moment consumed by the
Chapter 7 score CLT, together with the scalar squared-error moment needed for
Hansen Theorem 12.3's homoskedastic covariance consistency. The package also
records Hansen's `Ω > 0` condition. -/
structure TwoSLSSplitIidFourthMomentPositiveCovarianceConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    : Prop extends TwoSLSSplitIidSecondMomentRankConditions μ Z X e where
  error_sq_integrable : Integrable (fun ω => e 0 ω ^ 2) μ
  score_outer_integrable :
    Integrable (fun ω => Matrix.vecMulVec (e 0 ω • Z 0 ω) (e 0 ω • Z 0 ω)) μ
  omega_posDef : (scoreCovMat μ Z e).PosDef

/-- Hansen-facing single-row iid Assumption 12.2 surface with the finite
fourth-moment objects used by the Chapter 12 proof engine. -/
structure TwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    : Prop extends TwoSLSResidualJointIidSecondMomentRankConditions μ Z X e where
  error_sq_integrable : Integrable (fun ω => e 0 ω ^ 2) μ
  score_outer_integrable :
    Integrable (fun ω => Matrix.vecMulVec (e 0 ω • Z 0 ω) (e 0 ω • Z 0 ω)) μ
  omega_posDef : (scoreCovMat μ Z e).PosDef

namespace TwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions

omit [DecidableEq k] [DecidableEq l] in
/-- Convert the single-row iid Assumption 12.2 package into the existing
split-row finite-fourth package used by the proof engine. -/
theorem toIidFourthConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions μ Z X e) :
    TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e where
  toTwoSLSSplitIidSecondMomentRankConditions :=
    h.toTwoSLSResidualJointIidSecondMomentRankConditions.toIidConditions
  error_sq_integrable := h.error_sq_integrable
  score_outer_integrable := h.score_outer_integrable
  omega_posDef := h.omega_posDef

end TwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions

namespace TwoSLSSplitIidFourthMomentPositiveCovarianceConditions

omit [DecidableEq k] in
/-- The iid finite-fourth Assumption 12.2 package supplies the existing
Gram/score-CLT package used by the 2SLS asymptotic-normality theorem. -/
theorem toGramConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e) :
    TwoSLSGramScoreCLTPositiveCovarianceConditions μ Z X e where
  toTwoSLSGramInstrumentMomentRankConditions :=
    h.toTwoSLSSplitIidSecondMomentRankConditions.toGramConditions
  score_clt :=
    scoreCLTConditions_of_iid_score_outer
      (μ := μ) (X := Z) (e := e)
      (h.z_aestronglyMeasurable 0) (h.e_aestronglyMeasurable 0)
      h.instrument_joint_iIndep h.instrument_joint_identDistrib
      h.instrument_norm_sq_integrable h.instrument_cross_integrable
      h.score_outer_integrable
      h.toTwoSLSSplitIidSecondMomentRankConditions.instrument_popGram_nonsing
      h.orthogonality
  omega_posDef := h.omega_posDef

omit [DecidableEq k] in
/-- The iid finite-fourth Assumption 12.2 package supplies Chapter 7's HC0
true-error score-covariance WLLN package for the instrument-error score. -/
theorem toSampleHC0Assumption76
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e) :
    SampleHC0Assumption76 μ Z e where
  toScoreCLTConditions := h.toGramConditions.score_clt
  indep_score_outer := by
    have hout : iIndepFun
        (fun i ω => Matrix.vecMulVec (e i ω • Z i ω) (e i ω • Z i ω)) μ := by
      simpa [Function.comp] using
        h.instrument_joint_iIndep.comp
          (fun _ z => Matrix.vecMulVec (z.2 • z.1) (z.2 • z.1))
          (fun _ => measurable_pair_score_outer (q := l))
    intro i j hij
    exact hout.indepFun hij
  ident_score_outer := by
    intro i
    have hi := (h.instrument_joint_identDistrib i).comp
      (measurable_pair_score_outer (q := l))
    simpa [Function.comp] using hi
  int_score_outer := h.score_outer_integrable

omit [DecidableEq k] in
/-- The iid finite-fourth Assumption 12.2 package supplies Chapter 7's scalar
squared-error WLLN package used by Hansen Theorem 12.3's homoskedastic
covariance estimator. -/
theorem toSampleVarianceAssumption74
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e) :
    SampleVarianceAssumption74 μ Z e where
  toLeastSquaresConsistencyConditions :=
    h.toTwoSLSSplitIidSecondMomentRankConditions.toGramConditions.instrument_moments
  indep_error_sq := by
    have hsquare : iIndepFun (fun i ω => e i ω ^ 2) μ := by
      simpa [Function.comp] using
        h.instrument_joint_iIndep.comp
          (fun _ z => z.2 ^ 2)
          (fun _ => ((measurable_snd : Measurable (fun z : (l → ℝ) × ℝ => z.2)).pow_const 2))
    intro i j hij
    exact hsquare.indepFun hij
  ident_error_sq := by
    intro i
    have hi := (h.instrument_joint_identDistrib i).comp
      ((measurable_snd : Measurable (fun z : (l → ℝ) × ℝ => z.2)).pow_const 2)
    simpa [Function.comp] using hi
  int_error_sq := h.error_sq_integrable

set_option linter.flexible false in
omit [DecidableEq k] [DecidableEq l] in
/-- Hansen Theorem 12.3 ideal true-error robust middle WLLN from the primitive
iid Assumption 12.2 package. -/
theorem twoSLSOmegaIdeal_tendstoInMeasure_scoreCovMat
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e) :
    TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaIdeal
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => e i.val ω))
      atTop (fun _ => scoreCovMat μ Z e) := by
  classical
  have hideal :=
    sampleScoreCovIdeal_stack_tendstoInMeasure_scoreCovMat
      (μ := μ) (X := Z) (e := e) h.toSampleHC0Assumption76
  exact hideal.congr_left (fun n => ae_of_all μ (fun ω => by
    by_cases hn : n = 0
    · subst n
      simp [twoSLSOmegaIdeal, sampleScoreCovIdeal, stackRegressors, stackErrors]
    ext a b
    simp [twoSLSOmegaIdeal, sampleScoreCovIdeal, stackRegressors, stackErrors, hn,
      Matrix.smul_apply, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp [Matrix.vecMulVec_apply, pow_two]
    ring))

omit [DecidableEq k] [DecidableEq l] in
/-- Hansen Theorem 12.3 ideal true-error scalar variance WLLN from the
primitive iid Assumption 12.2 package. -/
theorem sampleErrorSecondMoment_tendstoInMeasure_errorVariance
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e) :
    TendstoInMeasure μ
      (fun n ω => sampleErrorSecondMoment (fun i : Fin n => e i.val ω))
      atTop (fun _ => errorVariance μ e) := by
  classical
  simpa [stackErrors] using
    sampleErrorSecondMoment_stack_tendstoInMeasure_errVariance
      (μ := μ) (X := Z) (e := e) h.toSampleVarianceAssumption74

end TwoSLSSplitIidFourthMomentPositiveCovarianceConditions

set_option maxHeartbeats 1200000 in
-- The matrix-valued CMT proof composes several tendstoInMeasure products and inverses.
/-- CMT bridge for Hansen's 2SLS linearization matrix.

If the three sample IV moment matrices converge to their population limits and
the limiting instrument and 2SLS bread matrices are nonsingular, then
`((Q̂_XZ Q̂_ZZ^{-1} Q̂_ZX)^{-1} Q̂_XZ Q̂_ZZ^{-1})` converges to Hansen's
population linearization matrix. -/
theorem twoSLSLinearizationMatrix_tendstoInMeasure_of_sample_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX) :
    TendstoInMeasure μ
      (fun n ω =>
        twoSLSLinearizationMatrix
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω))
      atTop (fun _ => twoSLSPopulationLinearizationMatrix QXZ QZZ QZX) := by
  let QXZhat : ℕ → Ω → Matrix k l ℝ := fun n ω =>
    sampleQXZ (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
  let QZZhat : ℕ → Ω → Matrix l l ℝ := fun n ω =>
    sampleQZZ (fun i : Fin n => Z i.val ω)
  let QZXhat : ℕ → Ω → Matrix l k ℝ := fun n ω =>
    sampleQZX (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
  have hQZZinv_meas : ∀ n,
      AEStronglyMeasurable (fun ω => (QZZhat n ω)⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (h.qzz_meas n)
  have hQZZinv : TendstoInMeasure μ
      (fun n ω => (QZZhat n ω)⁻¹) atTop (fun _ => QZZ⁻¹) :=
    tendstoInMeasure_matrix_inv (μ := μ) h.qzz_meas h.qzz_tendsto
      (fun _ => h.qzz_nonsing)
  have hQXZ_QZZinv_meas : ∀ n,
      AEStronglyMeasurable (fun ω => QXZhat n ω * (QZZhat n ω)⁻¹) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((h.qxz_meas n).prodMk (hQZZinv_meas n))
  have hQXZ_QZZinv : TendstoInMeasure μ
      (fun n ω => QXZhat n ω * (QZZhat n ω)⁻¹)
      atTop (fun _ => QXZ * QZZ⁻¹) :=
    tendstoInMeasure_matrix_mul_rect h.qxz_meas hQZZinv_meas
      h.qxz_tendsto hQZZinv
  have hbread_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => QXZhat n ω * (QZZhat n ω)⁻¹ * QZXhat n ω) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hQXZ_QZZinv_meas n).prodMk (h.qzx_meas n))
  have hbread : TendstoInMeasure μ
      (fun n ω => QXZhat n ω * (QZZhat n ω)⁻¹ * QZXhat n ω)
      atTop (fun _ => twoSLSBread QXZ QZZ QZX) := by
    simpa [twoSLSBread, Matrix.mul_assoc] using
      tendstoInMeasure_matrix_mul_rect hQXZ_QZZinv_meas h.qzx_meas
        hQXZ_QZZinv h.qzx_tendsto
  have hbreadInv_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => (QXZhat n ω * (QZZhat n ω)⁻¹ * QZXhat n ω)⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (hbread_meas n)
  have hbreadInv : TendstoInMeasure μ
      (fun n ω => (QXZhat n ω * (QZZhat n ω)⁻¹ * QZXhat n ω)⁻¹)
      atTop (fun _ => (twoSLSBread QXZ QZZ QZX)⁻¹) :=
    tendstoInMeasure_matrix_inv (μ := μ) hbread_meas hbread
      (fun _ => h.bread_nonsing)
  have hleft_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => (QXZhat n ω * (QZZhat n ω)⁻¹ * QZXhat n ω)⁻¹ *
          QXZhat n ω) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hbreadInv_meas n).prodMk (h.qxz_meas n))
  have hleft : TendstoInMeasure μ
      (fun n ω => (QXZhat n ω * (QZZhat n ω)⁻¹ * QZXhat n ω)⁻¹ *
        QXZhat n ω)
      atTop (fun _ => (twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ) :=
    tendstoInMeasure_matrix_mul_rect hbreadInv_meas h.qxz_meas
      hbreadInv h.qxz_tendsto
  have hlin : TendstoInMeasure μ
      (fun n ω =>
        ((QXZhat n ω * (QZZhat n ω)⁻¹ * QZXhat n ω)⁻¹ *
          QXZhat n ω) * (QZZhat n ω)⁻¹)
      atTop
        (fun _ => ((twoSLSBread QXZ QZZ QZX)⁻¹ * QXZ) * QZZ⁻¹) :=
    tendstoInMeasure_matrix_mul_rect hleft_meas hQZZinv_meas hleft hQZZinv
  simpa [twoSLSLinearizationMatrix, twoSLSPopulationLinearizationMatrix,
    twoSLSBread, QXZhat, QZZhat, QZXhat, Matrix.mul_assoc] using hlin

set_option maxHeartbeats 800000 in
-- This is the bread-only part of the preceding CMT proof, exposed because the
-- finite-sample estimator identities need high-probability nonsingularity.
/-- CMT bridge for Hansen's normalized sample 2SLS bread
`Q̂_XZ Q̂_ZZ^{-1} Q̂_ZX`. -/
theorem twoSLSBread_tendstoInMeasure_of_sample_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX) :
    TendstoInMeasure μ
      (fun n ω =>
        twoSLSBread
          (sampleQXZ (fun i : Fin n => Z i.val ω)
            (fun i : Fin n => X i.val ω))
          (sampleQZZ (fun i : Fin n => Z i.val ω))
          (sampleQZX (fun i : Fin n => Z i.val ω)
            (fun i : Fin n => X i.val ω)))
      atTop (fun _ => twoSLSBread QXZ QZZ QZX) := by
  let QXZhat : ℕ → Ω → Matrix k l ℝ := fun n ω =>
    sampleQXZ (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
  let QZZhat : ℕ → Ω → Matrix l l ℝ := fun n ω =>
    sampleQZZ (fun i : Fin n => Z i.val ω)
  let QZXhat : ℕ → Ω → Matrix l k ℝ := fun n ω =>
    sampleQZX (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
  have hQZZinv_meas : ∀ n,
      AEStronglyMeasurable (fun ω => (QZZhat n ω)⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (h.qzz_meas n)
  have hQZZinv : TendstoInMeasure μ
      (fun n ω => (QZZhat n ω)⁻¹) atTop (fun _ => QZZ⁻¹) :=
    tendstoInMeasure_matrix_inv (μ := μ) h.qzz_meas h.qzz_tendsto
      (fun _ => h.qzz_nonsing)
  have hQXZ_QZZinv_meas : ∀ n,
      AEStronglyMeasurable (fun ω => QXZhat n ω * (QZZhat n ω)⁻¹) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((h.qxz_meas n).prodMk (hQZZinv_meas n))
  have hQXZ_QZZinv : TendstoInMeasure μ
      (fun n ω => QXZhat n ω * (QZZhat n ω)⁻¹)
      atTop (fun _ => QXZ * QZZ⁻¹) :=
    tendstoInMeasure_matrix_mul_rect h.qxz_meas hQZZinv_meas
      h.qxz_tendsto hQZZinv
  have hbread_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => QXZhat n ω * (QZZhat n ω)⁻¹ * QZXhat n ω) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hQXZ_QZZinv_meas n).prodMk (h.qzx_meas n))
  have hbread : TendstoInMeasure μ
      (fun n ω => QXZhat n ω * (QZZhat n ω)⁻¹ * QZXhat n ω)
      atTop (fun _ => twoSLSBread QXZ QZZ QZX) := by
    simpa [twoSLSBread, Matrix.mul_assoc] using
      tendstoInMeasure_matrix_mul_rect hQXZ_QZZinv_meas h.qzx_meas
        hQXZ_QZZinv h.qzx_tendsto
  simpa [twoSLSBread, QXZhat, QZZhat, QZXhat, Matrix.mul_assoc] using hbread

/-- The normalized sample 2SLS bread is singular with asymptotically vanishing
probability whenever the sample IV moments converge and the population bread is
nonsingular. -/
theorem measure_twoSLSBread_singular_tendsto_zero_of_sample_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX) :
    Tendsto
      (fun n => μ {ω |
        ¬ IsUnit
          (twoSLSBread
            (sampleQXZ (fun i : Fin n => Z i.val ω)
              (fun i : Fin n => X i.val ω))
            (sampleQZZ (fun i : Fin n => Z i.val ω))
            (sampleQZX (fun i : Fin n => Z i.val ω)
              (fun i : Fin n => X i.val ω))).det})
      atTop (𝓝 0) := by
  let QXZhat : ℕ → Ω → Matrix k l ℝ := fun n ω =>
    sampleQXZ (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
  let QZZhat : ℕ → Ω → Matrix l l ℝ := fun n ω =>
    sampleQZZ (fun i : Fin n => Z i.val ω)
  let QZXhat : ℕ → Ω → Matrix l k ℝ := fun n ω =>
    sampleQZX (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
  have hQZZinv_meas : ∀ n,
      AEStronglyMeasurable (fun ω => (QZZhat n ω)⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (h.qzz_meas n)
  have hQXZ_QZZinv_meas : ∀ n,
      AEStronglyMeasurable (fun ω => QXZhat n ω * (QZZhat n ω)⁻¹) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((h.qxz_meas n).prodMk (hQZZinv_meas n))
  have hbread_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          twoSLSBread
            (sampleQXZ (fun i : Fin n => Z i.val ω)
              (fun i : Fin n => X i.val ω))
            (sampleQZZ (fun i : Fin n => Z i.val ω))
            (sampleQZX (fun i : Fin n => Z i.val ω)
              (fun i : Fin n => X i.val ω))) μ := by
    intro n
    simpa [twoSLSBread, QXZhat, QZZhat, QZXhat, Matrix.mul_assoc] using
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        ((hQXZ_QZZinv_meas n).prodMk (h.qzx_meas n))
  have hDet : TendstoInMeasure μ
      (fun n ω =>
        (twoSLSBread
          (sampleQXZ (fun i : Fin n => Z i.val ω)
            (fun i : Fin n => X i.val ω))
          (sampleQZZ (fun i : Fin n => Z i.val ω))
          (sampleQZX (fun i : Fin n => Z i.val ω)
            (fun i : Fin n => X i.val ω))).det)
      atTop (fun _ => (twoSLSBread QXZ QZZ QZX).det) :=
    tendstoInMeasure_continuous_comp hbread_meas
      (twoSLSBread_tendstoInMeasure_of_sample_moments
        (μ := μ) (Z := Z) (X := X) (e := e) h)
      (Continuous.matrix_det continuous_id)
  have hqne : (twoSLSBread QXZ QZZ QZX).det ≠ 0 := h.bread_nonsing.ne_zero
  set ε : ℝ := |(twoSLSBread QXZ QZZ QZX).det| / 2 with hε_def
  have hε_pos : 0 < ε := half_pos (abs_pos.mpr hqne)
  have hε_le : ε ≤ |(twoSLSBread QXZ QZZ QZX).det| := by
    rw [hε_def]
    linarith [abs_nonneg (twoSLSBread QXZ QZZ QZX).det]
  have hmeas_eps := hDet (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε_pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmeas_eps
    (fun _ => zero_le _) (fun n => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq, isUnit_iff_ne_zero, not_not] at hω
  simp only [Set.mem_setOf_eq, hω, edist_dist, Real.dist_eq, zero_sub, abs_neg]
  exact ENNReal.ofReal_le_ofReal hε_le

/-- Proof-facing condition package for Hansen Theorem 12.1.

It records the convergence ingredients used after the WLLN/CMT reduction from
Assumption 12.1: the sample 2SLS linearization matrix converges to its population
counterpart and the instrument-error score `n^{-1}Z'e` converges to zero. -/
structure TwoSLSConsistencyConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (QXZ : Matrix k l ℝ) (QZZ : Matrix l l ℝ) (QZX : Matrix l k ℝ) : Prop where
  linearization_meas : ∀ n,
    AEStronglyMeasurable
      (fun ω =>
        twoSLSLinearizationMatrix
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)) μ
  linearization_tendsto : TendstoInMeasure μ
    (fun n ω =>
      twoSLSLinearizationMatrix
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω))
    atTop (fun _ => twoSLSPopulationLinearizationMatrix QXZ QZZ QZX)
  score_meas : ∀ n,
    AEStronglyMeasurable
      (fun ω => sampleCrossMoment (fun i : Fin n => Z i.val ω)
        (fun i : Fin n => e i.val ω)) μ
  score_tendsto_zero : TendstoInMeasure μ
    (fun n ω => sampleCrossMoment (fun i : Fin n => Z i.val ω)
      (fun i : Fin n => e i.val ω))
    atTop (fun _ => 0)

/-- Build the proof-facing Hansen Theorem 12.1 condition package from the
more explicit sample-moment convergence package. -/
theorem TwoSLSSampleMomentConvergenceConditions.toConsistencyConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX) :
    TwoSLSConsistencyConditions μ Z X e QXZ QZZ QZX where
  linearization_meas := h.linearization_meas
  linearization_tendsto :=
    twoSLSLinearizationMatrix_tendstoInMeasure_of_sample_moments
      (μ := μ) (Z := Z) (X := X) (e := e) h
  score_meas := h.score_meas
  score_tendsto_zero := h.score_tendsto_zero

/-- The 2SLS leading consistency term
`((Q̂_XZ Q̂_ZZ^{-1} Q̂_ZX)^{-1} Q̂_XZ Q̂_ZZ^{-1})(n^{-1}Z'e)`
converges to zero when the linearization matrix converges and the IV score
converges to zero. -/
theorem twoSLSLinearizedScore_tendstoInMeasure_zero
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSConsistencyConditions μ Z X e QXZ QZZ QZX) :
    TendstoInMeasure μ
      (fun n ω =>
        twoSLSLinearizationMatrix
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω) *ᵥ
          sampleCrossMoment (fun i : Fin n => Z i.val ω)
            (fun i : Fin n => e i.val ω))
      atTop (fun _ => 0) := by
  have hmul := tendstoInMeasure_mulVec_rect
    (μ := μ) h.linearization_meas h.score_meas
    h.linearization_tendsto h.score_tendsto_zero
  simpa using hmul

/-- Exact finite-sample linearization premise for Hansen Theorem 12.1.

Under the structural equation `Y_i = X_i'β + e_i` and nonsingularity of the
Star 2SLS bread on positive sample sizes, the estimator-linearization remainder
used by `twoSLSBetaStar_tendstoInMeasure_beta_of_linearization` is identically
zero. -/
theorem twoSLSBetaStar_linearization_tendstoInMeasure_zero_of_model_nonsingular
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω) - β) -
        fun (t : ℕ) ω =>
          twoSLSLinearizationMatrix
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω) *ᵥ
            sampleCrossMoment (fun i : Fin t => Z i.val ω)
              (fun i : Fin t => e i.val ω))
      atTop (fun _ => 0) := by
  have hzero : TendstoInMeasure μ
      (fun (_ : ℕ) (_ : Ω) => (0 : k → ℝ)) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all μ (fun _ => tendsto_const_nhds))
  refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hzero
  filter_upwards [eventually_gt_atTop 0] with n hn_pos
  exact ae_of_all μ (fun ω => by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
    have hY :
        stackOutcomes Y n ω =
          stackRegressors X n ω *ᵥ β + stackErrors e n ω :=
      stack_linear_model X e Y β hmodel n ω
    change (0 : k → ℝ) =
      (twoSLSBetaStar (stackRegressors Z n ω) (stackRegressors X n ω)
        (stackOutcomes Y n ω) - β) -
      twoSLSLinearizationMatrix (stackRegressors Z n ω) (stackRegressors X n ω) *ᵥ
        sampleCrossMoment (stackRegressors Z n ω) (stackErrors e n ω)
    rw [hY]
    have hlin := twoSLSBetaStar_sub_eq_linearizedScore_of_nonsingular
      (Z := stackRegressors Z n ω) (X := stackRegressors X n ω)
      (β := β) (e := stackErrors e n ω) (hunit := hunit n ω hn_pos)
    rw [hlin]
    simp)

/-- Hansen Theorem 12.1 linearization from sample-moment convergence.

The exact Star identity holds on the event where Hansen's normalized sample
2SLS bread is nonsingular; the complement has probability tending to zero by
`measure_twoSLSBread_singular_tendsto_zero_of_sample_moments`. -/
theorem twoSLSBetaStar_linearization_tendstoInMeasure_zero_of_sample_moments_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω) - β) -
        fun (t : ℕ) ω =>
          twoSLSLinearizationMatrix
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω) *ᵥ
            sampleCrossMoment (fun i : Fin t => Z i.val ω)
              (fun i : Fin t => e i.val ω))
      atTop (fun _ => 0) := by
  have hsingular :=
    measure_twoSLSBread_singular_tendsto_zero_of_sample_moments
      (μ := μ) (Z := Z) (X := X) (e := e) h
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsingular
    (Eventually.of_forall (fun _ => zero_le _)) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn_pos
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro hbread
  haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
  have hstar_unit :
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det :=
    isUnit_twoSLSMomentMatrixStar_det_of_sample_bread
      (Z := fun i : Fin n => Z i.val ω)
      (X := fun i : Fin n => X i.val ω) hbread
  have hY :
      stackOutcomes Y n ω =
        stackRegressors X n ω *ᵥ β + stackErrors e n ω :=
    stack_linear_model X e Y β hmodel n ω
  have hR :
      (twoSLSBetaStar (stackRegressors Z n ω) (stackRegressors X n ω)
          (stackOutcomes Y n ω) - β) -
        twoSLSLinearizationMatrix (stackRegressors Z n ω) (stackRegressors X n ω) *ᵥ
          sampleCrossMoment (stackRegressors Z n ω) (stackErrors e n ω) =
        0 := by
    rw [hY]
    have hlin := twoSLSBetaStar_sub_eq_linearizedScore_of_nonsingular
      (Z := stackRegressors Z n ω) (X := stackRegressors X n ω)
      (β := β) (e := stackErrors e n ω) (hunit := hstar_unit)
    rw [hlin]
    simp
  change ε ≤ edist
      ((twoSLSBetaStar (stackRegressors Z n ω) (stackRegressors X n ω)
          (stackOutcomes Y n ω) - β) -
        twoSLSLinearizationMatrix (stackRegressors Z n ω) (stackRegressors X n ω) *ᵥ
          sampleCrossMoment (stackRegressors Z n ω) (stackErrors e n ω)) 0 at hω
  rw [hR, edist_self] at hω
  exact absurd hω (not_le.mpr hε)

/-- Hansen Theorem 12.1 proof-engine endpoint from a proved 2SLS
linearization.

The condition package supplies the convergence of Hansen's leading term
`((Q̂_XZ Q̂_ZZ^{-1} Q̂_ZX)^{-1} Q̂_XZ Q̂_ZZ^{-1})(n^{-1}Z'e)` to zero.
The remaining premise is the exact estimator-linearization remainder; once it
is established from the finite-sample Star identity, the totalized Star 2SLS
estimator is consistent. -/
theorem twoSLSBetaStar_tendstoInMeasure_beta_of_linearization
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSConsistencyConditions μ Z X e QXZ QZZ QZX) (β : k → ℝ)
    (hlinearization : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω) - β) -
        fun (t : ℕ) ω =>
          twoSLSLinearizationMatrix
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω) *ᵥ
            sampleCrossMoment (fun i : Fin t => Z i.val ω)
              (fun i : Fin t => e i.val ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) := by
  let βhat : ℕ → Ω → k → ℝ := fun t ω =>
    twoSLSBetaStar
      (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
      (fun i : Fin t => Y i.val ω)
  let lin : ℕ → Ω → k → ℝ := fun t ω =>
    twoSLSLinearizationMatrix
      (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω) *ᵥ
      sampleCrossMoment (fun i : Fin t => Z i.val ω)
        (fun i : Fin t => e i.val ω)
  have hlin0 : TendstoInMeasure μ lin atTop (fun _ => 0) := by
    simpa [lin] using
      twoSLSLinearizedScore_tendstoInMeasure_zero
        (μ := μ) (Z := Z) (X := X) (e := e) h
  have hdiff : TendstoInMeasure μ
      (fun t ω => βhat t ω - β) atTop (fun _ => 0) := by
    exact TendstoInMeasure.of_sub_tendsto_zero_vector
      (by simpa [βhat, lin] using hlinearization) hlin0
  have hconst : TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => β)
      atTop (fun _ => β) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all μ (fun _ => tendsto_const_nhds))
  exact TendstoInMeasure.of_sub_tendsto_zero_vector
    (by simpa [βhat] using hdiff) hconst

/-- Hansen Theorem 12.1 textbook-facing OrZero wrapper.

The repo's OrZero convention makes the public estimator agree with the Star
proof engine, so the consistency theorem transfers directly. -/
theorem twoSLSBetaOrZero_tendstoInMeasure_beta_of_linearization
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSConsistencyConditions μ Z X e QXZ QZZ QZX) (β : k → ℝ)
    (hlinearization : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω) - β) -
        fun (t : ℕ) ω =>
          twoSLSLinearizationMatrix
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω) *ᵥ
            sampleCrossMoment (fun i : Fin t => Z i.val ω)
              (fun i : Fin t => e i.val ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) := by
  simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using
    twoSLSBetaStar_tendstoInMeasure_beta_of_linearization
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hlinearization

/-- Hansen Theorem 12.1 endpoint from the structural equation and positive-sample
nonsingularity of the 2SLS bread.

This composes the WLLN/CMT condition package with the exact finite-sample Star
identity, so callers no longer need to provide the estimator-linearization
remainder separately. -/
theorem twoSLSBetaStar_tendstoInMeasure_beta_of_model_nonsingular
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSConsistencyConditions μ Z X e QXZ QZZ QZX) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) := by
  exact twoSLSBetaStar_tendstoInMeasure_beta_of_linearization
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β
    (twoSLSBetaStar_linearization_tendstoInMeasure_zero_of_model_nonsingular
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) β hmodel hunit)

/-- Textbook-facing OrZero version of the Hansen Theorem 12.1 structural-model
consistency endpoint. -/
theorem twoSLSBetaOrZero_tendstoInMeasure_beta_of_model_nonsingular
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSConsistencyConditions μ Z X e QXZ QZZ QZX) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) := by
  simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using
    twoSLSBetaStar_tendstoInMeasure_beta_of_model_nonsingular
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel hunit

/-- Hansen Theorem 12.1 endpoint from explicit sample-moment convergence.

This wrapper derives the random linearization-matrix convergence by CMT from
the sample IV moment matrices, then applies the structural-model Star identity.
The primitive iid WLLN and high-probability nonsingularity steps remain outside
this theorem. -/
theorem twoSLSBetaStar_tendstoInMeasure_beta_of_sample_moments_model_nonsingular
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) :=
  twoSLSBetaStar_tendstoInMeasure_beta_of_model_nonsingular
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toConsistencyConditions β hmodel hunit

/-- Textbook-facing OrZero version of the sample-moment Theorem 12.1 wrapper. -/
theorem twoSLSBetaOrZero_tendstoInMeasure_beta_of_sample_moments_model_nonsingular
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) :=
  twoSLSBetaOrZero_tendstoInMeasure_beta_of_model_nonsingular
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toConsistencyConditions β hmodel hunit

/-- Hansen Theorem 12.1 endpoint from explicit sample-moment convergence and
the structural equation.

This version derives the high-probability nonsingularity step from the same
sample-moment package, so it does not require a pointwise finite-sample
nonsingularity premise. -/
theorem twoSLSBetaStar_tendstoInMeasure_beta_of_sample_moments_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) :=
  twoSLSBetaStar_tendstoInMeasure_beta_of_linearization
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toConsistencyConditions β
    (twoSLSBetaStar_linearization_tendstoInMeasure_zero_of_sample_moments_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel)

/-- Textbook-facing OrZero version of the Hansen Theorem 12.1 sample-moment
endpoint without a pointwise finite-sample nonsingularity premise. -/
theorem twoSLSBetaOrZero_tendstoInMeasure_beta_of_sample_moments_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) := by
  simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using
    twoSLSBetaStar_tendstoInMeasure_beta_of_sample_moments_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel

/-- Hansen Theorem 12.1 endpoint from the Hansen-facing Assumption 12.1
condition package and the structural equation. -/
theorem twoSLSBetaStar_tendstoInMeasure_beta_of_assumption12_1_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSCombinedSampleMomentRankConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) :=
  twoSLSBetaStar_tendstoInMeasure_beta_of_sample_moments_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toSampleMomentConvergenceConditions β hmodel

/-- Textbook-facing OrZero version of the Hansen Theorem 12.1 endpoint from the
Hansen-facing Assumption 12.1 condition package. -/
theorem twoSLSBetaOrZero_tendstoInMeasure_beta_of_assumption12_1_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSCombinedSampleMomentRankConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) :=
  twoSLSBetaOrZero_tendstoInMeasure_beta_of_sample_moments_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toSampleMomentConvergenceConditions β hmodel

/-- Hansen Theorem 12.1 endpoint from the primitive Assumption 12.1 Gram
package and the structural equation. -/
theorem twoSLSBetaStar_tendstoInMeasure_beta_of_assumption12_1_gram_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSGramInstrumentMomentRankConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) :=
  twoSLSBetaStar_tendstoInMeasure_beta_of_sample_moments_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toSampleMomentConvergenceConditions β hmodel

/-- Textbook-facing OrZero version of the Hansen Theorem 12.1 endpoint from the
primitive Assumption 12.1 Gram package. -/
theorem twoSLSBetaOrZero_tendstoInMeasure_beta_of_assumption12_1_gram_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSGramInstrumentMomentRankConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) :=
  twoSLSBetaOrZero_tendstoInMeasure_beta_of_sample_moments_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toSampleMomentConvergenceConditions β hmodel

/-- Hansen Theorem 12.1 endpoint from the iid finite-second-moment Assumption
12.1 package and the structural equation. -/
theorem twoSLSBetaStar_tendstoInMeasure_beta_of_assumption12_1_iid_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidSecondMomentRankConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) :=
  twoSLSBetaStar_tendstoInMeasure_beta_of_assumption12_1_gram_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toGramConditions β hmodel

/-- Textbook-facing OrZero version of Hansen Theorem 12.1 from the iid
finite-second-moment Assumption 12.1 package. -/
theorem twoSLSBetaOrZero_tendstoInMeasure_beta_of_assumption12_1_iid_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidSecondMomentRankConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) :=
  twoSLSBetaOrZero_tendstoInMeasure_beta_of_assumption12_1_gram_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toGramConditions β hmodel

/-- Hansen Theorem 12.1 endpoint from the single-row iid Assumption 12.1
package and the structural equation. -/
theorem twoSLSBetaStar_tendstoInMeasure_beta_of_assumption12_1_joint_iid_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidSecondMomentRankConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) :=
  twoSLSBetaStar_tendstoInMeasure_beta_of_assumption12_1_iid_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toIidConditions β hmodel

/-- Textbook-facing OrZero version of Hansen Theorem 12.1 from the single-row
iid Assumption 12.1 package. -/
theorem twoSLSBetaOrZero_tendstoInMeasure_beta_of_assumption12_1_joint_iid_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidSecondMomentRankConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) :=
  twoSLSBetaOrZero_tendstoInMeasure_beta_of_assumption12_1_iid_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toIidConditions β hmodel

/-- **Hansen Theorem 12.1**, literal observed-row iid finite-second-moment
surface.

The iid condition is stated on `((Z_i, X_i), Y_i)` and the proof reuses the
single-row residual package obtained from the structural equation. -/
theorem twoSLSBetaStar_tendstoInMeasure_beta_of_textbook12_1_joint_iid_second
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidSecondMomentRankConditions μ Z X e Y β0) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β0) :=
  twoSLSBetaStar_tendstoInMeasure_beta_of_assumption12_1_joint_iid_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toJointIidConditions β0 h.model

/-- Textbook-facing OrZero version of Hansen Theorem 12.1 from the literal
observed-row iid finite-second-moment surface. -/
theorem twoSLSBetaOrZero_tendstoInMeasure_beta_of_textbook12_1_joint_iid_second
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidSecondMomentRankConditions μ Z X e Y β0) :
    TendstoInMeasure μ
      (fun t ω =>
        twoSLSBetaOrZero
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β0) :=
  twoSLSBetaOrZero_tendstoInMeasure_beta_of_assumption12_1_joint_iid_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toJointIidConditions β0 h.model

/-- Proof-facing condition package for Hansen Theorem 12.2 after the score CLT
and random-matrix Slutsky steps have identified the linearized 2SLS statistic. -/
structure TwoSLSAsymptoticNormalConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (Vβ : Matrix k k ℝ) : Prop where
  linearized_limit : TendstoInDistribution
    (fun n ω =>
      twoSLSLinearizationMatrix
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω) *ᵥ
        (Real.sqrt (n : ℝ) •
      sampleCrossMoment (fun i : Fin n => Z i.val ω)
        (fun i : Fin n => e i.val ω)))
    atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
    (multivariateGaussian 0 Vβ)

/-- Formula-facing condition package for Hansen Theorem 12.2.

This is the same proof-facing CLT interface as
`TwoSLSAsymptoticNormalConditions`, but it fixes the covariance matrix to
Hansen's displayed formula
`(Q_XZ Q_ZZ^{-1} Q_ZX)^{-1}
  (Q_XZ Q_ZZ^{-1} Ω Q_ZZ^{-1} Q_ZX)
  (Q_XZ Q_ZZ^{-1} Q_ZX)^{-1}`. -/
abbrev TwoSLSFormulaAsymptoticNormalConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (QXZ : Matrix k l ℝ) (QZZ Omega : Matrix l l ℝ)
    (QZX : Matrix l k ℝ) : Prop :=
  TwoSLSAsymptoticNormalConditions μ Z X e
    (twoSLSAsymptoticVariance QXZ QZZ Omega QZX)

omit [DecidableEq k] in
/-- Rectangular random-linear-map Slutsky bridge for Chapter 12.

If `Tₙ ⇒ T` and a random rectangular matrix `Aₙ` converges in probability to a
constant `A`, then `AₙTₙ ⇒ AT`. This is the rectangular analogue of the Chapter
7 square-matrix CMT used for OLS. -/
theorem matrixContinuousLinearMap_tendstoInDistribution_of_vector_and_matrix
    {Ω' : Type*} [MeasurableSpace Ω'] {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {T : ℕ → Ω → EuclideanSpace ℝ l} {Zlim : Ω' → EuclideanSpace ℝ l}
    {Ahat : ℕ → Ω → Matrix k l ℝ} {A : Matrix k l ℝ}
    (hT : TendstoInDistribution T atTop Zlim (fun _ => μ) ν)
    (hA_meas : ∀ n, AEStronglyMeasurable (Ahat n) μ)
    (hA : TendstoInMeasure μ Ahat atTop (fun _ => A)) :
    TendstoInDistribution
      (fun n ω => matrixContinuousLinearMap (Ahat n ω) (T n ω))
      atTop (fun ω => matrixContinuousLinearMap A (Zlim ω)) (fun _ => μ) ν := by
  have hA_meas' : ∀ n, AEMeasurable (Ahat n) μ :=
    fun n => (hA_meas n).aemeasurable
  have hcont : Continuous
      (fun p : EuclideanSpace ℝ l × Matrix k l ℝ =>
        WithLp.toLp 2 (p.2 *ᵥ p.1.ofLp : k → ℝ)) := by
    exact (PiLp.continuous_toLp 2 (fun _ : k => ℝ)).comp
      (Continuous.matrix_mulVec continuous_snd
        ((PiLp.continuous_ofLp 2 (fun _ : l => ℝ)).comp continuous_fst))
  have hraw := hT.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : EuclideanSpace ℝ l × Matrix k l ℝ =>
      WithLp.toLp 2 (p.2 *ᵥ p.1.ofLp : k → ℝ))
    hcont hA hA_meas'
  simpa [Function.comp_def, matrixContinuousLinearMap_apply] using hraw

/-- Algebraic bridge from the linear-map covariance `A Ω A'` to Hansen's
displayed 2SLS sandwich covariance.

The hypotheses record the population symmetry facts normally supplied by
`Q_ZZ = E[ZZ']` and `Q_ZX = Q_XZ'`. -/
theorem twoSLSAsymptoticVariance_eq_linearization_covariance
    (QXZ : Matrix k l ℝ) (QZZ Omega : Matrix l l ℝ) (QZX : Matrix l k ℝ)
    (hQZZ_symm : QZZᵀ = QZZ) (hQZX : QZX = QXZᵀ) :
    twoSLSAsymptoticVariance QXZ QZZ Omega QZX =
      twoSLSPopulationLinearizationMatrix QXZ QZZ QZX * Omega *
        (twoSLSPopulationLinearizationMatrix QXZ QZZ QZX)ᵀ := by
  have hQZZ_inv_symm : (QZZ⁻¹)ᵀ = QZZ⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hQZZ_symm]
  have hQXZ_t : QXZᵀ = QZX := hQZX.symm
  have hQZX_t : QZXᵀ = QXZ := by
    rw [hQZX, Matrix.transpose_transpose]
  have hbread_symm :
      (twoSLSBread QXZ QZZ QZX)ᵀ = twoSLSBread QXZ QZZ QZX := by
    simp [twoSLSBread, Matrix.transpose_mul, hQZZ_inv_symm, hQXZ_t, hQZX_t,
      Matrix.mul_assoc]
  have hbread_inv_symm :
      ((twoSLSBread QXZ QZZ QZX)⁻¹)ᵀ =
        (twoSLSBread QXZ QZZ QZX)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hbread_symm]
  simp [twoSLSAsymptoticVariance, twoSLSPopulationLinearizationMatrix, hQZZ_inv_symm,
    hQXZ_t, hbread_inv_symm, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Positive-semidefiniteness of Hansen's displayed 2SLS sandwich covariance.

This is the covariance nonnegativity bridge used by downstream Wald and
Delta-method wrappers. It proves the textbook sandwich positive semidefinite by
rewriting it as the linear-map covariance `A Ω A'`. -/
theorem twoSLSAsymptoticVariance_posSemidef
    (QXZ : Matrix k l ℝ) (QZZ Omega : Matrix l l ℝ) (QZX : Matrix l k ℝ)
    (hOmega : Omega.PosSemidef)
    (hQZZ_symm : QZZᵀ = QZZ) (hQZX : QZX = QXZᵀ) :
    (twoSLSAsymptoticVariance QXZ QZZ Omega QZX).PosSemidef := by
  rw [twoSLSAsymptoticVariance_eq_linearization_covariance
    (QXZ := QXZ) (QZZ := QZZ) (Omega := Omega) (QZX := QZX)
    hQZZ_symm hQZX]
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosSemidef.mul_mul_conjTranspose_same hOmega
      (twoSLSPopulationLinearizationMatrix QXZ QZZ QZX)

set_option linter.flexible false in
/-- Build Hansen Theorem 12.2's proof-facing normality package from the
Chapter 7 vector score CLT and the Chapter 12 sample-moment CMT.

This reuses Chapter 7 for the instrument-error score `√n n⁻¹Z'e`, then applies
the rectangular random-linear-map Slutsky bridge. The symmetry assumptions are
the exact algebra needed to identify the resulting `A Ω A'` covariance with
Hansen's displayed 2SLS sandwich formula. -/
theorem TwoSLSSampleMomentConvergenceConditions.toFormulaAsymptoticNormalConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e)
    (hQZZ_symm : QZZᵀ = QZZ) (hQZX : QZX = QXZᵀ) :
    TwoSLSFormulaAsymptoticNormalConditions
      μ Z X e QXZ QZZ (scoreCovMat μ Z e) QZX where
  linearized_limit := by
    let A : Matrix k l ℝ := twoSLSPopulationLinearizationMatrix QXZ QZZ QZX
    let T : ℕ → Ω → EuclideanSpace ℝ l := fun n ω =>
      WithLp.toLp 2
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors Z n ω) (stackErrors e n ω))
    have hT : TendstoInDistribution T atTop
        (fun z : EuclideanSpace ℝ l => z) (fun _ => μ)
        (multivariateGaussian 0 (scoreCovMat μ Z e)) := by
      have hBase :=
        scoreEuclidean_sampleCrossMoment_tendstoInDistribution_multivariateGaussian
          (μ := μ) (X := Z) (e := e) hScore
      simpa [T] using hBase
    have hA : TendstoInMeasure μ
        (fun n ω =>
          twoSLSLinearizationMatrix
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω))
        atTop (fun _ => A) := by
      simpa [A] using
        twoSLSLinearizationMatrix_tendstoInMeasure_of_sample_moments
          (μ := μ) (Z := Z) (X := X) (e := e) hMom
    have hlin := matrixContinuousLinearMap_tendstoInDistribution_of_vector_and_matrix
      (μ := μ)
      (T := T) (Zlim := fun z : EuclideanSpace ℝ l => z)
      (Ahat := fun n ω =>
        twoSLSLinearizationMatrix
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω))
      (A := A)
      hT hMom.linearization_meas hA
    have hΩ : (scoreCovMat μ Z e).PosSemidef :=
      scoreCovMat_posSemidef (μ := μ) (X := Z) (e := e) hScore
    have hLaw :
        HasLaw (fun z : EuclideanSpace ℝ l => matrixContinuousLinearMap A z)
          (multivariateGaussian 0 (A * scoreCovMat μ Z e * Aᵀ))
          (multivariateGaussian 0 (scoreCovMat μ Z e)) := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
        hasLaw_multivariateGaussian_zero_linearMap (n := l) (q := k) hΩ A
    have htarget :
        TendstoInDistribution
          (fun n ω =>
            matrixContinuousLinearMap
              (twoSLSLinearizationMatrix
                (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω))
              (T n ω))
          atTop (fun z : EuclideanSpace ℝ k => z) (fun _ => μ)
          (multivariateGaussian 0 (A * scoreCovMat μ Z e * Aᵀ)) := by
      simpa [Function.comp_def] using
        tendstoInDistribution_id_of_hasLaw_limit
          (E := EuclideanSpace ℝ k) hlin hLaw
    have htarget_vec := htarget.continuous_comp
      (PiLp.continuous_ofLp 2 (fun _ : k => ℝ))
    have hdesired :
        TendstoInDistribution
          (fun n ω =>
            (twoSLSLinearizationMatrix
              (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)) *ᵥ
              (Real.sqrt (n : ℝ) •
                sampleCrossMoment (fun i : Fin n => Z i.val ω)
                  (fun i : Fin n => e i.val ω)))
          atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
          (multivariateGaussian 0 (A * scoreCovMat μ Z e * Aᵀ)) := by
      refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) htarget_vec
      intro n
      exact ae_of_all μ (fun ω => by
        have hZeq :
            stackRegressors Z n ω =
              (fun i : Fin n => Z i.val ω : Matrix (Fin n) l ℝ) := by
          ext i j
          rfl
        have hXeq :
            stackRegressors X n ω =
              (fun i : Fin n => X i.val ω : Matrix (Fin n) k ℝ) := by
          ext i j
          rfl
        have heq :
            stackErrors e n ω = (fun i : Fin n => e i.val ω) := rfl
        simp only [T]
        rw [← hZeq, ← hXeq, ← heq]
        rw [sampleCrossMoment_stackRegressors_stackErrors_eq_avg,
          sum_fin_eq_sum_range_smul]
        simp [Matrix.mulVec_smul, Matrix.mulVec_sum, Finset.smul_sum, smul_smul]
        rw [hZeq, hXeq])
    simpa [A,
      twoSLSAsymptoticVariance_eq_linearization_covariance
        (QXZ := QXZ) (QZZ := QZZ) (Omega := scoreCovMat μ Z e)
        (QZX := QZX) hQZZ_symm hQZX] using hdesired

namespace TwoSLSCombinedSampleMomentScoreCLTPositiveCovarianceConditions

/-- A Hansen Assumption 12.2 package supplies the formula-facing normality
conditions for Theorem 12.2 by combining Chapter 7's instrument-score CLT with
the Chapter 12 sample-moment CMT. -/
theorem toFormulaAsymptoticNormalConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSCombinedSampleMomentScoreCLTPositiveCovarianceConditions μ Z X e) :
    TwoSLSFormulaAsymptoticNormalConditions μ Z X e
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) := by
  rcases h.toTwoSLSCombinedSampleMomentRankConditions.combined_moments with ⟨u, hCombined⟩
  have hQsymm :
      (popGram μ (twoSLSCombinedRegressors Z X))ᵀ =
        popGram μ (twoSLSCombinedRegressors Z X) :=
    (popGram_isSymm (μ := μ) (X := twoSLSCombinedRegressors Z X)
      hCombined.int_outer).eq
  have hMom :=
    h.toTwoSLSCombinedSampleMomentRankConditions.toSampleMomentConvergenceConditions
  exact hMom.toFormulaAsymptoticNormalConditions h.score_clt
    (twoSLSCombinedQZZ_transpose_eq_of_symm _ hQsymm)
    (twoSLSCombinedQZX_eq_transpose_of_symm _ hQsymm)

end TwoSLSCombinedSampleMomentScoreCLTPositiveCovarianceConditions

namespace TwoSLSGramScoreCLTConditions

/-- The semidefinite-capable Gram/score engine supplies the formula-facing
normality conditions used by the coefficient CLT. -/
theorem toFormulaAsymptoticNormalConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSGramScoreCLTConditions μ Z X e) :
    TwoSLSFormulaAsymptoticNormalConditions μ Z X e
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) := by
  have hQsymm :
      (popGram μ (twoSLSCombinedRegressors Z X))ᵀ =
        popGram μ (twoSLSCombinedRegressors Z X) :=
    (popGram_isSymm (μ := μ) (X := twoSLSCombinedRegressors Z X)
      h.combined_gram.int_outer).eq
  have hMom :=
    h.toTwoSLSGramInstrumentMomentRankConditions.toSampleMomentConvergenceConditions
  exact hMom.toFormulaAsymptoticNormalConditions h.score_clt
    (twoSLSCombinedQZZ_transpose_eq_of_symm _ hQsymm)
    (twoSLSCombinedQZX_eq_transpose_of_symm _ hQsymm)

end TwoSLSGramScoreCLTConditions

namespace TwoSLSGramScoreCLTPositiveCovarianceConditions

omit [DecidableEq k] in
/-- Forget only Hansen's positive-definiteness condition when a downstream
coefficient theorem permits a degenerate Gaussian limit. -/
theorem toGramScoreCLTConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Z X e) :
    TwoSLSGramScoreCLTConditions μ Z X e where
  toTwoSLSGramInstrumentMomentRankConditions :=
    h.toTwoSLSGramInstrumentMomentRankConditions
  score_clt := h.score_clt

/-- The primitive Assumption 12.2 Gram package supplies the formula-facing
normality conditions for Theorem 12.2. -/
theorem toFormulaAsymptoticNormalConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Z X e) :
    TwoSLSFormulaAsymptoticNormalConditions μ Z X e
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))) := by
  have hQsymm :
      (popGram μ (twoSLSCombinedRegressors Z X))ᵀ =
        popGram μ (twoSLSCombinedRegressors Z X) :=
    (popGram_isSymm (μ := μ) (X := twoSLSCombinedRegressors Z X)
      h.combined_gram.int_outer).eq
  have hMom :=
    h.toTwoSLSGramInstrumentMomentRankConditions.toSampleMomentConvergenceConditions
  exact hMom.toFormulaAsymptoticNormalConditions h.score_clt
    (twoSLSCombinedQZZ_transpose_eq_of_symm _ hQsymm)
    (twoSLSCombinedQZX_eq_transpose_of_symm _ hQsymm)

end TwoSLSGramScoreCLTPositiveCovarianceConditions

/-- Exact scaled finite-sample linearization premise for Hansen Theorem 12.2.

The structural equation and positive-sample nonsingularity identify
`√n(β̂₂ₛₗₛ - β)` with Hansen's linearized score exactly, so the distributional
endpoint only needs the linearized-score CLT. -/
theorem twoSLSBetaStar_sqrt_linearization_tendstoInMeasure_zero_of_model_nonsingular
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          twoSLSLinearizationMatrix
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω) *ᵥ
            (Real.sqrt (t : ℝ) •
              sampleCrossMoment (fun i : Fin t => Z i.val ω)
                (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0) := by
  have hzero : TendstoInMeasure μ
      (fun (_ : ℕ) (_ : Ω) => (0 : k → ℝ)) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all μ (fun _ => tendsto_const_nhds))
  refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hzero
  filter_upwards [eventually_gt_atTop 0] with n hn_pos
  exact ae_of_all μ (fun ω => by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
    have hY :
        stackOutcomes Y n ω =
          stackRegressors X n ω *ᵥ β + stackErrors e n ω :=
      stack_linear_model X e Y β hmodel n ω
    change (0 : k → ℝ) =
      Real.sqrt (n : ℝ) •
        (twoSLSBetaStar (stackRegressors Z n ω) (stackRegressors X n ω)
          (stackOutcomes Y n ω) - β) -
      twoSLSLinearizationMatrix (stackRegressors Z n ω) (stackRegressors X n ω) *ᵥ
        (Real.sqrt (n : ℝ) • sampleCrossMoment (stackRegressors Z n ω) (stackErrors e n ω))
    rw [hY]
    have hlin := twoSLSBetaStar_sub_eq_linearizedScore_of_nonsingular
      (Z := stackRegressors Z n ω) (X := stackRegressors X n ω)
      (β := β) (e := stackErrors e n ω) (hunit := hunit n ω hn_pos)
    rw [hlin]
    simp [Matrix.mulVec_smul])

/-- Hansen Theorem 12.2 scaled linearization from sample-moment convergence.

The exact scaled Star identity holds on the nonsingular normalized-bread event;
the singular event has probability tending to zero under the sample-moment
package. -/
theorem twoSLSBetaStar_sqrt_linearization_tendstoInMeasure_zero_of_sample_moments_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          twoSLSLinearizationMatrix
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω) *ᵥ
            (Real.sqrt (t : ℝ) •
              sampleCrossMoment (fun i : Fin t => Z i.val ω)
                (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0) := by
  have hsingular :=
    measure_twoSLSBread_singular_tendsto_zero_of_sample_moments
      (μ := μ) (Z := Z) (X := X) (e := e) h
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsingular
    (Eventually.of_forall (fun _ => zero_le _)) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn_pos
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro hbread
  haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
  have hstar_unit :
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det :=
    isUnit_twoSLSMomentMatrixStar_det_of_sample_bread
      (Z := fun i : Fin n => Z i.val ω)
      (X := fun i : Fin n => X i.val ω) hbread
  have hY :
      stackOutcomes Y n ω =
        stackRegressors X n ω *ᵥ β + stackErrors e n ω :=
    stack_linear_model X e Y β hmodel n ω
  have hR :
      Real.sqrt (n : ℝ) •
          (twoSLSBetaStar (stackRegressors Z n ω) (stackRegressors X n ω)
            (stackOutcomes Y n ω) - β) -
        twoSLSLinearizationMatrix (stackRegressors Z n ω) (stackRegressors X n ω) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors Z n ω) (stackErrors e n ω)) =
        0 := by
    rw [hY]
    have hlin := twoSLSBetaStar_sub_eq_linearizedScore_of_nonsingular
      (Z := stackRegressors Z n ω) (X := stackRegressors X n ω)
      (β := β) (e := stackErrors e n ω) (hunit := hstar_unit)
    rw [hlin]
    simp [Matrix.mulVec_smul]
  change ε ≤ edist
      (Real.sqrt (n : ℝ) •
          (twoSLSBetaStar (stackRegressors Z n ω) (stackRegressors X n ω)
            (stackOutcomes Y n ω) - β) -
        twoSLSLinearizationMatrix (stackRegressors Z n ω) (stackRegressors X n ω) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors Z n ω) (stackErrors e n ω))) 0 at hω
  rw [hR, edist_self] at hω
  exact absurd hω (not_le.mpr hε)

/-- Hansen Theorem 12.2 interface: asymptotic normality of 2SLS from a linearized
IV score CLT and the remaining estimator linearization. -/
theorem twoSLSBetaStar_tendstoInDistribution_of_linearization
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {Vβ : Matrix k k ℝ}
    (h : TwoSLSAsymptoticNormalConditions μ Z X e Vβ) (β : k → ℝ)
    (hlinearization : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          twoSLSLinearizationMatrix
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω) *ᵥ
            (Real.sqrt (t : ℝ) •
              sampleCrossMoment (fun i : Fin t => Z i.val ω)
                (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0))
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 Vβ) := by
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (t : ℕ) ω =>
      twoSLSLinearizationMatrix
        (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω) *ᵥ
        (Real.sqrt (t : ℝ) •
          sampleCrossMoment (fun i : Fin t => Z i.val ω)
            (fun i : Fin t => e i.val ω)))
    (Y := fun (t : ℕ) ω =>
      Real.sqrt (t : ℝ) •
        (twoSLSBetaStar
          (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
          (fun i : Fin t => Y i.val ω) - β))
    (Z := fun z : EuclideanSpace ℝ k => z.ofLp)
    h.linearized_limit hlinearization hmeas

/-- Hansen Theorem 12.2 textbook-facing OrZero wrapper.

This is the same distributional statement as
`twoSLSBetaStar_tendstoInDistribution_of_linearization`, exposed through the
repo's OrZero totalization convention. -/
theorem twoSLSBetaOrZero_tendstoInDistribution_of_linearization
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {Vβ : Matrix k k ℝ}
    (h : TwoSLSAsymptoticNormalConditions μ Z X e Vβ) (β : k → ℝ)
    (hlinearization : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          twoSLSLinearizationMatrix
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω) *ᵥ
            (Real.sqrt (t : ℝ) •
              sampleCrossMoment (fun i : Fin t => Z i.val ω)
                (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0))
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 Vβ) := by
  have hstar_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ := by
    intro t
    simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using hmeas t
  have hstar :=
    twoSLSBetaStar_tendstoInDistribution_of_linearization
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hlinearization hstar_meas
  simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using hstar

/-- Hansen Theorem 12.2 endpoint from the structural equation and positive-sample
nonsingularity of the 2SLS bread.

This version composes the linearized-score CLT with the exact scaled
finite-sample 2SLS identity, avoiding a separate estimator-linearization
premise. -/
theorem twoSLSBetaStar_tendstoInDistribution_of_model_nonsingular
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {Vβ : Matrix k k ℝ}
    (h : TwoSLSAsymptoticNormalConditions μ Z X e Vβ) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 Vβ) := by
  exact twoSLSBetaStar_tendstoInDistribution_of_linearization
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β
    (twoSLSBetaStar_sqrt_linearization_tendstoInMeasure_zero_of_model_nonsingular
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) β hmodel hunit)
    hmeas

/-- Textbook-facing OrZero version of the Hansen Theorem 12.2 structural-model
asymptotic-normality endpoint. -/
theorem twoSLSBetaOrZero_tendstoInDistribution_of_model_nonsingular
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {Vβ : Matrix k k ℝ}
    (h : TwoSLSAsymptoticNormalConditions μ Z X e Vβ) (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 Vβ) := by
  have hstar_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ := by
    intro t
    simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using hmeas t
  have hstar :=
    twoSLSBetaStar_tendstoInDistribution_of_model_nonsingular
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel hunit hstar_meas
  simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using hstar

/-- Hansen Theorem 12.2 structural-model normality endpoint from a linearized
2SLS CLT and sample-moment convergence.

Unlike `twoSLSBetaStar_tendstoInDistribution_of_model_nonsingular`, this
version derives the high-probability finite-sample nonsingularity step from the
sample IV moment convergence package. -/
theorem twoSLSBetaStar_tendstoInDistribution_of_sample_moments_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {Vβ : Matrix k k ℝ}
    (h : TwoSLSAsymptoticNormalConditions μ Z X e Vβ)
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 Vβ) :=
  twoSLSBetaStar_tendstoInDistribution_of_linearization
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β
    (twoSLSBetaStar_sqrt_linearization_tendstoInMeasure_zero_of_sample_moments_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) hMom β hmodel)
    hmeas

/-- Textbook-facing OrZero version of the Hansen Theorem 12.2 sample-moment
structural endpoint without a pointwise finite-sample nonsingularity premise. -/
theorem twoSLSBetaOrZero_tendstoInDistribution_of_sample_moments_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    {Vβ : Matrix k k ℝ}
    (h : TwoSLSAsymptoticNormalConditions μ Z X e Vβ)
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 Vβ) := by
  have hstar_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ := by
    intro t
    simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using hmeas t
  have hstar :=
    twoSLSBetaStar_tendstoInDistribution_of_sample_moments_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h hMom β hmodel hstar_meas
  simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using hstar

/-- Hansen Theorem 12.2 formula-facing endpoint from the Chapter 7 score CLT,
sample IV moment convergence, and the structural equation. -/
theorem twoSLSBetaStar_tendstoInDistribution_formula_of_scoreCLT_sample_moments_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e)
    (hQZZ_symm : QZZᵀ = QZZ) (hQZX : QZX = QXZᵀ)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (twoSLSAsymptoticVariance QXZ QZZ (scoreCovMat μ Z e) QZX)) :=
  twoSLSBetaStar_tendstoInDistribution_of_sample_moments_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (hMom.toFormulaAsymptoticNormalConditions hScore hQZZ_symm hQZX)
    hMom β hmodel hmeas

/-- Textbook-facing OrZero version of the Hansen Theorem 12.2 formula-facing
sample-moment endpoint. -/
theorem twoSLSBetaOrZero_tendstoInDistribution_formula_of_scoreCLT_sample_moments_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (hMom : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hScore : ScoreCLTConditions μ Z e)
    (hQZZ_symm : QZZᵀ = QZZ) (hQZX : QZX = QXZᵀ)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (twoSLSAsymptoticVariance QXZ QZZ (scoreCovMat μ Z e) QZX)) := by
  have hstar_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ := by
    intro t
    simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using hmeas t
  have hstar :=
    twoSLSBetaStar_tendstoInDistribution_formula_of_scoreCLT_sample_moments_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      hMom hScore hQZZ_symm hQZX β hmodel hstar_meas
  simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using hstar

/-- Hansen Theorem 12.2 formula-facing endpoint from the Hansen-facing
Assumption 12.2 condition package and the structural equation. -/
theorem twoSLSBetaStar_tendstoInDistribution_formula_of_assumption12_2_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSCombinedSampleMomentScoreCLTPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :=
  twoSLSBetaStar_tendstoInDistribution_of_sample_moments_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toFormulaAsymptoticNormalConditions
    h.toTwoSLSCombinedSampleMomentRankConditions.toSampleMomentConvergenceConditions
    β hmodel hmeas

/-- Textbook-facing OrZero version of the Hansen Theorem 12.2 formula endpoint
from the Hansen-facing Assumption 12.2 condition package. -/
theorem twoSLSBetaOrZero_tendstoInDistribution_formula_of_assumption12_2_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSCombinedSampleMomentScoreCLTPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) := by
  have hstar_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ := by
    intro t
    simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using hmeas t
  have hstar :=
    twoSLSBetaStar_tendstoInDistribution_formula_of_assumption12_2_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h β hmodel hstar_meas
  simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using hstar

/-- Formula-facing coefficient CLT from the semidefinite-capable Gram/score
engine and the structural equation. -/
theorem twoSLSBetaStar_tendstoInDistribution_formula_of_gram_score_clt_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSGramScoreCLTConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :=
  twoSLSBetaStar_tendstoInDistribution_of_sample_moments_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toFormulaAsymptoticNormalConditions
    h.toTwoSLSGramInstrumentMomentRankConditions.toSampleMomentConvergenceConditions
    β hmodel hmeas

/-- Hansen Theorem 12.2 formula-facing endpoint from the primitive Assumption
12.2 Gram package and the structural equation. -/
theorem twoSLSBetaStar_tendstoInDistribution_formula_of_assumption12_2_gram_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :=
  twoSLSBetaStar_tendstoInDistribution_of_sample_moments_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toFormulaAsymptoticNormalConditions
    h.toTwoSLSGramInstrumentMomentRankConditions.toSampleMomentConvergenceConditions
    β hmodel hmeas

/-- Textbook-facing OrZero version of the Hansen Theorem 12.2 formula endpoint
from the primitive Assumption 12.2 Gram package. -/
theorem twoSLSBetaOrZero_tendstoInDistribution_formula_of_assumption12_2_gram_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSGramScoreCLTPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) := by
  have hstar_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ := by
    intro t
    simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using hmeas t
  have hstar :=
    twoSLSBetaStar_tendstoInDistribution_formula_of_assumption12_2_gram_model
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h β hmodel hstar_meas
  simpa [twoSLSBetaOrZero_eq_twoSLSBetaStar] using hstar

/-- Hansen Theorem 12.2 formula-facing endpoint from the iid finite-fourth
Assumption 12.2 package and the structural equation. -/
theorem twoSLSBetaStar_tendstoInDistribution_formula_of_assumption12_2_iid_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) := by
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  exact twoSLSBetaStar_tendstoInDistribution_formula_of_assumption12_2_gram_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toGramConditions β hmodel
    (fun t =>
      twoSLSBetaStar_scaled_centered_aemeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y)
        h.z_aestronglyMeasurable h.x_aestronglyMeasurable hY β)

/-- Textbook-facing OrZero version of Hansen Theorem 12.2 from the iid
finite-fourth Assumption 12.2 package. -/
theorem twoSLSBetaOrZero_tendstoInDistribution_formula_of_assumption12_2_iid_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) := by
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  exact twoSLSBetaOrZero_tendstoInDistribution_formula_of_assumption12_2_gram_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toGramConditions β hmodel
    (fun t =>
      twoSLSBetaOrZero_scaled_centered_aemeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y)
        h.z_aestronglyMeasurable h.x_aestronglyMeasurable hY β)

/-- Hansen Theorem 12.2 formula-facing endpoint from the single-row iid
finite-fourth Assumption 12.2 package and the structural equation. -/
theorem twoSLSBetaStar_tendstoInDistribution_formula_of_assumption12_2_joint_iid_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :=
  twoSLSBetaStar_tendstoInDistribution_formula_of_assumption12_2_iid_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toIidFourthConditions β hmodel

/-- Textbook-facing OrZero version of Hansen Theorem 12.2 from the single-row
iid finite-fourth Assumption 12.2 package. -/
theorem twoSLSBetaOrZero_tendstoInDistribution_formula_of_assumption12_2_joint_iid_model
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :=
  twoSLSBetaOrZero_tendstoInDistribution_formula_of_assumption12_2_iid_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toIidFourthConditions β hmodel

/-- Hansen Theorem 12.2 formula-facing structural endpoint.

Compared with `twoSLSBetaStar_tendstoInDistribution_of_model_nonsingular`, this
wrapper fixes the Gaussian covariance to Hansen's displayed 2SLS sandwich
formula. The primitive IV score CLT and high-probability nonsingularity
constructors remain outside this theorem. -/
theorem twoSLSBetaStar_tendstoInDistribution_formula_of_model_nonsingular
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSFormulaAsymptoticNormalConditions μ Z X e QXZ QZZ Omega QZX)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (twoSLSAsymptoticVariance QXZ QZZ Omega QZX)) :=
  twoSLSBetaStar_tendstoInDistribution_of_model_nonsingular
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel hunit hmeas

/-- Textbook-facing OrZero version of the Hansen Theorem 12.2
formula-facing structural endpoint. -/
theorem twoSLSBetaOrZero_tendstoInDistribution_formula_of_model_nonsingular
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSFormulaAsymptoticNormalConditions μ Z X e QXZ QZZ Omega QZX)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hunit : ∀ n ω, 0 < n →
      IsUnit
        (twoSLSMomentMatrixStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)).det)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (twoSLSAsymptoticVariance QXZ QZZ Omega QZX)) :=
  twoSLSBetaOrZero_tendstoInDistribution_of_model_nonsingular
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel hunit hmeas

set_option maxHeartbeats 1200000 in
-- The robust covariance CMT assembles five rectangular matrix products plus two inverses.
/-- Hansen Theorem 12.3 robust covariance assembly from middle-matrix consistency.

Once the sample IV moments converge and the feasible robust middle
`Ω̂ = n⁻¹∑ZᵢZᵢ'êᵢ²` converges to `Ω`, the 2SLS sandwich covariance estimator
converges to Hansen's displayed robust covariance formula. -/
theorem twoSLSVHatStar_tendstoInMeasure_formula_of_middle
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hOmega_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSOmegaHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω)) μ)
    (hOmega : TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω))
      atTop (fun _ => Omega)) :
    TendstoInMeasure μ
      (fun n ω =>
        twoSLSVHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω))
      atTop (fun _ => twoSLSAsymptoticVariance QXZ QZZ Omega QZX) := by
  let QXZhat : ℕ → Ω → Matrix k l ℝ := fun n ω =>
    sampleQXZ (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
  let QZZhat : ℕ → Ω → Matrix l l ℝ := fun n ω =>
    sampleQZZ (fun i : Fin n => Z i.val ω)
  let QZXhat : ℕ → Ω → Matrix l k ℝ := fun n ω =>
    sampleQZX (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
  let Omegahat : ℕ → Ω → Matrix l l ℝ := fun n ω =>
    twoSLSOmegaHatStar
      (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
      (fun i : Fin n => Y i.val ω)
  have hOmega_meas' : ∀ n, AEStronglyMeasurable (Omegahat n) μ := by
    intro n
    simpa [Omegahat] using hOmega_meas n
  have hOmega' : TendstoInMeasure μ Omegahat atTop (fun _ => Omega) := by
    simpa [Omegahat] using hOmega
  have hQZZinv_meas : ∀ n,
      AEStronglyMeasurable (fun ω => (QZZhat n ω)⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (h.qzz_meas n)
  have hQZZinv : TendstoInMeasure μ
      (fun n ω => (QZZhat n ω)⁻¹) atTop (fun _ => QZZ⁻¹) :=
    tendstoInMeasure_matrix_inv (μ := μ) h.qzz_meas h.qzz_tendsto
      (fun _ => h.qzz_nonsing)
  have hQXZ_QZZinv_meas : ∀ n,
      AEStronglyMeasurable (fun ω => QXZhat n ω * (QZZhat n ω)⁻¹) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((h.qxz_meas n).prodMk (hQZZinv_meas n))
  have hQXZ_QZZinv : TendstoInMeasure μ
      (fun n ω => QXZhat n ω * (QZZhat n ω)⁻¹)
      atTop (fun _ => QXZ * QZZ⁻¹) :=
    tendstoInMeasure_matrix_mul_rect h.qxz_meas hQZZinv_meas
      h.qxz_tendsto hQZZinv
  have hmiddleLeft_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => QXZhat n ω * (QZZhat n ω)⁻¹ * Omegahat n ω) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hQXZ_QZZinv_meas n).prodMk (hOmega_meas' n))
  have hmiddleLeft : TendstoInMeasure μ
      (fun n ω => QXZhat n ω * (QZZhat n ω)⁻¹ * Omegahat n ω)
      atTop (fun _ => (QXZ * QZZ⁻¹) * Omega) :=
    tendstoInMeasure_matrix_mul_rect hQXZ_QZZinv_meas
      hOmega_meas' hQXZ_QZZinv hOmega'
  have hmiddleLeftInv_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          (QXZhat n ω * (QZZhat n ω)⁻¹ * Omegahat n ω) *
            (QZZhat n ω)⁻¹) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hmiddleLeft_meas n).prodMk (hQZZinv_meas n))
  have hmiddleLeftInv : TendstoInMeasure μ
      (fun n ω =>
        (QXZhat n ω * (QZZhat n ω)⁻¹ * Omegahat n ω) *
          (QZZhat n ω)⁻¹)
      atTop (fun _ => ((QXZ * QZZ⁻¹) * Omega) * QZZ⁻¹) :=
    tendstoInMeasure_matrix_mul_rect hmiddleLeft_meas hQZZinv_meas
      hmiddleLeft hQZZinv
  have hmiddleFull_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          ((QXZhat n ω * (QZZhat n ω)⁻¹ * Omegahat n ω) *
            (QZZhat n ω)⁻¹) * QZXhat n ω) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hmiddleLeftInv_meas n).prodMk (h.qzx_meas n))
  have hmiddleFull : TendstoInMeasure μ
      (fun n ω =>
        ((QXZhat n ω * (QZZhat n ω)⁻¹ * Omegahat n ω) *
          (QZZhat n ω)⁻¹) * QZXhat n ω)
      atTop (fun _ => (((QXZ * QZZ⁻¹) * Omega) * QZZ⁻¹) * QZX) :=
    tendstoInMeasure_matrix_mul_rect hmiddleLeftInv_meas h.qzx_meas
      hmiddleLeftInv h.qzx_tendsto
  have hbread_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω)) μ := by
    intro n
    have hprod : AEStronglyMeasurable
        (fun ω => QXZhat n ω * (QZZhat n ω)⁻¹ * QZXhat n ω) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        ((hQXZ_QZZinv_meas n).prodMk (h.qzx_meas n))
    simpa [twoSLSBread, Matrix.mul_assoc] using hprod
  have hbread := twoSLSBread_tendstoInMeasure_of_sample_moments
    (μ := μ) (Z := Z) (X := X) (e := e)
    (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) h
  have hbreadInv_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (hbread_meas n)
  have hbreadInv : TendstoInMeasure μ
      (fun n ω => (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹)
      atTop (fun _ => (twoSLSBread QXZ QZZ QZX)⁻¹) :=
    tendstoInMeasure_matrix_inv (μ := μ) hbread_meas
      (by simpa [QXZhat, QZZhat, QZXhat] using hbread)
      (fun _ => h.bread_nonsing)
  have hleft_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹ *
            (((QXZhat n ω * (QZZhat n ω)⁻¹ * Omegahat n ω) *
              (QZZhat n ω)⁻¹) * QZXhat n ω)) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hbreadInv_meas n).prodMk (hmiddleFull_meas n))
  have hleft : TendstoInMeasure μ
      (fun n ω =>
        (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹ *
          (((QXZhat n ω * (QZZhat n ω)⁻¹ * Omegahat n ω) *
            (QZZhat n ω)⁻¹) * QZXhat n ω))
      atTop
        (fun _ =>
          (twoSLSBread QXZ QZZ QZX)⁻¹ *
            ((((QXZ * QZZ⁻¹) * Omega) * QZZ⁻¹) * QZX)) :=
    tendstoInMeasure_matrix_mul hbreadInv_meas hmiddleFull_meas
      hbreadInv hmiddleFull
  have hfull : TendstoInMeasure μ
      (fun n ω =>
        ((twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹ *
          (((QXZhat n ω * (QZZhat n ω)⁻¹ * Omegahat n ω) *
            (QZZhat n ω)⁻¹) * QZXhat n ω)) *
          (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹)
      atTop
        (fun _ =>
          ((twoSLSBread QXZ QZZ QZX)⁻¹ *
            ((((QXZ * QZZ⁻¹) * Omega) * QZZ⁻¹) * QZX)) *
            (twoSLSBread QXZ QZZ QZX)⁻¹) :=
    tendstoInMeasure_matrix_mul hleft_meas hbreadInv_meas hleft hbreadInv
  simpa [twoSLSVHatStar, twoSLSAsymptoticVariance, twoSLSBread,
    QXZhat, QZZhat, QZXhat, Omegahat, Matrix.mul_assoc] using hfull

set_option maxHeartbeats 800000 in
-- Scalar-matrix CMT for the homoskedastic 2SLS covariance formula.
/-- Hansen Theorem 12.3 homoskedastic covariance assembly from residual-variance consistency. -/
theorem twoSLSHomoskedasticVHatStar_tendstoInMeasure_formula_of_sigma
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ} {sigma2 : ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (hsigma_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω)) μ)
    (hsigma : TendstoInMeasure μ
      (fun n ω =>
        twoSLSSigmaSqHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω))
      atTop (fun _ => sigma2)) :
    TendstoInMeasure μ
      (fun n ω =>
        twoSLSHomoskedasticVHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω))
      atTop (fun _ => twoSLSHomoskedasticAsymptoticVariance QXZ QZZ QZX sigma2) := by
  let QXZhat : ℕ → Ω → Matrix k l ℝ := fun n ω =>
    sampleQXZ (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
  let QZZhat : ℕ → Ω → Matrix l l ℝ := fun n ω =>
    sampleQZZ (fun i : Fin n => Z i.val ω)
  let QZXhat : ℕ → Ω → Matrix l k ℝ := fun n ω =>
    sampleQZX (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
  let sigmaHat : ℕ → Ω → ℝ := fun n ω =>
    twoSLSSigmaSqHatStar
      (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
      (fun i : Fin n => Y i.val ω)
  have hsigma_meas' : ∀ n, AEStronglyMeasurable (sigmaHat n) μ := by
    intro n
    simpa [sigmaHat] using hsigma_meas n
  have hsigma' : TendstoInMeasure μ sigmaHat atTop (fun _ => sigma2) := by
    simpa [sigmaHat] using hsigma
  have hQZZinv_meas : ∀ n,
      AEStronglyMeasurable (fun ω => (QZZhat n ω)⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (h.qzz_meas n)
  have hQXZ_QZZinv_meas : ∀ n,
      AEStronglyMeasurable (fun ω => QXZhat n ω * (QZZhat n ω)⁻¹) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((h.qxz_meas n).prodMk (hQZZinv_meas n))
  have hbread_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω)) μ := by
    intro n
    have hprod : AEStronglyMeasurable
        (fun ω => QXZhat n ω * (QZZhat n ω)⁻¹ * QZXhat n ω) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        ((hQXZ_QZZinv_meas n).prodMk (h.qzx_meas n))
    simpa [twoSLSBread, Matrix.mul_assoc] using hprod
  have hbread := twoSLSBread_tendstoInMeasure_of_sample_moments
    (μ := μ) (Z := Z) (X := X) (e := e)
    (QXZ := QXZ) (QZZ := QZZ) (QZX := QZX) h
  have hbreadInv_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (hbread_meas n)
  have hbreadInv : TendstoInMeasure μ
      (fun n ω => (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹)
      atTop (fun _ => (twoSLSBread QXZ QZZ QZX)⁻¹) :=
    tendstoInMeasure_matrix_inv (μ := μ) hbread_meas
      (by simpa [QXZhat, QZZhat, QZXhat] using hbread)
      (fun _ => h.bread_nonsing)
  have hprod_meas : ∀ n, AEStronglyMeasurable
      (fun ω => (sigmaHat n ω,
        (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹)) μ := by
    intro n
    exact (hsigma_meas' n).prodMk (hbreadInv_meas n)
  have hcont : Continuous
      (fun p : ℝ × Matrix k k ℝ => p.1 • p.2) :=
    continuous_fst.smul continuous_snd
  have hprod : TendstoInMeasure μ
      (fun n ω => (sigmaHat n ω,
        (twoSLSBread (QXZhat n ω) (QZZhat n ω) (QZXhat n ω))⁻¹))
      atTop (fun _ => (sigma2, (twoSLSBread QXZ QZZ QZX)⁻¹)) :=
    tendstoInMeasure_prodMk hsigma' hbreadInv
  have hcov := tendstoInMeasure_continuous_comp hprod_meas hprod hcont
  simpa [twoSLSHomoskedasticVHatStar, twoSLSHomoskedasticAsymptoticVariance,
    QXZhat, QZZhat, QZXhat, sigmaHat] using hcov

omit [IsProbabilityMeasure μ] in
/-- Hansen Theorem 12.3 scalar residual-variance consistency from explicit
residual-substitution remainders.

If the true-error second moment converges to `σ²` and the two scalar
coefficient-error remainders in
`twoSLSSigmaSqHatStar_linear_model_expansion` are `oₚ(1)`, then Hansen's
structural 2SLS residual variance estimator converges to `σ²`. -/
theorem twoSLSSigmaSqHatStar_tendstoInMeasure_of_linear_model_remainders
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {sigma2 : ℝ} (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (herr : TendstoInMeasure μ
      (fun n ω => sampleErrorSecondMoment (fun i : Fin n => e i.val ω))
      atTop (fun _ => sigma2))
    (hcross : TendstoInMeasure μ
      (fun n ω =>
        -2 * (sampleCrossMoment (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω) ⬝ᵥ
            (twoSLSBetaStar
              (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω) - β)))
      atTop (fun _ => 0))
    (hquad : TendstoInMeasure μ
      (fun n ω =>
        (twoSLSBetaStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω) - β) ⬝ᵥ
          (sampleGram (fun i : Fin n => X i.val ω) *ᵥ
            (twoSLSBetaStar
              (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω) - β)))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        twoSLSSigmaSqHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω))
      atTop (fun _ => sigma2) := by
  have herr0 := TendstoInMeasure.sub_limit_zero_real herr
  have hsum :=
    TendstoInMeasure.add_zero_real
      (TendstoInMeasure.add_zero_real herr0 hcross) hquad
  have hcenter : TendstoInMeasure μ
      (fun n ω =>
        twoSLSSigmaSqHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω) - sigma2)
      atTop (fun _ => 0) := by
    refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
    have hY : (fun i : Fin n => Y i.val ω) =
        (fun i : Fin n => X i.val ω) *ᵥ β +
          (fun i : Fin n => e i.val ω) := by
      ext i
      simp [Matrix.mulVec, dotProduct, hmodel]
    dsimp
    rw [hY, twoSLSSigmaSqHatStar_linear_model_expansion]
    ring
  exact TendstoInMeasure.of_sub_limit_zero_real hcenter

omit [IsProbabilityMeasure μ] in
/-- Hansen Theorem 12.3 robust middle consistency from explicit
residual-substitution remainders.

If the ideal true-error middle converges to `Ω` and the cross and quadratic
matrix remainders in `twoSLSOmegaHatStar_linear_model_expansion` are `oₚ(1)`,
then the feasible robust 2SLS middle `Ω̂` converges to `Ω`. -/
theorem twoSLSOmegaHatStar_tendstoInMeasure_of_linear_model_remainders
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {Omega : Matrix l l ℝ} (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hIdeal : TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaIdeal
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => e i.val ω))
      atTop (fun _ => Omega))
    (hCross : TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaCrossRemainder
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω)
          (twoSLSBetaStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω) - β))
      atTop (fun _ => 0))
    (hQuad : TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaQuadraticRemainder
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (twoSLSBetaStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω) - β))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω))
      atTop (fun _ => Omega) := by
  let ideal : ℕ → Ω → Matrix l l ℝ := fun n ω =>
    twoSLSOmegaIdeal
      (fun i : Fin n => Z i.val ω) (fun i : Fin n => e i.val ω)
  let cross : ℕ → Ω → Matrix l l ℝ := fun n ω =>
    twoSLSOmegaCrossRemainder
      (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
      (fun i : Fin n => e i.val ω)
      (twoSLSBetaStar
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
        (fun i : Fin n => Y i.val ω) - β)
  let quad : ℕ → Ω → Matrix l l ℝ := fun n ω =>
    twoSLSOmegaQuadraticRemainder
      (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
      (twoSLSBetaStar
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
        (fun i : Fin n => Y i.val ω) - β)
  refine tendstoInMeasure_pi (μ := μ) (fun a => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun b => ?_)
  have hIdeal_ab : TendstoInMeasure μ
      (fun n ω => ideal n ω a b) atTop (fun _ => Omega a b) := by
    simpa [ideal] using TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hIdeal a) b
  have hCross_ab : TendstoInMeasure μ
      (fun n ω => cross n ω a b) atTop (fun _ => 0) := by
    simpa [cross] using TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hCross a) b
  have hQuad_ab : TendstoInMeasure μ
      (fun n ω => quad n ω a b) atTop (fun _ => 0) := by
    simpa [quad] using TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hQuad a) b
  have hCentered := TendstoInMeasure.sub_limit_zero_real hIdeal_ab
  have hCross2 := TendstoInMeasure.const_mul_zero_real (μ := μ) (2 : ℝ) hCross_ab
  have hSub := TendstoInMeasure.sub_zero_real hCentered hCross2
  have hAdd := TendstoInMeasure.add_zero_real hSub hQuad_ab
  refine TendstoInMeasure.of_sub_limit_zero_real ?_
  refine hAdd.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  have hY : (fun i : Fin n => Y i.val ω) =
      (fun i : Fin n => X i.val ω) *ᵥ β +
        (fun i : Fin n => e i.val ω) := by
    ext i
    simp [Matrix.mulVec, dotProduct, hmodel]
  have hOmega :
      twoSLSOmegaHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω) =
        ideal n ω - (2 : ℝ) • cross n ω + quad n ω := by
    dsimp [ideal, cross, quad]
    rw [hY, twoSLSOmegaHatStar_linear_model_expansion]
  calc
    ((ideal n ω a b - Omega a b) - 2 * cross n ω a b) + quad n ω a b =
        (ideal n ω - (2 : ℝ) • cross n ω + quad n ω) a b - Omega a b := by
          simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
          ring
    _ =
        twoSLSOmegaHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω) a b - Omega a b := by
          rw [← hOmega]

/-- Middle-moment condition package for Hansen Theorem 12.3.

This sits between primitive Assumption 12.2 and the final covariance theorem:
it assumes sample IV moment convergence plus consistency of the feasible robust
middle and residual variance, and the converter below performs only the
matrix continuous-mapping assembly. -/
structure TwoSLSCovarianceMomentConsistencyConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e Y : ℕ → Ω → ℝ)
    (QXZ : Matrix k l ℝ) (QZZ Omega : Matrix l l ℝ)
    (QZX : Matrix l k ℝ) (sigma2 : ℝ) : Prop where
  sample_moments : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX
  omega_meas : ∀ n : ℕ, AEStronglyMeasurable
    (fun ω =>
      twoSLSOmegaHatStar
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
        (fun i : Fin n => Y i.val ω)) μ
  omega_tendsto : TendstoInMeasure μ
    (fun n ω =>
      twoSLSOmegaHatStar
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
        (fun i : Fin n => Y i.val ω))
    atTop (fun _ => Omega)
  sigma_meas : ∀ n : ℕ, AEStronglyMeasurable
    (fun ω =>
      twoSLSSigmaSqHatStar
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
        (fun i : Fin n => Y i.val ω)) μ
  sigma_tendsto : TendstoInMeasure μ
    (fun n ω =>
      twoSLSSigmaSqHatStar
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
        (fun i : Fin n => Y i.val ω))
    atTop (fun _ => sigma2)

/-- Proof-facing condition package for Hansen Theorem 12.3.

The two covariance conclusions are deliberately separate fields: Hansen states
consistency of both the robust covariance estimator and the homoskedastic
covariance estimator. Both are built from the structural residual
`Y_i - X_i'β̂₂ₛₗₛ`, via `twoSLSVHatStar` and `twoSLSHomoskedasticVHatStar`. -/
structure TwoSLSCovarianceConsistencyConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (Vβ Vβ0 : Matrix k k ℝ) : Prop where
  robust_tendsto : TendstoInMeasure μ
    (fun n ω =>
      twoSLSVHatStar
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
        (fun i : Fin n => Y i.val ω))
    atTop (fun _ => Vβ)
  homoskedastic_tendsto : TendstoInMeasure μ
    (fun n ω =>
      twoSLSHomoskedasticVHatStar
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
        (fun i : Fin n => Y i.val ω))
    atTop (fun _ => Vβ0)

/-- Hansen Theorem 12.3 interface: both 2SLS covariance estimators are
consistent. The robust and homoskedastic conclusions are returned together so a
chapter-facing crosswalk cannot silently drop one half of Hansen's statement. -/
theorem twoSLSCovariances_tendstoInMeasure
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {Vβ Vβ0 : Matrix k k ℝ}
    (h : TwoSLSCovarianceConsistencyConditions μ Z X Y Vβ Vβ0) :
    TendstoInMeasure μ
        (fun n ω =>
          twoSLSVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop (fun _ => Vβ) ∧
      TendstoInMeasure μ
        (fun n ω =>
          twoSLSHomoskedasticVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop (fun _ => Vβ0) :=
  ⟨h.robust_tendsto, h.homoskedastic_tendsto⟩

/-- Hansen-formula condition package for Theorem 12.3.

Unlike the generic `TwoSLSCovarianceConsistencyConditions`, this package fixes
the two covariance limits to Hansen's displayed robust and homoskedastic
2SLS covariance formulas. The remaining proof obligation is still the
residual-substitution and WLLN argument that derives these fields from
primitive Assumption 12.2. -/
structure TwoSLSCovarianceFormulaConsistencyConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (QXZ : Matrix k l ℝ) (QZZ Omega : Matrix l l ℝ)
    (QZX : Matrix l k ℝ) (sigma2 : ℝ) : Prop where
  robust_tendsto : TendstoInMeasure μ
    (fun n ω =>
      twoSLSVHatStar
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
        (fun i : Fin n => Y i.val ω))
    atTop (fun _ => twoSLSAsymptoticVariance QXZ QZZ Omega QZX)
  homoskedastic_tendsto : TendstoInMeasure μ
    (fun n ω =>
      twoSLSHomoskedasticVHatStar
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
        (fun i : Fin n => Y i.val ω))
    atTop (fun _ => twoSLSHomoskedasticAsymptoticVariance QXZ QZZ QZX sigma2)

/-- Exact residual-substitution remainder package for Hansen Theorem 12.3.

The ideal true-error robust middle and scalar variance WLLNs are derived from
Assumption 12.2 by the constructor below. These four fields isolate the
remaining probabilistic work: show that substituting structural 2SLS residuals
for true errors has no first-order effect in the robust and homoskedastic
middle matrices. -/
structure TwoSLSCovarianceRemainderConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e Y : ℕ → Ω → ℝ)
    (β : k → ℝ) : Prop where
  omega_cross_tendsto : TendstoInMeasure μ
    (fun n ω =>
      twoSLSOmegaCrossRemainder
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
        (fun i : Fin n => e i.val ω)
        (twoSLSBetaStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω) - β))
    atTop (fun _ => 0)
  omega_quadratic_tendsto : TendstoInMeasure μ
    (fun n ω =>
      twoSLSOmegaQuadraticRemainder
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
        (twoSLSBetaStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω) - β))
    atTop (fun _ => 0)
  sigma_cross_tendsto : TendstoInMeasure μ
    (fun n ω =>
      -2 * (sampleCrossMoment (fun i : Fin n => X i.val ω)
        (fun i : Fin n => e i.val ω) ⬝ᵥ
          (twoSLSBetaStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω) - β)))
    atTop (fun _ => 0)
  sigma_quadratic_tendsto : TendstoInMeasure μ
    (fun n ω =>
      (twoSLSBetaStar
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
        (fun i : Fin n => Y i.val ω) - β) ⬝ᵥ
        (sampleGram (fun i : Fin n => X i.val ω) *ᵥ
          (twoSLSBetaStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω) - β)))
    atTop (fun _ => 0)

omit [IsProbabilityMeasure μ] in
/-- Empirical third-moment weight multiplying one coordinate of
`β̂₂sls - β` in the robust IV middle cross remainder. -/
noncomputable def twoSLSOmegaCrossWeight
    {n : Type*} [Fintype n]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (e : n → ℝ)
    (a b : l) (j : k) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * ∑ i : n, e i * X i j * Z i a * Z i b

omit [IsProbabilityMeasure μ] in
/-- Empirical fourth-moment weight multiplying two coordinates of
`β̂₂sls - β` in the robust IV middle quadratic remainder. -/
noncomputable def twoSLSOmegaQuadraticWeight
    {n : Type*} [Fintype n]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ)
    (a b : l) (j m : k) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * ∑ i : n, X i j * X i m * Z i a * Z i b

set_option linter.flexible false in
omit [Fintype l] [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
/-- Coordinate representation of the robust IV middle cross remainder. -/
theorem twoSLSOmegaCrossRemainder_apply_eq_sum_weight
    {n : Type*} [Fintype n]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (e : n → ℝ)
    (d : k → ℝ) (a b : l) :
    twoSLSOmegaCrossRemainder Z X e d a b =
      ∑ j : k, d j * twoSLSOmegaCrossWeight Z X e a b j := by
  classical
  unfold twoSLSOmegaCrossRemainder twoSLSOmegaCrossWeight
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, dotProduct,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [Finset.sum_comm]

set_option linter.flexible false in
omit [Fintype l] [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
/-- Coordinate representation of the robust IV middle quadratic remainder. -/
theorem twoSLSOmegaQuadraticRemainder_apply_eq_sum_weight
    {n : Type*} [Fintype n]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (d : k → ℝ) (a b : l) :
    twoSLSOmegaQuadraticRemainder Z X d a b =
      ∑ j : k, ∑ m : k,
        d j * d m * twoSLSOmegaQuadraticWeight Z X a b j m := by
  classical
  unfold twoSLSOmegaQuadraticRemainder twoSLSOmegaQuadraticWeight
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, dotProduct,
    Finset.mul_sum, pow_two, mul_assoc, mul_left_comm, mul_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

/-- Bounded empirical-weight sufficient conditions for the exact
residual-substitution remainders in Hansen Theorem 12.3. -/
structure TwoSLSCovarianceRemainderBoundedWeightConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    : Prop where
  omega_cross_weight_bounded : ∀ a b : l, ∀ j : k,
    BoundedInProbability μ
      (fun n ω =>
        twoSLSOmegaCrossWeight
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω) a b j)
  omega_quadratic_weight_bounded : ∀ a b : l, ∀ j m : k,
    BoundedInProbability μ
      (fun n ω =>
        twoSLSOmegaQuadraticWeight
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω) a b j m)
  sigma_cross_bounded : ∀ j : k,
    BoundedInProbability μ
      (fun n ω =>
        sampleCrossMoment (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω) j)
  sigma_gram_bounded : ∀ j m : k,
    BoundedInProbability μ
      (fun n ω => sampleGram (fun i : Fin n => X i.val ω) j m)

/-- Scalar WLLN sufficient conditions for the empirical weights appearing in
Hansen Theorem 12.3's residual-substitution remainders.

Assumption 12.2 supplies the ideal `Z_i e_i` score covariance WLLN and the
combined `[Z_i, X_i]` Gram WLLN.  The feasible residual substitution also needs
empirical averages of `e_i X_{ij} Z_{ia} Z_{ib}`, `X_{ij} X_{im} Z_{ia} Z_{ib}`,
and `e_i X_{ij}`. This package records exactly those scalar summands so the
bounded-weight constructor below is enforceable and does not assume the final
remainder conclusion. -/
structure TwoSLSCovarianceWeightWLLNConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    : Prop where
  /-- Integrability of the robust-middle cross-weight summands. -/
  omega_cross_integrable : ∀ a b : l, ∀ j : k,
    Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ
  /-- Pairwise independence of the robust-middle cross-weight summands. -/
  omega_cross_pairwise_indep : ∀ a b : l, ∀ j : k,
    Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => e i ω * X i ω j * Z i ω a * Z i ω b))
  /-- Identical distribution of the robust-middle cross-weight summands. -/
  omega_cross_identDistrib : ∀ a b : l, ∀ j : k, ∀ i,
    IdentDistrib
      (fun ω => e i ω * X i ω j * Z i ω a * Z i ω b)
      (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ μ
  /-- Integrability of the robust-middle quadratic-weight summands. -/
  omega_quadratic_integrable : ∀ a b : l, ∀ j m : k,
    Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ
  /-- Pairwise independence of the robust-middle quadratic-weight summands. -/
  omega_quadratic_pairwise_indep : ∀ a b : l, ∀ j m : k,
    Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => X i ω j * X i ω m * Z i ω a * Z i ω b))
  /-- Identical distribution of the robust-middle quadratic-weight summands. -/
  omega_quadratic_identDistrib : ∀ a b : l, ∀ j m : k, ∀ i,
    IdentDistrib
      (fun ω => X i ω j * X i ω m * Z i ω a * Z i ω b)
      (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ μ
  /-- Integrability of the homoskedastic scalar cross-moment summands. -/
  sigma_cross_integrable : ∀ j : k,
    Integrable (fun ω => e 0 ω * X 0 ω j) μ
  /-- Pairwise independence of the homoskedastic scalar cross-moment summands. -/
  sigma_cross_pairwise_indep : ∀ j : k,
    Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω * X i ω j))
  /-- Identical distribution of the homoskedastic scalar cross-moment summands. -/
  sigma_cross_identDistrib : ∀ j : k, ∀ i,
    IdentDistrib
      (fun ω => e i ω * X i ω j)
      (fun ω => e 0 ω * X 0 ω j) μ μ

namespace TwoSLSCovarianceWeightWLLNConditions

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
private lemma measurable_joint_row_Z (a : l) :
    Measurable (fun row : ((l → ℝ) × (k → ℝ)) × ℝ => row.1.1 a) :=
  (measurable_pi_apply a).comp (measurable_fst.comp measurable_fst)

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
private lemma measurable_joint_row_X (j : k) :
    Measurable (fun row : ((l → ℝ) × (k → ℝ)) × ℝ => row.1.2 j) :=
  (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
private lemma measurable_joint_row_e :
    Measurable (fun row : ((l → ℝ) × (k → ℝ)) × ℝ => row.2) :=
  measurable_snd

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
private lemma measurable_joint_omega_cross_weight (a b : l) (j : k) :
    Measurable (fun row : ((l → ℝ) × (k → ℝ)) × ℝ =>
      row.2 * row.1.2 j * row.1.1 a * row.1.1 b) :=
  (((measurable_joint_row_e (l := l) (k := k)).mul
    (measurable_joint_row_X (l := l) (k := k) j)).mul
    (measurable_joint_row_Z (l := l) (k := k) a)).mul
    (measurable_joint_row_Z (l := l) (k := k) b)

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
private lemma measurable_joint_omega_quadratic_weight (a b : l) (j m : k) :
    Measurable (fun row : ((l → ℝ) × (k → ℝ)) × ℝ =>
      row.1.2 j * row.1.2 m * row.1.1 a * row.1.1 b) :=
  (((measurable_joint_row_X (l := l) (k := k) j).mul
    (measurable_joint_row_X (l := l) (k := k) m)).mul
    (measurable_joint_row_Z (l := l) (k := k) a)).mul
    (measurable_joint_row_Z (l := l) (k := k) b)

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] [IsProbabilityMeasure μ] in
private lemma measurable_joint_sigma_cross_weight (j : k) :
    Measurable (fun row : ((l → ℝ) × (k → ℝ)) × ℝ =>
      row.2 * row.1.2 j) :=
  (measurable_joint_row_e (l := l) (k := k)).mul
    (measurable_joint_row_X (l := l) (k := k) j)

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] in
/-- Joint iid observations imply the scalar WLLN package for Hansen Theorem 12.3
residual-substitution weights.

The only remaining analytic premises are integrability of Hansen's displayed
mixed third/fourth moment summands. Independence and identical distribution of
the coordinate products are derived by measurable composition from iid
`((Z_i, X_i), e_i)` rows. -/
theorem of_joint_iid
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (hjoint : iIndepFun (fun i ω => ((Z i ω, X i ω), e i ω)) μ)
    (hident : ∀ i,
      IdentDistrib
        (fun ω => ((Z i ω, X i ω), e i ω))
        (fun ω => ((Z 0 ω, X 0 ω), e 0 ω)) μ μ)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ) :
    TwoSLSCovarianceWeightWLLNConditions μ Z X e where
  omega_cross_integrable := hOmegaCross
  omega_cross_pairwise_indep := by
    intro a b j
    have hind : iIndepFun
        (fun i ω => e i ω * X i ω j * Z i ω a * Z i ω b) μ := by
      simpa [Function.comp_def] using
        hjoint.comp
          (fun _ => fun row : ((l → ℝ) × (k → ℝ)) × ℝ =>
            row.2 * row.1.2 j * row.1.1 a * row.1.1 b)
          (fun _ => measurable_joint_omega_cross_weight (l := l) (k := k) a b j)
    exact fun i j hij => hind.indepFun hij
  omega_cross_identDistrib := by
    intro a b j i
    have hi := (hident i).comp
      (measurable_joint_omega_cross_weight (l := l) (k := k) a b j)
    simpa [Function.comp_def] using hi
  omega_quadratic_integrable := hOmegaQuadratic
  omega_quadratic_pairwise_indep := by
    intro a b j m
    have hind : iIndepFun
        (fun i ω => X i ω j * X i ω m * Z i ω a * Z i ω b) μ := by
      simpa [Function.comp_def] using
        hjoint.comp
          (fun _ => fun row : ((l → ℝ) × (k → ℝ)) × ℝ =>
            row.1.2 j * row.1.2 m * row.1.1 a * row.1.1 b)
          (fun _ => measurable_joint_omega_quadratic_weight (l := l) (k := k) a b j m)
    exact fun i j hij => hind.indepFun hij
  omega_quadratic_identDistrib := by
    intro a b j m i
    have hi := (hident i).comp
      (measurable_joint_omega_quadratic_weight (l := l) (k := k) a b j m)
    simpa [Function.comp_def] using hi
  sigma_cross_integrable := hSigmaCross
  sigma_cross_pairwise_indep := by
    intro j
    have hind : iIndepFun (fun i ω => e i ω * X i ω j) μ := by
      simpa [Function.comp_def] using
        hjoint.comp
          (fun _ => fun row : ((l → ℝ) × (k → ℝ)) × ℝ => row.2 * row.1.2 j)
          (fun _ => measurable_joint_sigma_cross_weight (l := l) (k := k) j)
    exact fun i j hij => hind.indepFun hij
  sigma_cross_identDistrib := by
    intro j i
    have hi := (hident i).comp
      (measurable_joint_sigma_cross_weight (l := l) (k := k) j)
    simpa [Function.comp_def] using hi

end TwoSLSCovarianceWeightWLLNConditions

namespace TwoSLSCovarianceRemainderBoundedWeightConditions

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] in
/-- Empirical robust-middle cross weights are bounded in probability when the
corresponding scalar summands satisfy the WLLN primitive hypotheses. -/
theorem omegaCrossWeight_bounded_of_wlln
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (a b : l) (j : k)
    (hint : Integrable
      (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => e i ω * X i ω j * Z i ω a * Z i ω b)))
    (hident : ∀ i,
      IdentDistrib
        (fun ω => e i ω * X i ω j * Z i ω a * Z i ω b)
        (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ μ) :
    BoundedInProbability μ
      (fun n ω =>
        twoSLSOmegaCrossWeight
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω) a b j) := by
  let W : ℕ → Ω → ℝ := fun i ω =>
    e i ω * X i ω j * Z i ω a * Z i ω b
  have hWLLN : TendstoInMeasure μ
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, W i ω)
      atTop (fun _ => μ[W 0]) :=
    tendstoInMeasure_wlln W hint hindep hident
  have hWeight : TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaCrossWeight
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω) a b j)
      atTop (fun _ => μ[W 0]) := by
    refine hWLLN.congr_left (fun n => ae_of_all μ (fun ω => ?_))
    have hsum :
        (∑ i : Fin n, e i.val ω * X i.val ω j * Z i.val ω a * Z i.val ω b) =
          ∑ i ∈ Finset.range n, e i ω * X i ω j * Z i ω a * Z i ω b :=
      Fin.sum_univ_eq_sum_range
        (fun i => e i ω * X i ω j * Z i ω a * Z i ω b) n
    simp [twoSLSOmegaCrossWeight, W, Fintype.card_fin, hsum, smul_eq_mul]
  exact BoundedInProbability.of_tendstoInMeasure_const hWeight

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] in
/-- Empirical robust-middle quadratic weights are bounded in probability when
the corresponding scalar summands satisfy the WLLN primitive hypotheses. -/
theorem omegaQuadraticWeight_bounded_of_wlln
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    (a b : l) (j m : k)
    (hint : Integrable
      (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => X i ω j * X i ω m * Z i ω a * Z i ω b)))
    (hident : ∀ i,
      IdentDistrib
        (fun ω => X i ω j * X i ω m * Z i ω a * Z i ω b)
        (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ μ) :
    BoundedInProbability μ
      (fun n ω =>
        twoSLSOmegaQuadraticWeight
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω) a b j m) := by
  let W : ℕ → Ω → ℝ := fun i ω =>
    X i ω j * X i ω m * Z i ω a * Z i ω b
  have hWLLN : TendstoInMeasure μ
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, W i ω)
      atTop (fun _ => μ[W 0]) :=
    tendstoInMeasure_wlln W hint hindep hident
  have hWeight : TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaQuadraticWeight
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω) a b j m)
      atTop (fun _ => μ[W 0]) := by
    refine hWLLN.congr_left (fun n => ae_of_all μ (fun ω => ?_))
    have hsum :
        (∑ i : Fin n, X i.val ω j * X i.val ω m * Z i.val ω a * Z i.val ω b) =
          ∑ i ∈ Finset.range n, X i ω j * X i ω m * Z i ω a * Z i ω b :=
      Fin.sum_univ_eq_sum_range
        (fun i => X i ω j * X i ω m * Z i ω a * Z i ω b) n
    simp [twoSLSOmegaQuadraticWeight, W, Fintype.card_fin, hsum, smul_eq_mul]
  exact BoundedInProbability.of_tendstoInMeasure_const hWeight

omit [Fintype k] [DecidableEq k] in
/-- The sample `X'e/n` coordinates are bounded in probability when the scalar
summands satisfy the WLLN primitive hypotheses. -/
theorem sigmaCross_bounded_of_wlln
    {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (j : k)
    (hint : Integrable (fun ω => e 0 ω * X 0 ω j) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω * X i ω j)))
    (hident : ∀ i,
      IdentDistrib
        (fun ω => e i ω * X i ω j)
        (fun ω => e 0 ω * X 0 ω j) μ μ) :
    BoundedInProbability μ
      (fun n ω =>
        sampleCrossMoment (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω) j) := by
  let W : ℕ → Ω → ℝ := fun i ω => e i ω * X i ω j
  have hWLLN : TendstoInMeasure μ
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, W i ω)
      atTop (fun _ => μ[W 0]) :=
    tendstoInMeasure_wlln W hint hindep hident
  have hWeight : TendstoInMeasure μ
      (fun n ω =>
        sampleCrossMoment (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω) j)
      atTop (fun _ => μ[W 0]) := by
    refine hWLLN.congr_left (fun n => ae_of_all μ (fun ω => ?_))
    have havg :
        sampleCrossMoment (fun i : Fin n => X i.val ω)
            (fun i : Fin n => e i.val ω) j =
          ((n : ℝ)⁻¹ • ∑ i : Fin n, e i.val ω • X i.val ω) j := by
      simpa [stackRegressors, stackErrors] using
        congrArg (fun v => v j)
          (sampleCrossMoment_stackRegressors_stackErrors_eq_avg X e n ω)
    have hsum :
        (∑ i : Fin n, e i.val ω * X i.val ω j) =
          ∑ i ∈ Finset.range n, e i ω * X i ω j :=
      Fin.sum_univ_eq_sum_range (fun i => e i ω * X i ω j) n
    calc
      (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, W i ω =
          (n : ℝ)⁻¹ * ∑ i : Fin n, e i.val ω * X i.val ω j := by
          change (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, e i ω * X i ω j) =
            (n : ℝ)⁻¹ * ∑ i : Fin n, e i.val ω * X i.val ω j
          exact congrArg (fun s => (n : ℝ)⁻¹ * s) hsum.symm
      _ = ((n : ℝ)⁻¹ • ∑ i : Fin n, e i.val ω • X i.val ω) j := by
          simp only [Pi.smul_apply]
          congr 1
          simp [Finset.sum_apply, smul_eq_mul]
      _ = sampleCrossMoment (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω) j := havg.symm
  exact BoundedInProbability.of_tendstoInMeasure_const hWeight

/-- The sample `X'X/n` coordinates are bounded in probability as right-right
blocks of the combined `[Z X]` sample-Gram WLLN. -/
theorem sigmaGram_bounded_of_combined_sampleGram
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {Q : Matrix (l ⊕ k) (l ⊕ k) ℝ}
    (h : TwoSLSCombinedSampleMomentConvergenceConditions μ Z X e Q)
    (j m : k) :
    BoundedInProbability μ
      (fun n ω => sampleGram (fun i : Fin n => X i.val ω) j m) := by
  have hGram :=
    sampleGramX_tendstoInMeasure_of_combined_sampleGram
      (μ := μ) (Z := Z) (X := X) h.combined_meas h.combined_tendsto
  exact BoundedInProbability.of_tendstoInMeasure_const
    (TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hGram j) m)

/-- Build the bounded empirical-weight package from scalar WLLNs for the
third/fourth residual-substitution weights plus the existing combined sample
Gram WLLN for `X'X/n`. -/
theorem of_weight_wlln_combined_sampleGram
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {Q : Matrix (l ⊕ k) (l ⊕ k) ℝ}
    (hCombined : TwoSLSCombinedSampleMomentConvergenceConditions μ Z X e Q)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e) :
    TwoSLSCovarianceRemainderBoundedWeightConditions μ Z X e where
  omega_cross_weight_bounded := fun a b j =>
    omegaCrossWeight_bounded_of_wlln (μ := μ) (Z := Z) (X := X) (e := e) a b j
      (hw.omega_cross_integrable a b j)
      (hw.omega_cross_pairwise_indep a b j)
      (hw.omega_cross_identDistrib a b j)
  omega_quadratic_weight_bounded := fun a b j m =>
    omegaQuadraticWeight_bounded_of_wlln (μ := μ) (Z := Z) (X := X) a b j m
      (hw.omega_quadratic_integrable a b j m)
      (hw.omega_quadratic_pairwise_indep a b j m)
      (hw.omega_quadratic_identDistrib a b j m)
  sigma_cross_bounded := fun j =>
    sigmaCross_bounded_of_wlln (μ := μ) (X := X) (e := e) j
      (hw.sigma_cross_integrable j)
      (hw.sigma_cross_pairwise_indep j)
      (hw.sigma_cross_identDistrib j)
  sigma_gram_bounded :=
    sigmaGram_bounded_of_combined_sampleGram (μ := μ) (Z := Z) (X := X) (e := e) hCombined

omit [DecidableEq k] [DecidableEq l] in
/-- Hansen Assumption 12.2 supplies the ideal score/sigma WLLNs and the
combined sample Gram. The extra scalar-weight WLLN package supplies the
third/fourth empirical weights needed to make the feasible residual
substitution negligible. -/
theorem of_assumption12_2_iid_weight_wlln
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e) :
    TwoSLSCovarianceRemainderBoundedWeightConditions μ Z X e := by
  classical
  exact of_weight_wlln_combined_sampleGram
    (μ := μ) (Z := Z) (X := X) (e := e)
    h.toGramConditions.toCombinedSampleMomentConvergenceConditions hw

end TwoSLSCovarianceRemainderBoundedWeightConditions

namespace TwoSLSCovarianceRemainderConditions

/-- Robust IV middle cross remainder from bounded empirical third-moment
weights and 2SLS coefficient consistency. -/
theorem omegaCross_tendstoInMeasure_zero_of_bounded_weights
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hweights : TwoSLSCovarianceRemainderBoundedWeightConditions μ Z X e) :
    TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaCrossRemainder
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω)
          (twoSLSBetaStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω) - β))
      atTop (fun _ => 0) := by
  have hBeta := twoSLSBetaStar_tendstoInMeasure_beta_of_sample_moments_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel
  refine tendstoInMeasure_pi (μ := μ) (fun a => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun b => ?_)
  have hTerm : ∀ j ∈ (Finset.univ : Finset k),
      TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBetaStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω) - β) j *
          twoSLSOmegaCrossWeight
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => e i.val ω) a b j)
        atTop (fun _ => 0) := by
    intro j _
    have hj := TendstoInMeasure.pi_apply hBeta j
    have hdj : TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBetaStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω) - β) j)
        atTop (fun _ => 0) := by
      simpa [Pi.sub_apply] using TendstoInMeasure.sub_limit_zero_real hj
    exact TendstoInMeasure.mul_boundedInProbability hdj
      (hweights.omega_cross_weight_bounded a b j)
  have hsum := tendstoInMeasure_finset_sum_zero_real (μ := μ)
    (s := (Finset.univ : Finset k))
    (X := fun j n ω =>
      (twoSLSBetaStar
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
        (fun i : Fin n => Y i.val ω) - β) j *
      twoSLSOmegaCrossWeight
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
        (fun i : Fin n => e i.val ω) a b j)
    hTerm
  refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  exact (twoSLSOmegaCrossRemainder_apply_eq_sum_weight
    (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
    (fun i : Fin n => e i.val ω)
    (twoSLSBetaStar
      (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
      (fun i : Fin n => Y i.val ω) - β) a b).symm

/-- Robust IV middle quadratic remainder from bounded empirical fourth-moment
weights and 2SLS coefficient consistency. -/
theorem omegaQuadratic_tendstoInMeasure_zero_of_bounded_weights
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hweights : TwoSLSCovarianceRemainderBoundedWeightConditions μ Z X e) :
    TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaQuadraticRemainder
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (twoSLSBetaStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω) - β))
      atTop (fun _ => 0) := by
  have hBeta := twoSLSBetaStar_tendstoInMeasure_beta_of_sample_moments_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel
  let d : ℕ → Ω → k → ℝ := fun n ω =>
    twoSLSBetaStar
      (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
      (fun i : Fin n => Y i.val ω) - β
  have hd : ∀ j : k, TendstoInMeasure μ (fun n ω => d n ω j) atTop (fun _ => 0) := by
    intro j
    have hj := TendstoInMeasure.pi_apply hBeta j
    simpa [d, Pi.sub_apply] using TendstoInMeasure.sub_limit_zero_real hj
  refine tendstoInMeasure_pi (μ := μ) (fun a => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun b => ?_)
  have hInner : ∀ j ∈ (Finset.univ : Finset k),
      TendstoInMeasure μ
        (fun n ω => ∑ m : k,
          d n ω j * d n ω m *
            twoSLSOmegaQuadraticWeight
              (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω) a b j m)
        atTop (fun _ => 0) := by
    intro j _
    have hTerm : ∀ m ∈ (Finset.univ : Finset k),
        TendstoInMeasure μ
          (fun n ω =>
            d n ω j * d n ω m *
              twoSLSOmegaQuadraticWeight
                (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω) a b j m)
          atTop (fun _ => 0) := by
      intro m _
      have hprod := TendstoInMeasure.mul_zero_real (hd j) (hd m)
      exact TendstoInMeasure.mul_boundedInProbability hprod
        (hweights.omega_quadratic_weight_bounded a b j m)
    simpa using tendstoInMeasure_finset_sum_zero_real (μ := μ)
      (s := (Finset.univ : Finset k))
      (X := fun m n ω =>
        d n ω j * d n ω m *
          twoSLSOmegaQuadraticWeight
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω) a b j m)
      hTerm
  have hsum := tendstoInMeasure_finset_sum_zero_real (μ := μ)
    (s := (Finset.univ : Finset k))
    (X := fun j n ω => ∑ m : k,
      d n ω j * d n ω m *
        twoSLSOmegaQuadraticWeight
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω) a b j m)
    hInner
  refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  exact (twoSLSOmegaQuadraticRemainder_apply_eq_sum_weight
    (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
    (d n ω) a b).symm

/-- Scalar residual-variance cross remainder from bounded sample `X'e/n` and
2SLS coefficient consistency. -/
theorem sigmaCross_tendstoInMeasure_zero_of_bounded_weights
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hweights : TwoSLSCovarianceRemainderBoundedWeightConditions μ Z X e) :
    TendstoInMeasure μ
      (fun n ω =>
        -2 * (sampleCrossMoment (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω) ⬝ᵥ
            (twoSLSBetaStar
              (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω) - β)))
      atTop (fun _ => 0) := by
  have hBeta := twoSLSBetaStar_tendstoInMeasure_beta_of_sample_moments_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel
  have hTerm : ∀ j ∈ (Finset.univ : Finset k),
      TendstoInMeasure μ
        (fun n ω =>
          sampleCrossMoment (fun i : Fin n => X i.val ω)
            (fun i : Fin n => e i.val ω) j *
          (twoSLSBetaStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω) - β) j)
        atTop (fun _ => 0) := by
    intro j _
    have hj := TendstoInMeasure.pi_apply hBeta j
    have hdj : TendstoInMeasure μ
        (fun n ω =>
          (twoSLSBetaStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω) - β) j)
        atTop (fun _ => 0) := by
      simpa [Pi.sub_apply] using TendstoInMeasure.sub_limit_zero_real hj
    have hprod := TendstoInMeasure.mul_boundedInProbability hdj
      (hweights.sigma_cross_bounded j)
    refine hprod.congr_left (fun n => ae_of_all μ (fun ω => ?_))
    ring
  have hsum := tendstoInMeasure_finset_sum_zero_real (μ := μ)
    (s := (Finset.univ : Finset k))
    (X := fun j n ω =>
      sampleCrossMoment (fun i : Fin n => X i.val ω)
        (fun i : Fin n => e i.val ω) j *
      (twoSLSBetaStar
        (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
        (fun i : Fin n => Y i.val ω) - β) j)
    hTerm
  have hdot : TendstoInMeasure μ
      (fun n ω =>
        sampleCrossMoment (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω) ⬝ᵥ
            (twoSLSBetaStar
              (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω) - β))
      atTop (fun _ => 0) := by
    refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
    simp [dotProduct]
  simpa using TendstoInMeasure.const_mul_zero_real (μ := μ) (-2) hdot

/-- Scalar residual-variance quadratic remainder from bounded sample `X'X/n`
and 2SLS coefficient consistency. -/
theorem sigmaQuadratic_tendstoInMeasure_zero_of_bounded_weights
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hweights : TwoSLSCovarianceRemainderBoundedWeightConditions μ Z X e) :
    TendstoInMeasure μ
      (fun n ω =>
        (twoSLSBetaStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω) - β) ⬝ᵥ
          (sampleGram (fun i : Fin n => X i.val ω) *ᵥ
            (twoSLSBetaStar
              (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω) - β)))
      atTop (fun _ => 0) := by
  have hBeta := twoSLSBetaStar_tendstoInMeasure_beta_of_sample_moments_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel
  let d : ℕ → Ω → k → ℝ := fun n ω =>
    twoSLSBetaStar
      (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
      (fun i : Fin n => Y i.val ω) - β
  have hd : ∀ j : k, TendstoInMeasure μ (fun n ω => d n ω j) atTop (fun _ => 0) := by
    intro j
    have hj := TendstoInMeasure.pi_apply hBeta j
    simpa [d, Pi.sub_apply] using TendstoInMeasure.sub_limit_zero_real hj
  have hInner : ∀ j ∈ (Finset.univ : Finset k),
      TendstoInMeasure μ
        (fun n ω => ∑ m : k,
          d n ω j * d n ω m *
            sampleGram (fun i : Fin n => X i.val ω) j m)
        atTop (fun _ => 0) := by
    intro j _
    have hTerm : ∀ m ∈ (Finset.univ : Finset k),
        TendstoInMeasure μ
          (fun n ω =>
            d n ω j * d n ω m *
              sampleGram (fun i : Fin n => X i.val ω) j m)
          atTop (fun _ => 0) := by
      intro m _
      have hprod := TendstoInMeasure.mul_zero_real (hd j) (hd m)
      exact TendstoInMeasure.mul_boundedInProbability hprod
        (hweights.sigma_gram_bounded j m)
    simpa using tendstoInMeasure_finset_sum_zero_real (μ := μ)
      (s := (Finset.univ : Finset k))
      (X := fun m n ω =>
        d n ω j * d n ω m *
          sampleGram (fun i : Fin n => X i.val ω) j m)
      hTerm
  have hsum := tendstoInMeasure_finset_sum_zero_real (μ := μ)
    (s := (Finset.univ : Finset k))
    (X := fun j n ω => ∑ m : k,
      d n ω j * d n ω m *
        sampleGram (fun i : Fin n => X i.val ω) j m)
    hInner
  refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  simp [d, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_left_comm, mul_comm]

/-- Build the exact Hansen Theorem 12.3 residual-substitution remainder package
from bounded empirical weights and 2SLS coefficient consistency. -/
theorem of_bounded_weights
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ : Matrix l l ℝ} {QZX : Matrix l k ℝ}
    (h : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hweights : TwoSLSCovarianceRemainderBoundedWeightConditions μ Z X e) :
    TwoSLSCovarianceRemainderConditions μ Z X e Y β where
  omega_cross_tendsto :=
    omegaCross_tendstoInMeasure_zero_of_bounded_weights
      (Z := Z) (X := X) (e := e) (Y := Y)
      h β hmodel hweights
  omega_quadratic_tendsto :=
    omegaQuadratic_tendstoInMeasure_zero_of_bounded_weights
      (Z := Z) (X := X) (e := e) (Y := Y)
      h β hmodel hweights
  sigma_cross_tendsto :=
    sigmaCross_tendstoInMeasure_zero_of_bounded_weights
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h β hmodel hweights
  sigma_quadratic_tendsto :=
    sigmaQuadratic_tendstoInMeasure_zero_of_bounded_weights
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h β hmodel hweights

/-- Build the exact residual-substitution remainder package from primitive
Assumption 12.2 plus scalar WLLN conditions for the empirical third/fourth
weights. -/
theorem of_assumption12_2_iid_weight_wlln
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e) :
    TwoSLSCovarianceRemainderConditions μ Z X e Y β :=
  of_bounded_weights
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toGramConditions.toSampleMomentConvergenceConditions β hmodel
    (TwoSLSCovarianceRemainderBoundedWeightConditions.of_assumption12_2_iid_weight_wlln
      (μ := μ) (Z := Z) (X := X) (e := e) h hw)

end TwoSLSCovarianceRemainderConditions

namespace TwoSLSCovarianceMomentConsistencyConditions

/-- Build the Hansen 12.3 middle/sigma consistency package entirely from
ideal true-error limits and explicit residual-substitution remainders.

This is the strongest proof-facing constructor currently available for
Theorem 12.3: it derives both feasible robust middle consistency and
homoskedastic residual-variance consistency from the deterministic expansions
in `Chapter12InstrumentalVariables.Basic`. -/
theorem of_remainders
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ}
    {QZX : Matrix l k ℝ} {sigma2 : ℝ}
    (sample_moments : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (omega_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSOmegaHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω)) μ)
    (sigma_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω)) μ)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaIdeal : TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaIdeal
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => e i.val ω))
      atTop (fun _ => Omega))
    (hOmegaCross : TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaCrossRemainder
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω)
          (twoSLSBetaStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω) - β))
      atTop (fun _ => 0))
    (hOmegaQuad : TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaQuadraticRemainder
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (twoSLSBetaStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω) - β))
      atTop (fun _ => 0))
    (hSigmaIdeal : TendstoInMeasure μ
      (fun n ω => sampleErrorSecondMoment (fun i : Fin n => e i.val ω))
      atTop (fun _ => sigma2))
    (hSigmaCross : TendstoInMeasure μ
      (fun n ω =>
        -2 * (sampleCrossMoment (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω) ⬝ᵥ
            (twoSLSBetaStar
              (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω) - β)))
      atTop (fun _ => 0))
    (hSigmaQuad : TendstoInMeasure μ
      (fun n ω =>
        (twoSLSBetaStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω) - β) ⬝ᵥ
          (sampleGram (fun i : Fin n => X i.val ω) *ᵥ
            (twoSLSBetaStar
              (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω) - β)))
      atTop (fun _ => 0)) :
    TwoSLSCovarianceMomentConsistencyConditions
      μ Z X e Y QXZ QZZ Omega QZX sigma2 where
  sample_moments := sample_moments
  omega_meas := omega_meas
  omega_tendsto :=
    twoSLSOmegaHatStar_tendstoInMeasure_of_linear_model_remainders
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      β hmodel hOmegaIdeal hOmegaCross hOmegaQuad
  sigma_meas := sigma_meas
  sigma_tendsto :=
    twoSLSSigmaSqHatStar_tendstoInMeasure_of_linear_model_remainders
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      β hmodel hSigmaIdeal hSigmaCross hSigmaQuad

/-- Build the Hansen 12.3 middle/sigma consistency package when the
homoskedastic residual variance consistency is proved from the explicit scalar
residual-substitution remainders. The robust middle consistency remains a
separate field because it is matrix-valued and requires the corresponding
weighted residual-substitution argument. -/
theorem of_sigma_remainders
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ}
    {QZX : Matrix l k ℝ} {sigma2 : ℝ}
    (sample_moments : TwoSLSSampleMomentConvergenceConditions μ Z X e QXZ QZZ QZX)
    (omega_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSOmegaHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω)) μ)
    (omega_tendsto : TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω))
      atTop (fun _ => Omega))
    (sigma_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω =>
        twoSLSSigmaSqHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω)) μ)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (herr : TendstoInMeasure μ
      (fun n ω => sampleErrorSecondMoment (fun i : Fin n => e i.val ω))
      atTop (fun _ => sigma2))
    (hcross : TendstoInMeasure μ
      (fun n ω =>
        -2 * (sampleCrossMoment (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω) ⬝ᵥ
            (twoSLSBetaStar
              (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω) - β)))
      atTop (fun _ => 0))
    (hquad : TendstoInMeasure μ
      (fun n ω =>
        (twoSLSBetaStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω) - β) ⬝ᵥ
          (sampleGram (fun i : Fin n => X i.val ω) *ᵥ
            (twoSLSBetaStar
              (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω) - β)))
      atTop (fun _ => 0)) :
    TwoSLSCovarianceMomentConsistencyConditions
      μ Z X e Y QXZ QZZ Omega QZX sigma2 where
  sample_moments := sample_moments
  omega_meas := omega_meas
  omega_tendsto := omega_tendsto
  sigma_meas := sigma_meas
  sigma_tendsto :=
    twoSLSSigmaSqHatStar_tendstoInMeasure_of_linear_model_remainders
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      β hmodel herr hcross hquad

/-- Build Hansen Theorem 12.3's middle/sigma consistency package from the
primitive iid Assumption 12.2 surface plus the exact residual-substitution
remainder limits.

This constructor derives the sample IV moments, the ideal true-error robust
middle WLLN, the scalar error-variance WLLN, and finite-sample measurability
from `TwoSLSSplitIidFourthMomentPositiveCovarianceConditions`. The only remaining stochastic
inputs are the four residual-substitution remainders packaged in
`TwoSLSCovarianceRemainderConditions`. -/
theorem of_assumption12_2_iid_remainders
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hr : TwoSLSCovarianceRemainderConditions μ Z X e Y β) :
    TwoSLSCovarianceMomentConsistencyConditions
      μ Z X e Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (errorVariance μ e) := by
  have hYmeas : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) β
      h.x_aestronglyMeasurable h.e_aestronglyMeasurable hmodel
  exact of_remainders
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (sample_moments := h.toGramConditions.toSampleMomentConvergenceConditions)
    (omega_meas := fun n =>
      twoSLSOmegaHatStar_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y)
        h.z_aestronglyMeasurable h.x_aestronglyMeasurable hYmeas)
    (sigma_meas := fun n =>
      twoSLSSigmaSqHatStar_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y)
        h.z_aestronglyMeasurable h.x_aestronglyMeasurable hYmeas)
    β hmodel
    (TwoSLSSplitIidFourthMomentPositiveCovarianceConditions.twoSLSOmegaIdeal_tendstoInMeasure_scoreCovMat
      (μ := μ) (Z := Z) (X := X) (e := e) h)
    hr.omega_cross_tendsto
    hr.omega_quadratic_tendsto
    (TwoSLSSplitIidFourthMomentPositiveCovarianceConditions.sampleErrorSecondMoment_tendstoInMeasure_errorVariance
      (μ := μ) (Z := Z) (X := X) (e := e) h)
    hr.sigma_cross_tendsto
    hr.sigma_quadratic_tendsto

/-- Build Hansen Theorem 12.3's middle/sigma consistency package from
Assumption 12.2 and scalar WLLN conditions for the empirical residual-
substitution weights. -/
theorem of_assumption12_2_iid_weight_wlln
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e) :
    TwoSLSCovarianceMomentConsistencyConditions
      μ Z X e Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (errorVariance μ e) :=
  of_assumption12_2_iid_remainders
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h β hmodel
    (TwoSLSCovarianceRemainderConditions.of_assumption12_2_iid_weight_wlln
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel hw)

/-- Convert middle/sigma consistency into the final Hansen 12.3 covariance
formula consistency package. -/
theorem toFormulaConsistencyConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ}
    {QZX : Matrix l k ℝ} {sigma2 : ℝ}
    (h : TwoSLSCovarianceMomentConsistencyConditions
      μ Z X e Y QXZ QZZ Omega QZX sigma2) :
    TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y QXZ QZZ Omega QZX sigma2 where
  robust_tendsto :=
    twoSLSVHatStar_tendstoInMeasure_formula_of_middle
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h.sample_moments h.omega_meas h.omega_tendsto
  homoskedastic_tendsto :=
    twoSLSHomoskedasticVHatStar_tendstoInMeasure_formula_of_sigma
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h.sample_moments h.sigma_meas h.sigma_tendsto

end TwoSLSCovarianceMomentConsistencyConditions

/-- Single-row iid Assumption 12.2 plus the mixed moment integrability needed
for Hansen Theorem 12.3's feasible residual substitution.

The parent `TwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions` supplies the primitive
Assumption 12.2 score and sample-moment surface. These extra fields are exactly
the scalar products used to bound the robust-middle and homoskedastic
residual-substitution remainders; independence and identical distribution of
those products are derived from the parent joint-iid row fields. -/
structure TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    : Prop extends TwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions μ Z X e where
  omega_cross_integrable : ∀ a b : l, ∀ j : k,
    Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ
  omega_quadratic_integrable : ∀ a b : l, ∀ j m : k,
    Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ
  sigma_cross_integrable : ∀ j : k,
    Integrable (fun ω => e 0 ω * X 0 ω j) μ

namespace TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions

omit [DecidableEq k] [DecidableEq l] in
/-- The mixed-moment Assumption 12.2 package supplies the scalar WLLN package
for the residual-substitution weights in Hansen Theorem 12.3. -/
theorem toWeightWLLNConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Z X e) :
    TwoSLSCovarianceWeightWLLNConditions μ Z X e :=
  TwoSLSCovarianceWeightWLLNConditions.of_joint_iid
    (μ := μ) (Z := Z) (X := X) (e := e)
    h.joint_iIndep h.joint_identDistrib
    h.omega_cross_integrable h.omega_quadratic_integrable h.sigma_cross_integrable

/-- The mixed-moment Assumption 12.2 package supplies Hansen Theorem 12.3's
middle and scalar residual-variance consistency package. -/
theorem toCovarianceMomentConsistencyConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TwoSLSCovarianceMomentConsistencyConditions
      μ Z X e Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (errorVariance μ e) :=
  TwoSLSCovarianceMomentConsistencyConditions.of_assumption12_2_iid_weight_wlln
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions.toIidFourthConditions
    β hmodel
    (TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions.toWeightWLLNConditions
      (μ := μ) (Z := Z) (X := X) (e := e) h)

/-- The mixed-moment Assumption 12.2 package supplies Hansen Theorem 12.3's
formula-facing covariance consistency package. -/
theorem toCovarianceFormulaConsistencyConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (errorVariance μ e) :=
  (TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions.toCovarianceMomentConsistencyConditions
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel).toFormulaConsistencyConditions

end TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions

/-- Literal finite-fourth-moment iid surface for Hansen Assumption 12.2.

This package keeps Hansen's stated moments explicit:
`E[Y₁⁴] < ∞`, `E‖X₁‖⁴ < ∞`, and `E‖Z₁‖⁴ < ∞`, together with the structural
equation and the positive-definite instrument-score covariance `Ω`.  It
derives the score and residual-substitution mixed moments consumed by the
existing proof engine. -/
structure TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e Y : ℕ → Ω → ℝ)
    (β0 : k → ℝ)
    : Prop extends TwoSLSResidualJointIidSecondMomentRankConditions μ Z X e where
  /-- Linear structural equation. -/
  model : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω
  /-- Hansen's finite fourth moment for the scalar response. -/
  response_fourth_integrable : Integrable (fun ω => Y 0 ω ^ 4) μ
  /-- Hansen's finite fourth moment for regressors. -/
  regressor_norm_fourth_integrable : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ
  /-- Hansen's finite fourth moment for instruments. -/
  instrument_norm_fourth_integrable : Integrable (fun ω => ‖Z 0 ω‖ ^ 4) μ
  /-- Hansen's positive-definite `Ω = E[Z Z' e²]` condition. -/
  omega_posDef : (scoreCovMat μ Z e).PosDef

namespace TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions

omit [DecidableEq k] [DecidableEq l] in
/-- The structural equation and row measurability imply response
measurability. -/
theorem y_aestronglyMeasurable
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Z X e Y β0) :
    ∀ i, AEStronglyMeasurable (Y i) μ :=
  outcome_aestronglyMeasurable_of_linear_model
    (μ := μ) (X := X) (e := e) (Y := Y) β0
    h.x_aestronglyMeasurable h.e_aestronglyMeasurable h.model

omit [DecidableEq k] [DecidableEq l] in
/-- Hansen's response and regressor fourth moments imply a structural-error
fourth moment through the linear model. -/
private theorem error_memLp_four
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Z X e Y β0) :
    MemLp (fun ω => e 0 ω) 4 μ :=
  error_memLp_four_of_response_regressor_fourth
    (μ := μ) (X := X) (e := e) (Y := Y) (β := β0)
    (h.x_aestronglyMeasurable 0) (h.y_aestronglyMeasurable 0)
    (h.model 0) h.response_fourth_integrable h.regressor_norm_fourth_integrable

omit [DecidableEq k] [DecidableEq l] in
/-- Convert the literal Hansen Assumption 12.2 fourth-moment package into the
mixed-moment package used by the covariance and smooth-function proof engine. -/
theorem toJointIidMixedMomentConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Z X e Y β0) :
    TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Z X e := by
  have he4 : MemLp (fun ω => e 0 ω) 4 μ :=
    h.error_memLp_four
  have hX4 : ∀ j : k, MemLp (fun ω => X 0 ω j) 4 μ :=
    fun j =>
      coordinate_memLp_four_of_norm_fourth
        (μ := μ) (X := X) (h.x_aestronglyMeasurable 0)
        h.regressor_norm_fourth_integrable j
  have hZ4 : ∀ a : l, MemLp (fun ω => Z 0 ω a) 4 μ :=
    fun a =>
      coordinate_memLp_four_of_norm_fourth
        (μ := μ) (X := Z) (h.z_aestronglyMeasurable 0)
        h.instrument_norm_fourth_integrable a
  refine
    { toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions :=
        { toTwoSLSResidualJointIidSecondMomentRankConditions :=
            h.toTwoSLSResidualJointIidSecondMomentRankConditions
          error_sq_integrable :=
            error_sq_integrable_of_memLp_four (μ := μ) (e := e) he4
          score_outer_integrable :=
            score_outer_integrable_of_memLp_four (μ := μ) (Z := Z) (e := e)
              he4 hZ4
          omega_posDef := h.omega_posDef }
      omega_cross_integrable := ?_
      omega_quadratic_integrable := ?_
      sigma_cross_integrable := ?_ }
  · intro a b j
    exact omega_cross_integrable_of_memLp_four
      (μ := μ) (Z := Z) (X := X) (e := e) he4 hX4 hZ4 a b j
  · intro a b j m
    exact omega_quadratic_integrable_of_memLp_four
      (μ := μ) (Z := Z) (X := X) hX4 hZ4 a b j m
  · intro j
    exact sigma_cross_integrable_of_memLp_four
      (μ := μ) (X := X) (e := e) he4 hX4 j

end TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions

/-- Observed-row iid fourth-moment conditions for 2SLS coefficient normality
with a possibly singular score covariance.

This is the moment/rank surface needed by generated-regressor applications
such as Hansen Theorem 12.11. Unlike Assumption 12.2's Wald-facing package, it
does not require `Ω = E[ZZ'e²]` to be positive definite. -/
structure TwoSLSObservedIidFourthMomentConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e Y : ℕ → Ω → ℝ)
    (β0 : k → ℝ) : Prop where
  observed_aestronglyMeasurable :
    ∀ i, AEStronglyMeasurable (fun ω => ((Z i ω, X i ω), Y i ω)) μ
  observed_iIndep : iIndepFun (fun i ω => ((Z i ω, X i ω), Y i ω)) μ
  observed_identDistrib : ∀ i,
    IdentDistrib (fun ω => ((Z i ω, X i ω), Y i ω))
      (fun ω => ((Z 0 ω, X 0 ω), Y 0 ω)) μ μ
  model : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω
  response_fourth_integrable : Integrable (fun ω => Y 0 ω ^ 4) μ
  regressor_norm_fourth_integrable : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ
  instrument_norm_fourth_integrable : Integrable (fun ω => ‖Z 0 ω‖ ^ 4) μ
  orthogonality : μ[fun ω => e 0 ω • Z 0 ω] = 0
  qzz_posDef :
    (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X))).PosDef
  qzx_rank :
    Function.Injective
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))).mulVec

namespace TwoSLSObservedIidFourthMomentConditions

omit [DecidableEq k] [DecidableEq l] in
/-- The fourth-moment observed-row package supplies Hansen's finite-second
Assumption 12.1 layer. -/
theorem toTextbookSecondConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentConditions μ Z X e Y β0) :
    TwoSLSObservedIidSecondMomentRankConditions μ Z X e Y β0 := by
  have hZ0 : AEStronglyMeasurable (Z 0) μ :=
    (continuous_fst.comp continuous_fst).comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable 0)
  have hX0 : AEStronglyMeasurable (X 0) μ :=
    (continuous_snd.comp continuous_fst).comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable 0)
  have hY0 : AEStronglyMeasurable (Y 0) μ :=
    continuous_snd.comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable 0)
  exact
    { observed_aestronglyMeasurable := h.observed_aestronglyMeasurable
      observed_iIndep := h.observed_iIndep
      observed_identDistrib := h.observed_identDistrib
      model := h.model
      response_sq_integrable :=
        integrable_sq_of_integrable_fourth hY0 h.response_fourth_integrable
      regressor_norm_sq_integrable :=
        integrable_sq_of_integrable_fourth hX0.norm
          h.regressor_norm_fourth_integrable
      instrument_norm_sq_integrable :=
        integrable_sq_of_integrable_fourth hZ0.norm
          h.instrument_norm_fourth_integrable
      orthogonality := h.orthogonality
      qzz_posDef := h.qzz_posDef
      qzx_rank := h.qzx_rank }

omit [DecidableEq k] [DecidableEq l] in
/-- The displayed response and regressor fourth moments imply a fourth moment
for the structural error. -/
private theorem error_memLp_four
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentConditions μ Z X e Y β0) :
    MemLp (fun ω => e 0 ω) 4 μ := by
  have hX0 : AEStronglyMeasurable (X 0) μ :=
    (continuous_snd.comp continuous_fst).comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable 0)
  have hY0 : AEStronglyMeasurable (Y 0) μ :=
    continuous_snd.comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable 0)
  exact error_memLp_four_of_response_regressor_fourth
    (μ := μ) (X := X) (e := e) (Y := Y) (β := β0)
    hX0 hY0 (h.model 0) h.response_fourth_integrable
    h.regressor_norm_fourth_integrable

omit [DecidableEq k] in
/-- Convert the observed-row moments into the semidefinite-capable Gram/score
CLT engine. -/
theorem toGramScoreCLTConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentConditions μ Z X e Y β0) :
    TwoSLSGramScoreCLTConditions μ Z X e := by
  let hIid : TwoSLSSplitIidSecondMomentRankConditions μ Z X e :=
    h.toTextbookSecondConditions.toJointIidConditions.toIidConditions
  have hZ4 : ∀ a : l, MemLp (fun ω => Z 0 ω a) 4 μ :=
    fun a => coordinate_memLp_four_of_norm_fourth
      (μ := μ) (X := Z) (hIid.z_aestronglyMeasurable 0)
      h.instrument_norm_fourth_integrable a
  have hScoreOuter : Integrable
      (fun ω => Matrix.vecMulVec (e 0 ω • Z 0 ω) (e 0 ω • Z 0 ω)) μ :=
    score_outer_integrable_of_memLp_four
      (μ := μ) (Z := Z) (e := e) h.error_memLp_four hZ4
  exact
    { toTwoSLSGramInstrumentMomentRankConditions := hIid.toGramConditions
      score_clt :=
        scoreCLTConditions_of_iid_score_outer
          (μ := μ) (X := Z) (e := e)
          (hIid.z_aestronglyMeasurable 0) (hIid.e_aestronglyMeasurable 0)
          hIid.instrument_joint_iIndep hIid.instrument_joint_identDistrib
          hIid.instrument_norm_sq_integrable hIid.instrument_cross_integrable
          hScoreOuter hIid.instrument_popGram_nonsing hIid.orthogonality }

omit [DecidableEq k] in
/-- The observed-row fourth moments supply the true-error HC0 WLLN package
without requiring the limiting covariance to be invertible. -/
theorem toSampleHC0Assumption76
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentConditions μ Z X e Y β0) :
    SampleHC0Assumption76 μ Z e := by
  let hIid : TwoSLSSplitIidSecondMomentRankConditions μ Z X e :=
    h.toTextbookSecondConditions.toJointIidConditions.toIidConditions
  have hZ4 : ∀ a : l, MemLp (fun ω => Z 0 ω a) 4 μ :=
    fun a => coordinate_memLp_four_of_norm_fourth
      (μ := μ) (X := Z) (hIid.z_aestronglyMeasurable 0)
      h.instrument_norm_fourth_integrable a
  have hScoreOuter : Integrable
      (fun ω => Matrix.vecMulVec (e 0 ω • Z 0 ω) (e 0 ω • Z 0 ω)) μ :=
    score_outer_integrable_of_memLp_four
      (μ := μ) (Z := Z) (e := e) h.error_memLp_four hZ4
  exact
    { toScoreCLTConditions := h.toGramScoreCLTConditions.score_clt
      indep_score_outer := by
        have hout : iIndepFun
            (fun i ω => Matrix.vecMulVec (e i ω • Z i ω) (e i ω • Z i ω)) μ := by
          simpa [Function.comp] using
            hIid.instrument_joint_iIndep.comp
              (fun _ z => Matrix.vecMulVec (z.2 • z.1) (z.2 • z.1))
              (fun _ => measurable_pair_score_outer (q := l))
        intro i j hij
        exact hout.indepFun hij
      ident_score_outer := by
        intro i
        have hi := hIid.instrument_joint_identDistrib i
        exact hi.comp (measurable_pair_score_outer (q := l))
      int_score_outer := hScoreOuter }

omit [DecidableEq k] [DecidableEq l] in
/-- The observed-row fourth moments supply every scalar WLLN used in the
feasible 2SLS HC0 residual-substitution expansion. -/
theorem toCovarianceWeightWLLNConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentConditions μ Z X e Y β0) :
    TwoSLSCovarianceWeightWLLNConditions μ Z X e := by
  let hJoint : TwoSLSResidualJointIidSecondMomentRankConditions μ Z X e :=
    h.toTextbookSecondConditions.toJointIidConditions
  have he4 : MemLp (fun ω => e 0 ω) 4 μ := h.error_memLp_four
  have hX4 : ∀ j : k, MemLp (fun ω => X 0 ω j) 4 μ := fun j =>
    coordinate_memLp_four_of_norm_fourth
      (μ := μ) (X := X) (hJoint.x_aestronglyMeasurable 0)
      h.regressor_norm_fourth_integrable j
  have hZ4 : ∀ a : l, MemLp (fun ω => Z 0 ω a) 4 μ := fun a =>
    coordinate_memLp_four_of_norm_fourth
      (μ := μ) (X := Z) (hJoint.z_aestronglyMeasurable 0)
      h.instrument_norm_fourth_integrable a
  exact TwoSLSCovarianceWeightWLLNConditions.of_joint_iid
    (μ := μ) (Z := Z) (X := X) (e := e)
    hJoint.joint_iIndep hJoint.joint_identDistrib
    (fun a b j => omega_cross_integrable_of_memLp_four
      (μ := μ) (Z := Z) (X := X) (e := e) he4 hX4 hZ4 a b j)
    (fun a b j m => omega_quadratic_integrable_of_memLp_four
      (μ := μ) (Z := Z) (X := X) hX4 hZ4 a b j m)
    (fun j => sigma_cross_integrable_of_memLp_four
      (μ := μ) (X := X) (e := e) he4 hX4 j)

end TwoSLSObservedIidFourthMomentConditions

/-- Literal observed-row finite-fourth-moment surface for Hansen Assumption
12.2.

The iid condition is stated on Hansen's observed row `((Z_i, X_i), Y_i)`.
Fourth moments imply the finite-second fields needed by Assumption 12.1, and
the structural equation converts the package to the residual-row proof engine. -/
structure TwoSLSObservedIidFourthMomentPositiveCovarianceConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e Y : ℕ → Ω → ℝ)
    (β0 : k → ℝ) : Prop where
  observed_aestronglyMeasurable :
    ∀ i, AEStronglyMeasurable (fun ω => ((Z i ω, X i ω), Y i ω)) μ
  observed_iIndep : iIndepFun (fun i ω => ((Z i ω, X i ω), Y i ω)) μ
  observed_identDistrib : ∀ i,
    IdentDistrib (fun ω => ((Z i ω, X i ω), Y i ω))
      (fun ω => ((Z 0 ω, X 0 ω), Y 0 ω)) μ μ
  model : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β0 + e i ω
  response_fourth_integrable : Integrable (fun ω => Y 0 ω ^ 4) μ
  regressor_norm_fourth_integrable : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ
  instrument_norm_fourth_integrable : Integrable (fun ω => ‖Z 0 ω‖ ^ 4) μ
  orthogonality : μ[fun ω => e 0 ω • Z 0 ω] = 0
  qzz_posDef :
    (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X))).PosDef
  qzx_rank :
    Function.Injective
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))).mulVec
  omega_posDef : (scoreCovMat μ Z e).PosDef

namespace TwoSLSObservedIidFourthMomentPositiveCovarianceConditions

omit [DecidableEq k] [DecidableEq l] in
/-- Convert the observed-row finite-fourth Assumption 12.2 package to the
observed-row finite-second Assumption 12.1 package. -/
theorem toTextbookSecondConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Z X e Y β0) :
    TwoSLSObservedIidSecondMomentRankConditions μ Z X e Y β0 := by
  have hZ0 : AEStronglyMeasurable (Z 0) μ :=
    (continuous_fst.comp continuous_fst).comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable 0)
  have hX0 : AEStronglyMeasurable (X 0) μ :=
    (continuous_snd.comp continuous_fst).comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable 0)
  have hY0 : AEStronglyMeasurable (Y 0) μ :=
    continuous_snd.comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable 0)
  exact
    { observed_aestronglyMeasurable := h.observed_aestronglyMeasurable
      observed_iIndep := h.observed_iIndep
      observed_identDistrib := h.observed_identDistrib
      model := h.model
      response_sq_integrable :=
        integrable_sq_of_integrable_fourth hY0 h.response_fourth_integrable
      regressor_norm_sq_integrable :=
        integrable_sq_of_integrable_fourth hX0.norm
          h.regressor_norm_fourth_integrable
      instrument_norm_sq_integrable :=
        integrable_sq_of_integrable_fourth hZ0.norm
          h.instrument_norm_fourth_integrable
      orthogonality := h.orthogonality
      qzz_posDef := h.qzz_posDef
      qzx_rank := h.qzx_rank }

omit [DecidableEq k] [DecidableEq l] in
/-- Convert the observed-row finite-fourth Assumption 12.2 package to the
residual-row fourth-moment proof engine. -/
theorem toResidualTextbookFourthConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Z X e Y β0) :
    TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Z X e Y β0 :=
  { toTwoSLSResidualJointIidSecondMomentRankConditions :=
      h.toTextbookSecondConditions.toJointIidConditions
    model := h.model
    response_fourth_integrable := h.response_fourth_integrable
    regressor_norm_fourth_integrable := h.regressor_norm_fourth_integrable
    instrument_norm_fourth_integrable := h.instrument_norm_fourth_integrable
    omega_posDef := h.omega_posDef }

omit [DecidableEq k] [DecidableEq l] in
/-- Convert the observed-row finite-fourth Assumption 12.2 package to the
mixed-moment package used by covariance and smooth-function proof engines. -/
theorem toJointIidMixedMomentConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Z X e Y β0) :
    TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Z X e :=
  h.toResidualTextbookFourthConditions.toJointIidMixedMomentConditions

end TwoSLSObservedIidFourthMomentPositiveCovarianceConditions

/-- Formula-facing 2SLS coefficient CLT from observed-row fourth moments,
without an unnecessary positive-definiteness assumption on the score
covariance. The Gaussian limit may be degenerate. -/
theorem twoSLSBetaStar_tendstoInDistribution_formula_of_observed_iid_fourth_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentConditions μ Z X e Y β0) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β0))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) := by
  have hZ : ∀ i, AEStronglyMeasurable (Z i) μ := fun i =>
    (continuous_fst.comp continuous_fst).comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable i)
  have hX : ∀ i, AEStronglyMeasurable (X i) μ := fun i =>
    (continuous_snd.comp continuous_fst).comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable i)
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ := fun i =>
    continuous_snd.comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable i)
  exact twoSLSBetaStar_tendstoInDistribution_formula_of_gram_score_clt_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toGramScoreCLTConditions β0 h.model
    (fun t => twoSLSBetaStar_scaled_centered_aemeasurable_of_rows
      (μ := μ) (Z := Z) (X := X) (Y := Y) hZ hX hY β0)

set_option maxHeartbeats 1200000 in
-- The covariance proof assembles iid moment conversions and several matrix CMT layers.
set_option linter.flexible false in
/-- Robust 2SLS covariance consistency from observed-row fourth moments with
a possibly singular limiting score covariance. -/
theorem twoSLSVHatStar_tendstoInMeasure_formula_of_observed_iid_fourth_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentConditions μ Z X e Y β0) :
    TendstoInMeasure μ
      (fun n ω =>
        twoSLSVHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω))
      atTop
      (fun _ =>
        twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) := by
  classical
  let hGram := h.toGramScoreCLTConditions
  let hMom := hGram.toTwoSLSGramInstrumentMomentRankConditions.toSampleMomentConvergenceConditions
  have hZ : ∀ i, AEStronglyMeasurable (Z i) μ := fun i =>
    (continuous_fst.comp continuous_fst).comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable i)
  have hX : ∀ i, AEStronglyMeasurable (X i) μ := fun i =>
    (continuous_snd.comp continuous_fst).comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable i)
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ := fun i =>
    continuous_snd.comp_aestronglyMeasurable
      (h.observed_aestronglyMeasurable i)
  have hIdeal : TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaIdeal
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => e i.val ω))
      atTop (fun _ => scoreCovMat μ Z e) := by
    have hideal := sampleScoreCovIdeal_stack_tendstoInMeasure_scoreCovMat
      (μ := μ) (X := Z) (e := e) h.toSampleHC0Assumption76
    exact hideal.congr_left (fun n => ae_of_all μ (fun ω => by
      by_cases hn : n = 0
      · subst n
        simp [twoSLSOmegaIdeal, sampleScoreCovIdeal, stackRegressors, stackErrors]
      ext a b
      simp [twoSLSOmegaIdeal, sampleScoreCovIdeal, stackRegressors, stackErrors, hn,
        Matrix.smul_apply, Matrix.sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      simp [Matrix.vecMulVec_apply, pow_two]
      ring))
  have hWeights : TwoSLSCovarianceRemainderBoundedWeightConditions μ Z X e :=
    TwoSLSCovarianceRemainderBoundedWeightConditions.of_weight_wlln_combined_sampleGram
      (μ := μ) (Z := Z) (X := X) (e := e)
      hGram.toCombinedSampleMomentConvergenceConditions
      h.toCovarianceWeightWLLNConditions
  have hRem : TwoSLSCovarianceRemainderConditions μ Z X e Y β0 :=
    TwoSLSCovarianceRemainderConditions.of_bounded_weights
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      hMom β0 h.model hWeights
  have hOmega : TendstoInMeasure μ
      (fun n ω =>
        twoSLSOmegaHatStar
          (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω))
      atTop (fun _ => scoreCovMat μ Z e) :=
    twoSLSOmegaHatStar_tendstoInMeasure_of_linear_model_remainders
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      β0 h.model hIdeal hRem.omega_cross_tendsto hRem.omega_quadratic_tendsto
  exact twoSLSVHatStar_tendstoInMeasure_formula_of_middle
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    hMom
    (fun n => twoSLSOmegaHatStar_aestronglyMeasurable_of_rows
      (μ := μ) (Z := Z) (X := X) (Y := Y) hZ hX hY)
    hOmega

/-- Hansen Theorem 12.2 formula-facing endpoint from the literal
finite-fourth-moment version of Assumption 12.2.

This wrapper exposes the textbook-shaped assumptions directly. The structural
equation and the finite score-CLT package are derived internally from
`TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions`. -/
theorem twoSLSBetaStar_tendstoInDistribution_formula_of_textbook12_2_joint_iid_fourth
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Z X e Y β0) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β0))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :=
  twoSLSBetaStar_tendstoInDistribution_formula_of_assumption12_2_joint_iid_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toJointIidMixedMomentConditions.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions
    β0 h.model

/-- Textbook-facing OrZero version of Hansen Theorem 12.2 from the literal
finite-fourth-moment version of Assumption 12.2. -/
theorem twoSLSBetaOrZero_tendstoInDistribution_formula_of_textbook12_2_joint_iid_fourth
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Z X e Y β0) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β0))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :=
  twoSLSBetaOrZero_tendstoInDistribution_formula_of_assumption12_2_joint_iid_model
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toJointIidMixedMomentConditions.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions
    β0 h.model

/-- Hansen Theorem 12.2 formula-facing endpoint from the literal observed-row
finite-fourth-moment version of Assumption 12.2. -/
theorem twoSLSBetaStar_tendstoInDistribution_formula_of_textbook12_2_observed_iid_fourth
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Z X e Y β0) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaStar
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β0))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :=
  twoSLSBetaStar_tendstoInDistribution_formula_of_textbook12_2_joint_iid_fourth
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toResidualTextbookFourthConditions

/-- Textbook-facing OrZero endpoint for Hansen Theorem 12.2 from the literal
observed-row finite-fourth-moment version of Assumption 12.2. -/
theorem twoSLSBetaOrZero_tendstoInDistribution_formula_of_textbook12_2_observed_iid_fourth
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Z X e Y β0) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (twoSLSBetaOrZero
            (fun i : Fin t => Z i.val ω) (fun i : Fin t => X i.val ω)
            (fun i : Fin t => Y i.val ω) - β0))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (twoSLSAsymptoticVariance
          (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
          (scoreCovMat μ Z e)
          (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X))))) :=
  twoSLSBetaOrZero_tendstoInDistribution_formula_of_textbook12_2_joint_iid_fourth
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toResidualTextbookFourthConditions

namespace TwoSLSCovarianceRemainderConditions

/-- Package form of the exact Hansen Theorem 12.3 residual-substitution
remainders from a single-row iid Assumption 12.2 mixed-moment package.

This exposes the proof step used by the covariance endpoint without assuming
either final covariance consistency conclusion. -/
theorem of_assumption12_2_joint_iid_mixed_moment_conditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TwoSLSCovarianceRemainderConditions μ Z X e Y β :=
  of_assumption12_2_iid_weight_wlln
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toTwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions.toIidFourthConditions
    β hmodel
    (TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions.toWeightWLLNConditions
      (μ := μ) (Z := Z) (X := X) (e := e) h)

/-- Package form of the exact Hansen Theorem 12.3 residual-substitution
remainders from the literal finite-fourth-moment version of Assumption 12.2. -/
theorem of_textbook12_2_joint_iid_fourth
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Z X e Y β0) :
    TwoSLSCovarianceRemainderConditions μ Z X e Y β0 :=
  of_assumption12_2_joint_iid_mixed_moment_conditions
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions.toJointIidMixedMomentConditions
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h)
    β0 h.model

end TwoSLSCovarianceRemainderConditions

/-- Hansen Theorem 12.3 formula-facing interface.

It returns both textbook conclusions with the robust covariance limit
`(Q_XZ Q_ZZ^{-1}Q_ZX)^{-1} Q_XZ Q_ZZ^{-1} Ω Q_ZZ^{-1} Q_ZX
 (Q_XZ Q_ZZ^{-1}Q_ZX)^{-1}` and the homoskedastic limit
`σ² (Q_XZ Q_ZZ^{-1}Q_ZX)^{-1}`. -/
theorem twoSLSCovariances_tendstoInMeasure_formula
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ}
    {QZX : Matrix l k ℝ} {sigma2 : ℝ}
    (h : TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y QXZ QZZ Omega QZX sigma2) :
    TendstoInMeasure μ
        (fun n ω =>
          twoSLSVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop (fun _ => twoSLSAsymptoticVariance QXZ QZZ Omega QZX) ∧
      TendstoInMeasure μ
        (fun n ω =>
          twoSLSHomoskedasticVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop (fun _ => twoSLSHomoskedasticAsymptoticVariance QXZ QZZ QZX sigma2) :=
  ⟨h.robust_tendsto, h.homoskedastic_tendsto⟩

/-- Hansen Theorem 12.3 formula-facing interface from middle and residual-variance
consistency.

This is the preferred proof-facing assembly route: prove consistency of
`Ω̂` and `σ̂²`, then this theorem performs the continuous-mapping step for both
covariance estimators. -/
theorem twoSLSCovariances_tendstoInMeasure_formula_of_middle
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {QXZ : Matrix k l ℝ} {QZZ Omega : Matrix l l ℝ}
    {QZX : Matrix l k ℝ} {sigma2 : ℝ}
    (h : TwoSLSCovarianceMomentConsistencyConditions
      μ Z X e Y QXZ QZZ Omega QZX sigma2) :
    TendstoInMeasure μ
        (fun n ω =>
          twoSLSVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop (fun _ => twoSLSAsymptoticVariance QXZ QZZ Omega QZX) ∧
      TendstoInMeasure μ
        (fun n ω =>
          twoSLSHomoskedasticVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop (fun _ => twoSLSHomoskedasticAsymptoticVariance QXZ QZZ QZX sigma2) :=
  twoSLSCovariances_tendstoInMeasure_formula
    (TwoSLSCovarianceMomentConsistencyConditions.toFormulaConsistencyConditions h)

/-- Hansen Theorem 12.3 formula-facing endpoint from primitive iid Assumption
12.2 plus exact residual-substitution remainders.

The robust limit is Hansen's displayed sandwich with
`Ω = Var(Z_i e_i) = scoreCovMat μ Z e`; the homoskedastic limit uses
`σ² = E[e_i²] = errorVariance μ e`. -/
theorem twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_iid_remainders
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hr : TwoSLSCovarianceRemainderConditions μ Z X e Y β) :
    TendstoInMeasure μ
        (fun n ω =>
          twoSLSVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) ∧
      TendstoInMeasure μ
        (fun n ω =>
          twoSLSHomoskedasticVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop
        (fun _ =>
          twoSLSHomoskedasticAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
            (errorVariance μ e)) :=
  twoSLSCovariances_tendstoInMeasure_formula_of_middle
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (TwoSLSCovarianceMomentConsistencyConditions.of_assumption12_2_iid_remainders
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel hr)

/-- Hansen Theorem 12.3 formula-facing endpoint from primitive iid Assumption
12.2 plus scalar WLLN conditions for the empirical residual-substitution
weights.

This keeps Hansen's covariance conclusions unchanged while replacing the
manual four-remainder premise in
`twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_iid_remainders`
with enforceable WLLN assumptions for the exact third/fourth scalar summands. -/
theorem twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_iid_weight_wlln
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e) :
    TendstoInMeasure μ
        (fun n ω =>
          twoSLSVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) ∧
      TendstoInMeasure μ
        (fun n ω =>
          twoSLSHomoskedasticVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop
        (fun _ =>
          twoSLSHomoskedasticAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
            (errorVariance μ e)) :=
  twoSLSCovariances_tendstoInMeasure_formula_of_middle
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (TwoSLSCovarianceMomentConsistencyConditions.of_assumption12_2_iid_weight_wlln
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel hw)

/-- Hansen Theorem 12.3 formula-facing endpoint from primitive iid Assumption
12.2 plus joint-iid mixed-moment conditions for the empirical
residual-substitution weights.

This is the theorem-facing version of
`twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_iid_weight_wlln`
that derives the scalar WLLN package from iid joint rows `((Z_i, X_i), e_i)`.
The additional integrability hypotheses are exactly Hansen's mixed
third/fourth moment summands used in the feasible residual substitution. -/
theorem twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_joint_iid_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hjoint : iIndepFun (fun i ω => ((Z i ω, X i ω), e i ω)) μ)
    (hident : ∀ i,
      IdentDistrib
        (fun ω => ((Z i ω, X i ω), e i ω))
        (fun ω => ((Z 0 ω, X 0 ω), e 0 ω)) μ μ)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ) :
    TendstoInMeasure μ
        (fun n ω =>
          twoSLSVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) ∧
      TendstoInMeasure μ
        (fun n ω =>
          twoSLSHomoskedasticVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop
        (fun _ =>
          twoSLSHomoskedasticAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
            (errorVariance μ e)) := by
  exact twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_iid_weight_wlln
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h β (hmodel := hmodel)
    (hw := TwoSLSCovarianceWeightWLLNConditions.of_joint_iid
      (μ := μ) (Z := Z) (X := X) (e := e)
      hjoint hident hOmegaCross hOmegaQuadratic hSigmaCross)

/-- Hansen Theorem 12.3 formula-facing endpoint from the single-row iid
Assumption 12.2 package plus mixed third/fourth moment conditions for the
empirical residual-substitution weights.

This is the preferred theorem-shaped route when the primitive hypothesis is
`TwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions`: the iid and identical
distribution inputs are read directly from that package, leaving only the mixed
integrability premises that are not implied by its score-outer moment fields. -/
theorem twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_joint_iid_mixed_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ) :
    TendstoInMeasure μ
        (fun n ω =>
          twoSLSVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) ∧
      TendstoInMeasure μ
        (fun n ω =>
          twoSLSHomoskedasticVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop
        (fun _ =>
          twoSLSHomoskedasticAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
            (errorVariance μ e)) :=
  twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_joint_iid_moments
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toIidFourthConditions β hmodel h.joint_iIndep h.joint_identDistrib
    hOmegaCross hOmegaQuadratic hSigmaCross

/-- Hansen Theorem 12.3 formula-facing endpoint from a single-row iid
Assumption 12.2 mixed-moment package.

This is the packaged version of
`twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_joint_iid_mixed_moments`:
the parent Assumption 12.2 fields supply the Chapter 7 WLLN/CLT inputs and the
package's three mixed-integrability fields supply the residual-substitution
weight WLLNs. -/
theorem
    twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_joint_iid_mixed_moment_conditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
        (fun n ω =>
          twoSLSVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) ∧
      TendstoInMeasure μ
        (fun n ω =>
          twoSLSHomoskedasticVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop
        (fun _ =>
          twoSLSHomoskedasticAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
            (errorVariance μ e)) :=
  twoSLSCovariances_tendstoInMeasure_formula_of_middle
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions.toCovarianceMomentConsistencyConditions
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel)

/-- Hansen Theorem 12.3 formula-facing endpoint from the literal finite-fourth
moment version of Assumption 12.2.

This wrapper exposes the textbook-shaped assumptions directly. The
mixed-moment and residual-substitution inputs are derived internally by
`TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions.toJointIidMixedMomentConditions`. -/
theorem twoSLSCovariances_tendstoInMeasure_formula_of_textbook12_2_joint_iid_fourth
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Z X e Y β0) :
    TendstoInMeasure μ
        (fun n ω =>
          twoSLSVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) ∧
      TendstoInMeasure μ
        (fun n ω =>
          twoSLSHomoskedasticVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop
        (fun _ =>
          twoSLSHomoskedasticAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
            (errorVariance μ e)) :=
  twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_joint_iid_mixed_moment_conditions
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    (TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions.toJointIidMixedMomentConditions
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h)
    β0 h.model

/-- Hansen Theorem 12.3 formula-facing endpoint from the literal observed-row
finite-fourth-moment version of Assumption 12.2. -/
theorem twoSLSCovariances_tendstoInMeasure_formula_of_textbook12_2_observed_iid_fourth
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSObservedIidFourthMomentPositiveCovarianceConditions μ Z X e Y β0) :
    TendstoInMeasure μ
        (fun n ω =>
          twoSLSVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop
        (fun _ =>
          twoSLSAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (scoreCovMat μ Z e)
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))) ∧
      TendstoInMeasure μ
        (fun n ω =>
          twoSLSHomoskedasticVHatStar
            (fun i : Fin n => Z i.val ω) (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))
        atTop
        (fun _ =>
          twoSLSHomoskedasticAsymptoticVariance
            (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
            (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
            (errorVariance μ e)) :=
  twoSLSCovariances_tendstoInMeasure_formula_of_textbook12_2_joint_iid_fourth
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
    h.toResidualTextbookFourthConditions

namespace TwoSLSCovarianceFormulaConsistencyConditions

/-- Package form of the Hansen Theorem 12.3 covariance endpoint from primitive
iid Assumption 12.2 plus explicit residual-substitution remainders. -/
theorem of_assumption12_2_iid_remainders
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hr : TwoSLSCovarianceRemainderConditions μ Z X e Y β) :
    TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (errorVariance μ e) := by
  have hpair :=
    twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_iid_remainders
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel hr
  exact ⟨hpair.1, hpair.2⟩

/-- Package form of the Hansen Theorem 12.3 covariance endpoint from primitive
iid Assumption 12.2 plus scalar WLLN conditions for residual-substitution
weights. -/
theorem of_assumption12_2_iid_weight_wlln
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSSplitIidFourthMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hw : TwoSLSCovarianceWeightWLLNConditions μ Z X e) :
    TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (errorVariance μ e) := by
  have hpair :=
    twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_iid_weight_wlln
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel hw
  exact ⟨hpair.1, hpair.2⟩

/-- Package form of the Hansen Theorem 12.3 covariance endpoint from the
single-row iid Assumption 12.2 package plus mixed third/fourth moment
integrability for the exact residual-substitution weights. -/
theorem of_assumption12_2_joint_iid_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidFourthMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOmegaCross : ∀ a b : l, ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j * Z 0 ω a * Z 0 ω b) μ)
    (hOmegaQuadratic : ∀ a b : l, ∀ j m : k,
      Integrable (fun ω => X 0 ω j * X 0 ω m * Z 0 ω a * Z 0 ω b) μ)
    (hSigmaCross : ∀ j : k,
      Integrable (fun ω => e 0 ω * X 0 ω j) μ) :
    TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (errorVariance μ e) := by
  have hpair :=
    twoSLSCovariances_tendstoInMeasure_formula_of_assumption12_2_joint_iid_moments
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      h.toIidFourthConditions β hmodel
      h.joint_iIndep h.joint_identDistrib
      hOmegaCross hOmegaQuadratic hSigmaCross
  exact ⟨hpair.1, hpair.2⟩

/-- Package form of the Hansen Theorem 12.3 covariance endpoint from a
single-row iid Assumption 12.2 mixed-moment package. -/
theorem of_assumption12_2_joint_iid_mixed_moment_conditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    (h : TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions μ Z X e)
    (β : k → ℝ)
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (errorVariance μ e) :=
  TwoSLSResidualJointIidMixedMomentPositiveCovarianceConditions.toCovarianceFormulaConsistencyConditions
    (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h β hmodel

/-- Package form of the Hansen Theorem 12.3 covariance endpoint from the
literal finite-fourth-moment version of Assumption 12.2. -/
theorem of_textbook12_2_joint_iid_fourth
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β0 : k → ℝ}
    (h : TwoSLSResidualJointIidModelFourthMomentPositiveCovarianceConditions μ Z X e Y β0) :
    TwoSLSCovarianceFormulaConsistencyConditions
      μ Z X Y
      (twoSLSCombinedQXZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (twoSLSCombinedQZZ (popGram μ (twoSLSCombinedRegressors Z X)))
      (scoreCovMat μ Z e)
      (twoSLSCombinedQZX (popGram μ (twoSLSCombinedRegressors Z X)))
      (errorVariance μ e) := by
  have hpair :=
    twoSLSCovariances_tendstoInMeasure_formula_of_textbook12_2_joint_iid_fourth
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) h
  exact ⟨hpair.1, hpair.2⟩

end TwoSLSCovarianceFormulaConsistencyConditions

end HansenEconometrics
