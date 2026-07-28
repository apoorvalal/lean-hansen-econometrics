import Mathlib.Probability.CDF
import Mathlib.Probability.CondVar
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.CondDistrib
import HansenEconometrics.MultivariateNormal

/-! # Probability utilities

This module collects reusable probability bridges used across the econometrics chapters:

* `sumSquaresRV`, `standardizedCoords`, and `restrictedStandardizedCoords` support chi-square
  constructions from Gaussian coordinates;
* the `HasLaw.preimage` and CDF lemmas turn distributional identities into probability statements;
* `condExp_apply`, `condExp_apply_apply`, `integral_apply`, and `integral_apply_apply` expose
  coordinatewise conditional-expectation and integration rules;
* `meanVec`, `covVec`, and `covMat` provide finite-dimensional moment notation and algebra;
* `conditioningSpace`, `condExpOn`, `cefErrorOn`, `condVarOn`, and `residualVarOn` form the
  variable-conditioned public API; and
* the multivariate-Gaussian lemmas provide linear-image and independent-coordinate laws.
-/

open MeasureTheory ProbabilityTheory
open Matrix
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix Matrix.Norms.Elementwise

namespace HansenEconometrics

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Sum of squares of a finite family of real-valued random variables. This is the basic random
variable behind chi-square style constructions. -/
def sumSquaresRV [Fintype ι] (X : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ i, (X i ω) ^ 2

private lemma sumSquaresRV_nonneg [Fintype ι] (X : ι → Ω → ℝ) (ω : Ω) :
    0 ≤ sumSquaresRV X ω := by
  unfold sumSquaresRV
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

section StandardizedCoords

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Coordinates of a Euclidean-space random vector in an orthonormal basis, standardized by
`√σ²`. -/
noncomputable def standardizedCoords
    (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n))
    (σ2 : ℝ) (ε : Ω → EuclideanSpace ℝ n) : n → Ω → ℝ :=
  fun i ω => b.repr (ε ω) i / Real.sqrt σ2

/-- Restrict the standardized coordinate family along an index map. No injectivity is needed for
the definition itself; downstream independence results can add it when they need distinct
coordinates. -/
noncomputable def restrictedStandardizedCoords
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n))
    (φ : ι → n) (σ2 : ℝ) (ε : Ω → EuclideanSpace ℝ n) : ι → Ω → ℝ :=
  fun i => standardizedCoords b σ2 ε (φ i)

end StandardizedCoords

/-- Convenient wrapper around Mathlib's jointly-Gaussian + zero-covariance independence lemma for
real-valued pairs. -/
private lemma indep_of_jointGaussian_cov_zero
    {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hcov : cov[X, Y; P] = 0) :
    IndepFun X Y P :=
  hXY.indepFun_of_covariance_eq_zero hcov

/-- Finite-family version of Gaussian independence from pairwise zero covariance. -/
private lemma iIndep_of_jointGaussian_cov_zero [Finite ι]
    {X : ι → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω i => X i ω) P)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; P] = 0) :
    iIndepFun X P :=
  hX.iIndepFun_of_covariance_eq_zero hcov

section ConditionalDistributionHelpers

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {μ : Measure α} {D : α → β} {Y : α → γ} {ν : Measure γ}

/-- If the regular conditional law of `Y` given `D` is a.e. the constant law
`ν`, then the unconditional law of `Y` is `ν`. -/
theorem HasLaw.of_condDistrib_eq_const
    [StandardBorelSpace γ] [Nonempty γ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hD : AEMeasurable D μ) (hY : AEMeasurable Y μ)
    (hcond : condDistrib Y D μ =ᵐ[μ.map D] Kernel.const β ν) :
    HasLaw Y ν μ := by
  refine ⟨hY, ?_⟩
  have hJoint :
      μ.map (fun x => (D x, Y x)) = μ.map D ⊗ₘ Kernel.const β ν :=
    (condDistrib_ae_eq_iff_measure_eq_compProd D hY (Kernel.const β ν)).mp hcond
  have hsnd := congrArg Measure.snd hJoint
  have hleft :
      (μ.map (fun x => (D x, Y x))).snd = μ.map Y := by
    change (μ.map (fun x => (D x, Y x))).map Prod.snd = μ.map Y
    rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
      (hD.prodMk hY)]
    rfl
  have hright :
      (μ.map D ⊗ₘ Kernel.const β ν).snd = ν := by
    haveI : IsProbabilityMeasure (μ.map D) :=
      Measure.isProbabilityMeasure_map hD
    rw [Measure.snd_compProd, Measure.const_comp, measure_univ, one_smul]
  rw [hleft, hright] at hsnd
  exact hsnd

end ConditionalDistributionHelpers

section ConditionalIndependenceIntegration

variable {mc mΩ : MeasurableSpace Ω} [@StandardBorelSpace Ω mΩ]
variable {μ : @Measure Ω mΩ} [IsFiniteMeasure μ]

/-- Conditional independence factors the conditional expectation of an integrable product.
Unlike an `L²`-based formulation, this only requires integrability of the two factors and their
product. -/
private theorem condExp_mul_eq_mul_condExp_of_condIndepFun
    {f g : Ω → ℝ} (hm : mc ≤ mΩ)
    (hfg : CondIndepFun (mΩ := mΩ) mc hm f g μ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg_int : Integrable (fun ω => f ω * g ω) μ) :
    μ[fun ω => f ω * g ω | mc] =ᵐ[μ]
      fun ω => μ[f | mc] ω * μ[g | mc] ω := by
  let f' : Ω → ℝ := hf.aestronglyMeasurable.mk f
  let g' : Ω → ℝ := hg.aestronglyMeasurable.mk g
  have hf'_meas : Measurable f' := hf.aestronglyMeasurable.measurable_mk
  have hg'_meas : Measurable g' := hg.aestronglyMeasurable.measurable_mk
  have hff' : f =ᵐ[μ] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hgg' : g =ᵐ[μ] g' := hg.aestronglyMeasurable.ae_eq_mk
  have hf'_int : Integrable f' μ := hf.congr hff'
  have hg'_int : Integrable g' μ := hg.congr hgg'
  have hff'_cond :
      ∀ᵐ z ∂μ.trim hm, f =ᵐ[condExpKernel μ mc z] f' := by
    apply @Measure.ae_ae_of_ae_comp Ω Ω mc mΩ
      (μ.trim hm) (condExpKernel μ mc) (fun z => f z = f' z)
    rw [condExpKernel_comp_trim hm]
    exact hff'
  have hgg'_cond :
      ∀ᵐ z ∂μ.trim hm, g =ᵐ[condExpKernel μ mc z] g' := by
    apply @Measure.ae_ae_of_ae_comp Ω Ω mc mΩ
      (μ.trim hm) (condExpKernel μ mc) (fun z => g z = g' z)
    rw [condExpKernel_comp_trim hm]
    exact hgg'
  have hfg' : CondIndepFun (mΩ := mΩ) mc hm f' g' μ :=
    Kernel.IndepFun.congr' hfg hff'_cond hgg'_cond
  have hmap :=
    (condIndepFun_iff_map_prod_eq_prod_map_map hf'_meas hg'_meas).mp hfg'
  have hkernel :
      (fun z => ∫ y, f' y * g' y ∂condExpKernel μ mc z) =ᵐ[μ.trim hm]
        fun z =>
          (∫ y, f' y ∂condExpKernel μ mc z) *
            ∫ y, g' y ∂condExpKernel μ mc z := by
    filter_upwards [hmap] with z hz
    have hpair : Measurable (fun y => (f' y, g' y)) :=
      hf'_meas.prodMk hg'_meas
    have hind : IndepFun f' g' (condExpKernel μ mc z) := by
      rw [indepFun_iff_map_prod_eq_prod_map_map
        hf'_meas.aemeasurable hg'_meas.aemeasurable]
      simpa only [Kernel.map_apply _ hpair, Kernel.map_apply _ hf'_meas,
        Kernel.map_apply _ hg'_meas, Kernel.prod_apply] using hz
    exact hind.integral_fun_mul_eq_mul_integral
      hf'_meas.aestronglyMeasurable hg'_meas.aestronglyMeasurable
  have hprod :
      (fun ω => f ω * g ω) =ᵐ[μ] fun ω => f' ω * g' ω := by
    filter_upwards [hff', hgg'] with ω hfω hgω
    rw [hfω, hgω]
  have hf'g'_int : Integrable (fun ω => f' ω * g' ω) μ :=
    hfg_int.congr hprod
  calc
    μ[fun ω => f ω * g ω | mc] =ᵐ[μ]
        μ[fun ω => f' ω * g' ω | mc] := condExp_congr_ae hprod
    _ =ᵐ[μ] (fun z => ∫ y, f' y * g' y ∂condExpKernel μ mc z) :=
      condExp_ae_eq_integral_condExpKernel hm hf'g'_int
    _ =ᵐ[μ] (fun z =>
        (∫ y, f' y ∂condExpKernel μ mc z) *
          ∫ y, g' y ∂condExpKernel μ mc z) :=
      ae_eq_of_ae_eq_trim hkernel
    _ =ᵐ[μ] (fun z => μ[f' | mc] z * μ[g' | mc] z) := by
      filter_upwards [
        (condExp_ae_eq_integral_condExpKernel hm hf'_int).symm,
        (condExp_ae_eq_integral_condExpKernel hm hg'_int).symm
      ] with z hfz hgz
      rw [hfz, hgz]
    _ =ᵐ[μ] (fun ω => μ[f | mc] ω * μ[g | mc] ω) := by
      filter_upwards [condExp_congr_ae hff', condExp_congr_ae hgg'] with ω hfω hgω
      rw [hfω, hgω]

end ConditionalIndependenceIntegration

section RealDistributionHelpers

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {X : Ω → ℝ} {ν : Measure ℝ}

/-- If `X` has law `ν`, then the probability of any measurable event of the form `X ∈ s` is just
the mass of `s` under `ν`. -/
theorem HasLaw.preimage_eq
    (hX : HasLaw X ν μ) {s : Set ℝ} (hs : MeasurableSet s) :
    μ (X ⁻¹' s) = ν s := by
  rw [← hX.map_eq, Measure.map_apply_of_aemeasurable hX.aemeasurable hs]

/-- Real-valued version of `HasLaw.preimage_eq`, expressed with `Measure.real`. -/
theorem HasLaw.real_preimage_eq
    (hX : HasLaw X ν μ) {s : Set ℝ} (hs : MeasurableSet s) :
    μ.real (X ⁻¹' s) = ν.real s := by
  rw [measureReal_def, HasLaw.preimage_eq hX hs, measureReal_def]

/-- If `X` has law `ν`, then the lower-tail event `{X ≤ x}` has probability `cdf ν x`. -/
theorem HasLaw.real_preimage_Iic_eq_cdf
    [IsProbabilityMeasure ν]
    (hX : HasLaw X ν μ) (x : ℝ) :
    μ.real (X ⁻¹' Set.Iic x) = cdf ν x := by
  rw [HasLaw.real_preimage_eq hX measurableSet_Iic, ProbabilityTheory.cdf_eq_real]

/-- If `X` has law `ν`, then interval events for `X` can be read directly from `ν`. -/
theorem HasLaw.real_preimage_Icc_eq
    (hX : HasLaw X ν μ) (a b : ℝ) :
    μ.real (X ⁻¹' Set.Icc a b) = ν.real (Set.Icc a b) := by
  exact HasLaw.real_preimage_eq hX measurableSet_Icc

/-- The symmetric event `|X| ≤ c` is the same as `X ∈ [-c, c]`, so its probability can be read
from the law of `X`. -/
theorem HasLaw.real_preimage_abs_le_eq_Icc
    (hX : HasLaw X ν μ) (c : ℝ) :
    μ.real {ω | |X ω| ≤ c} = ν.real (Set.Icc (-c) c) := by
  rw [show {ω | |X ω| ≤ c} = X ⁻¹' Set.Icc (-c) c by
    ext ω
    simp [abs_le]]
  exact HasLaw.real_preimage_Icc_eq hX (-c) c

/-- For a real probability measure, the mass of `(a, b]` is the cdf increment `F(b) - F(a)`. -/
theorem measureReal_Ioc_eq_cdf_sub
    [IsProbabilityMeasure ν] {a b : ℝ} (hab : a ≤ b) :
    ν.real (Set.Ioc a b) = cdf ν b - cdf ν a := by
  calc
    ν.real (Set.Ioc a b) = ((cdf ν).measure).real (Set.Ioc a b) := by
      rw [ProbabilityTheory.measure_cdf (μ := ν)]
    _ = cdf ν b - cdf ν a := by
      rw [measureReal_def, StieltjesFunction.measure_Ioc, ENNReal.toReal_ofReal]
      exact (sub_nonneg).2 ((ProbabilityTheory.monotone_cdf ν) hab)

/-- For a real probability measure, the mass of `[a, b]` is `F(b)` minus the left limit at `a`. -/
theorem measureReal_Icc_eq_cdf_sub_leftLim
    [IsProbabilityMeasure ν] {a b : ℝ} (hab : a ≤ b) :
    ν.real (Set.Icc a b) = cdf ν b - Function.leftLim (cdf ν) a := by
  calc
    ν.real (Set.Icc a b) = ((cdf ν).measure).real (Set.Icc a b) := by
      rw [ProbabilityTheory.measure_cdf (μ := ν)]
    _ = cdf ν b - Function.leftLim (cdf ν) a := by
      rw [measureReal_def, StieltjesFunction.measure_Icc, ENNReal.toReal_ofReal]
      exact (sub_nonneg).2 ((ProbabilityTheory.monotone_cdf ν).leftLim_le hab)

/-- CDF version of `HasLaw.real_preimage_abs_le_eq_Icc` for probability measures. -/
theorem HasLaw.real_preimage_abs_le_eq_cdf_sub_leftLim
    [IsProbabilityMeasure ν]
    (hX : HasLaw X ν μ) {c : ℝ} (hc : 0 ≤ c) :
    μ.real {ω | |X ω| ≤ c} = cdf ν c - Function.leftLim (cdf ν) (-c) := by
  rw [HasLaw.real_preimage_abs_le_eq_Icc hX c]
  simpa using measureReal_Icc_eq_cdf_sub_leftLim (ν := ν) (a := -c) (b := c) (by linarith)

/-- For an atomless real probability measure, the mass of `[a, b]` is the cdf increment
`F(b) - F(a)`. -/
theorem measureReal_Icc_eq_cdf_sub_of_noAtoms
    [IsProbabilityMeasure ν] [NoAtoms ν] {a b : ℝ} (hab : a ≤ b) :
    ν.real (Set.Icc a b) = cdf ν b - cdf ν a := by
  have hleft :
      Function.leftLim (cdf ν) a = cdf ν a := by
    have hzero : ENNReal.ofReal (cdf ν a - Function.leftLim (cdf ν) a) = 0 := by
      calc
        ENNReal.ofReal (cdf ν a - Function.leftLim (cdf ν) a)
            = (cdf ν).measure {a} := by
              rw [StieltjesFunction.measure_singleton]
        _ = ν {a} := by
              rw [ProbabilityTheory.measure_cdf (μ := ν)]
        _ = 0 := by
              simp
    have hle : cdf ν a - Function.leftLim (cdf ν) a ≤ 0 := ENNReal.ofReal_eq_zero.mp hzero
    have hleft_le : Function.leftLim (cdf ν) a ≤ cdf ν a :=
      (ProbabilityTheory.monotone_cdf ν).leftLim_le le_rfl
    have hcdf_le : cdf ν a ≤ Function.leftLim (cdf ν) a := by linarith
    exact le_antisymm hleft_le hcdf_le
  rw [measureReal_Icc_eq_cdf_sub_leftLim (ν := ν) hab, hleft]

/-- ENNReal-valued form of `measureReal_Icc_eq_cdf_sub_of_noAtoms`. -/
theorem measure_Icc_eq_ofReal_cdf_sub_of_noAtoms
    [IsProbabilityMeasure ν] [NoAtoms ν] {a b : ℝ} (hab : a ≤ b) :
    ν (Set.Icc a b) = ENNReal.ofReal (cdf ν b - cdf ν a) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top ν (Set.Icc a b)), ← Measure.real_def,
    measureReal_Icc_eq_cdf_sub_of_noAtoms (ν := ν) hab]

/-- If `X` has an atomless real probability law `ν`, then closed-interval events for `X` can be
read off directly from the cdf increment of `ν`. -/
theorem HasLaw.real_preimage_Icc_eq_cdf_sub_of_noAtoms
    [IsProbabilityMeasure ν] [NoAtoms ν]
    (hX : HasLaw X ν μ) {a b : ℝ} (hab : a ≤ b) :
    μ.real (X ⁻¹' Set.Icc a b) = cdf ν b - cdf ν a := by
  rw [HasLaw.real_preimage_Icc_eq hX, measureReal_Icc_eq_cdf_sub_of_noAtoms (ν := ν) hab]

/-- ENNReal-valued form of `HasLaw.real_preimage_Icc_eq_cdf_sub_of_noAtoms`. -/
theorem HasLaw.preimage_Icc_eq_ofReal_cdf_sub_of_noAtoms
    [IsProbabilityMeasure ν] [NoAtoms ν]
    (hX : HasLaw X ν μ) {a b : ℝ} (hab : a ≤ b) :
    μ (X ⁻¹' Set.Icc a b) = ENNReal.ofReal (cdf ν b - cdf ν a) := by
  rw [HasLaw.preimage_eq hX measurableSet_Icc,
    measure_Icc_eq_ofReal_cdf_sub_of_noAtoms (ν := ν) hab]

end RealDistributionHelpers

section ConditionalExpectationHelpers

variable {Ω ι κ E : Type*}
variable {m m₀ : MeasurableSpace Ω}
variable {μ : @Measure Ω m₀}
variable [Fintype ι] [Fintype κ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Coordinate projection commutes with conditional expectation for finite-dimensional
real-valued random vectors. -/
theorem condExp_apply
    {f : Ω → ι → E}
    (hf : Integrable f μ) (i : ι) :
    (fun ω => μ[f | m] ω i) =ᵐ[μ] μ[(fun ω => f ω i) | m] := by
  simpa using
    (ContinuousLinearMap.proj (R := ℝ) i).comp_condExp_comm
      (μ := μ) (m := m) (f := f) hf

/-- Applying two coordinate projections in succession commutes with conditional expectation for
finite-dimensional real-valued arrays. -/
theorem condExp_apply_apply
    {f : Ω → ι → κ → ℝ}
    (hf : Integrable f μ) (i : ι) (j : κ) :
    (fun ω => μ[f | m] ω i j) =ᵐ[μ] μ[(fun ω => f ω i j) | m] := by
  have houter :
      (fun ω => μ[f | m] ω i j) =ᵐ[μ] fun ω => μ[(fun ω => f ω i) | m] ω j := by
    filter_upwards [condExp_apply (m := m) (μ := μ) (f := f) hf i] with ω hω
    exact congrFun hω j
  exact houter.trans <|
    condExp_apply (m := m) (μ := μ) (ι := κ) (f := fun ω => f ω i) (Integrable.eval hf i) j

/-- Coordinate projection commutes with integration for finite-dimensional real-valued random
vectors. -/
theorem integral_apply
    {f : Ω → ι → E}
    (hf : Integrable f μ) (i : ι) :
    (∫ ω, f ω ∂μ) i = ∫ ω, f ω i ∂μ := by
  simpa using
    MeasureTheory.eval_integral (μ := μ) (f := f) (hf := fun j => Integrable.eval hf j) i

/-- Applying two coordinate projections in succession commutes with integration for
finite-dimensional real-valued arrays. -/
theorem integral_apply_apply
    {f : Ω → ι → κ → ℝ}
    (hf : Integrable f μ) (i : ι) (j : κ) :
    (∫ ω, f ω ∂μ) i j = ∫ ω, f ω i j ∂μ := by
  calc
    (∫ ω, f ω ∂μ) i j = (∫ ω, f ω i ∂μ) j := by
      exact congrFun (integral_apply (μ := μ) (f := f) hf i) j
    _ = ∫ ω, f ω i j ∂μ := by
      exact integral_apply (μ := μ) (f := fun ω => f ω i) (Integrable.eval hf i) j

end ConditionalExpectationHelpers

/-- Continuous linear map given by fixed matrix multiplication on the left and
right. -/
noncomputable def matrixLeftRightContinuousLinearMap
    {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a b ℝ) (B : Matrix c d ℝ) :
    Matrix b c ℝ →L[ℝ] Matrix a d ℝ :=
  ({ toFun := fun M => A * M * B
     map_add' := by
       intro M N
       ext i j
       simp [Matrix.mul_apply, Finset.sum_add_distrib, add_mul, mul_add]
     map_smul' := by
       intro r M
       ext i j
       simp [Matrix.mul_apply, Finset.mul_sum, mul_comm, mul_left_comm] } :
      Matrix b c ℝ →ₗ[ℝ] Matrix a d ℝ).toContinuousLinearMap

@[simp]
theorem matrixLeftRightContinuousLinearMap_apply
    {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a b ℝ) (B : Matrix c d ℝ) (M : Matrix b c ℝ) :
    matrixLeftRightContinuousLinearMap A B M = A * M * B :=
  rfl

section MatrixIntegrationHelpers

open Matrix

variable {Ω ι κ ν : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable [Fintype ι] [Fintype κ] [Fintype ν]

/-- Integrability is preserved by right multiplication by a constant real
matrix. -/
theorem integrable_matrix_mul_const
    {F : Ω → Matrix ι κ ℝ} (hF : Integrable F μ)
    (C : Matrix κ ν ℝ) :
    Integrable (fun ω => F ω * C) μ := by
  classical
  simpa using
    (matrixLeftRightContinuousLinearMap (1 : Matrix ι ι ℝ) C).integrable_comp hF

/-- Integration commutes with right multiplication by a constant real
matrix. -/
theorem integral_matrix_mul_const
    {F : Ω → Matrix ι κ ℝ} (hF : Integrable F μ)
    (C : Matrix κ ν ℝ) :
    ∫ ω, F ω * C ∂μ = (∫ ω, F ω ∂μ) * C := by
  classical
  simpa using
    (matrixLeftRightContinuousLinearMap (1 : Matrix ι ι ℝ) C).integral_comp_comm hF

/-- Integrability is preserved by left multiplication by a constant real
matrix. -/
theorem integrable_const_mul_matrix
    (C : Matrix ι κ ℝ) {F : Ω → Matrix κ ν ℝ}
    (hF : Integrable F μ) :
    Integrable (fun ω => C * F ω) μ := by
  classical
  simpa using
    (matrixLeftRightContinuousLinearMap C (1 : Matrix ν ν ℝ)).integrable_comp hF

/-- Integration commutes with left multiplication by a constant real
matrix. -/
theorem integral_const_mul_matrix
    (C : Matrix ι κ ℝ) {F : Ω → Matrix κ ν ℝ}
    (hF : Integrable F μ) :
    ∫ ω, C * F ω ∂μ = C * ∫ ω, F ω ∂μ := by
  classical
  simpa using
    (matrixLeftRightContinuousLinearMap C (1 : Matrix ν ν ℝ)).integral_comp_comm hF

end MatrixIntegrationHelpers

section MeanCovariance

open Matrix

variable {Ω k : Type*}
variable {mΩ : MeasurableSpace Ω}
variable {μ : Measure Ω}
variable [Fintype k]

/-- Population mean of a finite-dimensional random vector. -/
noncomputable def meanVec (μ : Measure Ω) (X : Ω → k → ℝ) : k → ℝ :=
  ∫ ω, X ω ∂μ

/-- Population covariance vector between a regressor vector `X` and a scalar outcome `Y`. -/
noncomputable def covVec (μ : Measure Ω) (X : Ω → k → ℝ) (Y : Ω → ℝ) : k → ℝ :=
  fun i => cov[fun ω => X ω i, Y; μ]

/-- Population covariance matrix of a finite-dimensional regressor vector `X`. -/
noncomputable def covMat (μ : Measure Ω) (X : Ω → k → ℝ) : Matrix k k ℝ :=
  fun i j => cov[fun ω => X ω i, fun ω => X ω j; μ]

omit [Fintype k] in
/-- Covariance is invariant under a.e. equality of both scalar arguments. -/
theorem covariance_congr_ae
    {X₁ X₂ Y₁ Y₂ : Ω → ℝ}
    (hX : X₁ =ᵐ[μ] X₂) (hY : Y₁ =ᵐ[μ] Y₂) :
    cov[X₁, Y₁; μ] = cov[X₂, Y₂; μ] := by
  have hmeanX : μ[X₁] = μ[X₂] := integral_congr_ae hX
  have hmeanY : μ[Y₁] = μ[Y₂] := integral_congr_ae hY
  rw [ProbabilityTheory.covariance]
  exact integral_congr_ae <| by
    filter_upwards [hX, hY] with ω hx hy
    simp [hx, hy, hmeanX, hmeanY]

omit [Fintype k] in
/-- The finite-dimensional covariance matrix is invariant under a.e. equality
of the underlying random vector. -/
theorem covMat_congr_ae
    {X Y : Ω → k → ℝ} (h : X =ᵐ[μ] Y) :
    covMat μ X = covMat μ Y := by
  ext i j
  exact covariance_congr_ae
    (h.mono fun _ hω => congrFun hω i)
    (h.mono fun _ hω => congrFun hω j)

omit [Fintype k] in
/-- A scalar fourth moment supplies the corresponding `L⁴` fact. -/
theorem scalar_memLp_four_of_integrable_fourth
    [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf_meas : AEStronglyMeasurable f μ)
    (hf_four : Integrable (fun ω => f ω ^ 4) μ) :
    MemLp f 4 μ := by
  rw [← integrable_norm_rpow_iff (μ := μ) hf_meas (by norm_num) (by norm_num)]
  convert hf_four using 1
  ext ω
  simpa [Real.norm_eq_abs] using (show Even (4 : ℕ) by decide).pow_abs (f ω)

omit [Fintype k] in
/-- Two scalar `L⁴` random variables have an `L²` product. -/
theorem mul_memLp_two_of_memLp_four
    [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : MemLp f 4 μ) (hg : MemLp g 4 μ) :
    MemLp (fun ω => f ω * g ω) 2 μ := by
  haveI : ENNReal.HolderTriple (4 : ℝ≥0∞) (4 : ℝ≥0∞) (2 : ℝ≥0∞) := by
    have hreal : Real.HolderTriple (4 : ℝ) (4 : ℝ) (2 : ℝ) := by
      refine ⟨?_, by norm_num, by norm_num⟩
      norm_num [inv_eq_one_div]
    simpa using (Real.HolderTriple.ennrealOfReal hreal)
  simpa [Pi.mul_apply, mul_comm] using hf.mul hg

omit [Fintype k] in
/-- Two scalar `L⁴` random variables have an integrable product. -/
theorem integrable_mul_of_memLp_four
    [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : MemLp f 4 μ) (hg : MemLp g 4 μ) :
    Integrable (fun ω => f ω * g ω) μ :=
  memLp_one_iff_integrable.mp
    ((mul_memLp_two_of_memLp_four (μ := μ) hf hg).mono_exponent one_le_two)

/-- A finite-dimensional fourth row-norm moment supplies fourth moments for
each coordinate. -/
theorem coordinate_memLp_four_of_integrable_norm_fourth
    [IsProbabilityMeasure μ] {X : Ω → k → ℝ}
    (hX : AEStronglyMeasurable X μ)
    (hNorm4 : Integrable (fun ω => ‖X ω‖ ^ 4) μ)
    (j : k) :
    MemLp (fun ω => X ω j) 4 μ := by
  have hXj : AEStronglyMeasurable (fun ω => X ω j) μ :=
    (continuous_apply j).comp_aestronglyMeasurable hX
  refine scalar_memLp_four_of_integrable_fourth hXj ?_
  refine hNorm4.mono' (hXj.aemeasurable.pow_const 4).aestronglyMeasurable
    (ae_of_all μ fun ω => ?_)
  have hxj : |X ω j| ≤ ‖X ω‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (X ω) j
  calc
    ‖X ω j ^ 4‖ = |X ω j| ^ 4 := by
      simp [Real.norm_eq_abs]
    _ ≤ ‖X ω‖ ^ 4 := by
      gcongr

/-- A finite-dimensional fourth row-norm moment supplies an `L⁴` bound for any
fixed linear index. -/
theorem dotProduct_memLp_four_of_integrable_norm_fourth
    [IsProbabilityMeasure μ] {X : Ω → k → ℝ}
    (hX : AEStronglyMeasurable X μ)
    (hNorm4 : Integrable (fun ω => ‖X ω‖ ^ 4) μ)
    (b : k → ℝ) :
    MemLp (fun ω => dotProduct (X ω) b) 4 μ := by
  classical
  convert (memLp_finset_sum' (s := Finset.univ)
    (f := fun j ω => X ω j * b j)
    (fun j _ =>
      (coordinate_memLp_four_of_integrable_norm_fourth
        (μ := μ) (X := X) hX hNorm4 j).mul_const (b j))) using 1
  ext ω
  simp [dotProduct]

/-- Coordinate `L⁴` bounds imply integrability of the finite-dimensional outer
product. -/
theorem vecMulVec_integrable_of_coordinate_memLp_four
    [IsProbabilityMeasure μ] {X : Ω → k → ℝ}
    (hX : ∀ j : k, MemLp (fun ω => X ω j) 4 μ) :
    Integrable (fun ω => Matrix.vecMulVec (X ω) (X ω)) μ := by
  classical
  refine Integrable.of_eval ?_
  intro a
  refine Integrable.of_eval ?_
  intro b
  have ha : MemLp (fun ω => X ω a) 2 μ :=
    (hX a).mono_exponent (by norm_num)
  have hb : MemLp (fun ω => X ω b) 2 μ :=
    (hX b).mono_exponent (by norm_num)
  simpa [Matrix.vecMulVec_apply] using ha.integrable_mul hb

omit [Fintype k] in
/-- A coordinate covariance matrix is Hermitian, equivalently symmetric over `ℝ`. -/
theorem covMat_isHermitian (μ : Measure Ω) (X : Ω → k → ℝ) :
    (covMat μ X).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [covMat, ProbabilityTheory.covariance_comm]

/-- Identically distributed finite-dimensional vectors have matching coordinate covariances. -/
theorem identDistrib_covariance_apply_eq
    {Ω' k : Type*} [MeasurableSpace Ω']
    {ν : Measure Ω'} {X : Ω → k → ℝ} {Y : Ω' → k → ℝ}
    (h : IdentDistrib X Y μ ν) (a b : k) :
    cov[fun ω => X ω a, fun ω => X ω b; μ] =
      cov[fun ω => Y ω a, fun ω => Y ω b; ν] := by
  have ha : μ[fun ω => X ω a] = ν[fun ω => Y ω a] := by
    exact (h.comp (by fun_prop : Measurable fun v : k → ℝ => v a)).integral_eq
  have hb : μ[fun ω => X ω b] = ν[fun ω => Y ω b] := by
    exact (h.comp (by fun_prop : Measurable fun v : k → ℝ => v b)).integral_eq
  have hcenter : IdentDistrib
      (fun ω => (X ω a - μ[fun ω => X ω a]) * (X ω b - μ[fun ω => X ω b]))
      (fun ω => (Y ω a - ν[fun ω => Y ω a]) * (Y ω b - ν[fun ω => Y ω b])) μ ν := by
    have hpair := h.comp (by fun_prop : Measurable fun v : k → ℝ => (v a, v b))
    convert hpair.comp (by
      fun_prop : Measurable fun p : ℝ × ℝ =>
        (p.1 - μ[fun ω => X ω a]) * (p.2 - μ[fun ω => X ω b])) using 1
    ext ω
    simp [ha, hb]
  simpa [ProbabilityTheory.covariance] using hcenter.integral_eq

/-- Integrating a linear form equals applying that linear form to the vector mean. -/
theorem integral_dotProduct_eq_meanVec_dotProduct
    (X : Ω → k → ℝ) (b : k → ℝ)
    (hX : ∀ i, Integrable (fun ω => X ω i) μ) :
    ∫ ω, dotProduct (X ω) b ∂μ = meanVec μ X ⬝ᵥ b := by
  simp_rw [dotProduct]
  rw [integral_finset_sum]
  · simp_rw [integral_mul_const]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [show (∫ ω, X ω i ∂μ) = (meanVec μ X) i by
      simpa [meanVec] using (MeasureTheory.eval_integral (μ := μ) (f := X) (hf := hX) i).symm]
  · intro i hi
    exact (hX i).mul_const (b i)

/-- The covariance vector with a linear form equals the covariance matrix times the coefficient
vector. -/
theorem covVec_dotProduct_eq_covMat_mulVec
    [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ) (b : k → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) :
    covVec μ X (fun ω => dotProduct (X ω) b) = covMat μ X *ᵥ b := by
  ext i
  change cov[fun ω => X ω i, fun ω => ∑ j, X ω j * b j; μ] =
    ∑ j, cov[fun ω => X ω i, fun ω => X ω j; μ] * b j
  rw [ProbabilityTheory.covariance_fun_sum_right
      (X := fun j ω => X ω j * b j) (Y := fun ω => X ω i)]
  · simp_rw [ProbabilityTheory.covariance_mul_const_right]
  · intro j
    exact (hX j).mul_const (b j)
  · exact hX i

/-- The variance of a finite-dimensional linear projection is the corresponding covariance
quadratic form. -/
theorem variance_dotProduct_eq_dotProduct_covMat_mulVec
    [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ) (b : k → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ) :
    Var[fun ω => dotProduct (X ω) b; μ] = b ⬝ᵥ (covMat μ X *ᵥ b) := by
  classical
  have hlin : MemLp (fun ω => dotProduct (X ω) b) 2 μ := by
    convert (memLp_finset_sum' (s := Finset.univ)
      (f := fun i ω => X ω i * b i)
      (fun i _ => (hX i).mul_const (b i))) using 1
    ext ω
    simp [dotProduct]
  rw [← ProbabilityTheory.covariance_self hlin.aemeasurable]
  calc
    cov[fun ω => dotProduct (X ω) b, fun ω => dotProduct (X ω) b; μ]
        = ∑ i, cov[fun ω => X ω i * b i, fun ω => dotProduct (X ω) b; μ] := by
          change cov[fun ω => ∑ i, X ω i * b i, fun ω => dotProduct (X ω) b; μ] = _
          rw [ProbabilityTheory.covariance_fun_sum_left]
          · intro i
            exact (hX i).mul_const (b i)
          · exact hlin
    _ = ∑ i, (covMat μ X *ᵥ b) i * b i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [ProbabilityTheory.covariance_mul_const_left]
          have hcov := congrFun
            (covVec_dotProduct_eq_covMat_mulVec (μ := μ) X b hX) i
          simpa [covVec, mul_comm] using congrArg (fun x => x * b i) hcov
    _ = b ⬝ᵥ (covMat μ X *ᵥ b) := by
          simp [dotProduct, mul_comm]

/-- On a finite probability space, the expected squared Euclidean deviation
from the mean is the trace of the coordinate covariance matrix. -/
theorem integral_norm_sq_sub_mean_eq_trace_covMat_euclidean_of_finite
    [Finite Ω] [MeasurableSingletonClass Ω] [IsProbabilityMeasure μ]
    (X : Ω → EuclideanSpace ℝ k) :
    ∫ ω, ‖X ω - ∫ ω, X ω ∂μ‖ ^ 2 ∂μ =
      Matrix.trace (covMat μ (fun ω i => X ω i)) := by
  classical
  have hX_int : Integrable X μ := Integrable.of_finite
  have hmean_apply :
      ∀ i, (∫ ω, X ω ∂μ) i = ∫ ω, X ω i ∂μ := by
    intro i
    have h := (EuclideanSpace.proj i).integral_comp_comm hX_int
    simpa using h.symm
  have hnorm :
      ∀ ω, ‖X ω - ∫ ω, X ω ∂μ‖ ^ 2 =
        ∑ i, (X ω i - ∫ ω, X ω i ∂μ) ^ 2 := by
    intro ω
    calc
      ‖X ω - ∫ ω, X ω ∂μ‖ ^ 2 =
          ∑ i, ((X ω - ∫ ω, X ω ∂μ) i) ^ 2 :=
            EuclideanSpace.real_norm_sq_eq (X ω - ∫ ω, X ω ∂μ)
      _ = ∑ i, (X ω i - ∫ ω, X ω i ∂μ) ^ 2 := by
            simp [hmean_apply]
  calc
    ∫ ω, ‖X ω - ∫ ω, X ω ∂μ‖ ^ 2 ∂μ =
        ∫ ω, ∑ i, (X ω i - ∫ ω, X ω i ∂μ) ^ 2 ∂μ := by
          exact integral_congr_ae (ae_of_all _ hnorm)
    _ = ∑ i, ∫ ω, (X ω i - ∫ ω, X ω i ∂μ) ^ 2 ∂μ := by
          rw [integral_finset_sum]
          intro i _hi
          exact Integrable.of_finite
    _ = ∑ i, Var[fun ω => X ω i; μ] := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact (ProbabilityTheory.variance_eq_integral
            (measurable_of_finite (fun ω => X ω i)).aemeasurable).symm
    _ = Matrix.trace (covMat μ (fun ω i => X ω i)) := by
          rw [Matrix.trace]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact (ProbabilityTheory.covariance_self
            (measurable_of_finite (fun ω => X ω i)).aemeasurable).symm

/-- Covariances in an affine linear model decompose into the fitted part and the residual part. -/
theorem covVec_affineModel
    [IsProbabilityMeasure μ]
    (X : Ω → k → ℝ) (e : Ω → ℝ) (α : ℝ) (β : k → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (he : MemLp e 2 μ) :
    covVec μ X (fun ω => α + dotProduct (X ω) β + e ω) =
      covMat μ X *ᵥ β + covVec μ X e := by
  have hlin : MemLp (fun ω => dotProduct (X ω) β) 2 μ := by
    classical
    convert (memLp_finset_sum' (s := Finset.univ) (f := fun j ω => X ω j * β j)
      (fun j _ => (hX j).mul_const (β j))) using 1
    ext ω
    simp [dotProduct]
  ext i
  change cov[fun ω => X ω i, fun ω => α + dotProduct (X ω) β + e ω; μ] =
    (covMat μ X *ᵥ β) i + cov[fun ω => X ω i, e; μ]
  calc
    cov[fun ω => X ω i, fun ω => α + dotProduct (X ω) β + e ω; μ]
        = cov[fun ω => X ω i, fun ω => α + dotProduct (X ω) β; μ] +
            cov[fun ω => X ω i, e; μ] := by
              change cov[fun ω => X ω i, (fun ω => α + dotProduct (X ω) β) + e; μ] = _
              simpa using
                (ProbabilityTheory.covariance_add_right (X := fun ω => X ω i)
                  (Y := fun ω => α + dotProduct (X ω) β) (Z := e)
                  (hX i) ((memLp_const α).add hlin) he)
    _ = cov[fun ω => X ω i, fun ω => dotProduct (X ω) β; μ] +
          cov[fun ω => X ω i, e; μ] := by
            simpa using
              (ProbabilityTheory.covariance_const_add_right (X := fun ω => X ω i)
                (Y := fun ω => dotProduct (X ω) β) (μ := μ)
                (hlin.integrable (by norm_num)) α)
    _ = (covMat μ X *ᵥ β) i + cov[fun ω => X ω i, e; μ] := by
          rw [show cov[fun ω => X ω i, fun ω => dotProduct (X ω) β; μ] =
              (covMat μ X *ᵥ β) i by
                simpa [covVec] using
                  congrFun (covVec_dotProduct_eq_covMat_mulVec (μ := μ) X β hX) i]

end MeanCovariance

section ConditioningSpaces

variable {Ω β : Type*}
variable [MeasurableSpace β]

/-- The sigma-algebra generated by a conditioning variable `X`. -/
@[reducible] def conditioningSpace (X : Ω → β) : MeasurableSpace Ω :=
  MeasurableSpace.comap X inferInstance

/-- `conditioningSpace X` is a thin wrapper around the standard `comap` construction. -/
@[simp] theorem conditioningSpace_eq_comap (X : Ω → β) :
    conditioningSpace X = MeasurableSpace.comap X inferInstance := rfl

end ConditioningSpaces

section ProbabilityOnRandomVars

variable {Ω β γ E : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace γ]
variable {μ : Measure Ω}

/-- A function is measurable with respect to the sigma-algebra generated by `X`. -/
def XMeasurable [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (X : Ω → β) (g : Ω → E) : Prop :=
  AEStronglyMeasurable[conditioningSpace X] g μ

/-- Conditional expectation of `Y` given a random variable `X`. -/
noncomputable def condExpOn [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) (Y : Ω → E) (X : Ω → β) : Ω → E :=
  μ[Y | conditioningSpace X]

/-- Conditional expectation error `Y - E[Y | X]`. -/
noncomputable def cefErrorOn
    (μ : Measure Ω) (Y : Ω → ℝ) (X : Ω → β) : Ω → ℝ :=
  fun ω => Y ω - condExpOn μ Y X ω

/-- Conditional variance of `Y` given a random variable `X`. -/
noncomputable def condVarOn
    (μ : Measure Ω) (Y : Ω → ℝ) (X : Ω → β) : Ω → ℝ :=
  Var[Y; μ | conditioningSpace X]

/-- Variance of the conditional expectation error after conditioning on `X`. -/
noncomputable def residualVarOn
    (μ : Measure Ω) (Y : Ω → ℝ) (X : Ω → β) : ℝ :=
  Var[cefErrorOn μ Y X; μ]

/-- Conditional expectation with respect to `X` is conditional expectation with respect to the
generated sigma-algebra. -/
@[simp] theorem condExpOn_eq_condExp
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : Ω → E) (X : Ω → β) :
    condExpOn μ Y X = μ[Y | conditioningSpace X] := rfl

/-- The variable-conditioned error is definitionally `Y - E[Y | X]`. -/
@[simp] theorem cefErrorOn_eq_sub
    (Y : Ω → ℝ) (X : Ω → β) :
    cefErrorOn μ Y X = fun ω => Y ω - condExpOn μ Y X ω := rfl

/-- Conditional variance with respect to `X` is conditional variance with respect to `σ(X)`. -/
@[simp] theorem condVarOn_eq_condVar
    (Y : Ω → ℝ) (X : Ω → β) :
    condVarOn μ Y X = Var[Y; μ | conditioningSpace X] := rfl

/-- If `X` is measurable, then the sigma-algebra it generates is a sub-sigma-algebra of the
ambient space. -/
theorem conditioningSpace_le
    {X : Ω → β}
    (hX : Measurable X) :
    conditioningSpace X ≤ (inferInstance : MeasurableSpace Ω) :=
  hX.comap_le

/-- Conditional independence given a random variable factors the conditional
expectation of an integrable product. -/
theorem condExpOn_mul_eq_mul_condExpOn_of_condIndepFun
    [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {Z : Ω → β} {f g : Ω → ℝ}
    (hZ : Measurable Z)
    (hfg : CondIndepFun (conditioningSpace Z) (conditioningSpace_le hZ) f g μ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg_int : Integrable (fun ω => f ω * g ω) μ) :
    condExpOn μ (fun ω => f ω * g ω) Z =ᵐ[μ]
      fun ω => condExpOn μ f Z ω * condExpOn μ g Z ω := by
  simpa [condExpOn] using
    condExp_mul_eq_mul_condExp_of_condIndepFun
      (conditioningSpace_le hZ) hfg hf hg hfg_int

/-- Conditional expectation commutes with multiplication by fixed matrices on
the left and right. -/
theorem condExpOn_matrix_mul_left_right
    {ζ a b c d : Type*} [MeasurableSpace ζ]
    [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    {Z : Ω → ζ} (A : Matrix a b ℝ) (B : Matrix c d ℝ)
    {F : Ω → Matrix b c ℝ} {M : Matrix b c ℝ}
    (hF : Integrable F μ)
    (hcond : condExpOn μ F Z =ᵐ[μ] fun _ => M) :
    condExpOn μ (fun ω => A * F ω * B) Z =ᵐ[μ] fun _ => A * M * B := by
  let T : Matrix b c ℝ →L[ℝ] Matrix a d ℝ :=
    matrixLeftRightContinuousLinearMap A B
  have hcomm :
      T ∘ condExpOn μ F Z =ᵐ[μ] condExpOn μ (T ∘ F) Z := by
    simpa [condExpOn] using
      (T.comp_condExp_comm (μ := μ) (m := conditioningSpace Z) hF)
  have hconst :
      T ∘ condExpOn μ F Z =ᵐ[μ] fun _ => A * M * B := by
    filter_upwards [hcond] with ω hω
    change A * condExpOn μ F Z ω * B = A * M * B
    exact congrArg (fun N => A * N * B) hω
  have htarget : condExpOn μ (T ∘ F) Z =ᵐ[μ] fun _ => A * M * B :=
    hcomm.symm.trans hconst
  simpa [T, Function.comp_def] using htarget

end ProbabilityOnRandomVars

section ConditioningSpaceFactors

variable {Ω β γ : Type*}
variable [MeasurableSpace β] [MeasurableSpace γ]

/-- If `X₁ = f(X₂)` for a measurable map `f`, then conditioning on `X₂` is at least as rich as
conditioning on `X₁`. -/
theorem conditioningSpace_le_of_factor
    {X₁ : Ω → β} {X₂ : Ω → γ} {f : γ → β}
    (hf : Measurable f)
    (hX : X₁ = f ∘ X₂) :
    conditioningSpace X₁ ≤ conditioningSpace X₂ := by
  have hX₂_meas : Measurable[conditioningSpace X₂] X₂ :=
    Measurable.of_comap_le le_rfl
  have hmeas : Measurable[conditioningSpace X₂] X₁ := by
    rw [hX]
    exact hf.comp hX₂_meas
  exact hmeas.comap_le

end ConditioningSpaceFactors

section MultivariateGaussian

variable {n : Type*}
variable [Fintype n] [DecidableEq n]

private theorem continuousLinearMap_mean_multivariateGaussian_zero
    {S : Matrix n n ℝ} (L : EuclideanSpace ℝ n →L[ℝ] ℝ) :
    (multivariateGaussian 0 S)[L] = 0 := by
  rw [ContinuousLinearMap.integral_comp_id_comm]
  · simp [integral_id_multivariateGaussian]
  · exact IsGaussian.integrable_id (μ := multivariateGaussian 0 S)

/-- A fixed dot-product projection of a centered multivariate Gaussian is a
one-dimensional Gaussian with variance given by the matching quadratic form. -/
theorem hasLaw_multivariateGaussian_zero_dotProduct
    {S : Matrix n n ℝ} (hS : S.PosSemidef) (a : n → ℝ) :
    HasLaw (fun z : EuclideanSpace ℝ n => z.ofLp ⬝ᵥ a)
      (gaussianReal 0 (a ⬝ᵥ (S *ᵥ a)).toNNReal) (multivariateGaussian 0 S) := by
  let u : EuclideanSpace ℝ n := WithLp.toLp 2 a
  let L : EuclideanSpace ℝ n →L[ℝ] ℝ := (innerSL ℝ) u
  have hEq := IsGaussian.map_eq_gaussianReal (μ := multivariateGaussian 0 S) L
  have hMean : (multivariateGaussian 0 S)[L] = 0 :=
    continuousLinearMap_mean_multivariateGaussian_zero L
  have hVar : Var[L; multivariateGaussian 0 S] = a ⬝ᵥ (S *ᵥ a) := by
    have hLfun : (⇑L : EuclideanSpace ℝ n → ℝ) = fun x => inner ℝ u x := by
      rfl
    rw [← covariance_self (Measurable.aemeasurable <| by fun_prop), hLfun,
      ← covarianceBilin_apply_eq_cov]
    · calc
        covarianceBilin (multivariateGaussian 0 S) u u = u ⬝ᵥ (S *ᵥ u) := by
          rw [covarianceBilin_multivariateGaussian hS]
        _ = a ⬝ᵥ (S *ᵥ a) := by
          simp [u]
    · exact IsGaussian.memLp_two_id (μ := multivariateGaussian 0 S)
  rw [hMean, hVar] at hEq
  refine ⟨by fun_prop, ?_⟩
  rw [show (fun z : EuclideanSpace ℝ n => z.ofLp ⬝ᵥ a) = L by
    funext z
    change z.ofLp ⬝ᵥ a = inner ℝ (WithLp.toLp 2 a : EuclideanSpace ℝ n) z
    calc
      z.ofLp ⬝ᵥ a =
          inner ℝ (WithLp.toLp 2 a : EuclideanSpace ℝ n) (WithLp.toLp 2 z.ofLp) := by
        simpa using (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := n) a z.ofLp).symm
      _ = inner ℝ (WithLp.toLp 2 a : EuclideanSpace ℝ n) z := by simp,
    hEq]

/-- A fixed matrix image of a centered multivariate Gaussian is a centered
multivariate Gaussian with covariance `R S Rᵀ`. -/
theorem hasLaw_multivariateGaussian_zero_linearMap
    {q : Type*} [Fintype q] [DecidableEq q]
    {S : Matrix n n ℝ} (hS : S.PosSemidef) (R : Matrix q n ℝ) :
    HasLaw
      (fun z : EuclideanSpace ℝ n => WithLp.toLp 2 (R *ᵥ z.ofLp))
      (multivariateGaussian 0 (R * S * Rᵀ))
      (multivariateGaussian 0 S) := by
  simpa [matrixContinuousLinearMap, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hasLaw_affine_multivariateGaussian
      (Ω := EuclideanSpace ℝ n) (P := multivariateGaussian 0 S) (X := id)
      (μ := 0) (S := S) hS ProbabilityTheory.HasLaw.id (0 : EuclideanSpace ℝ q) R

set_option maxHeartbeats 800000 in
-- Expanding the generic Gaussian covariance calculation is elaboration-intensive.
/-- Orthogonal fixed matrix images of an isotropic Gaussian vector are independent.

The matrix condition `A * Bᵀ = 0` is exactly the zero cross-covariance condition. This is the
shared Gaussian engine behind the OLS coefficient/residual and F-numerator/residual independence
arguments in Chapter 5. -/
theorem matrixMulVec_indepFun_of_mul_transpose_eq_zero
    {p q : Type*} [Finite p] [Finite q]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Matrix p n ℝ) (B : Matrix q n ℝ) (hAB : A * Bᵀ = 0)
    {σ2 : ℝ} (hσ2 : 0 < σ2) (ε : Ω → EuclideanSpace ℝ n)
    (hε : HasLaw ε (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    (fun ω => A *ᵥ WithLp.ofLp (ε ω)) ⟂ᵢ[μ]
      (fun ω => B *ᵥ WithLp.ofLp (ε ω)) := by
  letI := Fintype.ofFinite p
  letI := Fintype.ofFinite q
  classical
  let Amap : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ p :=
    (Matrix.toEuclideanLin A).toContinuousLinearMap
  let Bmap : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ q :=
    (Matrix.toEuclideanLin B).toContinuousLinearMap
  let AX : Ω → EuclideanSpace ℝ p := fun ω => Amap (ε ω)
  let BX : Ω → EuclideanSpace ℝ q := fun ω => Bmap (ε ω)
  have hJoint : HasGaussianLaw (fun ω => (AX ω, BX ω)) μ := by
    simpa [AX, BX, Amap, Bmap] using hε.hasGaussianLaw.map_fun (Amap.prod Bmap)
  have hS :
      (((σ2 : ℝ) • (1 : Matrix n n ℝ)) : Matrix n n ℝ).PosSemidef := by
    simpa [smul_one_eq_diagonal] using
      (Matrix.PosSemidef.diagonal (n := n) (d := fun _ => σ2) fun _ => hσ2.le)
  have hBadjointLin :
      (Matrix.toEuclideanLin B).adjoint = Matrix.toEuclideanLin Bᵀ := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := B)).symm
  have hBadjoint :
      Bmap.adjoint = (Matrix.toEuclideanLin Bᵀ).toContinuousLinearMap := by
    simpa [Bmap, LinearMap.adjoint_toContinuousLinearMap] using
      congrArg LinearMap.toContinuousLinearMap hBadjointLin
  have hcomp : Amap ∘L Bmap.adjoint = 0 := by
    rw [hBadjoint]
    ext z i
    simpa [Amap, Matrix.mulVec_mulVec] using
      congrArg (fun C : Matrix p q ℝ => (C *ᵥ WithLp.ofLp z) i) hAB
  have hCov :
      ∀ x y,
        cov[fun ω => inner ℝ x (AX ω), fun ω => inner ℝ y (BX ω); μ] = 0 := by
    intro x y
    have hcomp_apply : Amap (Bmap.adjoint y) = 0 := by
      simpa using congrArg
        (fun T : EuclideanSpace ℝ q →L[ℝ] EuclideanSpace ℝ p => T y) hcomp
    have hcov :=
      hε.covariance_fun_comp
        (f := fun z : EuclideanSpace ℝ n => inner ℝ x (Amap z))
        (g := fun z : EuclideanSpace ℝ n => inner ℝ y (Bmap z))
        (by fun_prop) (by fun_prop)
    have hAfun :
        (fun z : EuclideanSpace ℝ n => inner ℝ x (Amap z)) =
          fun z => inner ℝ (Amap.adjoint x) z := by
      ext z
      simpa [Amap] using (Amap.adjoint_inner_left z x).symm
    have hBfun :
        (fun z : EuclideanSpace ℝ n => inner ℝ y (Bmap z)) =
          fun z => inner ℝ (Bmap.adjoint y) z := by
      ext z
      simpa [Bmap] using (Bmap.adjoint_inner_left z y).symm
    have hmem :
        MemLp id 2 (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) :=
      IsGaussian.memLp_two_id
    calc
      cov[fun ω => inner ℝ x (AX ω), fun ω => inner ℝ y (BX ω); μ]
          = cov[fun z : EuclideanSpace ℝ n => inner ℝ (Amap.adjoint x) z,
              fun z : EuclideanSpace ℝ n => inner ℝ (Bmap.adjoint y) z;
                multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))] := by
              simpa [AX, BX, hAfun, hBfun] using hcov
      _ = covarianceBilin (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ)))
            (Amap.adjoint x) (Bmap.adjoint y) := by
              symm
              exact covarianceBilin_apply_eq_cov hmem (Amap.adjoint x) (Bmap.adjoint y)
      _ = (Amap.adjoint x) ⬝ᵥ
            (((σ2 : ℝ) • (1 : Matrix n n ℝ)) *ᵥ (Bmap.adjoint y)) := by
              rw [covarianceBilin_multivariateGaussian hS]
      _ = (σ2 : ℝ) *
            ((Amap.adjoint x : EuclideanSpace ℝ n) ⬝ᵥ (Bmap.adjoint y)) := by
              simp [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
      _ = 0 := by
              have hinner : inner ℝ (Amap.adjoint x) (Bmap.adjoint y) = 0 := by
                calc
                  inner ℝ (Amap.adjoint x) (Bmap.adjoint y) =
                      inner ℝ x (Amap (Bmap.adjoint y)) := by
                        simpa [Amap] using Amap.adjoint_inner_left (Bmap.adjoint y) x
                  _ = 0 := by simp [hcomp_apply]
              have hdot :
                  ((Amap.adjoint x : EuclideanSpace ℝ n) ⬝ᵥ (Bmap.adjoint y)) = 0 := by
                have hdot' :
                    (Bmap.adjoint y).ofLp ⬝ᵥ
                        star (((Amap.adjoint x : EuclideanSpace ℝ n)).ofLp) = 0 := by
                  simpa [EuclideanSpace.inner_eq_star_dotProduct] using hinner
                simpa [dotProduct, Pi.star_apply, conj_trivial, mul_comm] using hdot'
              rw [hdot, mul_zero]
  have hIndEuclid : AX ⟂ᵢ[μ] BX := hJoint.indepFun_of_covariance_inner hCov
  have hIndToLp :
      (fun ω => WithLp.toLp 2 (A *ᵥ WithLp.ofLp (ε ω))) ⟂ᵢ[μ]
        (fun ω => WithLp.toLp 2 (B *ᵥ WithLp.ofLp (ε ω))) := by
    refine IndepFun.congr hIndEuclid ?_ ?_
    · filter_upwards with ω
      simpa [AX, Amap] using (Matrix.toLpLin_apply (p := 2) (q := 2) A (ε ω))
    · filter_upwards with ω
      simpa [BX, Bmap] using (Matrix.toLpLin_apply (p := 2) (q := 2) B (ε ω))
  have hp : Measurable (WithLp.ofLp : EuclideanSpace ℝ p → p → ℝ) :=
    WithLp.measurable_ofLp (p := 2) (X := p → ℝ)
  have hq : Measurable (WithLp.ofLp : EuclideanSpace ℝ q → q → ℝ) :=
    WithLp.measurable_ofLp (p := 2) (X := q → ℝ)
  simpa using
    (IndepFun.comp (φ := (WithLp.ofLp : EuclideanSpace ℝ p → p → ℝ))
      (ψ := (WithLp.ofLp : EuclideanSpace ℝ q → q → ℝ)) hIndToLp hp hq)

/-- In an isotropic multivariate Gaussian, the coordinates in any orthonormal basis, scaled by the
standard deviation, are independent standard normals. This is the bridge from Gaussian vectors to
chi-square arguments in Chapter 5. -/
theorem orthonormalBasis_coords_div_sqrt_iIndep_standardGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n))
    {σ2 : ℝ} (hσ2 : 0 < σ2) (e : Ω → EuclideanSpace ℝ n)
    (he : HasLaw e (multivariateGaussian 0 ((σ2 : ℝ) • (1 : Matrix n n ℝ))) μ) :
    let W : n → Ω → ℝ := fun i ω => (b.repr (e ω)).ofLp i / Real.sqrt σ2
    (∀ i, HasLaw (W i) (gaussianReal 0 1) μ) ∧ ProbabilityTheory.iIndepFun W μ := by
  let Z : n → Ω → ℝ := fun i ω => (b.repr (e ω)).ofLp i
  let S : Matrix n n ℝ := (σ2 : ℝ) • (1 : Matrix n n ℝ)
  have hS : S.PosSemidef := by
    simpa [S, smul_one_eq_diagonal] using
      (Matrix.PosSemidef.diagonal (n := n) (d := fun _ => σ2) fun _ => hσ2.le)
  have hZ_gauss : HasGaussianLaw (fun ω => b.repr (e ω)) μ := by
    let L : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n :=
      b.repr.toContinuousLinearEquiv.toContinuousLinearMap
    simpa [L] using (he.hasGaussianLaw.map_fun L)
  have hdiag (i : n) : (b i).ofLp ⬝ᵥ (b i).ofLp = 1 := by
    calc
      (b i).ofLp ⬝ᵥ (b i).ofLp = ‖b i‖ ^ 2 := by
        simpa [dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq (b i)).symm
      _ = 1 := by nlinarith [b.norm_eq_one i]
  have hmeanZ : ∀ i, μ[Z i] = 0 := by
    intro i
    let Li : EuclideanSpace ℝ n →L[ℝ] ℝ :=
      (EuclideanSpace.proj i).comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap
    rw [show (fun ω => Z i ω) = Li ∘ e by
      funext ω
      simp [Z, Li]]
    rw [he.integral_comp (Measurable.aestronglyMeasurable <| by fun_prop)]
    exact continuousLinearMap_mean_multivariateGaussian_zero Li
  have hcovZ : ∀ i j, cov[Z i, Z j; μ] = if i = j then σ2 else 0 := by
    intro i j
    have hZi : (fun x : EuclideanSpace ℝ n => (b.repr x).ofLp i) =
        fun x => inner ℝ (b i) x := by
      funext x
      simpa using (OrthonormalBasis.repr_apply_apply (b := b) (v := x) (i := i))
    have hZj : (fun x : EuclideanSpace ℝ n => (b.repr x).ofLp j) =
        fun x => inner ℝ (b j) x := by
      funext x
      simpa using (OrthonormalBasis.repr_apply_apply (b := b) (v := x) (i := j))
    rw [he.covariance_fun_comp (f := fun x : EuclideanSpace ℝ n => (b.repr x).ofLp i)
      (g := fun x : EuclideanSpace ℝ n => (b.repr x).ofLp j) (by fun_prop) (by fun_prop), hZi, hZj,
      ← covarianceBilin_apply_eq_cov]
    · rw [covarianceBilin_multivariateGaussian hS]
      by_cases hij : i = j
      · subst hij
        rw [smul_mulVec, one_mulVec, dotProduct_smul]
        simp [hdiag i]
      · rw [smul_mulVec, one_mulVec, dotProduct_smul]
        have hdot : (b i).ofLp ⬝ᵥ (b j).ofLp = 0 := by
          have hInner : inner ℝ (b i) (b j) = 0 := by
            rw [orthonormal_iff_ite.mp b.orthonormal i j]
            simp [hij]
          have htoInner' : inner ℝ (b j) (b i) = (b i).ofLp ⬝ᵥ (b j).ofLp := by
            rw [PiLp.inner_apply, dotProduct]
            refine Finset.sum_congr rfl ?_
            intro a ha
            have hscalar : inner ℝ ((b j).ofLp a) ((b i).ofLp a) =
                (b j).ofLp a * (b i).ofLp a := by
              simpa using (RCLike.inner_apply' ((b j).ofLp a) ((b i).ofLp a))
            simpa [mul_comm] using hscalar
          calc
            (b i).ofLp ⬝ᵥ (b j).ofLp = inner ℝ (b j) (b i) := by
              exact htoInner'.symm
            _ = inner ℝ (b i) (b j) := by rw [real_inner_comm]
            _ = 0 := hInner
        simp [hij, hdot]
    · exact IsGaussian.memLp_two_id (μ := multivariateGaussian 0 S)
  have hZ_gauss_family : HasGaussianLaw (fun ω ↦ (Z · ω)) μ := by
    simpa [Z] using
      hZ_gauss.map_equiv (EuclideanSpace.equiv n ℝ)
  have hZ_indep : ProbabilityTheory.iIndepFun Z μ :=
    hZ_gauss_family.iIndepFun_of_covariance_eq_zero fun i j hij => by
      rw [hcovZ i j, if_neg hij]
  have hW_law : ∀ i, HasLaw (fun ω => Z i ω / Real.sqrt σ2) (gaussianReal 0 1) μ := by
    intro i
    have hZi_law : HasLaw (Z i) (gaussianReal 0 ⟨σ2, hσ2.le⟩) μ := by
      let Li : EuclideanSpace ℝ n →L[ℝ] ℝ :=
        (EuclideanSpace.proj i).comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap
      have hLiMap : (multivariateGaussian 0 S).map Li = gaussianReal 0 ⟨σ2, hσ2.le⟩ := by
        have hEq := IsGaussian.map_eq_gaussianReal (μ := multivariateGaussian 0 S) Li
        have hMean : (multivariateGaussian 0 S)[Li] = 0 :=
          continuousLinearMap_mean_multivariateGaussian_zero Li
        have hVar : Var[Li; multivariateGaussian 0 S] = σ2 := by
          rw [← covariance_self (Measurable.aemeasurable <| by fun_prop),
            show Li = fun x => inner ℝ (b i) x by
              ext x
              simpa [Li] using (OrthonormalBasis.repr_apply_apply (b := b) (v := x) (i := i)),
            ← covarianceBilin_apply_eq_cov]
          · rw [covarianceBilin_multivariateGaussian hS, smul_mulVec, one_mulVec, dotProduct_smul]
            simp [hdiag i]
          · exact IsGaussian.memLp_two_id (μ := multivariateGaussian 0 S)
        rw [hMean, hVar, Real.toNNReal_of_nonneg hσ2.le] at hEq
        simpa using hEq
      refine (HasLaw.comp ⟨by fun_prop, hLiMap⟩ he).congr ?_
      filter_upwards with ω
      simp [Z, Li]
    convert gaussianReal_div_const hZi_law (Real.sqrt σ2) using 2
    · simp
    · ext
      simp [Real.sq_sqrt hσ2.le, hσ2.ne']
  have hW_indep : ProbabilityTheory.iIndepFun (fun i ω => Z i ω / Real.sqrt σ2) μ := by
    exact hZ_indep.comp (fun _ x => x / Real.sqrt σ2) fun _ => measurable_id.div_const _
  change (∀ i, HasLaw (fun ω => Z i ω / Real.sqrt σ2) (gaussianReal 0 1) μ) ∧
      ProbabilityTheory.iIndepFun (fun i ω => Z i ω / Real.sqrt σ2) μ
  exact And.intro hW_law hW_indep

end MultivariateGaussian

section GaussianCoordinates

variable {n : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The coordinates of a standard Gaussian vector in an orthonormal basis are i.i.d. standard
normal. -/
lemma hasLaw_coords_of_stdGaussian
    (b : OrthonormalBasis (Fin n) ℝ E)
    {Z : Ω → E} (hZ : HasLaw Z (stdGaussian E)) :
    (∀ i, HasLaw (fun ω => b.repr (Z ω) i) (gaussianReal 0 1)) ∧
      iIndepFun (fun i ω => b.repr (Z ω) i) := by
  -- Package `b.repr` as a HasLaw via Mathlib's `stdGaussian_map`.
  have hRepr : HasLaw (fun x : E => (b.repr x : EuclideanSpace ℝ (Fin n)))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) (stdGaussian E) :=
    ⟨b.repr.continuous.aemeasurable, stdGaussian_map b.repr⟩
  have hbZ : HasLaw (fun ω => b.repr (Z ω)) (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    hRepr.comp hZ
  -- Bridge from `stdGaussian` on `EuclideanSpace` to `Measure.pi (fun _ => gaussianReal 0 1)`
  -- via the `ofLp` coercion (inverse of `toLp 2`).
  have hm_of : Measurable (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) := by fun_prop
  have hm_to : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) := by fun_prop
  have hOfLp_map : (stdGaussian (EuclideanSpace ℝ (Fin n))).map
        (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))
      = Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
    rw [← map_pi_eq_stdGaussian (ι := Fin n), Measure.map_map hm_of hm_to]
    simp [Function.comp_def]
  have hOfLp : HasLaw (fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    ⟨hm_of.aemeasurable, hOfLp_map⟩
  have hbZ_coord : HasLaw (fun ω => ((b.repr (Z ω)) : Fin n → ℝ))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    hOfLp.comp hbZ
  -- Per-coordinate laws via projection through the product measure.
  have hLaw : ∀ i : Fin n, HasLaw (fun ω => b.repr (Z ω) i) (gaussianReal 0 1) := by
    intro i
    refine ⟨hbZ_coord.aemeasurable.eval i, ?_⟩
    have h1 : (volume : Measure Ω).map (fun ω => b.repr (Z ω) i)
        = ((volume : Measure Ω).map (fun ω => ((b.repr (Z ω)) : Fin n → ℝ))).map
            (fun f : Fin n → ℝ => f i) := by
      rw [AEMeasurable.map_map_of_aemeasurable (measurable_pi_apply i).aemeasurable
        hbZ_coord.aemeasurable]
      rfl
    rw [h1, hbZ_coord.map_eq]
    exact (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq
  -- Independence via the product-measure characterization.
  refine ⟨hLaw, ?_⟩
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hLaw i).aemeasurable)]
  rw [show (fun (ω : Ω) (i : Fin n) => b.repr (Z ω) i)
      = (fun ω => ((b.repr (Z ω)) : Fin n → ℝ)) from rfl]
  rw [hbZ_coord.map_eq]
  congr 1
  funext i
  exact ((hLaw i).map_eq).symm

/-- Finite-index version of `hasLaw_coords_of_stdGaussian`.

The core proof is the `Fin n` theorem above; this wrapper reindexes an arbitrary finite
orthonormal basis through `Fintype.equivFin`, which is the natural shape of matrix eigenbases in
the chapter files. -/
lemma hasLaw_coords_of_stdGaussian_fintype
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E)
    {Z : Ω → E} (hZ : HasLaw Z (stdGaussian E)) :
    (∀ i, HasLaw (fun ω => b.repr (Z ω) i) (gaussianReal 0 1)) ∧
      iIndepFun (fun i ω => b.repr (Z ω) i) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let bFin : OrthonormalBasis (Fin (Fintype.card ι)) ℝ E := b.reindex e
  obtain ⟨hLawFin, hIndepFin⟩ := hasLaw_coords_of_stdGaussian bFin hZ
  have hLaw : ∀ i, HasLaw (fun ω => b.repr (Z ω) i) (gaussianReal 0 1) := by
    intro i
    simpa [bFin, OrthonormalBasis.repr_reindex] using hLawFin (e i)
  have hIndep : iIndepFun (fun i ω => b.repr (Z ω) i) := by
    have hpre := hIndepFin.precomp e.injective
    simpa [bFin, OrthonormalBasis.repr_reindex] using hpre
  exact ⟨hLaw, hIndep⟩

end GaussianCoordinates

end HansenEconometrics
