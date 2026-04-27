import Mathlib.Probability.CDF
import Mathlib.Probability.CondVar
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory
open Matrix
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix

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
private theorem HasLaw.real_preimage_Iic_eq_cdf
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
private theorem measureReal_Ioc_eq_cdf_sub
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
private theorem measureReal_Icc_eq_cdf_sub_of_noAtoms
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

/-- If `X` has an atomless real probability law `ν`, then closed-interval events for `X` can be
read off directly from the cdf increment of `ν`. -/
theorem HasLaw.real_preimage_Icc_eq_cdf_sub_of_noAtoms
    [IsProbabilityMeasure ν] [NoAtoms ν]
    (hX : HasLaw X ν μ) {a b : ℝ} (hab : a ≤ b) :
    μ.real (X ⁻¹' Set.Icc a b) = cdf ν b - cdf ν a := by
  rw [HasLaw.real_preimage_Icc_eq hX, measureReal_Icc_eq_cdf_sub_of_noAtoms (ν := ν) hab]

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
private theorem covVec_dotProduct_eq_covMat_mulVec
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
@[simp] private theorem conditioningSpace_eq_comap (X : Ω → β) :
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
@[simp] private theorem condExpOn_eq_condExp
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : Ω → E) (X : Ω → β) :
    condExpOn μ Y X = μ[Y | conditioningSpace X] := rfl

/-- The variable-conditioned error is definitionally `Y - E[Y | X]`. -/
@[simp] private theorem cefErrorOn_eq_sub
    (Y : Ω → ℝ) (X : Ω → β) :
    cefErrorOn μ Y X = fun ω => Y ω - condExpOn μ Y X ω := rfl

/-- Conditional variance with respect to `X` is conditional variance with respect to `σ(X)`. -/
@[simp] private theorem condVarOn_eq_condVar
    (Y : Ω → ℝ) (X : Ω → β) :
    condVarOn μ Y X = Var[Y; μ | conditioningSpace X] := rfl

/-- If `X` is measurable, then the sigma-algebra it generates is a sub-sigma-algebra of the
ambient space. -/
theorem conditioningSpace_le
    {X : Ω → β}
    (hX : Measurable X) :
    conditioningSpace X ≤ (inferInstance : MeasurableSpace Ω) :=
  hX.comap_le

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

/-- Move a fixed matrix multiplication from the left side of a dot product to the right side. -/
private theorem mulVec_dotProduct_right
    {n : Type*} [Fintype n] {m : Type*} [Fintype m]
    (M : Matrix m n ℝ) (v : n → ℝ) (a : m → ℝ) :
    (M *ᵥ v) ⬝ᵥ a = v ⬝ᵥ (Mᵀ *ᵥ a) := by
  have hvec : a ᵥ* M = Mᵀ *ᵥ a := by
    ext i
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, hvec, dotProduct_comm]

/-- A fixed dot-product projection of a centered multivariate Gaussian is a
one-dimensional Gaussian with variance given by the matching quadratic form. -/
theorem hasLaw_multivariateGaussian_zero_dotProduct
    {S : Matrix n n ℝ} (hS : S.PosSemidef) (a : n → ℝ) :
    HasLaw (fun z : EuclideanSpace ℝ n => z.ofLp ⬝ᵥ a)
      (gaussianReal 0 (a ⬝ᵥ (S *ᵥ a)).toNNReal) (multivariateGaussian 0 S) := by
  let u : EuclideanSpace ℝ n := WithLp.toLp 2 a
  let L : EuclideanSpace ℝ n →L[ℝ] ℝ := (innerSL ℝ) u
  have hEq := IsGaussian.map_eq_gaussianReal (μ := multivariateGaussian 0 S) L
  have hMean : (multivariateGaussian 0 S)[L] = 0 := by
    rw [ContinuousLinearMap.integral_comp_id_comm]
    · simp [L, integral_id_multivariateGaussian]
    · exact IsGaussian.integrable_id (μ := multivariateGaussian 0 S)
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
  let L : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ q :=
    (Matrix.toEuclideanLin R).toContinuousLinearMap
  have hLadjointLin :
      (Matrix.toEuclideanLin R).adjoint = Matrix.toEuclideanLin Rᵀ := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A := R)).symm
  have hLadjoint : L.adjoint = (Matrix.toEuclideanLin Rᵀ).toContinuousLinearMap := by
    simpa [L, LinearMap.adjoint_toContinuousLinearMap] using
      congrArg LinearMap.toContinuousLinearMap hLadjointLin
  have hRSR : (R * S * Rᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.PosSemidef.mul_mul_conjTranspose_same hS R)
  have hMap : (multivariateGaussian 0 S).map L = multivariateGaussian 0 (R * S * Rᵀ) := by
    refine ProbabilityTheory.IsGaussian.ext ?_ ?_
    · change ∫ x, x ∂((multivariateGaussian 0 S).map L) =
          ∫ x, x ∂(multivariateGaussian 0 (R * S * Rᵀ))
      rw [ContinuousLinearMap.integral_id_map]
      · simp [integral_id_multivariateGaussian]
      · exact IsGaussian.integrable_id (μ := multivariateGaussian 0 S)
    · ext x y
      calc
        covarianceBilin ((multivariateGaussian 0 S).map L) x y
            = (Rᵀ *ᵥ x.ofLp) ⬝ᵥ (S *ᵥ (Rᵀ *ᵥ y.ofLp)) := by
                rw [covarianceBilin_map
                  (h := IsGaussian.memLp_two_id (μ := multivariateGaussian 0 S)) L x y]
                rw [hLadjoint, covarianceBilin_multivariateGaussian hS]
                simp
        _ = x.ofLp ⬝ᵥ (R *ᵥ (S *ᵥ (Rᵀ *ᵥ y.ofLp))) := by
              simpa [Matrix.transpose_transpose] using
                (mulVec_dotProduct_right (M := Rᵀ) (v := x.ofLp)
                  (a := S *ᵥ (Rᵀ *ᵥ y.ofLp)))
        _ = x.ofLp ⬝ᵥ ((R * S * Rᵀ) *ᵥ y.ofLp) := by
              simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = covarianceBilin (multivariateGaussian 0 (R * S * Rᵀ)) x y := by
              rw [covarianceBilin_multivariateGaussian hRSR]
  refine ⟨by fun_prop, ?_⟩
  simpa [L] using hMap

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
  have hmeanZ : ∀ i, μ[Z i] = 0 := by
    intro i
    let Li : EuclideanSpace ℝ n →L[ℝ] ℝ :=
      (EuclideanSpace.proj i).comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap
    rw [show (fun ω => Z i ω) = Li ∘ e by
      funext ω
      simp [Z, Li]]
    rw [he.integral_comp (Measurable.aestronglyMeasurable <| by fun_prop)]
    rw [ContinuousLinearMap.integral_comp_id_comm]
    · simp [integral_id_multivariateGaussian]
    · exact IsGaussian.integrable_id (μ := multivariateGaussian 0 S)
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
        have hdot : (b i).ofLp ⬝ᵥ (b i).ofLp = 1 := by
          calc
            (b i).ofLp ⬝ᵥ (b i).ofLp = ‖b i‖ ^ 2 := by
              simpa [dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq (b i)).symm
            _ = 1 := by nlinarith [b.norm_eq_one i]
        simp [hdot]
      · rw [smul_mulVec, one_mulVec, dotProduct_smul]
        have hdot : (b i).ofLp ⬝ᵥ (b j).ofLp = 0 := by
          have hInner : inner ℝ (b i) (b j) = 0 := by
            simpa [hij] using (orthonormal_iff_ite.mp b.orthonormal i j)
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
        have hMean : (multivariateGaussian 0 S)[Li] = 0 := by
          rw [ContinuousLinearMap.integral_comp_id_comm]
          · simp [integral_id_multivariateGaussian]
          · exact IsGaussian.integrable_id (μ := multivariateGaussian 0 S)
        have hVar : Var[Li; multivariateGaussian 0 S] = σ2 := by
          rw [← covariance_self (Measurable.aemeasurable <| by fun_prop), show Li = fun x => inner ℝ (b i) x by
            ext x
            simpa [Li] using (OrthonormalBasis.repr_apply_apply (b := b) (v := x) (i := i))
            , ← covarianceBilin_apply_eq_cov]
          · rw [covarianceBilin_multivariateGaussian hS, smul_mulVec, one_mulVec, dotProduct_smul]
            have hdot : (b i).ofLp ⬝ᵥ (b i).ofLp = 1 := by
              calc
                (b i).ofLp ⬝ᵥ (b i).ofLp = ‖b i‖ ^ 2 := by
                  simpa [dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq (b i)).symm
                _ = 1 := by nlinarith [b.norm_eq_one i]
            simp [hdot]
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

end GaussianCoordinates

end HansenEconometrics
