import Mathlib

open MeasureTheory ProbabilityTheory
open Matrix
open scoped ENNReal Topology MeasureTheory ProbabilityTheory
open scoped Matrix

namespace HansenEconometrics

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Sum of squares of a finite family of real-valued random variables. This is the basic random
variable behind chi-square style constructions. -/
def sumSquaresRV [Fintype ι] (X : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ i, (X i ω) ^ 2

lemma sumSquaresRV_nonneg [Fintype ι] (X : ι → Ω → ℝ) (ω : Ω) :
    0 ≤ sumSquaresRV X ω := by
  unfold sumSquaresRV
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Convenient wrapper around Mathlib's jointly-Gaussian + zero-covariance independence lemma for
real-valued pairs. -/
lemma indep_of_jointGaussian_cov_zero
    {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hcov : cov[X, Y; P] = 0) :
    IndepFun X Y P :=
  hXY.indepFun_of_covariance_eq_zero hcov

/-- Finite-family version of Gaussian independence from pairwise zero covariance. -/
lemma iIndep_of_jointGaussian_cov_zero [Finite ι]
    {X : ι → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω i => X i ω) P)
    (hcov : ∀ i j, i ≠ j → cov[X i, X j; P] = 0) :
    iIndepFun X P :=
  hX.iIndepFun_of_covariance_eq_zero hcov

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

section MeanCovarianceHelpers

variable {Ω k : Type*}
variable [Fintype k]
variable {mΩ : MeasurableSpace Ω}
variable {μ : Measure Ω}

/-- Population mean of a finite-dimensional random vector. -/
noncomputable def meanVec (μ : Measure Ω) (X : Ω → k → ℝ) : k → ℝ :=
  ∫ ω, X ω ∂μ

/-- Population covariance vector between a regressor vector `X` and a scalar outcome `Y`. -/
noncomputable def covVec (μ : Measure Ω) (X : Ω → k → ℝ) (Y : Ω → ℝ) : k → ℝ :=
  fun i => cov[fun ω => X ω i, Y; μ]

/-- Population covariance matrix of a finite-dimensional random vector `X`. -/
noncomputable def covMat (μ : Measure Ω) (X : Ω → k → ℝ) : Matrix k k ℝ :=
  fun i j => cov[fun ω => X ω i, fun ω => X ω j; μ]

/-- Integrating a linear form equals applying that linear form to the vector mean. -/
theorem integral_dotProduct_eq_meanVec_dotProduct
    (X : Ω → k → ℝ) (b : k → ℝ)
    (hX : ∀ i, Integrable (fun ω => X ω i) μ) :
    ∫ ω, dotProduct (X ω) b ∂μ = meanVec μ X ⬝ᵥ b := by
  classical
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
  classical
  ext i
  change cov[fun ω => X ω i, fun ω => ∑ j, X ω j * b j; μ] =
    ∑ j, cov[fun ω => X ω i, fun ω => X ω j; μ] * b j
  rw [ProbabilityTheory.covariance_fun_sum_right
      (X := fun j ω => X ω j * b j) (Y := fun ω => X ω i)]
  · simp_rw [ProbabilityTheory.covariance_mul_const_right]
  · intro j
    exact (hX j).mul_const (b j)
  · exact hX i

end MeanCovarianceHelpers

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

end HansenEconometrics
