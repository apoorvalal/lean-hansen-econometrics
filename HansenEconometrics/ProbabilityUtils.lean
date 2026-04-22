import Mathlib

open MeasureTheory ProbabilityTheory
open Matrix
open scoped ENNReal Topology MeasureTheory ProbabilityTheory

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

section StandardizedCoords

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Coordinates of a Euclidean-space random vector in an orthonormal basis, standardized by
`√σ²`. -/
noncomputable def standardizedCoords
    (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n))
    (σ2 : ℝ) (ε : Ω → EuclideanSpace ℝ n) : n → Ω → ℝ :=
  fun i ω => b.repr (ε ω) i / Real.sqrt σ2

/-- Restrict the standardized coordinate family along an injective index map. -/
noncomputable def restrictedStandardizedCoords
    {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n))
    (φ : ι → n) (σ2 : ℝ) (ε : Ω → EuclideanSpace ℝ n) : ι → Ω → ℝ :=
  fun i => standardizedCoords b σ2 ε (φ i)

end StandardizedCoords

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

section MultivariateGaussian

variable {n : Type*}
variable [Fintype n] [DecidableEq n]

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

end HansenEconometrics
