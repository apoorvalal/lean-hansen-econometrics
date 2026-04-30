import HansenEconometrics.Chapter2CondExp
import HansenEconometrics.Chapter7Asymptotics.Consistency

/-!
# Chapter 7 Asymptotics: Sample Middle Matrices (RobustCovariance, part 1/3)

This file contains the population-layer covariance definitions and the HC0–HC3 sample
middle-matrix definitions used by Chapter 7's robust covariance development.

It was extracted from the former `RobustCovariance.lean` together with
`MiddleConsistency.lean` and `SandwichAssembly.lean`.
-/

open scoped Matrix Real

namespace HansenEconometrics

open Matrix

section Assumption72

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.Elementwise Function Topology ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {n : Type*} [Fintype n]
variable {k : Type*} [Fintype k] [DecidableEq k]

omit [DecidableEq k] in
@[reducible]
private noncomputable def matrixBorelMeasurableSpaceInst :
    MeasurableSpace (Matrix k k ℝ) :=
  matrixBorelMeasurableSpace k k

attribute [local instance] matrixBorelMeasurableSpaceInst

omit [DecidableEq k] in
private lemma matrixBorelSpaceInst : BorelSpace (Matrix k k ℝ) :=
  matrixBorelSpace k k

attribute [local instance] matrixBorelSpaceInst

/-- Descriptive public condition package for the current Lean proof behind Hansen
Assumption 7.2 / Theorem 7.2 / Theorem 7.3.

Mathlib currently supplies a one-dimensional iid CLT. To use it for Hansen's
vector score `eᵢXᵢ`, we ask for full independence of those score vectors and
square integrability of every fixed scalar projection. The resulting theorem is
the scalar-projection/Cramér-Wold face of Hansen Assumption 7.2, rather than a
literal textbook iid encoding. -/
structure ScoreCLTConditions (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    extends LeastSquaresConsistencyConditions μ X e where
  /-- Full independence of the score-vector sequence `e i • X i`. -/
  iIndep_cross : iIndepFun (fun i ω => e i ω • X i ω) μ
  /-- Square integrability of every scalar projection of the score vector. -/
  memLp_cross_projection :
    ∀ a : k → ℝ, MemLp (fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a) 2 μ

/-- Compatibility name for the CLT proof bundle behind `ScoreCLTConditions`. -/
abbrev SampleCLTAssumption72
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) :=
  ScoreCLTConditions μ X e

namespace ScoreCLTConditions

/-- Compatibility projection for code that still names the internal CLT bundle. -/
abbrev toSampleCLTAssumption72
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) :
    SampleCLTAssumption72 μ X e := h

/-- Compatibility constructor from the old internal CLT-bundle name. -/
abbrev ofSample
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) :
    ScoreCLTConditions μ X e := h

end ScoreCLTConditions

omit [DecidableEq k] in
/-- Measurability of a fixed dot-product projection on finite-dimensional vectors. -/
theorem measurable_dotProduct_right (a : k → ℝ) :
    Measurable (fun v : k → ℝ => v ⬝ᵥ a) := by
  classical
  simpa [dotProduct] using
    (continuous_finset_sum Finset.univ
      (fun i _ => (continuous_apply i).mul continuous_const)).measurable

/-- The scalar score projection has mean zero under the orthogonality axiom. -/
theorem scoreProj_integral_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (a : k → ℝ) :
    μ[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a] = 0 := by
  have hdot := integral_dotProduct_eq_meanVec_dotProduct
    (μ := μ) (X := fun ω => e 0 ω • X 0 ω) a
    (fun i => Integrable.eval h.int_cross i)
  simpa [meanVec, h.orthogonality] using hdot

/-- Coordinate square-integrability of the score vector under Assumption 7.2. -/
theorem scoreCoordinate_memLp_two
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (j : k) :
    MemLp (fun ω => (e 0 ω • X 0 ω) j) 2 μ := by
  classical
  have hproj := h.memLp_cross_projection (Pi.single j 1)
  simpa [dotProduct_single_one] using hproj

/-- Vector square-integrability of the score vector under Assumption 7.2. -/
theorem scoreVector_memLp_two
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) :
    MemLp (fun ω => e 0 ω • X 0 ω) 2 μ :=
  MemLp.of_eval (fun j => scoreCoordinate_memLp_two (μ := μ) (X := X) (e := e) h j)

/-- Hansen's score covariance matrix `Ω := Var(e₀X₀)`. Under the population
orthogonality condition this agrees entrywise with `E[e₀² X₀ X₀']`. -/
noncomputable def scoreCovMat
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) : Matrix k k ℝ :=
  covMat μ (fun ω => e 0 ω • X 0 ω)

/-- Scalar asymptotic variance of the projection `a'√n(β̂ₙ - β)`:
`((Q⁻¹)'a)' Ω ((Q⁻¹)'a)`. This avoids needing to prove symmetry of `Q⁻¹`
before stating the scalar CLT in textbook covariance notation. -/
noncomputable def olsProjectionAsymVar
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    (a : k → ℝ) : ℝ :=
  let b := ((popGram μ X)⁻¹)ᵀ *ᵥ a
  b ⬝ᵥ (scoreCovMat μ X e *ᵥ b)

/-- **Theorem 7.2 finite second-moment face.**

Every entry of the score second-moment matrix
`E[(e₀X₀)_j (e₀X₀)_ℓ]` is finite. This is the Lean-facing version of the
textbook statement that the asymptotic covariance matrix `Ω` has finite
entries under Assumption 7.2. -/
theorem scoreSecondMoment_integrable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (j l : k) :
    Integrable (fun ω => (e 0 ω • X 0 ω) j * (e 0 ω • X 0 ω) l) μ := by
  exact (scoreCoordinate_memLp_two (μ := μ) (X := X) (e := e) h j).integrable_mul
    (scoreCoordinate_memLp_two (μ := μ) (X := X) (e := e) h l)

omit [Fintype k] [DecidableEq k] in
/-- The score covariance matrix is symmetric. -/
theorem scoreCovMat_isSymm
    {μ : Measure Ω}
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} :
    (scoreCovMat μ X e).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro j l
  simp [scoreCovMat, covMat, ProbabilityTheory.covariance_comm]

/-- **Theorem 7.2 covariance-matrix face.**

The variance of every scalar projection of the score vector is the quadratic
form of Hansen's score covariance matrix `Ω`. This is the matrix-language
version of the scalar variance appearing in the one-dimensional CLT below. -/
theorem scoreProj_variance_eq_quadraticScoreCovariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ) :
    Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a; μ] =
      a ⬝ᵥ (scoreCovMat μ X e *ᵥ a) := by
  exact variance_dotProduct_eq_dotProduct_covMat_mulVec
    (μ := μ) (X := fun ω => e 0 ω • X 0 ω) a
    (fun j => scoreCoordinate_memLp_two (μ := μ) (X := X) (e := e) h j)

/-- Hansen's score covariance matrix has nonnegative quadratic forms under Assumption 7.2. -/
theorem scoreCovMat_quadratic_nonneg
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ) :
    0 ≤ a ⬝ᵥ (scoreCovMat μ X e *ᵥ a) := by
  rw [← scoreProj_variance_eq_quadraticScoreCovariance
    (μ := μ) (X := X) (e := e) h a]
  exact ProbabilityTheory.variance_nonneg _ _

/-- Hansen's score covariance matrix `Ω` is positive semidefinite. -/
theorem scoreCovMat_posSemidef
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) :
    (scoreCovMat μ X e).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · simpa [Matrix.IsHermitian] using (scoreCovMat_isSymm
      (μ := μ) (X := X) (e := e)).eq
  · intro a
    simpa using scoreCovMat_quadratic_nonneg
      (μ := μ) (X := X) (e := e) h a

/-- The scalar OLS projection asymptotic variance is nonnegative. -/
theorem olsProjectionAsymVar_nonneg
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ) :
    0 ≤ olsProjectionAsymVar μ X e a := by
  exact scoreCovMat_quadratic_nonneg
    (μ := μ) (X := X) (e := e) h (((popGram μ X)⁻¹)ᵀ *ᵥ a)

/-- Under the Chapter 7 orthogonality condition, each entry of `Ω` is the corresponding
score second moment. -/
theorem scoreCovMat_apply_eq_secondMoment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (j l : k) :
    scoreCovMat μ X e j l =
      ∫ ω, (e 0 ω • X 0 ω) j * (e 0 ω • X 0 ω) l ∂μ := by
  have hmean_j : μ[fun ω => (e 0 ω • X 0 ω) j] = 0 := by
    have hcoord := congrFun h.toSampleMomentAssumption71.orthogonality j
    rw [← integral_apply (μ := μ) (f := fun ω => e 0 ω • X 0 ω)
      h.toSampleMomentAssumption71.int_cross j]
    exact hcoord
  have hmean_l : μ[fun ω => (e 0 ω • X 0 ω) l] = 0 := by
    have hcoord := congrFun h.toSampleMomentAssumption71.orthogonality l
    rw [← integral_apply (μ := μ) (f := fun ω => e 0 ω • X 0 ω)
      h.toSampleMomentAssumption71.int_cross l]
    exact hcoord
  rw [scoreCovMat, covMat, ProbabilityTheory.covariance_eq_sub
    (scoreCoordinate_memLp_two (μ := μ) (X := X) (e := e) h j)
    (scoreCoordinate_memLp_two (μ := μ) (X := X) (e := e) h l),
    hmean_j, hmean_l]
  simp [Pi.mul_apply]

omit [DecidableEq k] in
/-- Variable-facing homoskedasticity assumption for Chapter 7.

The squared structural error has constant conditional expectation given the
regressor vector: `E[e₀² | X₀] = E[e₀²]`. -/
def HomoskedasticErrorVariance
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) : Prop :=
  condExpOn μ (fun ω => e 0 ω ^ 2) (X 0) =ᵐ[μ]
    fun _ => errorVariance μ e

omit [DecidableEq k] in
/-- A function of `X` is measurable with respect to the sigma-algebra generated by `X`. -/
theorem xMeasurable_comp_self_real
    {μ : Measure Ω} {β : Type*} [MeasurableSpace β]
    {X : Ω → β} {f : β → ℝ}
    (hf : Measurable f) :
    XMeasurable μ X (fun ω => f (X ω)) := by
  exact (hf.comp (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

omit [Fintype n] in
/-- Homoskedasticity implies Hansen's score-covariance identity `Ω = σ²Q`.

This is the variable-facing bridge used to replace public assumptions of the
already-finished covariance identity. -/
theorem scoreCovMat_eq_errorVariance_smul_popGram_homo
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (hclt : SampleCLTAssumption72 μ X e)
    (hvar : SampleVarianceAssumption74 μ X e)
    (hX0 : Measurable (X 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hX0))]
    (hhomo : HomoskedasticErrorVariance μ X e) :
    scoreCovMat μ X e = errorVariance μ e • popGram μ X := by
  classical
  ext j l
  let g : Ω → ℝ := fun ω => X 0 ω j * X 0 ω l
  let Y : Ω → ℝ := fun ω => e 0 ω ^ 2
  have hg : XMeasurable μ (X 0) g := by
    have hf : Measurable (fun x : k → ℝ => x j * x l) :=
      ((continuous_apply j).mul (continuous_apply l)).measurable
    simpa [g] using xMeasurable_comp_self_real (μ := μ) (X := X 0) hf
  have hgY : Integrable (fun ω => g ω * Y ω) μ := by
    have hscore := scoreSecondMoment_integrable
      (μ := μ) (X := X) (e := e) hclt j l
    convert hscore using 1
    ext ω
    simp [g, Y, Pi.smul_apply, pow_two]
    ring
  have hY : Integrable Y μ := by
    simpa [Y] using hvar.int_error_sq
  have hcond :
      ∫ ω, g ω * Y ω ∂μ =
        ∫ ω, g ω * condExpOn μ Y (X 0) ω ∂μ := by
    simpa [XMeasurable, condExpOn, conditioningSpace, g, Y] using
      conditioning_theorem_integral
        (m := conditioningSpace (X 0))
        (m₀ := inferInstance)
        (μ := μ)
        (g := g)
        (Y := Y)
        (conditioningSpace_le hX0)
        hg
        hgY
        hY
  have hhom_ae :
      (fun ω => g ω * condExpOn μ Y (X 0) ω) =ᵐ[μ]
        fun ω => g ω * errorVariance μ e := by
    filter_upwards [hhomo] with ω hω
    change g ω * condExpOn μ (fun ω => e 0 ω ^ 2) (X 0) ω =
      g ω * errorVariance μ e
    exact congrArg (fun z => g ω * z) hω
  have hcond_const :
      ∫ ω, g ω * condExpOn μ Y (X 0) ω ∂μ =
        ∫ ω, g ω * errorVariance μ e ∂μ :=
    integral_congr_ae hhom_ae
  have hg_int : Integrable g μ := by
    have hentry := Integrable.eval
      (Integrable.eval hvar.toSampleMomentAssumption71.int_outer j) l
    simpa [g, Matrix.vecMulVec_apply] using hentry
  have hfactor :
      ∫ ω, g ω * errorVariance μ e ∂μ =
        errorVariance μ e * ∫ ω, g ω ∂μ := by
    rw [show (fun ω => g ω * errorVariance μ e) =
        fun ω => errorVariance μ e * g ω by
          funext ω
          ring]
    exact integral_const_mul (errorVariance μ e) g
  have hQ :
      popGram μ X j l = ∫ ω, g ω ∂μ := by
    calc
      popGram μ X j l
          = ∫ ω, (Matrix.vecMulVec (X 0 ω) (X 0 ω)) j l ∂μ := by
            simpa [popGram] using
              integral_apply_apply
                (μ := μ)
                (f := fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω))
                hvar.toSampleMomentAssumption71.int_outer j l
      _ = ∫ ω, g ω ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with ω
            simp [g, Matrix.vecMulVec_apply]
  calc
    scoreCovMat μ X e j l
        = ∫ ω, (e 0 ω • X 0 ω) j * (e 0 ω • X 0 ω) l ∂μ := by
          exact scoreCovMat_apply_eq_secondMoment
            (μ := μ) (X := X) (e := e) hclt j l
    _ = ∫ ω, g ω * Y ω ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with ω
          simp [g, Y, Pi.smul_apply, pow_two]
          ring
    _ = errorVariance μ e * ∫ ω, g ω ∂μ := by
          rw [hcond, hcond_const, hfactor]
    _ = (errorVariance μ e • popGram μ X) j l := by
          simp [Matrix.smul_apply, hQ]

/-- Hansen's true-error second-moment matrix `E[e₀² X₀X₀']`, equal to `Ω`
under orthogonality. We represent it as the outer product of the score vector
`e₀X₀`; entrywise this is the textbook `E[e₀² X₀j X₀ℓ]`. -/
noncomputable def scoreSecondMomMat
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) : Matrix k k ℝ :=
  μ[fun ω => Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω)]

/-- The true-error score covariance sample average:
`n⁻¹∑ eᵢ² XᵢXᵢ'`, represented as `n⁻¹∑(eᵢXᵢ)(eᵢXᵢ)'`. This is the
first term in Hansen's proof of Theorem 7.6. -/
noncomputable def sampleScoreCovIdeal (X : Matrix n k ℝ) (e : n → ℝ) :
    Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n, Matrix.vecMulVec (e i • X i) (e i • X i)

/-- The HC0 score covariance sample average using totalized OLS residuals:
`n⁻¹∑ êᵢ² XᵢXᵢ'`, represented as residual-score outer products. -/
noncomputable def sampleScoreCovStar (X : Matrix n k ℝ) (y : n → ℝ) :
    Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n, Matrix.vecMulVec (olsResidualStar X y i • X i) (olsResidualStar X y i • X i)

/-- **Measurability of the feasible HC0 middle matrix from component measurability.**

If the individual regressors and errors are a.e. strongly measurable, then the
residual HC0 middle matrix `n⁻¹∑ êᵢ²XᵢXᵢ'` is a.e. strongly measurable. This is
a sufficient condition for the measurability premise in the feasible HC0
sandwich theorems. -/
theorem sampleScoreCovStar_stack_aestronglyMeasurable_components
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  intro n
  have hBeta_meas := olsBetaStar_stack_aestronglyMeasurable
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel n
  have hdot_fixed_cont : Continuous (fun x : k → ℝ => x ⬝ᵥ β) := by
    simpa [dotProduct] using
      (continuous_finset_sum Finset.univ
        (fun i _ => (continuous_apply i).mul continuous_const))
  have hdot_pair_cont : Continuous (fun p : (k → ℝ) × (k → ℝ) => p.1 ⬝ᵥ p.2) := by
    simpa [dotProduct] using
      (continuous_finset_sum Finset.univ
        (fun i _ =>
          ((continuous_apply i).comp continuous_fst).mul
            ((continuous_apply i).comp continuous_snd)))
  have houter_cont : Continuous (fun v : k → ℝ => Matrix.vecMulVec v v) := by
    refine continuous_pi (fun a => ?_)
    refine continuous_pi (fun b => ?_)
    simpa [Matrix.vecMulVec_apply] using
      (continuous_apply a).mul (continuous_apply b)
  have hterm : ∀ i : Fin n, AEStronglyMeasurable
      (fun ω =>
        Matrix.vecMulVec
          (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i •
            stackRegressors X n ω i)
          (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i •
            stackRegressors X n ω i)) μ := by
    intro i
    have hXrow : AEStronglyMeasurable (fun ω => stackRegressors X n ω i) μ := by
      simpa [stackRegressors] using hX_meas i.val
    have hYrow : AEStronglyMeasurable (fun ω => stackOutcomes y n ω i) μ := by
      have hYexpr : AEStronglyMeasurable
          (fun ω => X i.val ω ⬝ᵥ β + e i.val ω) μ :=
        (hdot_fixed_cont.comp_aestronglyMeasurable (hX_meas i.val)).add (he_meas i.val)
      refine hYexpr.congr (ae_of_all μ (fun ω => ?_))
      simpa [stackOutcomes] using (hmodel i.val ω).symm
    have hfit : AEStronglyMeasurable
        (fun ω =>
          stackRegressors X n ω i ⬝ᵥ
            olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)) μ :=
      hdot_pair_cont.comp_aestronglyMeasurable (hXrow.prodMk hBeta_meas)
    have hres_exp : AEStronglyMeasurable
        (fun ω =>
          stackOutcomes y n ω i -
            stackRegressors X n ω i ⬝ᵥ
              olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)) μ :=
      hYrow.sub hfit
    have hres : AEStronglyMeasurable
        (fun ω => olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i) μ := by
      refine hres_exp.congr (ae_of_all μ (fun ω => ?_))
      simp [olsResidualStar, Matrix.mulVec, dotProduct]
    have hscore : AEStronglyMeasurable
        (fun ω =>
          olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i •
            stackRegressors X n ω i) μ :=
      hres.smul hXrow
    exact houter_cont.comp_aestronglyMeasurable hscore
  have hsum : AEStronglyMeasurable
      (fun ω =>
        ∑ i : Fin n,
          Matrix.vecMulVec
            (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i •
              stackRegressors X n ω i)
            (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i •
              stackRegressors X n ω i)) μ := by
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => hterm i)
  simpa [sampleScoreCovStar] using
    AEStronglyMeasurable.const_smul hsum ((Fintype.card (Fin n) : ℝ)⁻¹)

/-- Totalized leverage `hᵢᵢ = xᵢ' (X'X)⁻¹ xᵢ` used by HC2/HC3.

This mirrors the textbook hat-matrix diagonal but uses the total matrix inverse,
so it is defined even on singular finite samples. -/
noncomputable def leverageStar (X : Matrix n k ℝ) (i : n) : ℝ :=
  X i ⬝ᵥ ((Xᵀ * X)⁻¹ *ᵥ X i)

/-- On nonsingular samples, the totalized leverage is the usual hat-matrix diagonal. -/
theorem leverageStar_eq_hatMatrix_diag
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] (i : n) :
    leverageStar X i = hatMatrix X i i := by
  unfold leverageStar hatMatrix
  rw [← invOf_eq_nonsing_inv, Matrix.dotProduct_mulVec]
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.transpose_apply]

/-- On nonsingular samples, leverage scores are nonnegative. -/
theorem leverageStar_nonneg_of_nonsingular
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] (i : n) :
    0 ≤ leverageStar X i := by
  classical
  rw [leverageStar_eq_hatMatrix_diag]
  exact diag_nonneg_of_symm_idempotent
    (hatMatrix X) (hatMatrix_transpose X) (hatMatrix_idempotent X) i

/-- On nonsingular samples, leverage scores are bounded above by one. -/
theorem leverageStar_le_one_of_nonsingular
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] (i : n) :
    leverageStar X i ≤ 1 := by
  classical
  have hdiag_nonneg : 0 ≤ annihilatorMatrix X i i :=
    diag_nonneg_of_symm_idempotent
      (annihilatorMatrix X) (annihilatorMatrix_transpose X)
      (annihilatorMatrix_idempotent X) i
  have hdiag_eq : annihilatorMatrix X i i = 1 - hatMatrix X i i := by
    simp [annihilatorMatrix, Matrix.sub_apply]
  rw [leverageStar_eq_hatMatrix_diag]
  linarith

/-- On singular samples, the totalized leverage is zero because `nonsingInv`
vanishes. -/
theorem leverageStar_eq_zero_of_not_isUnit_det
    (X : Matrix n k ℝ) (hX : ¬ IsUnit (Xᵀ * X).det) (i : n) :
    leverageStar X i = 0 := by
  unfold leverageStar
  rw [Matrix.nonsing_inv_apply_not_isUnit _ hX, Matrix.zero_mulVec]
  exact dotProduct_zero (X i)

/-- Totalized leverage is always nonnegative: on nonsingular samples this is the
hat-matrix diagonal, and on singular samples it is zero. -/
theorem leverageStar_nonneg (X : Matrix n k ℝ) (i : n) :
    0 ≤ leverageStar X i := by
  by_cases hX : IsUnit (Xᵀ * X).det
  · letI : Invertible (Xᵀ * X) := Matrix.invertibleOfIsUnitDet (A := Xᵀ * X) hX
    exact leverageStar_nonneg_of_nonsingular X i
  · simp [leverageStar_eq_zero_of_not_isUnit_det X hX i]

/-- Totalized leverage is always at most one: on nonsingular samples this is the
usual hat-matrix bound, and on singular samples it is zero. -/
theorem leverageStar_le_one (X : Matrix n k ℝ) (i : n) :
    leverageStar X i ≤ 1 := by
  by_cases hX : IsUnit (Xᵀ * X).det
  · letI : Invertible (Xᵀ * X) := Matrix.invertibleOfIsUnitDet (A := Xᵀ * X) hX
    exact leverageStar_le_one_of_nonsingular X i
  · rw [leverageStar_eq_zero_of_not_isUnit_det X hX i]
    norm_num

/-- Supremum norm of the leverage vector, i.e. the finite-sample maximal
leverage under the repo's totalization convention. -/
noncomputable def maxLeverageStar (X : Matrix n k ℝ) : ℝ :=
  ‖fun i : n => leverageStar X i‖

/-- Every leverage coordinate is bounded by the maximal leverage. -/
theorem leverageStar_le_maxLeverageStar
    (X : Matrix n k ℝ) (i : n) :
    leverageStar X i ≤ maxLeverageStar X := by
  simpa [maxLeverageStar, Real.norm_eq_abs,
    abs_of_nonneg (leverageStar_nonneg X i)] using
    (norm_le_pi_norm (fun j : n => leverageStar X j) i)

/-- **Hansen Theorem 7.17, finite-sample leverage trace identity.**

On nonsingular samples, the totalized leverages sum to the number of regressors,
because they are the diagonal entries of the hat matrix. -/
theorem sum_leverageStar_eq_card_of_nonsingular
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] :
    ∑ i : n, leverageStar X i = (Fintype.card k : ℝ) := by
  calc
    ∑ i : n, leverageStar X i
        = ∑ i : n, hatMatrix X i i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [leverageStar_eq_hatMatrix_diag]
    _ = Matrix.trace (hatMatrix X) := by
          simp [Matrix.trace]
    _ = (Fintype.card k : ℝ) := by
          simpa using hatMatrix_trace (X := X)

/-- **Hansen Theorem 7.17, average leverage identity.**

The sample average of the nonsingular leverage diagonal is `k / n`. This is the
finite-sample identity behind the asymptotic max-leverage discussion. -/
theorem average_leverageStar_eq_card_div_card_of_nonsingular
    (X : Matrix n k ℝ) [Nonempty n] [Invertible (Xᵀ * X)] :
    (Fintype.card n : ℝ)⁻¹ * ∑ i : n, leverageStar X i =
      (Fintype.card k : ℝ) / (Fintype.card n : ℝ) := by
  have hn : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [sum_leverageStar_eq_card_of_nonsingular]
  field_simp [hn]

/-- Leverage-weighted residual-score covariance middle matrix.

This is the common engine behind HC2 and HC3: each estimator chooses a scalar
weight as a function of the leverage value `hᵢᵢ`, then forms
`n⁻¹∑ w(hᵢᵢ) êᵢ²xᵢxᵢ'`. -/
noncomputable def sampleScoreCovLevAdjStar
    (weight : ℝ → ℝ) (X : Matrix n k ℝ) (y : n → ℝ) :
    Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n,
      (weight (leverageStar X i) * (olsResidualStar X y i) ^ 2) •
        Matrix.vecMulVec (X i) (X i)

/-- Leverage-weighted middle-matrix adjustment relative to HC0. -/
noncomputable def sampleScoreCovLevAdjmtStar
    (weight : ℝ → ℝ) (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  sampleScoreCovLevAdjStar weight X y - sampleScoreCovStar X y

/-- Scalar entry of the generic leverage-weighted middle-matrix adjustment. -/
noncomputable def sampleScoreCovLevAdjmtEntryStar
    (weight : ℝ → ℝ) (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ *
    ∑ i : n, ((weight (leverageStar X i) - 1) *
      (olsResidualStar X y i) ^ 2 * X i a * X i b)

/-- Sup-norm of the leverage adjustment weights `w(hᵢᵢ)-1`. -/
noncomputable def levAdjWtNormStar
    (weight : ℝ → ℝ) (X : Matrix n k ℝ) : ℝ :=
  ‖fun i : n => weight (leverageStar X i) - 1‖

/-- Absolute residual-score average used to bound leverage adjustments entrywise. -/
noncomputable def sampleScoreCovResAbsWtStar
    (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ *
    ∑ i : n, |(olsResidualStar X y i) ^ 2 * X i a * X i b|

/-- The HC2 residual-score covariance middle matrix
`n⁻¹∑ êᵢ²/(1-hᵢᵢ) · xᵢxᵢ'`, totalized through `leverageStar`. -/
noncomputable def sampleScoreCovHC2Star (X : Matrix n k ℝ) (y : n → ℝ) :
    Matrix k k ℝ :=
  sampleScoreCovLevAdjStar (fun h => (1 - h)⁻¹) X y

/-- The HC3 residual-score covariance middle matrix
`n⁻¹∑ êᵢ²/(1-hᵢᵢ)² · xᵢxᵢ'`, totalized through `leverageStar`. -/
noncomputable def sampleScoreCovHC3Star (X : Matrix n k ℝ) (y : n → ℝ) :
    Matrix k k ℝ :=
  sampleScoreCovLevAdjStar (fun h => ((1 - h)⁻¹) ^ 2) X y

/-- HC2-minus-HC0 middle-matrix adjustment. Proving this is `oₚ(1)` is the
leverage-specific part of HC2 consistency. -/
noncomputable def sampleScoreCovHC2AdjStar
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  sampleScoreCovLevAdjmtStar (fun h => (1 - h)⁻¹) X y

/-- HC3-minus-HC0 middle-matrix adjustment. Proving this is `oₚ(1)` is the
leverage-specific part of HC3 consistency. -/
noncomputable def sampleScoreCovHC3AdjStar
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  sampleScoreCovLevAdjmtStar (fun h => ((1 - h)⁻¹) ^ 2) X y

end Assumption72

end HansenEconometrics
