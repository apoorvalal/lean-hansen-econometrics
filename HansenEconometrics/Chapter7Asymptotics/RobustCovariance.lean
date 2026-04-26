import HansenEconometrics.Chapter2CondExp
import HansenEconometrics.Chapter7Asymptotics.Consistency

/-!
# Chapter 7 Asymptotics: Robust Covariance

This file contains the Chapter 7 covariance layer:

* score covariance definitions and homoskedastic covariance identities;
* HC0/HC1/HC2/HC3 middle matrices and sandwich covariance estimators;
* measurability and convergence-in-probability results for robust covariance;
* leverage-adjustment scaffolding used by the current HC2/HC3 wrappers.
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
/-- Borel σ-algebra on `Matrix k k ℝ` inherited from the elementwise-L∞ norm,
reintroduced for the Chapter 7.2+ covariance-matrix random variables. -/
@[reducible]
private noncomputable def matrixBorelMeasurableSpace72 :
    MeasurableSpace (Matrix k k ℝ) := borel _

attribute [local instance] matrixBorelMeasurableSpace72

omit [Fintype k] [DecidableEq k] in
private lemma matrixBorelSpace72 : BorelSpace (Matrix k k ℝ) := ⟨rfl⟩

attribute [local instance] matrixBorelSpace72

/-- Strengthening of the Chapter 7.1 moment assumptions for the first CLT bridge.

Mathlib currently supplies a one-dimensional iid CLT. To use it for Hansen's
vector score `eᵢXᵢ`, we ask for full independence of those score vectors and
square integrability of every fixed scalar projection. The resulting theorem is
the scalar-projection/Cramér-Wold face of Hansen Assumption 7.2. -/
structure SampleCLTAssumption72 (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    extends SampleMomentAssumption71 μ X e where
  /-- Full independence of the score-vector sequence `e i • X i`. -/
  iIndep_cross : iIndepFun (fun i ω => e i ω • X i ω) μ
  /-- Square integrability of every scalar projection of the score vector. -/
  memLp_cross_projection :
    ∀ a : k → ℝ, MemLp (fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a) 2 μ

/-- Descriptive public condition package for the current Lean proof behind Hansen
Assumption 7.2 / Theorem 7.2 / Theorem 7.3.

This is the score-CLT-facing sufficient bundle used by the current formalized
normality layer. It strengthens the Chapter 7.1 moment package with full score
independence and projectionwise square integrability, rather than encoding the
textbook iid assumption literally. It extends the internal
`SampleCLTAssumption72` proof record. -/
structure ScoreCLTConditions (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    extends SampleCLTAssumption72 μ X e

namespace ScoreCLTConditions

/-- Promote the internal CLT proof package to the public Chapter 7 score-CLT condition. -/
protected def ofSample
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) :
    ScoreCLTConditions μ X e where
  toSampleCLTAssumption72 := h

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
theorem scoreProjection_integral_zero
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
noncomputable def scoreCovarianceMatrix
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) : Matrix k k ℝ :=
  covMat μ (fun ω => e 0 ω • X 0 ω)

/-- Scalar asymptotic variance of the projection `a'√n(β̂ₙ - β)`:
`((Q⁻¹)'a)' Ω ((Q⁻¹)'a)`. This avoids needing to prove symmetry of `Q⁻¹`
before stating the scalar CLT in textbook covariance notation. -/
noncomputable def olsProjectionAsymptoticVariance
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    (a : k → ℝ) : ℝ :=
  let b := ((popGram μ X)⁻¹)ᵀ *ᵥ a
  b ⬝ᵥ (scoreCovarianceMatrix μ X e *ᵥ b)

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
theorem scoreCovarianceMatrix_isSymm
    {μ : Measure Ω}
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} :
    (scoreCovarianceMatrix μ X e).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro j l
  simp [scoreCovarianceMatrix, covMat, ProbabilityTheory.covariance_comm]

/-- **Theorem 7.2 covariance-matrix face.**

The variance of every scalar projection of the score vector is the quadratic
form of Hansen's score covariance matrix `Ω`. This is the matrix-language
version of the scalar variance appearing in the one-dimensional CLT below. -/
theorem scoreProjection_variance_eq_quadraticScoreCovariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ) :
    Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a; μ] =
      a ⬝ᵥ (scoreCovarianceMatrix μ X e *ᵥ a) := by
  exact variance_dotProduct_eq_dotProduct_covMat_mulVec
    (μ := μ) (X := fun ω => e 0 ω • X 0 ω) a
    (fun j => scoreCoordinate_memLp_two (μ := μ) (X := X) (e := e) h j)

/-- Hansen's score covariance matrix has nonnegative quadratic forms under Assumption 7.2. -/
theorem scoreCovarianceMatrix_quadratic_nonneg
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ) :
    0 ≤ a ⬝ᵥ (scoreCovarianceMatrix μ X e *ᵥ a) := by
  rw [← scoreProjection_variance_eq_quadraticScoreCovariance
    (μ := μ) (X := X) (e := e) h a]
  exact ProbabilityTheory.variance_nonneg _ _

/-- Hansen's score covariance matrix `Ω` is positive semidefinite. -/
theorem scoreCovarianceMatrix_posSemidef
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) :
    (scoreCovarianceMatrix μ X e).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · simpa [Matrix.IsHermitian] using (scoreCovarianceMatrix_isSymm
      (μ := μ) (X := X) (e := e)).eq
  · intro a
    simpa using scoreCovarianceMatrix_quadratic_nonneg
      (μ := μ) (X := X) (e := e) h a

/-- The scalar OLS projection asymptotic variance is nonnegative. -/
theorem olsProjectionAsymptoticVariance_nonneg
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ) :
    0 ≤ olsProjectionAsymptoticVariance μ X e a := by
  exact scoreCovarianceMatrix_quadratic_nonneg
    (μ := μ) (X := X) (e := e) h (((popGram μ X)⁻¹)ᵀ *ᵥ a)

/-- Under the Chapter 7 orthogonality condition, each entry of `Ω` is the corresponding
score second moment. -/
theorem scoreCovarianceMatrix_apply_eq_secondMoment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (j l : k) :
    scoreCovarianceMatrix μ X e j l =
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
  rw [scoreCovarianceMatrix, covMat, ProbabilityTheory.covariance_eq_sub
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
theorem scoreCovarianceMatrix_eq_errorVariance_smul_popGram_of_homoskedastic
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (hclt : SampleCLTAssumption72 μ X e)
    (hvar : SampleVarianceAssumption74 μ X e)
    (hX0 : Measurable (X 0))
    [SigmaFinite (μ.trim (conditioningSpace_le hX0))]
    (hhomo : HomoskedasticErrorVariance μ X e) :
    scoreCovarianceMatrix μ X e = errorVariance μ e • popGram μ X := by
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
    scoreCovarianceMatrix μ X e j l
        = ∫ ω, (e 0 ω • X 0 ω) j * (e 0 ω • X 0 ω) l ∂μ := by
          exact scoreCovarianceMatrix_apply_eq_secondMoment
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
noncomputable def scoreSecondMomentMatrix
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) : Matrix k k ℝ :=
  μ[fun ω => Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω)]

/-- The true-error score covariance sample average:
`n⁻¹∑ eᵢ² XᵢXᵢ'`, represented as `n⁻¹∑(eᵢXᵢ)(eᵢXᵢ)'`. This is the
first term in Hansen's proof of Theorem 7.6. -/
noncomputable def sampleScoreCovarianceIdeal (X : Matrix n k ℝ) (e : n → ℝ) :
    Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n, Matrix.vecMulVec (e i • X i) (e i • X i)

/-- The HC0 score covariance sample average using totalized OLS residuals:
`n⁻¹∑ êᵢ² XᵢXᵢ'`, represented as residual-score outer products. -/
noncomputable def sampleScoreCovarianceStar (X : Matrix n k ℝ) (y : n → ℝ) :
    Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n, Matrix.vecMulVec (olsResidualStar X y i • X i) (olsResidualStar X y i • X i)

/-- **Measurability of the feasible HC0 middle matrix from component measurability.**

If the individual regressors and errors are a.e. strongly measurable, then the
residual HC0 middle matrix `n⁻¹∑ êᵢ²XᵢXᵢ'` is a.e. strongly measurable. This is
a sufficient condition for the measurability premise in the feasible HC0
sandwich theorems. -/
theorem sampleScoreCovarianceStar_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
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
  simpa [sampleScoreCovarianceStar] using
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
  simpa using (dotProduct_zero (X i))

/-- Totalized leverage is always nonnegative: on nonsingular samples this is the
hat-matrix diagonal, and on singular samples it is zero. -/
theorem leverageStar_nonneg (X : Matrix n k ℝ) (i : n) :
    0 ≤ leverageStar X i := by
  by_cases hX : IsUnit (Xᵀ * X).det
  · letI : Invertible (Xᵀ * X) := Matrix.invertibleOfIsUnitDet (A := Xᵀ * X) hX
    exact leverageStar_nonneg_of_nonsingular X i
  · simpa [leverageStar_eq_zero_of_not_isUnit_det X hX i]

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
noncomputable def sampleScoreCovarianceLeverageAdjustedStar
    (weight : ℝ → ℝ) (X : Matrix n k ℝ) (y : n → ℝ) :
    Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n,
      (weight (leverageStar X i) * (olsResidualStar X y i) ^ 2) •
        Matrix.vecMulVec (X i) (X i)

/-- Leverage-weighted middle-matrix adjustment relative to HC0. -/
noncomputable def sampleScoreCovarianceLeverageAdjustmentStar
    (weight : ℝ → ℝ) (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  sampleScoreCovarianceLeverageAdjustedStar weight X y - sampleScoreCovarianceStar X y

/-- Scalar entry of the generic leverage-weighted middle-matrix adjustment. -/
noncomputable def sampleScoreCovarianceLeverageAdjustmentEntryStar
    (weight : ℝ → ℝ) (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ *
    ∑ i : n, ((weight (leverageStar X i) - 1) *
      (olsResidualStar X y i) ^ 2 * X i a * X i b)

/-- Sup-norm of the leverage adjustment weights `w(hᵢᵢ)-1`. -/
noncomputable def leverageAdjustmentWeightNormStar
    (weight : ℝ → ℝ) (X : Matrix n k ℝ) : ℝ :=
  ‖fun i : n => weight (leverageStar X i) - 1‖

/-- Absolute residual-score average used to bound leverage adjustments entrywise. -/
noncomputable def sampleScoreCovarianceResidualAbsWeightStar
    (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ *
    ∑ i : n, |(olsResidualStar X y i) ^ 2 * X i a * X i b|

/-- The HC2 residual-score covariance middle matrix
`n⁻¹∑ êᵢ²/(1-hᵢᵢ) · xᵢxᵢ'`, totalized through `leverageStar`. -/
noncomputable def sampleScoreCovarianceHC2Star (X : Matrix n k ℝ) (y : n → ℝ) :
    Matrix k k ℝ :=
  sampleScoreCovarianceLeverageAdjustedStar (fun h => (1 - h)⁻¹) X y

/-- The HC3 residual-score covariance middle matrix
`n⁻¹∑ êᵢ²/(1-hᵢᵢ)² · xᵢxᵢ'`, totalized through `leverageStar`. -/
noncomputable def sampleScoreCovarianceHC3Star (X : Matrix n k ℝ) (y : n → ℝ) :
    Matrix k k ℝ :=
  sampleScoreCovarianceLeverageAdjustedStar (fun h => ((1 - h)⁻¹) ^ 2) X y

/-- HC2-minus-HC0 middle-matrix adjustment. Proving this is `oₚ(1)` is the
leverage-specific part of HC2 consistency. -/
noncomputable def sampleScoreCovarianceHC2AdjustmentStar
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  sampleScoreCovarianceLeverageAdjustmentStar (fun h => (1 - h)⁻¹) X y

/-- HC3-minus-HC0 middle-matrix adjustment. Proving this is `oₚ(1)` is the
leverage-specific part of HC3 consistency. -/
noncomputable def sampleScoreCovarianceHC3AdjustmentStar
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  sampleScoreCovarianceLeverageAdjustmentStar (fun h => ((1 - h)⁻¹) ^ 2) X y

/-- Measurability of a generic leverage-adjusted middle matrix from component
measurability and measurability of the scalar weight function. -/
theorem sampleScoreCovarianceLeverageAdjustedStar_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (weight : ℝ → ℝ) (hweight_meas : Measurable weight)
    (β : k → ℝ) (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceLeverageAdjustedStar weight
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  intro n
  have hBeta_meas := olsBetaStar_stack_aestronglyMeasurable
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel n
  have hRawGram_meas : AEStronglyMeasurable
      (fun ω => (stackRegressors X n ω)ᵀ * stackRegressors X n ω) μ := by
    have hform : (fun ω => (stackRegressors X n ω)ᵀ * stackRegressors X n ω) =
        (fun ω => ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [stackRegressors_transpose_mul_self_eq_sum, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hRawInv_meas : AEStronglyMeasurable
      (fun ω => ((stackRegressors X n ω)ᵀ * stackRegressors X n ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hRawGram_meas
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
        (weight (leverageStar (stackRegressors X n ω) i) *
            (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i) ^ 2) •
          Matrix.vecMulVec (stackRegressors X n ω i) (stackRegressors X n ω i)) μ := by
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
    have hmulVec : AEStronglyMeasurable
        (fun ω =>
          ((stackRegressors X n ω)ᵀ * stackRegressors X n ω)⁻¹ *ᵥ
            stackRegressors X n ω i) μ := by
      exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hRawInv_meas.prodMk hXrow)
    have hlev : AEStronglyMeasurable
        (fun ω => leverageStar (stackRegressors X n ω) i) μ := by
      refine hdot_pair_cont.comp_aestronglyMeasurable (hXrow.prodMk ?_)
      simpa [leverageStar] using hmulVec
    have hweight : AEStronglyMeasurable
        (fun ω => weight (leverageStar (stackRegressors X n ω) i)) μ := by
      exact (hweight_meas.comp_aemeasurable hlev.aemeasurable).aestronglyMeasurable
    have hcoeff : AEStronglyMeasurable
        (fun ω =>
          weight (leverageStar (stackRegressors X n ω) i) *
            (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i) ^ 2) μ :=
      hweight.mul (hres.pow 2)
    have houter : AEStronglyMeasurable
        (fun ω => Matrix.vecMulVec (stackRegressors X n ω i) (stackRegressors X n ω i)) μ :=
      houter_cont.comp_aestronglyMeasurable hXrow
    exact hcoeff.smul houter
  have hsum : AEStronglyMeasurable
      (fun ω =>
        ∑ i : Fin n,
          (weight (leverageStar (stackRegressors X n ω) i) *
              (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i) ^ 2) •
            Matrix.vecMulVec (stackRegressors X n ω i) (stackRegressors X n ω i)) μ := by
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => hterm i)
  simpa [sampleScoreCovarianceLeverageAdjustedStar] using
    AEStronglyMeasurable.const_smul hsum ((Fintype.card (Fin n) : ℝ)⁻¹)

/-- Measurability of the generic leverage-adjustment middle-matrix gap from
component measurability. -/
theorem sampleScoreCovarianceLeverageAdjustmentStar_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (weight : ℝ → ℝ) (hweight_meas : Measurable weight)
    (β : k → ℝ) (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceLeverageAdjustmentStar weight
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  intro n
  exact
    (sampleScoreCovarianceLeverageAdjustedStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y) weight hweight_meas
      β h hmodel hX_meas he_meas n).sub
    (sampleScoreCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y) β h hmodel hX_meas he_meas n)

private theorem measurable_hc2Weight : Measurable (fun h : ℝ => (1 - h)⁻¹) :=
  measurable_inv.comp (measurable_const.sub measurable_id)

private theorem measurable_hc3Weight : Measurable (fun h : ℝ => ((1 - h)⁻¹) ^ 2) :=
  measurable_hc2Weight.pow_const 2

/-- Measurability of the HC2 middle-matrix adjustment from component
measurability. -/
theorem sampleScoreCovarianceHC2AdjustmentStar_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC2AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  simpa [sampleScoreCovarianceHC2AdjustmentStar] using
    sampleScoreCovarianceLeverageAdjustmentStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      (weight := fun h => (1 - h)⁻¹) measurable_hc2Weight
      β h hmodel hX_meas he_meas

/-- Measurability of the HC3 middle-matrix adjustment from component
measurability. -/
theorem sampleScoreCovarianceHC3AdjustmentStar_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC3AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  simpa [sampleScoreCovarianceHC3AdjustmentStar] using
    sampleScoreCovarianceLeverageAdjustmentStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      (weight := fun h => ((1 - h)⁻¹) ^ 2) measurable_hc3Weight
      β h hmodel hX_meas he_meas

set_option linter.flexible false in
/-- **Generic leverage-adjustment expansion, entrywise form.**

The leverage-adjusted-minus-HC0 middle matrix is the sample average with scalar
weight `w(hᵢᵢ)-1` multiplying the usual residual-score outer product. -/
theorem sampleScoreCovarianceLeverageAdjustmentStar_apply
    (weight : ℝ → ℝ) (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) :
    sampleScoreCovarianceLeverageAdjustmentStar weight X y a b =
      sampleScoreCovarianceLeverageAdjustmentEntryStar weight X y a b := by
  simp [sampleScoreCovarianceLeverageAdjustmentStar,
    sampleScoreCovarianceLeverageAdjustedStar,
    sampleScoreCovarianceLeverageAdjustmentEntryStar,
    sampleScoreCovarianceStar, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

/-- **HC2 leverage-adjustment expansion, entrywise form.**

The HC2-minus-HC0 middle matrix is the sample average with scalar weight
`(1-hᵢᵢ)⁻¹ - 1` multiplying the usual residual-score outer product. -/
theorem sampleScoreCovarianceHC2AdjustmentStar_apply
    (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) :
    sampleScoreCovarianceHC2AdjustmentStar X y a b =
      (Fintype.card n : ℝ)⁻¹ *
        ∑ i : n, (((1 - leverageStar X i)⁻¹ - 1) *
          (olsResidualStar X y i) ^ 2 * X i a * X i b) := by
  change sampleScoreCovarianceLeverageAdjustmentStar
      (fun h => (1 - h)⁻¹) X y a b = _
  rw [sampleScoreCovarianceLeverageAdjustmentStar_apply]
  rfl

/-- **HC3 leverage-adjustment expansion, entrywise form.**

The HC3-minus-HC0 middle matrix is the sample average with scalar weight
`(1-hᵢᵢ)⁻² - 1` multiplying the usual residual-score outer product. -/
theorem sampleScoreCovarianceHC3AdjustmentStar_apply
    (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) :
    sampleScoreCovarianceHC3AdjustmentStar X y a b =
      (Fintype.card n : ℝ)⁻¹ *
        ∑ i : n, ((((1 - leverageStar X i)⁻¹) ^ 2 - 1) *
          (olsResidualStar X y i) ^ 2 * X i a * X i b) := by
  change sampleScoreCovarianceLeverageAdjustmentStar
      (fun h => ((1 - h)⁻¹) ^ 2) X y a b = _
  rw [sampleScoreCovarianceLeverageAdjustmentStar_apply]
  rfl

/-- Each scalar leverage-adjustment weight is bounded by its sup norm. -/
theorem leverageAdjustmentWeight_abs_le_norm
    (weight : ℝ → ℝ) (X : Matrix n k ℝ) (i : n) :
    |weight (leverageStar X i) - 1| ≤
      leverageAdjustmentWeightNormStar weight X := by
  simpa [leverageAdjustmentWeightNormStar, Real.norm_eq_abs] using
    norm_le_pi_norm (fun i : n => weight (leverageStar X i) - 1) i

/-- On leverage values `0 ≤ h ≤ 1/2`, the HC2 weight deviation is at most
`2h`. -/
theorem hc2Weight_abs_sub_one_le_two_mul
    {h : ℝ} (hh_nonneg : 0 ≤ h) (hh_half : h ≤ 1 / 2) :
    |(1 - h)⁻¹ - 1| ≤ 2 * h := by
  have hden_pos : 0 < 1 - h := by
    linarith
  have hrepr : (1 - h)⁻¹ - 1 = h / (1 - h) := by
    field_simp [hden_pos.ne']
    ring
  have hfrac_nonneg : 0 ≤ h / (1 - h) := by
    exact div_nonneg hh_nonneg hden_pos.le
  rw [hrepr, abs_of_nonneg hfrac_nonneg]
  rw [div_le_iff₀ hden_pos]
  nlinarith

/-- On leverage values `0 ≤ h ≤ 1/2`, the HC3 weight deviation is at most
`8h`. The constant is crude but sufficient for the `oₚ(1)` argument. -/
theorem hc3Weight_abs_sub_one_le_eight_mul
    {h : ℝ} (hh_nonneg : 0 ≤ h) (hh_half : h ≤ 1 / 2) :
    |((1 - h)⁻¹) ^ 2 - 1| ≤ 8 * h := by
  have hden_pos : 0 < 1 - h := by
    linarith
  have hrepr : ((1 - h)⁻¹) ^ 2 - 1 = (h * (2 - h)) / (1 - h) ^ 2 := by
    field_simp [hden_pos.ne']
    ring
  have hfrac_nonneg : 0 ≤ (h * (2 - h)) / (1 - h) ^ 2 := by
    have hnum_nonneg : 0 ≤ h * (2 - h) := by
      nlinarith
    exact div_nonneg hnum_nonneg (sq_nonneg _)
  rw [hrepr, abs_of_nonneg hfrac_nonneg]
  have hsq_pos : 0 < (1 - h) ^ 2 := by
    positivity
  rw [div_le_iff₀ hsq_pos]
  calc
    h * (2 - h) ≤ 2 * h := by
      nlinarith
    _ ≤ 8 * h * (1 - h) ^ 2 := by
      have hsq_lower : (1 / 4 : ℝ) ≤ (1 - h) ^ 2 := by
        nlinarith
      nlinarith

/-- If the maximal leverage is smaller than `δ ≤ 1/2`, then the HC2
adjustment-weight norm is smaller than `2δ`. -/
theorem leverageAdjustmentWeightNormStar_hc2_lt_of_maxLeverageStar_lt
    (X : Matrix n k ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ_half : δ ≤ 1 / 2)
    (hmax : maxLeverageStar X < δ) :
    leverageAdjustmentWeightNormStar (fun h => (1 - h)⁻¹) X < 2 * δ := by
  let z : n → ℝ := fun i => (1 - leverageStar X i)⁻¹ - 1
  have hcoords : ∀ i : n, leverageStar X i < δ := by
    intro i
    exact lt_of_le_of_lt (leverageStar_le_maxLeverageStar X i) hmax
  have hz : ‖z‖ < 2 * δ := by
    refine (@pi_norm_lt_iff n (fun _ : n => ℝ) _ (fun _ => (by infer_instance : SeminormedAddGroup ℝ))
      z (2 * δ)
      (show 0 < 2 * δ by positivity)).2 ?_
    intro i
    have hi_nonneg : 0 ≤ leverageStar X i := leverageStar_nonneg X i
    have hi_lt : leverageStar X i < δ := hcoords i
    have hi_half : leverageStar X i ≤ 1 / 2 := by
      linarith
    have hbound :
        |(1 - leverageStar X i)⁻¹ - 1| ≤ 2 * leverageStar X i :=
      hc2Weight_abs_sub_one_le_two_mul hi_nonneg hi_half
    have hlt : 2 * leverageStar X i < 2 * δ := by
      exact mul_lt_mul_of_pos_left hi_lt (by positivity)
    simpa [z, Real.norm_eq_abs] using lt_of_le_of_lt hbound hlt
  simpa [leverageAdjustmentWeightNormStar, z] using hz

/-- If the maximal leverage is smaller than `δ ≤ 1/2`, then the HC3
adjustment-weight norm is smaller than `8δ`. -/
theorem leverageAdjustmentWeightNormStar_hc3_lt_of_maxLeverageStar_lt
    (X : Matrix n k ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ_half : δ ≤ 1 / 2)
    (hmax : maxLeverageStar X < δ) :
    leverageAdjustmentWeightNormStar (fun h => ((1 - h)⁻¹) ^ 2) X < 8 * δ := by
  let z : n → ℝ := fun i => ((1 - leverageStar X i) ^ 2)⁻¹ - 1
  have hcoords : ∀ i : n, leverageStar X i < δ := by
    intro i
    exact lt_of_le_of_lt (leverageStar_le_maxLeverageStar X i) hmax
  have hz : ‖z‖ < 8 * δ := by
    refine (@pi_norm_lt_iff n (fun _ : n => ℝ) _ (fun _ => (by infer_instance : SeminormedAddGroup ℝ))
      z (8 * δ)
      (show 0 < 8 * δ by positivity)).2 ?_
    intro i
    have hi_nonneg : 0 ≤ leverageStar X i := leverageStar_nonneg X i
    have hi_lt : leverageStar X i < δ := hcoords i
    have hi_half : leverageStar X i ≤ 1 / 2 := by
      linarith
    have hbound :
        |((1 - leverageStar X i) ^ 2)⁻¹ - 1| ≤ 8 * leverageStar X i := by
      simpa [pow_two] using
        (hc3Weight_abs_sub_one_le_eight_mul (h := leverageStar X i) hi_nonneg hi_half)
    have hlt : 8 * leverageStar X i < 8 * δ := by
      exact mul_lt_mul_of_pos_left hi_lt (by positivity)
    simpa [z, Real.norm_eq_abs] using lt_of_le_of_lt hbound hlt
  simpa [leverageAdjustmentWeightNormStar, z, pow_two] using hz

/-- HC2 adjustment-weight norms are `oₚ(1)` once maximal leverage is `oₚ(1)`. -/
theorem leverageAdjustmentWeightNormStar_hc2_tendstoInMeasure_zero_of_maxLeverageStar
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)}
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        leverageAdjustmentWeightNormStar (fun h => (1 - h)⁻¹)
          (stackRegressors X n ω))
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hMax ⊢
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro η hη
  let δ : ℝ := min (1 / 4 : ℝ) (ε / 4)
  have hδ : 0 < δ := by
    dsimp [δ]
    refine lt_min ?_ ?_
    · norm_num
    · positivity
  have hδ_half : δ ≤ 1 / 2 := by
    dsimp [δ]
    have hle : min (1 / 4 : ℝ) (ε / 4) ≤ 1 / 4 := min_le_left _ _
    linarith
  have htwoδ_lt_ε : 2 * δ < ε := by
    dsimp [δ]
    have hle : min (1 / 4 : ℝ) (ε / 4) ≤ ε / 4 := min_le_right _ _
    nlinarith
  have hMaxevent := (hMax δ hδ).eventually_lt_const hη
  obtain ⟨N, hN⟩ := eventually_atTop.1 hMaxevent
  refine ⟨N, fun n hn => ?_⟩
  have hMaxn : μ {ω | δ ≤ dist (maxLeverageStar (stackRegressors X n ω)) 0} < η :=
    hN n hn
  have hcover :
      {ω | ε ≤ dist
          (leverageAdjustmentWeightNormStar (fun h => (1 - h)⁻¹)
            (stackRegressors X n ω)) 0} ⊆
        {ω | δ ≤ dist (maxLeverageStar (stackRegressors X n ω)) 0} := by
    intro ω hω
    by_contra hsmall
    have hmax_lt : maxLeverageStar (stackRegressors X n ω) < δ := by
      have hdist_lt : dist (maxLeverageStar (stackRegressors X n ω)) 0 < δ :=
        not_le.mp hsmall
      simpa [Real.dist_eq, maxLeverageStar, abs_of_nonneg (norm_nonneg _)] using hdist_lt
    have hweight_lt :
        leverageAdjustmentWeightNormStar (fun h => (1 - h)⁻¹)
          (stackRegressors X n ω) < 2 * δ :=
      leverageAdjustmentWeightNormStar_hc2_lt_of_maxLeverageStar_lt
        (X := stackRegressors X n ω) hδ hδ_half hmax_lt
    have hdist_lt :
        dist
            (leverageAdjustmentWeightNormStar (fun h => (1 - h)⁻¹)
              (stackRegressors X n ω))
            0 < ε := by
      simpa [Real.dist_eq, leverageAdjustmentWeightNormStar,
        abs_of_nonneg (norm_nonneg _)] using
        lt_trans hweight_lt htwoδ_lt_ε
    exact (not_le_of_gt hdist_lt) hω
  exact le_of_lt (lt_of_le_of_lt (measure_mono hcover) hMaxn)

/-- HC3 adjustment-weight norms are `oₚ(1)` once maximal leverage is `oₚ(1)`. -/
theorem leverageAdjustmentWeightNormStar_hc3_tendstoInMeasure_zero_of_maxLeverageStar
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)}
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        leverageAdjustmentWeightNormStar (fun h => ((1 - h)⁻¹) ^ 2)
          (stackRegressors X n ω))
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hMax ⊢
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro η hη
  let δ : ℝ := min (1 / 4 : ℝ) (ε / 16)
  have hδ : 0 < δ := by
    dsimp [δ]
    refine lt_min ?_ ?_
    · norm_num
    · positivity
  have hδ_half : δ ≤ 1 / 2 := by
    dsimp [δ]
    have hle : min (1 / 4 : ℝ) (ε / 16) ≤ 1 / 4 := min_le_left _ _
    linarith
  have heightδ_lt_ε : 8 * δ < ε := by
    dsimp [δ]
    have hle : min (1 / 4 : ℝ) (ε / 16) ≤ ε / 16 := min_le_right _ _
    nlinarith
  have hMaxevent := (hMax δ hδ).eventually_lt_const hη
  obtain ⟨N, hN⟩ := eventually_atTop.1 hMaxevent
  refine ⟨N, fun n hn => ?_⟩
  have hMaxn : μ {ω | δ ≤ dist (maxLeverageStar (stackRegressors X n ω)) 0} < η :=
    hN n hn
  have hcover :
      {ω | ε ≤ dist
          (leverageAdjustmentWeightNormStar (fun h => ((1 - h)⁻¹) ^ 2)
            (stackRegressors X n ω)) 0} ⊆
        {ω | δ ≤ dist (maxLeverageStar (stackRegressors X n ω)) 0} := by
    intro ω hω
    by_contra hsmall
    have hmax_lt : maxLeverageStar (stackRegressors X n ω) < δ := by
      have hdist_lt : dist (maxLeverageStar (stackRegressors X n ω)) 0 < δ :=
        not_le.mp hsmall
      simpa [Real.dist_eq, maxLeverageStar, abs_of_nonneg (norm_nonneg _)] using hdist_lt
    have hweight_lt :
        leverageAdjustmentWeightNormStar (fun h => ((1 - h)⁻¹) ^ 2)
          (stackRegressors X n ω) < 8 * δ :=
      leverageAdjustmentWeightNormStar_hc3_lt_of_maxLeverageStar_lt
        (X := stackRegressors X n ω) hδ hδ_half hmax_lt
    have hdist_lt :
        dist
            (leverageAdjustmentWeightNormStar (fun h => ((1 - h)⁻¹) ^ 2)
              (stackRegressors X n ω))
            0 < ε := by
      simpa [Real.dist_eq, leverageAdjustmentWeightNormStar,
        abs_of_nonneg (norm_nonneg _)] using
        lt_trans hweight_lt heightδ_lt_ε
    exact (not_le_of_gt hdist_lt) hω
  exact le_of_lt (lt_of_le_of_lt (measure_mono hcover) hMaxn)

/-- The residual absolute-weight average is nonnegative. -/
theorem sampleScoreCovarianceResidualAbsWeightStar_nonneg
    (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) :
    0 ≤ sampleScoreCovarianceResidualAbsWeightStar X y a b := by
  unfold sampleScoreCovarianceResidualAbsWeightStar
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun i _ => abs_nonneg _))

/-- Diagonal entries of the feasible HC0 middle matrix are nonnegative. -/
theorem sampleScoreCovarianceStar_apply_self_nonneg
    (X : Matrix n k ℝ) (y : n → ℝ) (a : k) :
    0 ≤ sampleScoreCovarianceStar X y a a := by
  simp [sampleScoreCovarianceStar, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  refine mul_nonneg (inv_nonneg.mpr (show 0 ≤ (Fintype.card n : ℝ) by positivity)) ?_
  refine Finset.sum_nonneg ?_
  intro i _
  have hsq : 0 ≤ ((olsResidualStar X y i) * X i a) ^ 2 := sq_nonneg _
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq

/-- The absolute residual-score average for entry `(a,b)` is bounded by the sum
of the two corresponding HC0 diagonal sample averages. -/
theorem sampleScoreCovarianceResidualAbsWeightStar_le_diag_add
    (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) :
    sampleScoreCovarianceResidualAbsWeightStar X y a b ≤
      sampleScoreCovarianceStar X y a a + sampleScoreCovarianceStar X y b b := by
  calc
    sampleScoreCovarianceResidualAbsWeightStar X y a b
        ≤ (Fintype.card n : ℝ)⁻¹ *
            ∑ i : n, ((olsResidualStar X y i) ^ 2 * X i a * X i a +
              (olsResidualStar X y i) ^ 2 * X i b * X i b) := by
          unfold sampleScoreCovarianceResidualAbsWeightStar
          refine mul_le_mul_of_nonneg_left ?_
            (inv_nonneg.mpr (show 0 ≤ (Fintype.card n : ℝ) by positivity))
          refine Finset.sum_le_sum ?_
          intro i _
          have hr2_nonneg : 0 ≤ (olsResidualStar X y i) ^ 2 := sq_nonneg _
          have habs : |X i a * X i b| ≤ X i a * X i a + X i b * X i b := by
            have habs2 : 2 * |X i a * X i b| ≤ X i a * X i a + X i b * X i b := by
              rw [abs_mul, two_mul]
              have htwo : 2 * |X i a| * |X i b| ≤ X i a * X i a + X i b * X i b :=
                by simpa [sq_abs, pow_two] using
                  (two_mul_le_add_sq |X i a| |X i b|)
              nlinarith
            nlinarith [abs_nonneg (X i a * X i b), habs2]
          calc
            |(olsResidualStar X y i) ^ 2 * X i a * X i b|
                = (olsResidualStar X y i) ^ 2 * |X i a * X i b| := by
                    rw [show
                      (olsResidualStar X y i) ^ 2 * X i a * X i b =
                        (olsResidualStar X y i) ^ 2 * (X i a * X i b) by ring]
                    rw [abs_mul, abs_of_nonneg hr2_nonneg]
            _ ≤ (olsResidualStar X y i) ^ 2 * (X i a * X i a + X i b * X i b) :=
                  mul_le_mul_of_nonneg_left habs hr2_nonneg
            _ = (olsResidualStar X y i) ^ 2 * X i a * X i a +
                  (olsResidualStar X y i) ^ 2 * X i b * X i b := by
                  ring
    _ = sampleScoreCovarianceStar X y a a + sampleScoreCovarianceStar X y b b := by
      simp [sampleScoreCovarianceStar, Matrix.smul_apply, Matrix.sum_apply,
        Matrix.vecMulVec_apply, smul_eq_mul, pow_two]
      rw [Finset.sum_add_distrib, mul_add]
      let c : ℝ := (Fintype.card n : ℝ)⁻¹
      have hA :
          ∑ x : n, olsResidualStar X y x * olsResidualStar X y x * X x a * X x a =
            ∑ x : n, olsResidualStar X y x * (olsResidualStar X y x * (X x a * X x a)) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        ring
      have hB :
          ∑ x : n, olsResidualStar X y x * olsResidualStar X y x * X x b * X x b =
            ∑ x : n, olsResidualStar X y x * (olsResidualStar X y x * (X x b * X x b)) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        ring
      calc
        c * ∑ x : n, olsResidualStar X y x * olsResidualStar X y x * X x a * X x a +
            c * ∑ x : n, olsResidualStar X y x * olsResidualStar X y x * X x b * X x b
            = c * ∑ x : n, olsResidualStar X y x * (olsResidualStar X y x * (X x a * X x a)) +
                c * ∑ x : n, olsResidualStar X y x * olsResidualStar X y x * X x b * X x b := by
              rw [hA]
        _ = c * ∑ x : n, olsResidualStar X y x * (olsResidualStar X y x * (X x a * X x a)) +
              c * ∑ x : n, olsResidualStar X y x * (olsResidualStar X y x * (X x b * X x b)) := by
              rw [hB]

/-- Deterministic entrywise bound for generic leverage adjustments.

The scalar HC2/HC3 remainder is bounded by the largest leverage-adjustment
weight times the absolute residual-score average. -/
theorem sampleScoreCovarianceLeverageAdjustmentEntryStar_abs_le
    (weight : ℝ → ℝ) (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) :
    |sampleScoreCovarianceLeverageAdjustmentEntryStar weight X y a b| ≤
      leverageAdjustmentWeightNormStar weight X *
        sampleScoreCovarianceResidualAbsWeightStar X y a b := by
  classical
  let c : ℝ := (Fintype.card n : ℝ)⁻¹
  let base : n → ℝ := fun i => (olsResidualStar X y i) ^ 2 * X i a * X i b
  have hc_nonneg : 0 ≤ c := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hentry :
      sampleScoreCovarianceLeverageAdjustmentEntryStar weight X y a b =
        c * ∑ i : n, (weight (leverageStar X i) - 1) * base i := by
    simp [sampleScoreCovarianceLeverageAdjustmentEntryStar, c, base, mul_assoc]
  have hsum_abs :
      |∑ i : n, (weight (leverageStar X i) - 1) * base i| ≤
        ∑ i : n, |(weight (leverageStar X i) - 1) * base i| :=
    Finset.abs_sum_le_sum_abs _ _
  have hsum_bound :
      ∑ i : n, |(weight (leverageStar X i) - 1) * base i| ≤
        ∑ i : n, leverageAdjustmentWeightNormStar weight X * |base i| := by
    refine Finset.sum_le_sum ?_
    intro i _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      (leverageAdjustmentWeight_abs_le_norm weight X i) (abs_nonneg _)
  calc
    |sampleScoreCovarianceLeverageAdjustmentEntryStar weight X y a b|
        = c * |∑ i : n, (weight (leverageStar X i) - 1) * base i| := by
          rw [hentry, abs_mul, abs_of_nonneg hc_nonneg]
    _ ≤ c * ∑ i : n, |(weight (leverageStar X i) - 1) * base i| :=
          mul_le_mul_of_nonneg_left hsum_abs hc_nonneg
    _ ≤ c * ∑ i : n, leverageAdjustmentWeightNormStar weight X * |base i| :=
          mul_le_mul_of_nonneg_left hsum_bound hc_nonneg
    _ = leverageAdjustmentWeightNormStar weight X *
          sampleScoreCovarianceResidualAbsWeightStar X y a b := by
          rw [← Finset.mul_sum]
          simp [sampleScoreCovarianceResidualAbsWeightStar, c, base]
          ring

/-- Scalar leverage-adjustment entries are `oₚ(1)` when the largest adjustment
weight is `oₚ(1)` and the corresponding absolute residual-score average is
`Oₚ(1)`. -/
theorem sampleScoreCovarianceLeverageAdjustmentEntryStar_tendstoInMeasure_zero_of_weight_norm
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (weight : ℝ → ℝ) (a b : k)
    (hWeight : TendstoInMeasure μ
      (fun n ω =>
        leverageAdjustmentWeightNormStar weight (stackRegressors X n ω))
      atTop (fun _ => 0))
    (hAbsWeight : BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceResidualAbsWeightStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceLeverageAdjustmentEntryStar weight
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)
      atTop (fun _ => 0) := by
  have hprod :=
    TendstoInMeasure.mul_boundedInProbability
      (μ := μ) hWeight hAbsWeight
  refine TendstoInMeasure.of_abs_le_zero_real hprod ?_
  intro n ω
  have hnonneg : 0 ≤
      leverageAdjustmentWeightNormStar weight (stackRegressors X n ω) *
        sampleScoreCovarianceResidualAbsWeightStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b := by
    exact mul_nonneg (norm_nonneg _)
      (sampleScoreCovarianceResidualAbsWeightStar_nonneg
        (stackRegressors X n ω) (stackOutcomes y n ω) a b)
  rw [abs_of_nonneg hnonneg]
  exact sampleScoreCovarianceLeverageAdjustmentEntryStar_abs_le
    (weight := weight) (X := stackRegressors X n ω)
    (y := stackOutcomes y n ω) a b

/-- Generic leverage-adjustment convergence from scalar entries.

This turns the remaining HC2/HC3 adjustment goal into one scalar sample-average
goal per matrix entry, leaving the max-leverage argument independent of matrix
convergence bookkeeping. -/
theorem sampleScoreCovarianceLeverageAdjustmentStar_stack_tendstoInMeasure_zero_of_entries
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (weight : ℝ → ℝ)
    (hEntry : ∀ a b : k, TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceLeverageAdjustmentEntryStar weight
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceLeverageAdjustmentStar weight
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0) := by
  refine tendstoInMeasure_pi (μ := μ) (fun a => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun b => ?_)
  have h := hEntry a b
  refine h.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  exact (sampleScoreCovarianceLeverageAdjustmentStar_apply
    (weight := weight) (X := stackRegressors X n ω)
    (y := stackOutcomes y n ω) a b).symm

/-- HC2 adjustment convergence from scalar entrywise adjustment sums. -/
private theorem sampleScoreCovarianceHC2AdjustmentStar_stack_tendstoInMeasure_zero_of_entries
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (hEntry : ∀ a b : k, TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceLeverageAdjustmentEntryStar (fun h => (1 - h)⁻¹)
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceHC2AdjustmentStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0) := by
  simpa [sampleScoreCovarianceHC2AdjustmentStar] using
    sampleScoreCovarianceLeverageAdjustmentStar_stack_tendstoInMeasure_zero_of_entries
      (μ := μ) (X := X) (y := y) (weight := fun h => (1 - h)⁻¹) hEntry

/-- HC3 adjustment convergence from scalar entrywise adjustment sums. -/
private theorem sampleScoreCovarianceHC3AdjustmentStar_stack_tendstoInMeasure_zero_of_entries
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (hEntry : ∀ a b : k, TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceLeverageAdjustmentEntryStar
          (fun h => ((1 - h)⁻¹) ^ 2)
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceHC3AdjustmentStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0) := by
  simpa [sampleScoreCovarianceHC3AdjustmentStar] using
    sampleScoreCovarianceLeverageAdjustmentStar_stack_tendstoInMeasure_zero_of_entries
      (μ := μ) (X := X) (y := y)
      (weight := fun h => ((1 - h)⁻¹) ^ 2) hEntry

/-- HC2 adjustment entries are `oₚ(1)` once maximal leverage is `oₚ(1)` and
the corresponding residual absolute-weight averages are `Oₚ(1)`. -/
private theorem sampleScoreCovarianceHC2AdjustmentEntryStar_tendstoInMeasure_zero_of_maxLeverageStar
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (a b : k)
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0))
    (hAbsWeight : BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceResidualAbsWeightStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceLeverageAdjustmentEntryStar (fun h => (1 - h)⁻¹)
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)
      atTop (fun _ => 0) := by
  exact sampleScoreCovarianceLeverageAdjustmentEntryStar_tendstoInMeasure_zero_of_weight_norm
    (μ := μ) (X := X) (y := y) (weight := fun h => (1 - h)⁻¹) a b
    (leverageAdjustmentWeightNormStar_hc2_tendstoInMeasure_zero_of_maxLeverageStar
      (μ := μ) (X := X) hMax)
    hAbsWeight

/-- HC3 adjustment entries are `oₚ(1)` once maximal leverage is `oₚ(1)` and
the corresponding residual absolute-weight averages are `Oₚ(1)`. -/
private theorem sampleScoreCovarianceHC3AdjustmentEntryStar_tendstoInMeasure_zero_of_maxLeverageStar
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (a b : k)
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0))
    (hAbsWeight : BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceResidualAbsWeightStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceLeverageAdjustmentEntryStar
          (fun h => ((1 - h)⁻¹) ^ 2)
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)
      atTop (fun _ => 0) := by
  exact sampleScoreCovarianceLeverageAdjustmentEntryStar_tendstoInMeasure_zero_of_weight_norm
    (μ := μ) (X := X) (y := y) (weight := fun h => ((1 - h)⁻¹) ^ 2) a b
    (leverageAdjustmentWeightNormStar_hc3_tendstoInMeasure_zero_of_maxLeverageStar
      (μ := μ) (X := X) hMax)
    hAbsWeight

/-- HC2 adjustment convergence from maximal leverage and residual
absolute-weight boundedness. -/
theorem sampleScoreCovarianceHC2AdjustmentStar_stack_tendstoInMeasure_zero_of_maxLeverageStar
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0))
    (hAbsWeight : ∀ a b : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceResidualAbsWeightStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceHC2AdjustmentStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0) := by
  exact sampleScoreCovarianceHC2AdjustmentStar_stack_tendstoInMeasure_zero_of_entries
    (μ := μ) (X := X) (y := y) (fun a b =>
      sampleScoreCovarianceHC2AdjustmentEntryStar_tendstoInMeasure_zero_of_maxLeverageStar
        (μ := μ) (X := X) (y := y) a b hMax (hAbsWeight a b))

/-- HC3 adjustment convergence from maximal leverage and residual
absolute-weight boundedness. -/
theorem sampleScoreCovarianceHC3AdjustmentStar_stack_tendstoInMeasure_zero_of_maxLeverageStar
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {y : ℕ → Ω → ℝ}
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0))
    (hAbsWeight : ∀ a b : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceResidualAbsWeightStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceHC3AdjustmentStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0) := by
  exact sampleScoreCovarianceHC3AdjustmentStar_stack_tendstoInMeasure_zero_of_entries
    (μ := μ) (X := X) (y := y) (fun a b =>
      sampleScoreCovarianceHC3AdjustmentEntryStar_tendstoInMeasure_zero_of_maxLeverageStar
        (μ := μ) (X := X) (y := y) a b hMax (hAbsWeight a b))

/-- **Theorem 7.6 residual-score expansion, entrywise form.**

Under the linear model, each residual score outer product decomposes into the
true-error score outer product, a cross term, and a quadratic estimation-error
term. This is the per-observation algebra behind feasible HC0 consistency. -/
theorem residualScoreOuter_linear_model_apply
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (i : n) (a b : k) :
    Matrix.vecMulVec
        (olsResidualStar X (X *ᵥ β + e) i • X i)
        (olsResidualStar X (X *ᵥ β + e) i • X i) a b =
      Matrix.vecMulVec (e i • X i) (e i • X i) a b -
        (2 * e i * (X i ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β))) *
          Matrix.vecMulVec (X i) (X i) a b +
        (X i ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) ^ 2 *
          Matrix.vecMulVec (X i) (X i) a b := by
  rw [olsResidualStar_linear_model_apply]
  simp [Matrix.vecMulVec_apply]
  ring

/-- Cross remainder in the HC0 residual-score expansion. -/
noncomputable def sampleScoreCovarianceCrossRemainder
    (X : Matrix n k ℝ) (e : n → ℝ) (d : k → ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n, (2 * e i * (X i ⬝ᵥ d)) • Matrix.vecMulVec (X i) (X i)

/-- Empirical third-moment weight multiplying one coordinate of `β̂ - β` in the
HC0 cross remainder. -/
noncomputable def sampleScoreCovarianceCrossWeight
    (X : Matrix n k ℝ) (e : n → ℝ) (a b l : k) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * ∑ i : n, 2 * e i * X i l * X i a * X i b

set_option linter.flexible false in
omit [DecidableEq k] in
/-- Coordinate representation of the HC0 cross remainder as coefficient error
times empirical third-moment weights. -/
theorem sampleScoreCovarianceCrossRemainder_apply_eq_sum_weight
    (X : Matrix n k ℝ) (e : n → ℝ) (d : k → ℝ) (a b : k) :
    sampleScoreCovarianceCrossRemainder X e d a b =
      ∑ l : k, d l * sampleScoreCovarianceCrossWeight X e a b l := by
  classical
  unfold sampleScoreCovarianceCrossRemainder sampleScoreCovarianceCrossWeight
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, dotProduct,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [Finset.sum_comm]

/-- Quadratic estimation-error remainder in the HC0 residual-score expansion. -/
noncomputable def sampleScoreCovarianceQuadraticRemainder
    (X : Matrix n k ℝ) (d : k → ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n, (X i ⬝ᵥ d) ^ 2 • Matrix.vecMulVec (X i) (X i)

/-- Empirical fourth-moment weight multiplying a pair of coefficient-error
coordinates in the HC0 quadratic remainder. -/
noncomputable def sampleScoreCovarianceQuadraticWeight
    (X : Matrix n k ℝ) (a b l m : k) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * ∑ i : n, X i l * X i m * X i a * X i b

set_option linter.flexible false in
omit [DecidableEq k] in
/-- Coordinate representation of the HC0 quadratic remainder as products of
coefficient errors times empirical fourth-moment weights. -/
theorem sampleScoreCovarianceQuadraticRemainder_apply_eq_sum_weight
    (X : Matrix n k ℝ) (d : k → ℝ) (a b : k) :
    sampleScoreCovarianceQuadraticRemainder X d a b =
      ∑ l : k, ∑ m : k,
        d l * d m * sampleScoreCovarianceQuadraticWeight X a b l m := by
  classical
  unfold sampleScoreCovarianceQuadraticRemainder sampleScoreCovarianceQuadraticWeight
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, dotProduct,
    Finset.mul_sum, pow_two, mul_assoc, mul_left_comm, mul_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]

/-- **Theorem 7.6 residual-score expansion, sample-average form.**

Under the linear model, the residual HC0 middle matrix equals the true-error
middle matrix minus a cross remainder plus a quadratic estimation-error
remainder. -/
theorem sampleScoreCovarianceStar_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    sampleScoreCovarianceStar X (X *ᵥ β + e) =
      sampleScoreCovarianceIdeal X e -
        sampleScoreCovarianceCrossRemainder X e
          (olsBetaStar X (X *ᵥ β + e) - β) +
        sampleScoreCovarianceQuadraticRemainder X
          (olsBetaStar X (X *ᵥ β + e) - β) := by
  ext a b
  simp [sampleScoreCovarianceStar, sampleScoreCovarianceIdeal,
    sampleScoreCovarianceCrossRemainder, sampleScoreCovarianceQuadraticRemainder,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, Finset.mul_sum]
  ring_nf
  simp_rw [olsResidualStar_sq_linear_model_apply X β e]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [dotProduct_sub]
  ring_nf

/-- Additional WLLN assumptions for the true-error HC0 score covariance average. -/
structure SampleHC0Assumption76 (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    extends SampleCLTAssumption72 μ X e where
  /-- Pairwise independence of the true-error score outer products. -/
  indep_score_outer : Pairwise ((· ⟂ᵢ[μ] ·) on
    (fun i ω => Matrix.vecMulVec (e i ω • X i ω) (e i ω • X i ω)))
  /-- Identical distribution of the true-error score outer products. -/
  ident_score_outer : ∀ i,
    IdentDistrib
      (fun ω => Matrix.vecMulVec (e i ω • X i ω) (e i ω • X i ω))
      (fun ω => Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω)) μ μ
  /-- Integrability of the true-error score outer product. -/
  int_score_outer :
    Integrable (fun ω => Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω)) μ

/-- Descriptive public condition package for the current Lean proof behind the
robust covariance / t-statistic / Wald layer in Hansen Chapter 7.

This is stronger than bare textbook Assumption 7.2: it packages the score CLT
bundle together with the true-error score-outer-product WLLN assumptions used to
prove HC0 consistency, and the later HC1/HC2/HC3 public wrappers still build on
that stronger sufficient layer. It extends the internal
`SampleHC0Assumption76` proof record. -/
structure RobustCovarianceConsistencyConditions (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    extends SampleHC0Assumption76 μ X e

namespace RobustCovarianceConsistencyConditions

/-- Promote the internal HC0 proof package to the public Chapter 7 robust-covariance condition. -/
protected def ofSample
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) :
    RobustCovarianceConsistencyConditions μ X e where
  toSampleHC0Assumption76 := h

end RobustCovarianceConsistencyConditions

omit [Fintype k] [DecidableEq k] in
/-- The ideal HC0 score covariance average of stacked samples is the range-indexed
sample mean used by the WLLN. -/
theorem sampleScoreCovarianceIdeal_stack_eq_avg
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    sampleScoreCovarianceIdeal (stackRegressors X n ω) (stackErrors e n ω) =
      (n : ℝ)⁻¹ •
        ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (e i ω • X i ω) (e i ω • X i ω) := by
  unfold sampleScoreCovarianceIdeal stackErrors stackRegressors
  rw [Fintype.card_fin]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun i => Matrix.vecMulVec (e i ω • X i ω) (e i ω • X i ω)) n

/-- Under the HC0 WLLN assumptions, the true-error score covariance average
converges to `E[e₀²X₀X₀']`. -/
theorem sampleScoreCovarianceIdeal_stack_tendstoInMeasure_scoreSecondMomentMatrix
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) :
    TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceIdeal (stackRegressors X n ω) (stackErrors e n ω))
      atTop
      (fun _ => scoreSecondMomentMatrix μ X e) := by
  have hfun_eq : (fun n ω =>
        sampleScoreCovarianceIdeal (stackRegressors X n ω) (stackErrors e n ω)) =
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
        ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (e i ω • X i ω) (e i ω • X i ω)) := by
    funext n ω
    rw [sampleScoreCovarianceIdeal_stack_eq_avg]
  rw [hfun_eq]
  exact tendstoInMeasure_wlln
    (fun i ω => Matrix.vecMulVec (e i ω • X i ω) (e i ω • X i ω))
    h.int_score_outer h.indep_score_outer h.ident_score_outer

/-- Under the HC0 assumptions and orthogonality, `E[e₀²X₀X₀']` is Hansen's
score covariance matrix `Ω`. -/
theorem scoreSecondMomentMatrix_eq_scoreCovarianceMatrix
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) :
    scoreSecondMomentMatrix μ X e = scoreCovarianceMatrix μ X e := by
  ext j l
  calc
    scoreSecondMomentMatrix μ X e j l
        = ∫ ω, (Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω)) j l ∂μ := by
          unfold scoreSecondMomentMatrix
          exact integral_apply_apply (μ := μ)
            (f := fun ω => Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω))
            h.int_score_outer j l
    _ = ∫ ω, (e 0 ω • X 0 ω) j * (e 0 ω • X 0 ω) l ∂μ := by
          rfl
    _ = scoreCovarianceMatrix μ X e j l := by
          exact (scoreCovarianceMatrix_apply_eq_secondMoment
            (μ := μ) (X := X) (e := e) h.toSampleCLTAssumption72 j l).symm

/-- **Theorem 7.6 ideal-`Ω` WLLN.**

The true-error HC0 score covariance average converges in probability to Hansen's
score covariance matrix `Ω`. This is the first, WLLN-driven term in the proof
of heteroskedastic covariance consistency. -/
theorem sampleScoreCovarianceIdeal_stack_tendstoInMeasure_scoreCovarianceMatrix
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) :
    TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceIdeal (stackRegressors X n ω) (stackErrors e n ω))
      atTop
      (fun _ => scoreCovarianceMatrix μ X e) := by
  simpa [scoreSecondMomentMatrix_eq_scoreCovarianceMatrix (μ := μ) (X := X) (e := e) h]
    using sampleScoreCovarianceIdeal_stack_tendstoInMeasure_scoreSecondMomentMatrix
      (μ := μ) (X := X) (e := e) h

/-- **Hansen Theorem 7.6, residual HC0 middle-matrix assembly.**

If the cross and quadratic residual-score remainders in
`sampleScoreCovarianceStar_linear_model` are `oₚ(1)`, then the feasible HC0
middle matrix `n⁻¹∑êᵢ²XᵢXᵢ'` converges in probability to `Ω`. -/
theorem sampleScoreCovarianceStar_stack_tendstoInMeasure_scoreCovarianceMatrix_of_remainders
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hCross : TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceCrossRemainder
          (stackRegressors X n ω) (stackErrors e n ω)
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun _ => 0))
    (hQuad : TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticRemainder
          (stackRegressors X n ω)
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e) := by
  let ideal : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    sampleScoreCovarianceIdeal (stackRegressors X n ω) (stackErrors e n ω)
  let cross : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    sampleScoreCovarianceCrossRemainder
      (stackRegressors X n ω) (stackErrors e n ω)
      (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)
  let quad : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    sampleScoreCovarianceQuadraticRemainder
      (stackRegressors X n ω)
      (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)
  have hIdeal := sampleScoreCovarianceIdeal_stack_tendstoInMeasure_scoreCovarianceMatrix
    (μ := μ) (X := X) (e := e) h
  refine tendstoInMeasure_pi (μ := μ) (fun a => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun b => ?_)
  have hIdeal_ab : TendstoInMeasure μ
      (fun n ω => ideal n ω a b) atTop
      (fun _ => scoreCovarianceMatrix μ X e a b) := by
    simpa [ideal] using TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hIdeal a) b
  have hCross_ab : TendstoInMeasure μ
      (fun n ω => cross n ω a b) atTop (fun _ => 0) := by
    simpa [cross] using TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hCross a) b
  have hQuad_ab : TendstoInMeasure μ
      (fun n ω => quad n ω a b) atTop (fun _ => 0) := by
    simpa [quad] using TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hQuad a) b
  have hCentered := TendstoInMeasure.sub_limit_zero_real hIdeal_ab
  have hSub := TendstoInMeasure.sub_zero_real hCentered hCross_ab
  have hAdd := TendstoInMeasure.add_zero_real hSub hQuad_ab
  refine TendstoInMeasure.of_sub_limit_zero_real ?_
  refine hAdd.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  have hstack := stack_linear_model X e y β hmodel n ω
  have hexp := sampleScoreCovarianceStar_linear_model
    (stackRegressors X n ω) β (stackErrors e n ω)
  calc
    (ideal n ω a b - scoreCovarianceMatrix μ X e a b) -
        cross n ω a b + quad n ω a b
        =
        (ideal n ω - cross n ω + quad n ω) a b -
          scoreCovarianceMatrix μ X e a b := by
          simp [Matrix.sub_apply, Matrix.add_apply]
          ring
    _ = sampleScoreCovarianceStar (stackRegressors X n ω) (stackOutcomes y n ω) a b -
        scoreCovarianceMatrix μ X e a b := by
          rw [hstack, hexp]
          simp [ideal, cross, quad, hstack]

/-- **Theorem 7.6 cross-remainder control.**

If each empirical third-moment weight in the HC0 cross remainder is bounded in
probability, consistency of `β̂*` makes the cross remainder `oₚ(1)`. -/
theorem sampleScoreCovarianceCrossRemainder_stack_tendstoInMeasure_zero_of_bounded_weights
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceCrossRemainder
          (stackRegressors X n ω) (stackErrors e n ω)
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun _ => 0) := by
  have hBeta := olsBetaStar_stack_tendstoInMeasure_beta
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel
  refine tendstoInMeasure_pi (μ := μ) (fun a => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun b => ?_)
  have hTerm : ∀ l ∈ (Finset.univ : Finset k),
      TendstoInMeasure μ
        (fun n ω =>
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) l *
            sampleScoreCovarianceCrossWeight
              (stackRegressors X n ω) (stackErrors e n ω) a b l)
        atTop (fun _ => 0) := by
    intro l _
    have hBeta_l : TendstoInMeasure μ
        (fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) l)
        atTop (fun _ => β l) := by
      simpa using TendstoInMeasure.pi_apply hBeta l
    have hd_l : TendstoInMeasure μ
        (fun n ω =>
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) l)
        atTop (fun _ => 0) := by
      simpa [Pi.sub_apply] using TendstoInMeasure.sub_limit_zero_real hBeta_l
    exact TendstoInMeasure.mul_boundedInProbability hd_l (hWeight a b l)
  have hsum := tendstoInMeasure_finset_sum_zero_real (μ := μ)
    (s := (Finset.univ : Finset k))
    (X := fun l n ω =>
      (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) l *
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l)
    hTerm
  refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  exact (sampleScoreCovarianceCrossRemainder_apply_eq_sum_weight
    (stackRegressors X n ω) (stackErrors e n ω)
    (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) a b).symm

/-- **Theorem 7.6 quadratic-remainder control.**

If each empirical fourth-moment weight in the HC0 quadratic remainder is bounded
in probability, consistency of `β̂*` makes the quadratic remainder `oₚ(1)`. -/
theorem sampleScoreCovarianceQuadraticRemainder_stack_tendstoInMeasure_zero_of_bounded_weights
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticRemainder
          (stackRegressors X n ω)
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun _ => 0) := by
  let d : ℕ → Ω → k → ℝ := fun n ω =>
    olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β
  have hBeta := olsBetaStar_stack_tendstoInMeasure_beta
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel
  have hd : ∀ l : k, TendstoInMeasure μ (fun n ω => d n ω l) atTop (fun _ => 0) := by
    intro l
    have hBeta_l : TendstoInMeasure μ
        (fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) l)
        atTop (fun _ => β l) := by
      simpa using TendstoInMeasure.pi_apply hBeta l
    simpa [d, Pi.sub_apply] using TendstoInMeasure.sub_limit_zero_real hBeta_l
  refine tendstoInMeasure_pi (μ := μ) (fun a => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun b => ?_)
  have hInner : ∀ l ∈ (Finset.univ : Finset k),
      TendstoInMeasure μ
        (fun n ω => ∑ m : k,
          d n ω l * d n ω m *
            sampleScoreCovarianceQuadraticWeight
              (stackRegressors X n ω) a b l m)
        atTop (fun _ => 0) := by
    intro l _
    have hTerm : ∀ m ∈ (Finset.univ : Finset k),
        TendstoInMeasure μ
          (fun n ω =>
            d n ω l * d n ω m *
              sampleScoreCovarianceQuadraticWeight
                (stackRegressors X n ω) a b l m)
          atTop (fun _ => 0) := by
      intro m _
      have hprod := TendstoInMeasure.mul_zero_real (hd l) (hd m)
      exact TendstoInMeasure.mul_boundedInProbability hprod (hWeight a b l m)
    simpa using tendstoInMeasure_finset_sum_zero_real (μ := μ)
      (s := (Finset.univ : Finset k))
      (X := fun m n ω =>
        d n ω l * d n ω m *
          sampleScoreCovarianceQuadraticWeight
            (stackRegressors X n ω) a b l m)
      hTerm
  have hsum := tendstoInMeasure_finset_sum_zero_real (μ := μ)
    (s := (Finset.univ : Finset k))
    (X := fun l n ω => ∑ m : k,
      d n ω l * d n ω m *
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)
    hInner
  refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  exact (sampleScoreCovarianceQuadraticRemainder_apply_eq_sum_weight
    (stackRegressors X n ω) (d n ω) a b).symm

/-- **Hansen Theorem 7.6, residual HC0 middle matrix under bounded weights.**

The feasible HC0 middle matrix converges to `Ω` when the empirical third- and
fourth-moment weights appearing in the residual-score remainders are bounded in
probability. -/
theorem sampleScoreCovarianceStar_stack_tendstoInMeasure_scoreCovarianceMatrix_of_bounded_weights
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e) := by
  have hCross :=
    sampleScoreCovarianceCrossRemainder_stack_tendstoInMeasure_zero_of_bounded_weights
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hCrossWeight
  have hQuad :=
    sampleScoreCovarianceQuadraticRemainder_stack_tendstoInMeasure_zero_of_bounded_weights
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hQuadWeight
  exact sampleScoreCovarianceStar_stack_tendstoInMeasure_scoreCovarianceMatrix_of_remainders
    (μ := μ) (X := X) (e := e) (y := y) h β hmodel hCross hQuad

/-- If the feasible HC0 middle matrix converges entrywise in probability, then
every residual absolute-weight average is `Oₚ(1)`. -/
theorem sampleScoreCovarianceResidualAbsWeightStar_boundedInProbability_of_middle
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hHC0 : TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e))
    (a b : k) :
    BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceResidualAbsWeightStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b) := by
  let diagA : ℕ → Ω → ℝ := fun n ω =>
    sampleScoreCovarianceStar
      (stackRegressors X n ω) (stackOutcomes y n ω) a a
  let diagB : ℕ → Ω → ℝ := fun n ω =>
    sampleScoreCovarianceStar
      (stackRegressors X n ω) (stackOutcomes y n ω) b b
  have hDiagA : TendstoInMeasure μ diagA atTop
      (fun _ => scoreCovarianceMatrix μ X e a a) := by
    simpa [diagA] using TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hHC0 a) a
  have hDiagB : TendstoInMeasure μ diagB atTop
      (fun _ => scoreCovarianceMatrix μ X e b b) := by
    simpa [diagB] using TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hHC0 b) b
  have hDiagA_bdd : BoundedInProbability μ diagA :=
    BoundedInProbability.of_tendstoInMeasure_const hDiagA
  have hDiagB_bdd : BoundedInProbability μ diagB :=
    BoundedInProbability.of_tendstoInMeasure_const hDiagB
  have hSum_bdd : BoundedInProbability μ (fun n ω => diagA n ω + diagB n ω) :=
    BoundedInProbability.add hDiagA_bdd hDiagB_bdd
  refine BoundedInProbability.of_abs_le hSum_bdd ?_
  intro n ω
  have hleft_nonneg :
      0 ≤ sampleScoreCovarianceResidualAbsWeightStar
        (stackRegressors X n ω) (stackOutcomes y n ω) a b :=
    sampleScoreCovarianceResidualAbsWeightStar_nonneg
      (stackRegressors X n ω) (stackOutcomes y n ω) a b
  have hright_nonneg :
      0 ≤ diagA n ω + diagB n ω := by
    exact add_nonneg
      (sampleScoreCovarianceStar_apply_self_nonneg
        (stackRegressors X n ω) (stackOutcomes y n ω) a)
      (sampleScoreCovarianceStar_apply_self_nonneg
        (stackRegressors X n ω) (stackOutcomes y n ω) b)
  rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg]
  simpa [diagA, diagB] using
    sampleScoreCovarianceResidualAbsWeightStar_le_diag_add
      (stackRegressors X n ω) (stackOutcomes y n ω) a b

/-- Under the HC0 bounded-weight hypotheses, every residual absolute-weight
average is `Oₚ(1)`. -/
theorem sampleScoreCovarianceResidualAbsWeightStar_boundedInProbability_of_bounded_weights
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (a b : k) :
    BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceResidualAbsWeightStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b) := by
  have hHC0 :=
    sampleScoreCovarianceStar_stack_tendstoInMeasure_scoreCovarianceMatrix_of_bounded_weights
      (μ := μ) (X := X) (e := e) (y := y)
      h β hmodel hCrossWeight hQuadWeight
  exact sampleScoreCovarianceResidualAbsWeightStar_boundedInProbability_of_middle
    (μ := μ) (X := X) (e := e) (y := y) hHC0 a b

/-- HC2 adjustment convergence from the existing HC0 bounded-weight hypotheses
plus maximal leverage `oₚ(1)`. -/
theorem sampleScoreCovarianceHC2AdjustmentStar_stack_tendstoInMeasure_zero_of_bounded_weights_and_maxLeverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceHC2AdjustmentStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0) := by
  have hAbsWeight : ∀ a b : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceResidualAbsWeightStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b) := by
    intro a b
    exact sampleScoreCovarianceResidualAbsWeightStar_boundedInProbability_of_bounded_weights
      (μ := μ) (X := X) (e := e) (y := y)
      h β hmodel hCrossWeight hQuadWeight a b
  exact sampleScoreCovarianceHC2AdjustmentStar_stack_tendstoInMeasure_zero_of_maxLeverageStar
    (μ := μ) (X := X) (y := y) hMax hAbsWeight

/-- HC3 adjustment convergence from the existing HC0 bounded-weight hypotheses
plus maximal leverage `oₚ(1)`. -/
theorem sampleScoreCovarianceHC3AdjustmentStar_stack_tendstoInMeasure_zero_of_bounded_weights_and_maxLeverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceHC3AdjustmentStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0) := by
  have hAbsWeight : ∀ a b : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceResidualAbsWeightStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b) := by
    intro a b
    exact sampleScoreCovarianceResidualAbsWeightStar_boundedInProbability_of_bounded_weights
      (μ := μ) (X := X) (e := e) (y := y)
      h β hmodel hCrossWeight hQuadWeight a b
  exact sampleScoreCovarianceHC3AdjustmentStar_stack_tendstoInMeasure_zero_of_maxLeverageStar
    (μ := μ) (X := X) (y := y) hMax hAbsWeight

/-- **Generic leverage-adjusted middle matrix from HC0 plus adjustment.**

If the feasible HC0 middle matrix converges to `Ω` and the leverage-weighted
adjustment is `oₚ(1)`, then the corresponding leverage-adjusted middle matrix
also converges to `Ω`. HC2 and HC3 are thin specializations with different
scalar leverage weights. -/
theorem sampleScoreCovarianceLeverageAdjustedStar_stack_tendstoInMeasure_of_adjustment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (weight : ℝ → ℝ)
    (hHC0_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hAdj_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceLeverageAdjustmentStar weight
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hHC0 : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e))
    (hAdj : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceLeverageAdjustmentStar weight
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceLeverageAdjustedStar weight
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e) := by
  have hsum := tendstoInMeasure_add hHC0_meas hAdj_meas hHC0 hAdj
  simpa [sampleScoreCovarianceLeverageAdjustmentStar,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsum

/-- **Hansen Theorem 7.7, HC2 middle matrix from HC0 plus adjustment.**

If the feasible HC0 middle matrix converges to `Ω` and the HC2 leverage
adjustment is `oₚ(1)`, then the HC2 middle matrix also converges to `Ω`. This
isolates the exact leverage remainder left for the HC2 proof. -/
private theorem sampleScoreCovarianceHC2Star_stack_tendstoInMeasure_scoreCovarianceMatrix_of_adjustment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hHC0_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hAdj_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC2AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hHC0 : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e))
    (hAdj : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceHC2AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceHC2Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e) := by
  simpa [sampleScoreCovarianceHC2Star, sampleScoreCovarianceHC2AdjustmentStar] using
    sampleScoreCovarianceLeverageAdjustedStar_stack_tendstoInMeasure_of_adjustment
      (μ := μ) (X := X) (e := e) (y := y)
      (weight := fun h => (1 - h)⁻¹)
      hHC0_meas hAdj_meas hHC0 hAdj

/-- **Hansen Theorem 7.7, HC3 middle matrix from HC0 plus adjustment.**

If the feasible HC0 middle matrix converges to `Ω` and the HC3 leverage
adjustment is `oₚ(1)`, then the HC3 middle matrix also converges to `Ω`. -/
private theorem sampleScoreCovarianceHC3Star_stack_tendstoInMeasure_scoreCovarianceMatrix_of_adjustment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hHC0_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hAdj_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC3AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hHC0 : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e))
    (hAdj : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceHC3AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceHC3Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e) := by
  simpa [sampleScoreCovarianceHC3Star, sampleScoreCovarianceHC3AdjustmentStar] using
    sampleScoreCovarianceLeverageAdjustedStar_stack_tendstoInMeasure_of_adjustment
      (μ := μ) (X := X) (e := e) (y := y)
      (weight := fun h => ((1 - h)⁻¹) ^ 2)
      hHC0_meas hAdj_meas hHC0 hAdj

/-- Hansen's heteroskedastic asymptotic covariance matrix
`V_β := Q⁻¹ Ω Q⁻¹`. -/
noncomputable def heteroskedasticAsymptoticCovariance
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) : Matrix k k ℝ :=
  (popGram μ X)⁻¹ * scoreCovarianceMatrix μ X e * (popGram μ X)⁻¹

/-- **Homoskedastic covariance bridge.**

If the score covariance satisfies the homoskedastic moment identity
`Ω = σ² Q`, then Hansen's homoskedastic asymptotic covariance `σ²Q⁻¹`
equals the robust sandwich covariance `Q⁻¹ΩQ⁻¹`. -/
theorem homoskedasticAsymptoticCovariance_eq_heteroskedasticAsymptoticCovariance
    {μ : Measure Ω}
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (hQ : IsUnit (popGram μ X).det)
    (hΩ : scoreCovarianceMatrix μ X e = errorVariance μ e • popGram μ X) :
    homoskedasticAsymptoticCovariance μ X e =
      heteroskedasticAsymptoticCovariance μ X e := by
  let Q : Matrix k k ℝ := popGram μ X
  let σ2 : ℝ := errorVariance μ e
  calc
    homoskedasticAsymptoticCovariance μ X e
        = σ2 • Q⁻¹ := by
          simp [homoskedasticAsymptoticCovariance, Q, σ2]
    _ = Q⁻¹ * (σ2 • Q) * Q⁻¹ := by
          have hright : Q⁻¹ * (σ2 • Q) * Q⁻¹ = σ2 • Q⁻¹ := by
            rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.nonsing_inv_mul Q hQ]
            simp
          exact hright.symm
    _ = heteroskedasticAsymptoticCovariance μ X e := by
          simp [heteroskedasticAsymptoticCovariance, hΩ, Q, σ2, Matrix.mul_assoc]

/-- The scalar projection variance agrees with the sandwich covariance quadratic form. -/
theorem olsProjectionAsymptoticVariance_eq_quadratic_heteroskedasticAsymptoticCovariance
    {μ : Measure Ω}
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (hX : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ)
    (a : k → ℝ) :
    olsProjectionAsymptoticVariance μ X e a =
      a ⬝ᵥ (heteroskedasticAsymptoticCovariance μ X e *ᵥ a) := by
  let A : Matrix k k ℝ := (popGram μ X)⁻¹
  let Ωm : Matrix k k ℝ := scoreCovarianceMatrix μ X e
  have hA : Aᵀ = A := (popGram_inv_isSymm μ X hX).eq
  calc
    olsProjectionAsymptoticVariance μ X e a
        = (A *ᵥ a) ⬝ᵥ (Ωm *ᵥ (A *ᵥ a)) := by
          simp [olsProjectionAsymptoticVariance, A, Ωm, hA]
    _ = (Matrix.vecMul a A) ⬝ᵥ (Ωm *ᵥ (A *ᵥ a)) := by
          rw [vecMul_eq_mulVec_transpose, hA]
    _ = a ⬝ᵥ (A *ᵥ (Ωm *ᵥ (A *ᵥ a))) := by
          rw [← Matrix.dotProduct_mulVec]
    _ = a ⬝ᵥ ((A * Ωm * A) *ᵥ a) := by
          simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = a ⬝ᵥ (heteroskedasticAsymptoticCovariance μ X e *ᵥ a) := by
          simp [heteroskedasticAsymptoticCovariance, A, Ωm, Matrix.mul_assoc]

/-- Linear-map scalar quadratic forms match the corresponding OLS projection variance. -/
theorem linearMapCovariance_quadratic_eq_olsProjectionAsymptoticVariance
    {μ : Measure Ω}
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q]
    (hX : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ)
    (R : Matrix q k ℝ) (c : q → ℝ) :
    c ⬝ᵥ ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) *ᵥ c) =
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ c) := by
  rw [olsProjectionAsymptoticVariance_eq_quadratic_heteroskedasticAsymptoticCovariance hX]
  let V : Matrix k k ℝ := heteroskedasticAsymptoticCovariance μ X e
  calc
    c ⬝ᵥ ((R * V * Rᵀ) *ᵥ c)
        = c ⬝ᵥ (R *ᵥ (V *ᵥ (Rᵀ *ᵥ c))) := by
          simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (Rᵀ *ᵥ c) ⬝ᵥ (V *ᵥ (Rᵀ *ᵥ c)) := by
          rw [Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose]
    _ = (Rᵀ *ᵥ c) ⬝ᵥ
        (heteroskedasticAsymptoticCovariance μ X e *ᵥ (Rᵀ *ᵥ c)) := by
          simp [V]

/-- For a one-row linear map, the sole sandwich-covariance entry is the projection variance. -/
theorem linearMapCovariance_unit_apply_eq_olsProjectionAsymptoticVariance
    {μ : Measure Ω}
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (hX : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ)
    (R : Matrix Unit k ℝ) :
    (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () =
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) := by
  simpa [dotProduct, Matrix.mulVec] using
    linearMapCovariance_quadratic_eq_olsProjectionAsymptoticVariance
      (μ := μ) (X := X) (e := e) hX R (fun _ : Unit => 1)

/-- **Generic sandwich CMT for Chapter 7 covariance estimators.**

Any totalized covariance estimator with middle matrix converging in probability
to `Ω` inherits the sandwich probability limit `Q⁻¹ Ω Q⁻¹`. This factors the
shared continuous-mapping step out of HC0/HC1/HC2/HC3-style estimators, leaving
each theorem to prove only the consistency of its own middle matrix. -/
theorem sandwichCovarianceStar_tendstoInMeasure_of_middle
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e)
    {middle : ℕ → Ω → Matrix k k ℝ}
    (hmiddle_meas : ∀ n, AEStronglyMeasurable (middle n) μ)
    (hmiddle : TendstoInMeasure μ middle atTop
      (fun _ => scoreCovarianceMatrix μ X e)) :
    TendstoInMeasure μ
      (fun n ω =>
        (sampleGram (stackRegressors X n ω))⁻¹ * middle n ω *
          (sampleGram (stackRegressors X n ω))⁻¹)
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  let invGram : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    (sampleGram (stackRegressors X n ω))⁻¹
  have hGram_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    intro n
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hInv_meas : ∀ n, AEStronglyMeasurable (invGram n) μ := by
    intro n
    exact aestronglyMeasurable_matrix_inv (hGram_meas n)
  have hInv := sampleGramInv_stackRegressors_tendstoInMeasure_popGramInv
    (μ := μ) (X := X) (e := e) h
  have hLeft := tendstoInMeasure_matrix_mul
    (μ := μ) (A := invGram) (B := middle)
    (Ainf := fun _ : Ω => (popGram μ X)⁻¹)
    (Binf := fun _ : Ω => scoreCovarianceMatrix μ X e)
    hInv_meas hmiddle_meas (by simpa [invGram] using hInv) hmiddle
  have hLeft_meas : ∀ n, AEStronglyMeasurable (fun ω => invGram n ω * middle n ω) μ := by
    intro n
    have hprod : AEStronglyMeasurable (fun ω => (invGram n ω, middle n ω)) μ :=
      (hInv_meas n).prodMk (hmiddle_meas n)
    have hcont : Continuous (fun p : Matrix k k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  have hFull := tendstoInMeasure_matrix_mul
    (μ := μ) (A := fun n ω => invGram n ω * middle n ω) (B := invGram)
    (Ainf := fun _ : Ω => (popGram μ X)⁻¹ * scoreCovarianceMatrix μ X e)
    (Binf := fun _ : Ω => (popGram μ X)⁻¹)
    hLeft_meas hInv_meas
    (by simpa [Matrix.mul_assoc] using hLeft) (by simpa [invGram] using hInv)
  simpa [heteroskedasticAsymptoticCovariance, invGram, Matrix.mul_assoc] using hFull

omit [DecidableEq k] in
/-- **Hansen Theorem 7.10, linear covariance continuous mapping.**

If a covariance estimator `V̂β` converges in probability to `Vβ`, then the
linear-function covariance estimator `R V̂β R'` converges to `R Vβ R'`. This is
the matrix CMT core behind covariance estimation for fixed linear functions of
parameters. -/
theorem linearMapCovariance_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {q : Type*} [Fintype q]
    {Vhat : ℕ → Ω → Matrix k k ℝ} {V : Matrix k k ℝ}
    (R : Matrix q k ℝ)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V)) :
    TendstoInMeasure μ
      (fun n ω => R * Vhat n ω * Rᵀ)
      atTop (fun _ => R * V * Rᵀ) := by
  have hR_meas : ∀ _ : ℕ, AEStronglyMeasurable (fun _ : Ω => R) μ :=
    fun _ => aestronglyMeasurable_const
  have hR_conv : TendstoInMeasure μ
      (fun _ : ℕ => fun _ : Ω => R) atTop (fun _ : Ω => R) :=
    tendstoInMeasure_of_tendsto_ae hR_meas
      (ae_of_all μ (fun _ => tendsto_const_nhds))
  have hRt_meas : ∀ _ : ℕ, AEStronglyMeasurable (fun _ : Ω => Rᵀ) μ :=
    fun _ => aestronglyMeasurable_const
  have hRt_conv : TendstoInMeasure μ
      (fun _ : ℕ => fun _ : Ω => Rᵀ) atTop (fun _ : Ω => Rᵀ) :=
    tendstoInMeasure_of_tendsto_ae hRt_meas
      (ae_of_all μ (fun _ => tendsto_const_nhds))
  have hLeft := tendstoInMeasure_matrix_mul_rect
    (μ := μ)
    (A := fun _ : ℕ => fun _ : Ω => R)
    (B := Vhat)
    (Ainf := fun _ : Ω => R)
    (Binf := fun _ : Ω => V)
    hR_meas hV_meas hR_conv hV
  have hLeft_meas : ∀ n, AEStronglyMeasurable (fun ω => R * Vhat n ω) μ := by
    intro n
    have hprod : AEStronglyMeasurable (fun ω => (R, Vhat n ω)) μ :=
      aestronglyMeasurable_const.prodMk (hV_meas n)
    have hcont : Continuous (fun p : Matrix q k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  have hFull := tendstoInMeasure_matrix_mul_rect
    (μ := μ)
    (A := fun n ω => R * Vhat n ω)
    (B := fun _ : ℕ => fun _ : Ω => Rᵀ)
    (Ainf := fun _ : Ω => R * V)
    (Binf := fun _ : Ω => Rᵀ)
    hLeft_meas hRt_meas hLeft hRt_conv
  simpa [Matrix.mul_assoc] using hFull

omit [DecidableEq k] in
/-- **Hansen Theorem 7.10, random linear covariance continuous mapping.**

If a derivative/linearization estimate `R̂ₙ` converges in probability to `R`
and a covariance estimator `V̂ₙ` converges to `V`, then
`R̂ₙ V̂ₙ R̂ₙᵀ →ₚ R V Rᵀ`. This is the generic covariance CMT needed for
nonlinear functions whose plug-in derivative is itself estimated. -/
theorem randomLinearMapCovariance_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {q : Type*} [Fintype q]
    {Rhat : ℕ → Ω → Matrix q k ℝ} {R : Matrix q k ℝ}
    {Vhat : ℕ → Ω → Matrix k k ℝ} {V : Matrix k k ℝ}
    (hR_meas : ∀ n, AEStronglyMeasurable (Rhat n) μ)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hR : TendstoInMeasure μ Rhat atTop (fun _ => R))
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V)) :
    TendstoInMeasure μ
      (fun n ω => Rhat n ω * Vhat n ω * (Rhat n ω)ᵀ)
      atTop (fun _ => R * V * Rᵀ) := by
  have hLeft := tendstoInMeasure_matrix_mul_rect
    (μ := μ)
    (A := Rhat)
    (B := Vhat)
    (Ainf := fun _ : Ω => R)
    (Binf := fun _ : Ω => V)
    hR_meas hV_meas hR hV
  have hLeft_meas : ∀ n, AEStronglyMeasurable
      (fun ω => Rhat n ω * Vhat n ω) μ := by
    intro n
    have hprod : AEStronglyMeasurable (fun ω => (Rhat n ω, Vhat n ω)) μ :=
      (hR_meas n).prodMk (hV_meas n)
    have hcont : Continuous (fun p : Matrix q k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  have htranspose_cont : Continuous (fun M : Matrix q k ℝ => Mᵀ) :=
    continuous_id.matrix_transpose
  have hRt_meas : ∀ n, AEStronglyMeasurable (fun ω => (Rhat n ω)ᵀ) μ :=
    fun n => htranspose_cont.comp_aestronglyMeasurable (hR_meas n)
  have hRt : TendstoInMeasure μ
      (fun n ω => (Rhat n ω)ᵀ) atTop (fun _ : Ω => Rᵀ) :=
    tendstoInMeasure_continuous_comp hR_meas hR htranspose_cont
  have hFull := tendstoInMeasure_matrix_mul_rect
    (μ := μ)
    (A := fun n ω => Rhat n ω * Vhat n ω)
    (B := fun n ω => (Rhat n ω)ᵀ)
    (Ainf := fun _ : Ω => R * V)
    (Binf := fun _ : Ω => Rᵀ)
    hLeft_meas hRt_meas hLeft hRt
  simpa [Matrix.mul_assoc] using hFull

omit [DecidableEq k] in
/-- AEMeasurability of a fixed linear covariance transform `R V Rᵀ`. -/
theorem linearMapCovariance_aestronglyMeasurable
    {μ : Measure Ω}
    {q : Type*}
    {Vhat : Ω → Matrix k k ℝ}
    (R : Matrix q k ℝ)
    (hV_meas : AEStronglyMeasurable Vhat μ) :
    AEStronglyMeasurable (fun ω => R * Vhat ω * Rᵀ) μ := by
  have hLeft : AEStronglyMeasurable (fun ω => R * Vhat ω) μ := by
    have hprod : AEStronglyMeasurable (fun ω => (R, Vhat ω)) μ :=
      aestronglyMeasurable_const.prodMk hV_meas
    have hcont : Continuous (fun p : Matrix q k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  have hprod : AEStronglyMeasurable (fun ω => (R * Vhat ω, Rᵀ)) μ :=
    hLeft.prodMk aestronglyMeasurable_const
  have hcont : Continuous (fun p : Matrix q k ℝ × Matrix k q ℝ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  exact hcont.comp_aestronglyMeasurable hprod

omit [DecidableEq k] in
/-- **Hansen §7.11, asymptotic standard-error CMT.**

If `R V̂β Rᵀ` estimates the asymptotic covariance of a fixed linear function
`R β`, then the square root of any diagonal element converges to the matching
population standard-error scale. This is the standard-error continuous-mapping
face used before forming t-statistics. -/
theorem linearMapCovarianceStdError_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {q : Type*} [Finite q]
    {Vhat : ℕ → Ω → Matrix k k ℝ} {V : Matrix k k ℝ}
    (R : Matrix q k ℝ) (j : q)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V)) :
    TendstoInMeasure μ
      (fun n ω => Real.sqrt ((R * Vhat n ω * Rᵀ) j j))
      atTop (fun _ => Real.sqrt ((R * V * Rᵀ) j j)) := by
  letI : Fintype q := Fintype.ofFinite q
  have hCov := linearMapCovariance_tendstoInMeasure
    (μ := μ) (R := R) hV_meas hV
  have hCov_meas : ∀ n, AEStronglyMeasurable
      (fun ω => R * Vhat n ω * Rᵀ) μ :=
    fun n => linearMapCovariance_aestronglyMeasurable
      (μ := μ) (R := R) (hV_meas n)
  have hentry_meas : ∀ n, AEStronglyMeasurable
      (fun ω => (R * Vhat n ω * Rᵀ) j j) μ := by
    intro n
    have hentry_cont : Continuous (fun M : Matrix q q ℝ => M j j) :=
      (continuous_apply j).comp (continuous_apply j)
    exact hentry_cont.comp_aestronglyMeasurable (hCov_meas n)
  have hentry : TendstoInMeasure μ
      (fun n ω => (R * Vhat n ω * Rᵀ) j j)
      atTop (fun _ => (R * V * Rᵀ) j j) :=
    TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hCov j) j
  exact tendstoInMeasure_continuous_comp hentry_meas hentry Real.continuous_sqrt

/-- **Hansen Theorem 7.10, homoskedastic covariance for fixed linear functions.**

For a fixed linear map `R`, the totalized homoskedastic plug-in covariance
estimator for `R β` converges to `R V⁰β Rᵀ`. -/
theorem linearMap_olsHomoskedasticCovarianceStar_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q]
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    TendstoInMeasure μ
      (fun n ω =>
        R * olsHomoskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)
      atTop (fun _ => R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) := by
  have hV_meas :=
    olsHomoskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hV :=
    olsHomoskedasticCovarianceStar_tendstoInMeasure
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel
  exact linearMapCovariance_tendstoInMeasure
    (μ := μ) (R := R)
    (Vhat := fun n ω =>
      olsHomoskedasticCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
    (V := homoskedasticAsymptoticCovariance μ X e)
    hV_meas hV

/-- **Hansen §7.11/§7.17, homoskedastic standard errors for fixed linear functions.**

The square root of a diagonal element of `R V̂⁰β Rᵀ` converges to the
corresponding population homoskedastic scale. -/
theorem olsHomoskedasticLinearStdErrorStar_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Finite q]
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ) (j : q)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    TendstoInMeasure μ
      (fun n ω =>
        Real.sqrt ((R * olsHomoskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) j j))
      atTop (fun _ =>
        Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) j j)) := by
  have hV_meas :=
    olsHomoskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hV :=
    olsHomoskedasticCovarianceStar_tendstoInMeasure
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel
  exact linearMapCovarianceStdError_tendstoInMeasure
    (μ := μ) (R := R) (j := j)
    (Vhat := fun n ω =>
      olsHomoskedasticCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
    (V := homoskedasticAsymptoticCovariance μ X e)
    hV_meas hV

/-- **Scalar Slutsky division with a positive denominator limit.**

If `Xₙ ⇒ Z` and `Yₙ →ₚ c` for `c > 0`, then `Xₙ / Yₙ ⇒ Z / c`.
The proof clips the denominator at `c / 2` to get a globally continuous map,
then removes the clip because the event `Yₙ < c / 2` has vanishing
probability. -/
theorem tendstoInDistribution_div_of_tendstoInMeasure_const_pos
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (hY : TendstoInMeasure μ Y atTop (fun _ => c))
    (hY_meas : ∀ n, AEMeasurable (Y n) μ)
    (hdiv_meas : ∀ n, AEMeasurable (fun ω => X n ω / Y n ω) μ) :
    TendstoInDistribution
      (fun n ω => X n ω / Y n ω)
      atTop (fun ω => Z ω / c) (fun _ => μ) ν := by
  let c₂ : ℝ := c / 2
  have hc₂ : 0 < c₂ := by positivity
  have hmax_c : max c c₂ = c := by
    have hc₂_le_c : c₂ ≤ c := by
      dsimp [c₂]
      linarith
    exact max_eq_left hc₂_le_c
  have hg : Continuous (fun p : ℝ × ℝ => p.1 / max p.2 c₂) := by
    refine continuous_fst.div (continuous_snd.max continuous_const) ?_
    intro p
    exact ne_of_gt (lt_of_lt_of_le hc₂ (le_max_right p.2 c₂))
  have hclip : TendstoInDistribution
      (fun n ω => X n ω / max (Y n ω) c₂)
      atTop (fun ω => Z ω / c) (fun _ => μ) ν := by
    have hraw := hX.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ => p.1 / max p.2 c₂) hg hY hY_meas
    simpa [Function.comp_def, c₂, hmax_c] using hraw
  have hdiff : TendstoInMeasure μ
      (fun n ω => X n ω / Y n ω - X n ω / max (Y n ω) c₂)
      atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have hYdist := hY
    rw [tendstoInMeasure_iff_dist] at hYdist
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hYdist c₂ hc₂) (fun _ => zero_le _) (fun n => ?_)
    refine measure_mono (fun ω hω => ?_)
    by_contra hnot
    have hdist_lt : dist (Y n ω) c < c₂ := not_le.mp hnot
    have hY_gt : c₂ < Y n ω := by
      rw [Real.dist_eq] at hdist_lt
      have hbounds := abs_lt.mp hdist_lt
      have hc_sub : c - c₂ = c₂ := by
        dsimp [c₂]
        ring
      linarith [hbounds.1, hc_sub]
    have hmax : max (Y n ω) c₂ = Y n ω := max_eq_left hY_gt.le
    have hdiff_zero : X n ω / Y n ω - X n ω / max (Y n ω) c₂ = 0 := by
      simp [hmax]
    have hε_le_zero : ε ≤ 0 := by
      simpa [Real.dist_eq, hdiff_zero] using hω
    exact (not_le_of_gt hε) hε_le_zero
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n ω => X n ω / max (Y n ω) c₂)
    (Y := fun n ω => X n ω / Y n ω)
    (Z := fun ω => Z ω / c)
    hclip hdiff hdiv_meas

/-- A zero-mean Gaussian with variance `c²`, divided by positive `c`, is standard normal. -/
theorem hasLaw_gaussianReal_div_const_standard
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {Z : Ω' → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hZ : HasLaw Z (gaussianReal 0 (c ^ 2).toNNReal) ν) :
    HasLaw (fun ω => Z ω / c) (gaussianReal 0 1) ν := by
  have hdiv := gaussianReal_div_const hZ c
  convert hdiv using 1
  · rw [gaussianReal_ext_iff]
    constructor
    · simp
    · rw [Real.toNNReal_of_nonneg (sq_nonneg c)]
      ext
      simp [hc.ne']

/-- Version of Gaussian normalization with an explicitly identified variance. -/
theorem hasLaw_gaussianReal_div_const_standard_of_variance_eq
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {Z : Ω' → ℝ} {σ2 c : ℝ}
    (hc : 0 < c)
    (hσ : σ2 = c ^ 2)
    (hZ : HasLaw Z (gaussianReal 0 σ2.toNNReal) ν) :
    HasLaw (fun ω => Z ω / c) (gaussianReal 0 1) ν := by
  have hZ' : HasLaw Z (gaussianReal 0 (c ^ 2).toNNReal) ν := by
    rwa [hσ] at hZ
  exact hasLaw_gaussianReal_div_const_standard hc hZ'

/-- Scaling the identity under a standard normal law gives a zero-mean Gaussian
with variance `c²`. -/
theorem hasLaw_const_mul_id_gaussianReal_of_variance_eq
    {σ2 c : ℝ}
    (hσ : σ2 = c ^ 2) :
    HasLaw (fun x : ℝ => c * x) (gaussianReal 0 σ2.toNNReal) (gaussianReal 0 1) := by
  have hid : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hscale := gaussianReal_const_mul hid c
  convert hscale using 1
  · rw [gaussianReal_ext_iff]
    constructor
    · ring
    · rw [hσ, Real.toNNReal_of_nonneg (sq_nonneg c)]
      simp

omit [Fintype k] [DecidableEq k] in
/-- **Hansen Theorem 7.3/7.13, generic matrix-vector distributional CMT.**

If a vector statistic `Tₙ` converges in distribution to `Z` and a random matrix
`Aₙ` converges in probability to a constant matrix `A`, then the transformed
statistic `AₙTₙ` converges in distribution to `AZ`. This is the vector Slutsky
bridge used to move from score CLTs to feasible OLS and Wald statistics. -/
theorem matrixMulVec_tendstoInDistribution_of_vector_and_matrix
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {q : Type*} [Fintype q]
    {T : ℕ → Ω → q → ℝ} {Z : Ω' → q → ℝ}
    {Ahat : ℕ → Ω → Matrix q q ℝ} {A : Matrix q q ℝ}
    (hT : TendstoInDistribution T atTop Z (fun _ => μ) ν)
    (hA_meas : ∀ n, AEStronglyMeasurable (Ahat n) μ)
    (hA : TendstoInMeasure μ Ahat atTop (fun _ => A)) :
    TendstoInDistribution
      (fun n ω => Ahat n ω *ᵥ T n ω)
      atTop (fun ω => A *ᵥ Z ω) (fun _ => μ) ν := by
  letI : BorelSpace (Matrix q q ℝ) := ⟨rfl⟩
  have hA_meas' : ∀ n, AEMeasurable (Ahat n) μ :=
    fun n => (hA_meas n).aemeasurable
  have hcont : Continuous (fun p : (q → ℝ) × Matrix q q ℝ => p.2 *ᵥ p.1) :=
    Continuous.matrix_mulVec continuous_snd continuous_fst
  have hraw := hT.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : (q → ℝ) × Matrix q q ℝ => p.2 *ᵥ p.1)
    hcont hA hA_meas'
  simpa [Function.comp_def] using hraw

omit [Fintype k] [DecidableEq k] in
/-- **Hansen Theorem 7.3/7.13, inverse matrix-vector distributional CMT.**

If `Tₙ ⇒ Z`, `Aₙ →ₚ A`, and the limiting matrix `A` is nonsingular, then
`Aₙ⁻¹Tₙ ⇒ A⁻¹Z`. This is the reusable random-inverse Slutsky bridge needed for
the feasible OLS leading term `Q̂ₙ⁻¹√nĝₙ(e)`. -/
theorem matrixInvMulVec_tendstoInDistribution_of_vector_and_matrix
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {q : Type*} [Fintype q] [DecidableEq q]
    {T : ℕ → Ω → q → ℝ} {Z : Ω' → q → ℝ}
    {Ahat : ℕ → Ω → Matrix q q ℝ} {A : Matrix q q ℝ}
    (hT : TendstoInDistribution T atTop Z (fun _ => μ) ν)
    (hA_meas : ∀ n, AEStronglyMeasurable (Ahat n) μ)
    (hA : TendstoInMeasure μ Ahat atTop (fun _ => A))
    (hA_nonsing : IsUnit A.det) :
    TendstoInDistribution
      (fun n ω => (Ahat n ω)⁻¹ *ᵥ T n ω)
      atTop (fun ω => A⁻¹ *ᵥ Z ω) (fun _ => μ) ν := by
  letI : BorelSpace (Matrix q q ℝ) := ⟨rfl⟩
  have hInv : TendstoInMeasure μ
      (fun n ω => (Ahat n ω)⁻¹) atTop (fun _ => A⁻¹) :=
    tendstoInMeasure_matrix_inv (μ := μ) hA_meas hA (fun _ => hA_nonsing)
  have hInv_meas : ∀ n, AEStronglyMeasurable (fun ω => (Ahat n ω)⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (hA_meas n)
  exact matrixMulVec_tendstoInDistribution_of_vector_and_matrix
    (μ := μ) (ν := ν) (T := T) (Z := Z)
    (Ahat := fun n ω => (Ahat n ω)⁻¹) (A := A⁻¹)
    hT hInv_meas hInv

omit [Fintype k] [DecidableEq k] in
/-- **Hansen Theorem 7.13, conditional multivariate Wald CMT.**

If a scaled vector statistic `Tₙ` converges in distribution to `Z` and the
plug-in covariance matrix `V̂ₙ` converges in probability to a nonsingular
constant `V`, then the Wald quadratic form formed with `V̂ₙ⁻¹` converges in
distribution to the matching population quadratic form. This is the generic
continuous-mapping/Slutsky bridge needed before the final chi-square law
identification. -/
theorem waldQuadraticForm_tendstoInDistribution_of_vector_and_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {q : Type*} [Fintype q] [DecidableEq q]
    {T : ℕ → Ω → q → ℝ} {Z : Ω' → q → ℝ}
    {Vhat : ℕ → Ω → Matrix q q ℝ} {V : Matrix q q ℝ}
    (hT : TendstoInDistribution T atTop Z (fun _ => μ) ν)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det) :
    TendstoInDistribution
      (fun n ω => T n ω ⬝ᵥ ((Vhat n ω)⁻¹ *ᵥ T n ω))
      atTop
      (fun ω => Z ω ⬝ᵥ (V⁻¹ *ᵥ Z ω))
      (fun _ => μ) ν := by
  letI : BorelSpace (Matrix q q ℝ) := ⟨rfl⟩
  have hInv : TendstoInMeasure μ
      (fun n ω => (Vhat n ω)⁻¹) atTop (fun _ => V⁻¹) :=
    tendstoInMeasure_matrix_inv (μ := μ) hV_meas hV (fun _ => hV_nonsing)
  have hInv_meas : ∀ n, AEMeasurable (fun ω => (Vhat n ω)⁻¹) μ :=
    fun n => (aestronglyMeasurable_matrix_inv (hV_meas n)).aemeasurable
  have hdot : Continuous (fun p : (q → ℝ) × (q → ℝ) => p.1 ⬝ᵥ p.2) := by
    classical
    simpa [dotProduct] using
      (continuous_finset_sum Finset.univ (fun i _ =>
        (((continuous_apply i).comp continuous_fst).mul
          ((continuous_apply i).comp continuous_snd))))
  have hmulVec : Continuous
      (fun p : (q → ℝ) × Matrix q q ℝ => p.2 *ᵥ p.1) :=
    Continuous.matrix_mulVec continuous_snd continuous_fst
  have hquad : Continuous
      (fun p : (q → ℝ) × Matrix q q ℝ => p.1 ⬝ᵥ (p.2 *ᵥ p.1)) :=
    hdot.comp (continuous_fst.prodMk hmulVec)
  have hraw := hT.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : (q → ℝ) × Matrix q q ℝ => p.1 ⬝ᵥ (p.2 *ᵥ p.1))
    hquad hInv hInv_meas
  simpa [Function.comp_def] using hraw

/-- Infeasible totalized HC0 sandwich estimator using true errors:
`Q̂⁻¹ (n⁻¹∑eᵢ²XᵢXᵢ') Q̂⁻¹`. -/
noncomputable def olsHeteroskedasticCovarianceIdealStar
    (X : Matrix n k ℝ) (e : n → ℝ) : Matrix k k ℝ :=
  (sampleGram X)⁻¹ * sampleScoreCovarianceIdeal X e * (sampleGram X)⁻¹

/-- Feasible totalized HC0 sandwich estimator using OLS residuals:
`Q̂⁻¹ (n⁻¹∑êᵢ²XᵢXᵢ') Q̂⁻¹`. -/
noncomputable def olsHeteroskedasticCovarianceStar
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  (sampleGram X)⁻¹ * sampleScoreCovarianceStar X y * (sampleGram X)⁻¹

/-- Totalized HC1 asymptotic sandwich estimator:
`(n / (n-k)) V̂_HC0`. -/
noncomputable def olsHeteroskedasticCovarianceHC1Star
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  ((Fintype.card n : ℝ) / (Fintype.card n - Fintype.card k : ℝ)) •
    olsHeteroskedasticCovarianceStar X y

/-- Generic totalized leverage-adjusted sandwich estimator. -/
noncomputable def olsHeteroskedasticCovarianceLeverageAdjustedStar
    (weight : ℝ → ℝ) (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  (sampleGram X)⁻¹ * sampleScoreCovarianceLeverageAdjustedStar weight X y *
    (sampleGram X)⁻¹

/-- Totalized HC2 asymptotic sandwich estimator. -/
noncomputable def olsHeteroskedasticCovarianceHC2Star
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  olsHeteroskedasticCovarianceLeverageAdjustedStar (fun h => (1 - h)⁻¹) X y

/-- Totalized HC3 asymptotic sandwich estimator. -/
noncomputable def olsHeteroskedasticCovarianceHC3Star
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  olsHeteroskedasticCovarianceLeverageAdjustedStar (fun h => ((1 - h)⁻¹) ^ 2) X y

/-- **Hansen Theorem 7.6, ideal sandwich consistency.**

The infeasible heteroskedastic sandwich estimator built from true errors
converges in probability to `Q⁻¹ Ω Q⁻¹`. This isolates the sandwich CMT from
the separate residual-substitution step needed for the feasible HC0 estimator. -/
theorem olsHeteroskedasticCovarianceIdealStar_tendstoInMeasure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceIdealStar
          (stackRegressors X n ω) (stackErrors e n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  let invGram : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    (sampleGram (stackRegressors X n ω))⁻¹
  let scoreCov : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    sampleScoreCovarianceIdeal (stackRegressors X n ω) (stackErrors e n ω)
  have hGram_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    intro n
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.toSampleMomentAssumption71.ident_outer i).integrable_iff.mpr
      h.toSampleMomentAssumption71.int_outer).aestronglyMeasurable
  have hInv_meas : ∀ n, AEStronglyMeasurable (invGram n) μ := by
    intro n
    exact aestronglyMeasurable_matrix_inv (hGram_meas n)
  have hScore_meas : ∀ n, AEStronglyMeasurable (scoreCov n) μ := by
    intro n
    have hform : scoreCov n =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n,
            Matrix.vecMulVec (e i ω • X i ω) (e i ω • X i ω)) := by
      funext ω
      dsimp [scoreCov]
      rw [sampleScoreCovarianceIdeal_stack_eq_avg]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_score_outer i).integrable_iff.mpr h.int_score_outer).aestronglyMeasurable
  have hInv := sampleGramInv_stackRegressors_tendstoInMeasure_popGramInv
    (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71
  have hScore := sampleScoreCovarianceIdeal_stack_tendstoInMeasure_scoreCovarianceMatrix
    (μ := μ) (X := X) (e := e) h
  have hLeft := tendstoInMeasure_matrix_mul
    (μ := μ) (A := invGram) (B := scoreCov)
    (Ainf := fun _ : Ω => (popGram μ X)⁻¹)
    (Binf := fun _ : Ω => scoreCovarianceMatrix μ X e)
    hInv_meas hScore_meas (by simpa [invGram] using hInv) (by simpa [scoreCov] using hScore)
  have hLeft_meas : ∀ n, AEStronglyMeasurable (fun ω => invGram n ω * scoreCov n ω) μ := by
    intro n
    have hprod : AEStronglyMeasurable (fun ω => (invGram n ω, scoreCov n ω)) μ :=
      (hInv_meas n).prodMk (hScore_meas n)
    have hcont : Continuous (fun p : Matrix k k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  have hFull := tendstoInMeasure_matrix_mul
    (μ := μ) (A := fun n ω => invGram n ω * scoreCov n ω) (B := invGram)
    (Ainf := fun _ : Ω => (popGram μ X)⁻¹ * scoreCovarianceMatrix μ X e)
    (Binf := fun _ : Ω => (popGram μ X)⁻¹)
    hLeft_meas hInv_meas
    (by simpa [Matrix.mul_assoc] using hLeft) (by simpa [invGram] using hInv)
  simpa [olsHeteroskedasticCovarianceIdealStar, heteroskedasticAsymptoticCovariance,
    invGram, scoreCov, Matrix.mul_assoc] using hFull

/-- **Hansen Theorem 7.6, feasible sandwich assembly.**

Once the residual HC0 middle matrix `n⁻¹∑êᵢ²XᵢXᵢ'` is known to converge in
probability to `Ω`, the totalized feasible sandwich estimator converges to
`Q⁻¹ Ω Q⁻¹`. The remaining feasible-HC0 work is therefore the residual
substitution theorem for the middle matrix. -/
theorem olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_scoreCovariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e)
    (hScore_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hScore : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  let invGram : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    (sampleGram (stackRegressors X n ω))⁻¹
  let scoreCov : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    sampleScoreCovarianceStar (stackRegressors X n ω) (stackOutcomes y n ω)
  have hGram_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    intro n
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hInv_meas : ∀ n, AEStronglyMeasurable (invGram n) μ := by
    intro n
    exact aestronglyMeasurable_matrix_inv (hGram_meas n)
  have hScore_meas' : ∀ n, AEStronglyMeasurable (scoreCov n) μ := by
    intro n
    simpa [scoreCov] using hScore_meas n
  have hInv := sampleGramInv_stackRegressors_tendstoInMeasure_popGramInv
    (μ := μ) (X := X) (e := e) h
  have hLeft := tendstoInMeasure_matrix_mul
    (μ := μ) (A := invGram) (B := scoreCov)
    (Ainf := fun _ : Ω => (popGram μ X)⁻¹)
    (Binf := fun _ : Ω => scoreCovarianceMatrix μ X e)
    hInv_meas hScore_meas' (by simpa [invGram] using hInv) (by simpa [scoreCov] using hScore)
  have hLeft_meas : ∀ n, AEStronglyMeasurable (fun ω => invGram n ω * scoreCov n ω) μ := by
    intro n
    have hprod : AEStronglyMeasurable (fun ω => (invGram n ω, scoreCov n ω)) μ :=
      (hInv_meas n).prodMk (hScore_meas' n)
    have hcont : Continuous (fun p : Matrix k k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  have hFull := tendstoInMeasure_matrix_mul
    (μ := μ) (A := fun n ω => invGram n ω * scoreCov n ω) (B := invGram)
    (Ainf := fun _ : Ω => (popGram μ X)⁻¹ * scoreCovarianceMatrix μ X e)
    (Binf := fun _ : Ω => (popGram μ X)⁻¹)
    hLeft_meas hInv_meas
    (by simpa [Matrix.mul_assoc] using hLeft) (by simpa [invGram] using hInv)
  simpa [olsHeteroskedasticCovarianceStar, heteroskedasticAsymptoticCovariance,
    invGram, scoreCov, Matrix.mul_assoc] using hFull

/-- **Hansen Theorem 7.6, feasible HC0 sandwich modulo remainder controls.**

The feasible totalized HC0 sandwich estimator is consistent once the residual
HC0 cross and quadratic middle-matrix remainders are controlled. -/
theorem olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_remainders
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hScore_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hCross : TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceCrossRemainder
          (stackRegressors X n ω) (stackErrors e n ω)
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun _ => 0))
    (hQuad : TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticRemainder
          (stackRegressors X n ω)
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  have hScore :=
    sampleScoreCovarianceStar_stack_tendstoInMeasure_scoreCovarianceMatrix_of_remainders
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel hCross hQuad
  exact olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_scoreCovariance
    (μ := μ) (X := X) (e := e) (y := y) h.toSampleMomentAssumption71
    hScore_meas hScore

/-- **Hansen Theorem 7.6, feasible HC0 sandwich under bounded weights.**

The feasible totalized HC0 sandwich estimator converges to `Q⁻¹ Ω Q⁻¹` under
the HC0 WLLN assumptions, bounded empirical third/fourth weights for the
residual remainders, and measurability of the residual HC0 middle matrix. -/
theorem olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_bounded_weights
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hScore_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  have hCross :=
    sampleScoreCovarianceCrossRemainder_stack_tendstoInMeasure_zero_of_bounded_weights
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hCrossWeight
  have hQuad :=
    sampleScoreCovarianceQuadraticRemainder_stack_tendstoInMeasure_zero_of_bounded_weights
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hQuadWeight
  exact olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_remainders
    (μ := μ) (X := X) (e := e) (y := y) h β hmodel hScore_meas hCross hQuad

/-- **Hansen Theorem 7.6, feasible HC0 sandwich under component measurability.**

This version derives the residual HC0 middle-matrix measurability premise from
component measurability of the regressors and errors, leaving only the empirical
third/fourth bounded-weight hypotheses as explicit stochastic remainder
controls. -/
theorem olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_bounded_weights_and_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  have hScore_meas :=
    sampleScoreCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y) β h.toSampleMomentAssumption71 hmodel
      hX_meas he_meas
  exact olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_bounded_weights
    (μ := μ) (X := X) (e := e) (y := y)
    h β hmodel hScore_meas hCrossWeight hQuadWeight

/-- AEMeasurability of the totalized feasible HC0 sandwich estimator from
component measurability. -/
theorem olsHeteroskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω =>
        olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  intro n
  let invGram : Ω → Matrix k k ℝ := fun ω =>
    (sampleGram (stackRegressors X n ω))⁻¹
  let scoreCov : Ω → Matrix k k ℝ := fun ω =>
    sampleScoreCovarianceStar (stackRegressors X n ω) (stackOutcomes y n ω)
  have hGram_meas : AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hInv_meas : AEStronglyMeasurable invGram μ := by
    exact aestronglyMeasurable_matrix_inv hGram_meas
  have hScore_meas : AEStronglyMeasurable scoreCov μ := by
    have hScore :=
      sampleScoreCovarianceStar_stack_aestronglyMeasurable_of_components
        (μ := μ) (X := X) (e := e) (y := y) β h hmodel hX_meas he_meas n
    simpa [scoreCov] using hScore
  have hLeft : AEStronglyMeasurable (fun ω => invGram ω * scoreCov ω) μ := by
    have hprod : AEStronglyMeasurable (fun ω => (invGram ω, scoreCov ω)) μ :=
      hInv_meas.prodMk hScore_meas
    have hcont : Continuous (fun p : Matrix k k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  have hFull : AEStronglyMeasurable
      (fun ω => invGram ω * scoreCov ω * invGram ω) μ := by
    have hprod : AEStronglyMeasurable
        (fun ω => (invGram ω * scoreCov ω, invGram ω)) μ :=
      hLeft.prodMk hInv_meas
    have hcont : Continuous (fun p : Matrix k k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  simpa [olsHeteroskedasticCovarianceStar, invGram, scoreCov, Matrix.mul_assoc] using hFull

/-- **Hansen Theorem 7.10, HC0 covariance for fixed linear functions.**

For a fixed linear map `R`, the totalized feasible HC0 covariance estimator for
`R β` converges to `R Vβ Rᵀ` once the existing HC0 bounded-weight assumptions
and component measurability hypotheses are available. -/
theorem linearMap_olsHC0CovarianceStar_tendstoInMeasure_of_bounded_weights_and_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q]
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        R * olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)
      atTop (fun _ => R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) := by
  have hV_meas :=
    olsHeteroskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hV :=
    olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_bounded_weights_and_components
      (μ := μ) (X := X) (e := e) (y := y)
      h β hmodel hX_meas he_meas hCrossWeight hQuadWeight
  exact linearMapCovariance_tendstoInMeasure
    (μ := μ) (R := R)
    (Vhat := fun n ω =>
      olsHeteroskedasticCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
    (V := heteroskedasticAsymptoticCovariance μ X e)
    hV_meas hV

/-- **Hansen §7.11, HC0 standard errors for fixed linear functions.**

For a fixed linear map `R`, the square root of any diagonal element of the
totalized feasible HC0 covariance estimator for `R β` converges to the matching
population scale. -/
theorem olsHC0LinearStdErrorStar_tendstoInMeasure_of_bounded_weights_and_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Finite q]
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ) (j : q)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        Real.sqrt ((R * olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) j j))
      atTop (fun _ =>
        Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) j j)) := by
  have hV_meas :=
    olsHeteroskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hV :=
    olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_bounded_weights_and_components
      (μ := μ) (X := X) (e := e) (y := y)
      h β hmodel hX_meas he_meas hCrossWeight hQuadWeight
  exact linearMapCovarianceStdError_tendstoInMeasure
    (μ := μ) (R := R) (j := j)
    (Vhat := fun n ω =>
      olsHeteroskedasticCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
    (V := heteroskedasticAsymptoticCovariance μ X e)
    hV_meas hV

/-- The HC1 finite-sample degrees-of-freedom multiplier `n / (n - k)` tends to `1`. -/
theorem hc1FiniteSampleScale_tendsto_one (k : Type*) [Fintype k] :
    Tendsto
      (fun n : ℕ => (n : ℝ) / ((n : ℝ) - (Fintype.card k : ℝ)))
      atTop (𝓝 1) := by
  let r : ℕ → ℝ := fun n =>
    (n : ℝ) / ((n : ℝ) - (Fintype.card k : ℝ))
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden : Tendsto
      (fun n : ℕ => (n : ℝ) - (Fintype.card k : ℝ)) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(Fintype.card k : ℝ)) hn
  have hrSub : Tendsto (fun n => r n - 1) atTop (𝓝 0) := by
    have hsmall : Tendsto
        (fun n : ℕ => (Fintype.card k : ℝ) /
          ((n : ℝ) - (Fintype.card k : ℝ))) atTop (𝓝 0) :=
      hden.const_div_atTop (Fintype.card k : ℝ)
    have heq : (fun n => r n - 1) =ᶠ[atTop]
        (fun n : ℕ => (Fintype.card k : ℝ) /
          ((n : ℝ) - (Fintype.card k : ℝ))) := by
      filter_upwards [eventually_gt_atTop (Fintype.card k)] with n hn_gt
      have hden_ne : (n : ℝ) - (Fintype.card k : ℝ) ≠ 0 := by
        have hgt : (Fintype.card k : ℝ) < (n : ℝ) := by
          exact_mod_cast hn_gt
        linarith
      dsimp [r]
      field_simp [hden_ne]
      ring
    rw [tendsto_congr' heq]
    exact hsmall
  have hadd := hrSub.add_const 1
  simpa [r, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hadd

/-- **Hansen Theorem 7.7, HC1 sandwich under bounded weights.**

The totalized HC1 sandwich estimator has the same probability limit as HC0,
because the finite-sample degrees-of-freedom multiplier `n/(n-k)` tends to `1`. -/
theorem olsHeteroskedasticCovarianceHC1Star_tendstoInMeasure_of_bounded_weights
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hScore_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  let r : ℕ → ℝ := fun n =>
    (n : ℝ) / ((n : ℝ) - (Fintype.card k : ℝ))
  have hr : Tendsto r atTop (𝓝 1) := by
    simpa [r] using hc1FiniteSampleScale_tendsto_one k
  have hHC0 := olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_bounded_weights
    (μ := μ) (X := X) (e := e) (y := y)
    h β hmodel hScore_meas hCrossWeight hQuadWeight
  refine tendstoInMeasure_pi (μ := μ) (fun a => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun b => ?_)
  have hHC0_ab : TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e a b) := by
    simpa using TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hHC0 a) b
  have hrMeasure : TendstoInMeasure μ
      (fun n (_ : Ω) => r n) atTop (fun _ => 1) :=
    tendstoInMeasure_const_real (μ := μ) hr
  have hprod := TendstoInMeasure.mul_limits_real hrMeasure hHC0_ab
  simpa [olsHeteroskedasticCovarianceHC1Star, r, Matrix.smul_apply, smul_eq_mul,
    Fintype.card_fin, div_eq_mul_inv] using hprod

/-- **Hansen Theorem 7.7, HC1 sandwich under component measurability.**

This is the HC1 analogue of
`olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_bounded_weights_and_components`:
component measurability supplies the feasible HC0 middle-matrix measurability
needed by the HC1 assembly theorem. -/
theorem olsHeteroskedasticCovarianceHC1Star_tendstoInMeasure_of_bounded_weights_and_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  have hScore_meas :=
    sampleScoreCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y) β h.toSampleMomentAssumption71 hmodel
      hX_meas he_meas
  exact olsHeteroskedasticCovarianceHC1Star_tendstoInMeasure_of_bounded_weights
    (μ := μ) (X := X) (e := e) (y := y)
    h β hmodel hScore_meas hCrossWeight hQuadWeight

/-- AEMeasurability of the totalized HC1 sandwich estimator from component
measurability. -/
theorem olsHC1CovarianceStar_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω =>
        olsHeteroskedasticCovarianceHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  intro n
  have hHC0 :=
    olsHeteroskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel hX_meas he_meas n
  simpa [olsHeteroskedasticCovarianceHC1Star] using
    hHC0.const_smul
      ((Fintype.card (Fin n) : ℝ) / (Fintype.card (Fin n) - Fintype.card k : ℝ))

/-- **Hansen Theorem 7.10, HC1 covariance for fixed linear functions.**

For a fixed linear map `R`, the totalized HC1 covariance estimator for `R β`
has the same `R Vβ Rᵀ` limit as HC0 under the bounded-weight and component
measurability hypotheses. -/
theorem linearMap_olsHC1CovarianceStar_tendstoInMeasure_of_bounded_weights_and_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q]
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        R * olsHeteroskedasticCovarianceHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)
      atTop (fun _ => R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) := by
  have hV_meas :=
    olsHC1CovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hV :=
    olsHeteroskedasticCovarianceHC1Star_tendstoInMeasure_of_bounded_weights_and_components
      (μ := μ) (X := X) (e := e) (y := y)
      h β hmodel hX_meas he_meas hCrossWeight hQuadWeight
  exact linearMapCovariance_tendstoInMeasure
    (μ := μ) (R := R)
    (Vhat := fun n ω =>
      olsHeteroskedasticCovarianceHC1Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
    (V := heteroskedasticAsymptoticCovariance μ X e)
    hV_meas hV

/-- **Hansen §7.11, HC1 standard errors for fixed linear functions.**

For a fixed linear map `R`, the square root of any diagonal element of the
totalized HC1 covariance estimator for `R β` converges to the same population
scale as HC0. -/
theorem olsHC1LinearStdErrorStar_tendstoInMeasure_of_bounded_weights_and_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Finite q]
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ) (j : q)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) j j))
      atTop (fun _ =>
        Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) j j)) := by
  have hV_meas :=
    olsHC1CovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hV :=
    olsHeteroskedasticCovarianceHC1Star_tendstoInMeasure_of_bounded_weights_and_components
      (μ := μ) (X := X) (e := e) (y := y)
      h β hmodel hX_meas he_meas hCrossWeight hQuadWeight
  exact linearMapCovarianceStdError_tendstoInMeasure
    (μ := μ) (R := R) (j := j)
    (Vhat := fun n ω =>
      olsHeteroskedasticCovarianceHC1Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
    (V := heteroskedasticAsymptoticCovariance μ X e)
    hV_meas hV

/-- **Generic leverage-adjusted sandwich assembly.**

Once a leverage-weighted middle matrix is known to converge in probability to
`Ω`, the corresponding totalized leverage-adjusted sandwich estimator converges
to `Q⁻¹ Ω Q⁻¹`. HC2 and HC3 differ only by the scalar leverage weight. -/
theorem olsHeteroskedasticCovarianceLeverageAdjustedStar_tendstoInMeasure_of_middle
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e)
    (weight : ℝ → ℝ)
    (hmiddle_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceLeverageAdjustedStar weight
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hmiddle : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceLeverageAdjustedStar weight
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceLeverageAdjustedStar weight
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  exact sandwichCovarianceStar_tendstoInMeasure_of_middle
    (μ := μ) (X := X) (e := e) h
    (middle := fun n ω => sampleScoreCovarianceLeverageAdjustedStar weight
      (stackRegressors X n ω) (stackOutcomes y n ω))
    hmiddle_meas hmiddle

/-- **Hansen Theorem 7.7, conditional HC2 sandwich assembly.**

Once the HC2 leverage-weighted middle matrix is known to converge in
probability to `Ω`, the totalized HC2 sandwich estimator converges to
`Q⁻¹ Ω Q⁻¹`. The remaining HC2 work is the leverage argument showing that
`(1-hᵢᵢ)⁻¹` is asymptotically harmless. -/
private theorem olsHeteroskedasticCovarianceHC2Star_tendstoInMeasure_of_middle
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e)
    (hHC2_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC2Star
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hHC2 : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceHC2Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceHC2Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  simpa [olsHeteroskedasticCovarianceHC2Star, sampleScoreCovarianceHC2Star] using
    olsHeteroskedasticCovarianceLeverageAdjustedStar_tendstoInMeasure_of_middle
      (μ := μ) (X := X) (e := e) (y := y)
      h (fun h => (1 - h)⁻¹) hHC2_meas hHC2

/-- **Hansen Theorem 7.7, conditional HC3 sandwich assembly.**

Once the HC3 leverage-weighted middle matrix is known to converge in
probability to `Ω`, the totalized HC3 sandwich estimator converges to
`Q⁻¹ Ω Q⁻¹`. The remaining HC3 work is the stronger leverage-weight argument
for `(1-hᵢᵢ)⁻²`. -/
private theorem olsHeteroskedasticCovarianceHC3Star_tendstoInMeasure_of_middle
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e)
    (hHC3_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC3Star
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hHC3 : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceHC3Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceHC3Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  simpa [olsHeteroskedasticCovarianceHC3Star, sampleScoreCovarianceHC3Star] using
    olsHeteroskedasticCovarianceLeverageAdjustedStar_tendstoInMeasure_of_middle
      (μ := μ) (X := X) (e := e) (y := y)
      h (fun h => ((1 - h)⁻¹) ^ 2) hHC3_meas hHC3

/-- Measurability of a leverage-adjusted sandwich estimator from component
measurability and measurability of the scalar leverage weight. -/
private theorem olsHeteroskedasticCovarianceLeverageAdjustedStar_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (weight : ℝ → ℝ) (hweight_meas : Measurable weight)
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω =>
        olsHeteroskedasticCovarianceLeverageAdjustedStar weight
          (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  intro n
  let invGram : Ω → Matrix k k ℝ := fun ω =>
    (sampleGram (stackRegressors X n ω))⁻¹
  let scoreCov : Ω → Matrix k k ℝ := fun ω =>
    sampleScoreCovarianceLeverageAdjustedStar weight
      (stackRegressors X n ω) (stackOutcomes y n ω)
  have hGram_meas : AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hInv_meas : AEStronglyMeasurable invGram μ := by
    exact aestronglyMeasurable_matrix_inv hGram_meas
  have hScore_meas : AEStronglyMeasurable scoreCov μ := by
    have hScore :=
      sampleScoreCovarianceLeverageAdjustedStar_stack_aestronglyMeasurable_of_components
        (μ := μ) (X := X) (e := e) (y := y)
        weight hweight_meas β h hmodel hX_meas he_meas n
    simpa [scoreCov] using hScore
  have hLeft : AEStronglyMeasurable (fun ω => invGram ω * scoreCov ω) μ := by
    have hprod : AEStronglyMeasurable (fun ω => (invGram ω, scoreCov ω)) μ :=
      hInv_meas.prodMk hScore_meas
    have hcont : Continuous (fun p : Matrix k k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  have hFull : AEStronglyMeasurable
      (fun ω => invGram ω * scoreCov ω * invGram ω) μ := by
    have hprod : AEStronglyMeasurable
        (fun ω => (invGram ω * scoreCov ω, invGram ω)) μ :=
      hLeft.prodMk hInv_meas
    have hcont : Continuous (fun p : Matrix k k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  simpa [olsHeteroskedasticCovarianceLeverageAdjustedStar, invGram, scoreCov,
    Matrix.mul_assoc] using hFull

/-- Generic leverage-adjusted sandwich consistency from the HC0 bounded-weight
layer, component measurability, and an `oₚ(1)` leverage adjustment. -/
private theorem olsHeteroskedasticCovarianceLeverageAdjustedStar_tendstoInMeasure_of_bounded_weights_components_and_adjustment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (weight : ℝ → ℝ) (hweight_meas : Measurable weight)
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hAdj : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceLeverageAdjustmentStar weight
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceLeverageAdjustedStar weight
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  have hHC0_meas :=
    sampleScoreCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y) β h.toSampleMomentAssumption71 hmodel
      hX_meas he_meas
  have hAdj_meas :=
    sampleScoreCovarianceLeverageAdjustmentStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      weight hweight_meas β h.toSampleMomentAssumption71 hmodel hX_meas he_meas
  have hHC0 :=
    sampleScoreCovarianceStar_stack_tendstoInMeasure_scoreCovarianceMatrix_of_bounded_weights
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel hCrossWeight hQuadWeight
  have hMiddle :=
    sampleScoreCovarianceLeverageAdjustedStar_stack_tendstoInMeasure_of_adjustment
      (μ := μ) (X := X) (e := e) (y := y)
      weight hHC0_meas hAdj_meas hHC0 hAdj
  have hMiddle_meas :=
    sampleScoreCovarianceLeverageAdjustedStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      weight hweight_meas β h.toSampleMomentAssumption71 hmodel hX_meas he_meas
  exact olsHeteroskedasticCovarianceLeverageAdjustedStar_tendstoInMeasure_of_middle
    (μ := μ) (X := X) (e := e) (y := y)
    h.toSampleMomentAssumption71 weight hMiddle_meas hMiddle

/-- AEMeasurability of the HC2 middle matrix from component measurability. -/
theorem sampleScoreCovarianceHC2Star_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC2Star
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  simpa [sampleScoreCovarianceHC2Star] using
    sampleScoreCovarianceLeverageAdjustedStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      (weight := fun h => (1 - h)⁻¹) measurable_hc2Weight
      β h hmodel hX_meas he_meas

/-- AEMeasurability of the HC3 middle matrix from component measurability. -/
theorem sampleScoreCovarianceHC3Star_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC3Star
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  simpa [sampleScoreCovarianceHC3Star] using
    sampleScoreCovarianceLeverageAdjustedStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      (weight := fun h => ((1 - h)⁻¹) ^ 2) measurable_hc3Weight
      β h hmodel hX_meas he_meas

/-- AEMeasurability of the totalized HC2 sandwich estimator from component
measurability. -/
theorem olsHC2CovarianceStar_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω =>
        olsHeteroskedasticCovarianceHC2Star
          (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  simpa [olsHeteroskedasticCovarianceHC2Star] using
    olsHeteroskedasticCovarianceLeverageAdjustedStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      (weight := fun h => (1 - h)⁻¹) measurable_hc2Weight
      h β hmodel hX_meas he_meas

/-- AEMeasurability of the totalized HC3 sandwich estimator from component
measurability. -/
theorem olsHC3CovarianceStar_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω =>
        olsHeteroskedasticCovarianceHC3Star
          (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  simpa [olsHeteroskedasticCovarianceHC3Star] using
    olsHeteroskedasticCovarianceLeverageAdjustedStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      (weight := fun h => ((1 - h)⁻¹) ^ 2) measurable_hc3Weight
      h β hmodel hX_meas he_meas

/-- **Hansen Theorem 7.7, HC2 sandwich from maximal leverage.**

This closes the asymptotic HC2 leverage step from the existing HC0 bounded
weight hypotheses plus maximal leverage `oₚ(1)`. -/
theorem olsHeteroskedasticCovarianceHC2Star_tendstoInMeasure_of_bounded_weights_components_and_maxLeverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceHC2Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  have hAdj :=
    sampleScoreCovarianceHC2AdjustmentStar_stack_tendstoInMeasure_zero_of_bounded_weights_and_maxLeverage
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleHC0Assumption76 β hmodel hCrossWeight hQuadWeight hMax
  simpa [olsHeteroskedasticCovarianceHC2Star] using
    olsHeteroskedasticCovarianceLeverageAdjustedStar_tendstoInMeasure_of_bounded_weights_components_and_adjustment
      (μ := μ) (X := X) (e := e) (y := y)
      (weight := fun h => (1 - h)⁻¹) measurable_hc2Weight
      h.toSampleHC0Assumption76 β hmodel hX_meas he_meas hCrossWeight hQuadWeight hAdj

/-- **Hansen Theorem 7.7, HC3 sandwich from maximal leverage.**

This closes the asymptotic HC3 leverage step from the existing HC0 bounded
weight hypotheses plus maximal leverage `oₚ(1)`. -/
theorem olsHeteroskedasticCovarianceHC3Star_tendstoInMeasure_of_bounded_weights_components_and_maxLeverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : RobustCovarianceConsistencyConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceHC3Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  have hAdj :=
    sampleScoreCovarianceHC3AdjustmentStar_stack_tendstoInMeasure_zero_of_bounded_weights_and_maxLeverage
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleHC0Assumption76 β hmodel hCrossWeight hQuadWeight hMax
  simpa [olsHeteroskedasticCovarianceHC3Star] using
    olsHeteroskedasticCovarianceLeverageAdjustedStar_tendstoInMeasure_of_bounded_weights_components_and_adjustment
      (μ := μ) (X := X) (e := e) (y := y)
      (weight := fun h => ((1 - h)⁻¹) ^ 2) measurable_hc3Weight
      h.toSampleHC0Assumption76 β hmodel hX_meas he_meas hCrossWeight hQuadWeight hAdj

/-- HC2 covariance for fixed linear functions from maximal leverage. -/
theorem linearMap_olsHC2CovarianceStar_tendstoInMeasure_of_bounded_weights_components_and_maxLeverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q]
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        R * olsHeteroskedasticCovarianceHC2Star
          (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)
      atTop (fun _ => R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) := by
  have hV_meas :=
    olsHC2CovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hV :=
    olsHeteroskedasticCovarianceHC2Star_tendstoInMeasure_of_bounded_weights_components_and_maxLeverage
      (μ := μ) (X := X) (e := e) (y := y)
      (RobustCovarianceConsistencyConditions.ofSample h) β hmodel hX_meas he_meas
      hCrossWeight hQuadWeight hMax
  exact linearMapCovariance_tendstoInMeasure
    (μ := μ) (R := R)
    (Vhat := fun n ω =>
      olsHeteroskedasticCovarianceHC2Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
    (V := heteroskedasticAsymptoticCovariance μ X e)
    hV_meas hV

/-- HC3 covariance for fixed linear functions from maximal leverage. -/
theorem linearMap_olsHC3CovarianceStar_tendstoInMeasure_of_bounded_weights_components_and_maxLeverage
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q]
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hMax : TendstoInMeasure μ
      (fun n ω => maxLeverageStar (stackRegressors X n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        R * olsHeteroskedasticCovarianceHC3Star
          (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)
      atTop (fun _ => R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) := by
  have hV_meas :=
    olsHC3CovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hV :=
    olsHeteroskedasticCovarianceHC3Star_tendstoInMeasure_of_bounded_weights_components_and_maxLeverage
      (μ := μ) (X := X) (e := e) (y := y)
      (RobustCovarianceConsistencyConditions.ofSample h) β hmodel hX_meas he_meas
      hCrossWeight hQuadWeight hMax
  exact linearMapCovariance_tendstoInMeasure
    (μ := μ) (R := R)
    (Vhat := fun n ω =>
      olsHeteroskedasticCovarianceHC3Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
    (V := heteroskedasticAsymptoticCovariance μ X e)
    hV_meas hV

end Assumption72

end HansenEconometrics
