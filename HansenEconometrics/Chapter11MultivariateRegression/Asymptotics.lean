import HansenEconometrics.Chapter6Asymptotics
import HansenEconometrics.Chapter8Asymptotics
import HansenEconometrics.AsymptoticUtils.DeltaMethod
import HansenEconometrics.Chapter11MultivariateRegression.Systems

/-!
# Chapter 11 — asymptotic regression-system interfaces

This file records the reusable Chapter 7/8 convergence layer needed by the
Chapter 11 regression-system theorems. It includes non-tautological
stacked-system wrappers for Theorems 11.1--11.2, exact system-matrix WLLN/CMT
assembly for the Theorem 11.3 covariance route, and compatibility projections
for theorem surfaces whose primitive assumptions are supplied elsewhere.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Function Topology MeasureTheory ProbabilityTheory

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

variable {Ω k q : Type*}
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
variable {m : Type*} [Fintype m] [DecidableEq m]

omit [DecidableEq q] [DecidableEq m] in
/-- System-score condition package for Hansen Theorem 11.1 at the
observation-system level.

It records the real probabilistic ingredients used by the proof route:
convergence of `Q̂ = n⁻¹∑ Xᵢ'Xᵢ`, a vector CLT for
`√n n⁻¹∑ Xᵢ'eᵢ`, nonsingularity and symmetry of the population Gram inverse,
and positive semidefiniteness of the score covariance. -/
structure SystemScoreCLTConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Q Omega : Matrix k k ℝ) : Prop where
  gram_meas : ∀ n,
    AEStronglyMeasurable
      (fun ω => systemNormalizedGram (fun i : Fin n => X i.val ω)) μ
  gram_tendsto : TendstoInMeasure μ
    (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
    atTop (fun _ => Q)
  gram_nonsing : IsUnit Q.det
  gram_inv_transpose : (Q⁻¹)ᵀ = Q⁻¹
  score_limit : TendstoInDistribution
    (fun (t : ℕ) ω =>
      Real.sqrt (t : ℝ) •
        systemScoreMean (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω))
    atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
    (multivariateGaussian 0 Omega)
  score_cov_posSemidef : Omega.PosSemidef

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- The Hansen coefficient covariance `Q⁻¹ΩQ⁻¹` is positive semidefinite when
`Ω` is positive semidefinite and `Q⁻¹` is symmetric. -/
theorem systemAsymptoticVariance_posSemidef
    {Q Omega : Matrix k k ℝ}
    (hOmega : Omega.PosSemidef) (hQsymm : (Q⁻¹)ᵀ = Q⁻¹) :
    (systemAsymptoticVariance Q Omega).PosSemidef := by
  have hpsd : (Q⁻¹ * Omega * (Q⁻¹)ᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose] using
      Matrix.PosSemidef.mul_mul_conjTranspose_same hOmega Q⁻¹
  simpa [systemAsymptoticVariance, hQsymm] using hpsd

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Hansen's population system Gram matrix `Q = E[Xᵢ'Xᵢ]`. -/
noncomputable def systemPopulationGram
    (μ : Measure Ω) (X : ℕ → Ω → Matrix m k ℝ) : Matrix k k ℝ :=
  μ[fun ω => (X 0 ω)ᵀ * X 0 ω]

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
/-- Hansen's population system score covariance middle
`Ω = E[Xᵢ'eᵢeᵢ'Xᵢ]`. -/
noncomputable def systemPopulationScoreCovariance
    (μ : Measure Ω) (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ) :
    Matrix k k ℝ :=
  μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)]

omit [Fintype q] [DecidableEq k] [DecidableEq q] in
private lemma measurable_vecMulVec_self :
    Measurable (fun x : k → ℝ => Matrix.vecMulVec x x) :=
  (Continuous.matrix_vecMulVec continuous_id continuous_id).measurable

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
/-- A zero-mean finite-dimensional covariance matrix is the second-moment
outer product. This is the reusable bridge from Mathlib's coordinate covariance
definition to Hansen's matrix notation. -/
theorem covMat_eq_integral_vecMulVec_of_meanVec_zero
    {Y : Ω → k → ℝ}
    (hY : MemLp Y 2 μ) (hmean : meanVec μ Y = 0) :
    covMat μ Y = μ[fun ω => Matrix.vecMulVec (Y ω) (Y ω)] := by
  classical
  have hYint : Integrable Y μ := hY.integrable (by norm_num)
  have houter_int : Integrable (fun ω => Matrix.vecMulVec (Y ω) (Y ω)) μ := by
    refine Integrable.of_eval ?_
    intro i
    refine Integrable.of_eval ?_
    intro j
    simpa [Matrix.vecMulVec_apply] using (hY.eval i).integrable_mul (hY.eval j)
  ext i j
  have hmean_i : μ[fun ω => Y ω i] = 0 := by
    have hcoord := congrFun hmean i
    rw [meanVec] at hcoord
    rw [integral_apply (μ := μ) (f := Y) hYint i] at hcoord
    exact hcoord
  have hmean_j : μ[fun ω => Y ω j] = 0 := by
    have hcoord := congrFun hmean j
    rw [meanVec] at hcoord
    rw [integral_apply (μ := μ) (f := Y) hYint j] at hcoord
    exact hcoord
  have hcov :
      covMat μ Y i j =
        μ[(fun ω => Y ω i) * (fun ω => Y ω j)] -
          μ[fun ω => Y ω i] * μ[fun ω => Y ω j] := by
    simpa [covMat] using
      (ProbabilityTheory.covariance_eq_sub (μ := μ)
        (X := fun ω => Y ω i) (Y := fun ω => Y ω j)
        (hY.eval i) (hY.eval j))
  have hzero :
      μ[(fun ω => Y ω i) * (fun ω => Y ω j)] -
          μ[fun ω => Y ω i] * μ[fun ω => Y ω j] =
        μ[(fun ω => Y ω i) * (fun ω => Y ω j)] := by
    rw [hmean_i, hmean_j, zero_mul, sub_zero]
  have hentry :
      μ[(fun ω => Y ω i) * (fun ω => Y ω j)] =
        (μ[fun ω => Matrix.vecMulVec (Y ω) (Y ω)]) i j := by
    simpa [Matrix.vecMulVec_apply] using
      (integral_apply_apply (μ := μ)
        (f := fun ω => Matrix.vecMulVec (Y ω) (Y ω)) houter_int i j).symm
  exact hcov.trans (hzero.trans hentry)

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
/-- Hansen's system middle `E[Xᵢ'eᵢeᵢ'Xᵢ]` is the covariance of the system
score `Xᵢ'eᵢ` when that score has mean zero. -/
theorem systemScore_covMat_eq_populationScoreCovariance
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hscore : MemLp (fun ω => systemScore (X 0 ω) (e 0 ω)) 2 μ)
    (hmean : meanVec μ (fun ω => systemScore (X 0 ω) (e 0 ω)) = 0) :
    covMat μ (fun ω => systemScore (X 0 ω) (e 0 ω)) =
      systemPopulationScoreCovariance μ X e := by
  classical
  simpa [systemPopulationScoreCovariance, systemRobustMiddleTerm_eq_vecMulVec_score] using
    covMat_eq_integral_vecMulVec_of_meanVec_zero
      (μ := μ) (Y := fun ω => systemScore (X 0 ω) (e 0 ω)) hscore hmean

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
/-- The population system Gram matrix is symmetric because every summand
`Xᵢ'Xᵢ` is symmetric. -/
theorem systemPopulationGram_isSymm
    {X : ℕ → Ω → Matrix m k ℝ}
    (hX : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ) :
    (systemPopulationGram μ X).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  calc
    (systemPopulationGram μ X) j i
        = ∫ ω, ((X 0 ω)ᵀ * X 0 ω) j i ∂μ := by
          simpa [systemPopulationGram] using
            integral_apply_apply (μ := μ)
              (f := fun ω => (X 0 ω)ᵀ * X 0 ω) hX j i
    _ = ∫ ω, ((X 0 ω)ᵀ * X 0 ω) i j ∂μ := by
          congr with ω
          have hterm : (((X 0 ω)ᵀ * X 0 ω)ᵀ) = (X 0 ω)ᵀ * X 0 ω := by
            simp [Matrix.transpose_mul]
          exact congrFun (congrFun hterm i) j
    _ = (systemPopulationGram μ X) i j := by
          simpa [systemPopulationGram] using
            (integral_apply_apply (μ := μ)
              (f := fun ω => (X 0 ω)ᵀ * X 0 ω) hX i j).symm

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- The inverse of Hansen's population system Gram matrix is symmetric. -/
theorem systemPopulationGram_inv_transpose
    {X : ℕ → Ω → Matrix m k ℝ}
    (hX : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ) :
    ((systemPopulationGram μ X)⁻¹)ᵀ = (systemPopulationGram μ X)⁻¹ := by
  have hsymm : (systemPopulationGram μ X)ᵀ = systemPopulationGram μ X :=
    (systemPopulationGram_isSymm (μ := μ) (X := X) hX).eq
  rw [Matrix.transpose_nonsing_inv, hsymm]

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Hansen Assumption 7.2 specialized to Chapter 11 system observations.

The package keeps the assumptions at the observation level: WLLN hypotheses for
`Xᵢ'Xᵢ`, an iid finite-variance CLT package for the vector score `Xᵢ'eᵢ`, zero
mean of that score, and nonsingularity of `Q`. The covariance identity
`cov(Xᵢ'eᵢ) = E[Xᵢ'eᵢeᵢ'Xᵢ]` is derived from these fields rather than assumed.
It deliberately does not assume the Chapter 11 Gaussian limit. -/
structure SystemAssumption72
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ) : Prop where
  gram_integrable : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ
  gram_independent : Pairwise ((· ⟂ᵢ[μ] ·) on
    (fun i ω => (X i ω)ᵀ * X i ω))
  gram_identDistrib : ∀ i,
    IdentDistrib (fun ω => (X i ω)ᵀ * X i ω)
      (fun ω => (X 0 ω)ᵀ * X 0 ω) μ μ
  score_memLp : MemLp (fun ω => systemScore (X 0 ω) (e 0 ω)) 2 μ
  score_iIndep : iIndepFun (fun i ω => systemScore (X i ω) (e i ω)) μ
  score_identDistrib : ∀ i,
    IdentDistrib (fun ω => systemScore (X i ω) (e i ω))
      (fun ω => systemScore (X 0 ω) (e 0 ω)) μ μ
  score_mean_zero :
    meanVec μ (fun ω => systemScore (X 0 ω) (e 0 ω)) = 0
  gram_nonsing : IsUnit (systemPopulationGram μ X).det

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
private theorem measurable_system_row_gram :
    Measurable (fun Xi : Matrix m k ℝ => Xiᵀ * Xi) :=
  (Continuous.matrix_mul (continuous_id.matrix_transpose) continuous_id).measurable

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
private theorem measurable_system_pair_gram :
    Measurable (fun row : Matrix m k ℝ × (m → ℝ) => row.1ᵀ * row.1) :=
  (measurable_system_row_gram (m := m) (k := k)).comp measurable_fst

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
private theorem measurable_system_row_score :
    Measurable (fun row : Matrix m k ℝ × (m → ℝ) => systemScore row.1 row.2) := by
  simpa [systemScore] using
    (Continuous.matrix_mulVec (continuous_fst.matrix_transpose) continuous_snd).measurable

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Literal row-iid constructor surface for Hansen Assumption 7.2 in Chapter 11.

This package keeps the stochastic primitive at the observation row
`(Xᵢ,eᵢ)`. The moment fields are exactly the finite population objects needed by
the current Chapter 11 theorem route: integrability of `Xᵢ'Xᵢ`, square
integrability and zero mean of `Xᵢ'eᵢ`, and nonsingularity of `Q`. The
conversion below derives the older split Gram/score iid fields by measurable
composition, so theorem-facing call sites do not have to assume those split
fields separately. -/
structure SystemAssumption72PrimitiveRow
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ) : Prop where
  row_iIndep : iIndepFun (fun i ω => (X i ω, e i ω)) μ
  row_identDistrib : ∀ i,
    IdentDistrib (fun ω => (X i ω, e i ω))
      (fun ω => (X 0 ω, e 0 ω)) μ μ
  gram_integrable : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ
  score_memLp : MemLp (fun ω => systemScore (X 0 ω) (e 0 ω)) 2 μ
  score_mean_zero :
    meanVec μ (fun ω => systemScore (X 0 ω) (e 0 ω)) = 0
  gram_nonsing : IsUnit (systemPopulationGram μ X).det

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
private theorem system_memLp_four_of_integrable_fourth
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfourth : Integrable (fun ω => f ω ^ 4) μ) :
    MemLp f 4 μ := by
  rw [← integrable_norm_rpow_iff (μ := μ) hf (by norm_num) (by norm_num)]
  convert hfourth using 1
  ext ω
  simpa [Real.norm_eq_abs] using (show Even (4 : ℕ) by decide).pow_abs (f ω)

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
private theorem system_memLp_two_mul_of_memLp_four
    {f g : Ω → ℝ} (hf : MemLp f 4 μ) (hg : MemLp g 4 μ) :
    MemLp (fun ω => f ω * g ω) 2 μ := by
  have hdiv : (4 : ENNReal) / 2 = 2 := by
    change ((4 : NNReal) : ENNReal) / ((2 : NNReal) : ENNReal) =
      ((2 : NNReal) : ENNReal)
    rw [← ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0)]
    norm_num
  have hf_sq : MemLp (fun ω => |f ω| ^ 2) 2 μ := by
    simpa [Real.norm_eq_abs, hdiv] using hf.norm_rpow_div 2
  have hg_sq : MemLp (fun ω => |g ω| ^ 2) 2 μ := by
    simpa [Real.norm_eq_abs, hdiv] using hg.norm_rpow_div 2
  have hprod : Integrable (fun ω => |f ω| ^ 2 * |g ω| ^ 2) μ :=
    hf_sq.integrable_mul hg_sq
  refine (memLp_two_iff_integrable_sq (hf.1.mul hg.1)).2 ?_
  convert hprod using 1
  ext ω
  change (f ω * g ω) ^ 2 = |f ω| ^ 2 * |g ω| ^ 2
  rw [mul_pow, sq_abs, sq_abs]

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
/-- Hansen Assumption 7.2 at the literal observed system row `(Xᵢ,Yᵢ)`.

The fourth moments are packaged as finite-dimensional row-norm moments, which
are equivalent to Hansen's coordinate fourth moments. The conversion below
derives the residual-row iid, Gram-integrability, and score-`L²` fields used by
the Chapter 11 proof engine; none of those consequences is assumed here. -/
structure SystemAssumption72ObservedResponseFourthConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Matrix m k ℝ) (e Y : ℕ → Ω → m → ℝ)
    (β : k → ℝ) : Prop where
  observed_iIndep : iIndepFun (fun i ω => (X i ω, Y i ω)) μ
  observed_identDistrib : ∀ i,
    IdentDistrib (fun ω => (X i ω, Y i ω))
      (fun ω => (X 0 ω, Y 0 ω)) μ μ
  model : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j
  response_norm_fourth_integrable : Integrable (fun ω => ‖Y 0 ω‖ ^ 4) μ
  design_norm_fourth_integrable : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ
  score_mean_zero :
    meanVec μ (fun ω => systemScore (X 0 ω) (e 0 ω)) = 0
  gram_posDef : (systemPopulationGram μ X).PosDef

namespace SystemAssumption72ObservedResponseFourthConditions

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
theorem observed_row_aestronglyMeasurable_at
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h : SystemAssumption72ObservedResponseFourthConditions μ X e Y β)
    (i : ℕ) : AEStronglyMeasurable (fun ω => (X i ω, Y i ω)) μ :=
  (h.observed_identDistrib i).aestronglyMeasurable_fst

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
theorem x_aestronglyMeasurable_at
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h : SystemAssumption72ObservedResponseFourthConditions μ X e Y β)
    (i : ℕ) : AEStronglyMeasurable (X i) μ :=
  (h.observed_row_aestronglyMeasurable_at i).fst

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
theorem y_aestronglyMeasurable_at
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h : SystemAssumption72ObservedResponseFourthConditions μ X e Y β)
    (i : ℕ) : AEStronglyMeasurable (Y i) μ :=
  (h.observed_row_aestronglyMeasurable_at i).snd

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
theorem design_memLp_four
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h : SystemAssumption72ObservedResponseFourthConditions μ X e Y β) :
    MemLp (X 0) 4 μ := by
  refine MemLp.of_eval fun a => MemLp.of_eval fun c => ?_
  have hcoord : AEStronglyMeasurable (fun ω => X 0 ω a c) μ :=
    (continuous_apply c).comp_aestronglyMeasurable
      ((continuous_apply a).comp_aestronglyMeasurable
        (h.x_aestronglyMeasurable_at 0))
  apply system_memLp_four_of_integrable_fourth hcoord
  refine h.design_norm_fourth_integrable.mono'
    (hcoord.aemeasurable.pow_const 4).aestronglyMeasurable
    (ae_of_all μ fun ω => ?_)
  have hentry : |X 0 ω a c| ≤ ‖X 0 ω‖ := by
    simpa [Real.norm_eq_abs] using
      (Matrix.norm_entry_le_entrywise_sup_norm (A := X 0 ω) (i := a) (j := c))
  calc
    ‖X 0 ω a c ^ 4‖ = |X 0 ω a c| ^ 4 := by simp [Real.norm_eq_abs]
    _ ≤ ‖X 0 ω‖ ^ 4 := by gcongr

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
theorem response_memLp_four
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h : SystemAssumption72ObservedResponseFourthConditions μ X e Y β) :
    MemLp (Y 0) 4 μ := by
  refine MemLp.of_eval fun a => ?_
  have hcoord : AEStronglyMeasurable (fun ω => Y 0 ω a) μ :=
    (continuous_apply a).comp_aestronglyMeasurable
      (h.y_aestronglyMeasurable_at 0)
  apply system_memLp_four_of_integrable_fourth hcoord
  refine h.response_norm_fourth_integrable.mono'
    (hcoord.aemeasurable.pow_const 4).aestronglyMeasurable
    (ae_of_all μ fun ω => ?_)
  have hentry : |Y 0 ω a| ≤ ‖Y 0 ω‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (Y 0 ω) a
  calc
    ‖Y 0 ω a ^ 4‖ = |Y 0 ω a| ^ 4 := by simp [Real.norm_eq_abs]
    _ ≤ ‖Y 0 ω‖ ^ 4 := by gcongr

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
theorem fitted_memLp_four
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h : SystemAssumption72ObservedResponseFourthConditions μ X e Y β) :
    MemLp (fun ω => X 0 ω *ᵥ β) 4 μ := by
  classical
  refine MemLp.of_eval fun a => ?_
  convert memLp_finset_sum' (s := Finset.univ)
    (f := fun c ω => X 0 ω a c * β c)
    (fun c _ => ((h.design_memLp_four.eval a).eval c).mul_const (β c)) using 1
  ext ω
  simp [Matrix.mulVec, dotProduct]

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
theorem error_memLp_four
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h : SystemAssumption72ObservedResponseFourthConditions μ X e Y β) :
    MemLp (e 0) 4 μ := by
  have hdiff := h.response_memLp_four.sub h.fitted_memLp_four
  convert hdiff using 1
  funext ω
  ext a
  change e 0 ω a = Y 0 ω a - (X 0 ω *ᵥ β) a
  rw [h.model 0 ω a]
  change e 0 ω a = X 0 ω a ⬝ᵥ β + e 0 ω a - X 0 ω a ⬝ᵥ β
  ring

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
private theorem observed_to_residual_measurable (β : k → ℝ) :
    Measurable (fun row : Matrix m k ℝ × (m → ℝ) =>
      (row.1, row.2 - row.1 *ᵥ β)) :=
  (continuous_fst.prodMk
    (continuous_snd.sub
      (Continuous.matrix_mulVec continuous_fst continuous_const))).measurable

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
private theorem observed_to_residual_apply
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h : SystemAssumption72ObservedResponseFourthConditions μ X e Y β)
    (i : ℕ) (ω : Ω) :
    ((X i ω, Y i ω).1, (X i ω, Y i ω).2 - (X i ω, Y i ω).1 *ᵥ β) =
      (X i ω, e i ω) := by
  apply Prod.ext
  · rfl
  · funext a
    change Y i ω a - (X i ω *ᵥ β) a = e i ω a
    rw [h.model i ω a]
    change X i ω a ⬝ᵥ β + e i ω a - X i ω a ⬝ᵥ β = e i ω a
    ring

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
theorem gram_integrable
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h : SystemAssumption72ObservedResponseFourthConditions μ X e Y β) :
    Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ := by
  have hX2 : MemLp (X 0) 2 μ := h.design_memLp_four.mono_exponent (by norm_num)
  refine Integrable.of_eval fun c => Integrable.of_eval fun d => ?_
  have hsum : Integrable (fun ω => ∑ a : m, X 0 ω a c * X 0 ω a d) μ :=
    integrable_finset_sum _ fun a _ =>
      ((hX2.eval a).eval c).integrable_mul ((hX2.eval a).eval d)
  simpa [Matrix.mul_apply, Matrix.transpose_apply] using hsum

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
theorem score_memLp_two
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h : SystemAssumption72ObservedResponseFourthConditions μ X e Y β) :
    MemLp (fun ω => systemScore (X 0 ω) (e 0 ω)) 2 μ := by
  classical
  refine MemLp.of_eval fun c => ?_
  convert memLp_finset_sum' (s := Finset.univ)
    (f := fun a ω => X 0 ω a c * e 0 ω a)
    (fun a _ => system_memLp_two_mul_of_memLp_four
      ((h.design_memLp_four.eval a).eval c) (h.error_memLp_four.eval a)) using 1
  ext ω
  simp [systemScore, Matrix.mulVec, dotProduct, Matrix.transpose_apply]

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
/-- Hansen's observed-row fourth moments imply the compact error second
moment used by the feasible covariance proof. -/
theorem error_norm_sq_integrable
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h : SystemAssumption72ObservedResponseFourthConditions μ X e Y β) :
    Integrable (fun ω => ‖e 0 ω‖ ^ 2) μ :=
  (h.error_memLp_four.mono_exponent (by norm_num : (2 : ENNReal) ≤ 4)).integrable_norm_pow
    (by norm_num)

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
/-- Hansen's observed-row fourth moments imply
`E[‖e₀‖ ‖X₀‖³] < ∞`, the compact mixed moment used by the feasible robust
covariance substitution. This is Young's inequality applied pointwise. -/
theorem error_design_norm_cubed_integrable
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h : SystemAssumption72ObservedResponseFourthConditions μ X e Y β) :
    Integrable (fun ω => ‖e 0 ω‖ * ‖X 0 ω‖ ^ 3) μ := by
  have he4 : Integrable (fun ω => ‖e 0 ω‖ ^ 4) μ :=
    h.error_memLp_four.integrable_norm_pow (by norm_num)
  have hdom : Integrable
      (fun ω => (4 : ℝ)⁻¹ * (‖e 0 ω‖ ^ 4 + 3 * ‖X 0 ω‖ ^ 4)) μ :=
    (he4.add (h.design_norm_fourth_integrable.const_mul 3)).const_mul (4 : ℝ)⁻¹
  have htarget : AEStronglyMeasurable
      (fun ω => ‖e 0 ω‖ * ‖X 0 ω‖ ^ 3) μ := by
    simpa only [Pi.mul_apply, Pi.pow_apply] using
      h.error_memLp_four.1.norm.mul (h.design_memLp_four.1.norm.pow 3)
  refine hdom.mono' htarget (ae_of_all μ fun ω => ?_)
  have hfactor :
      0 ≤ (‖e 0 ω‖ - ‖X 0 ω‖) ^ 2 *
        (‖e 0 ω‖ ^ 2 + 2 * ‖e 0 ω‖ * ‖X 0 ω‖ + 3 * ‖X 0 ω‖ ^ 2) := by
    positivity
  have hyoung :
      4 * (‖e 0 ω‖ * ‖X 0 ω‖ ^ 3) ≤
        ‖e 0 ω‖ ^ 4 + 3 * ‖X 0 ω‖ ^ 4 := by
    nlinarith
  norm_num at hyoung ⊢
  nlinarith

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Literal observed-row Assumption 7.2 implies the primitive residual-row
package used by Hansen Theorems 11.1--11.3. -/
theorem toSystemAssumption72PrimitiveRow
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h : SystemAssumption72ObservedResponseFourthConditions μ X e Y β) :
    SystemAssumption72PrimitiveRow μ X e where
  row_iIndep := by
    have hcomp := h.observed_iIndep.comp
      (fun _ row => (row.1, row.2 - row.1 *ᵥ β))
      (fun _ => observed_to_residual_measurable (m := m) (k := k) β)
    convert hcomp using 1
    funext i ω
    exact (h.observed_to_residual_apply i ω).symm
  row_identDistrib := by
    intro i
    have hcomp := (h.observed_identDistrib i).comp
      (observed_to_residual_measurable (m := m) (k := k) β)
    convert hcomp using 1 <;> funext ω
    · exact (h.observed_to_residual_apply i ω).symm
    · exact (h.observed_to_residual_apply 0 ω).symm
  gram_integrable := h.gram_integrable
  score_memLp := h.score_memLp_two
  score_mean_zero := h.score_mean_zero
  gram_nonsing := (Matrix.isUnit_iff_isUnit_det _).mp h.gram_posDef.isUnit

end SystemAssumption72ObservedResponseFourthConditions

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
/-- Coordinate version of the fact that integrability of `X'X` gives finite
second moments for the system-design coordinates. -/
theorem systemDesignCoordinate_memLp_two_of_gram_integrable
    {X0 : Ω → Matrix m k ℝ}
    (hX : AEStronglyMeasurable X0 μ)
    (hGram : Integrable (fun ω => (X0 ω)ᵀ * X0 ω) μ)
    (a : m) (c : k) :
    MemLp (fun ω => X0 ω a c) 2 μ := by
  have hcoord : AEStronglyMeasurable (fun ω => X0 ω a c) μ :=
    (continuous_apply c).comp_aestronglyMeasurable
      ((continuous_apply a).comp_aestronglyMeasurable hX)
  have hdiag : Integrable (fun ω => ((X0 ω)ᵀ * X0 ω) c c) μ :=
    Integrable.eval (Integrable.eval hGram c) c
  have hsq : Integrable (fun ω => (X0 ω a c) ^ 2) μ := by
    have hmeas : AEStronglyMeasurable (fun ω => (X0 ω a c) ^ 2) μ := by
      simpa [pow_two] using hcoord.mul hcoord
    refine hdiag.mono' hmeas (ae_of_all μ fun ω => ?_)
    have hle : (X0 ω a c) ^ 2 ≤ ((X0 ω)ᵀ * X0 ω) c c := by
      simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using
        (Finset.single_le_sum
          (fun b _ => sq_nonneg (X0 ω b c)) (Finset.mem_univ a))
    calc
      ‖(X0 ω a c) ^ 2‖ = (X0 ω a c) ^ 2 := by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
      _ ≤ ((X0 ω)ᵀ * X0 ω) c c := hle
  exact (memLp_two_iff_integrable_sq hcoord).2 hsq

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
/-- Integrability of `X'X` gives a finite second moment for the whole
matrix-valued system-design row, provided the row is a.e. strongly measurable. -/
theorem systemDesign_memLp_two_of_gram_integrable
    {X0 : Ω → Matrix m k ℝ}
    (hX : AEStronglyMeasurable X0 μ)
    (hGram : Integrable (fun ω => (X0 ω)ᵀ * X0 ω) μ) :
    MemLp X0 2 μ :=
  MemLp.of_eval
    (fun a => MemLp.of_eval
      (fun c => systemDesignCoordinate_memLp_two_of_gram_integrable
        (μ := μ) hX hGram a c))

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
/-- Coordinate-measurable version of
`systemDesign_memLp_two_of_gram_integrable`.

This bridge is useful when a chapter assumption exposes each design coordinate
as measurable with respect to a conditioning sigma-algebra, rather than first
packaging the row as an a.e. strongly measurable matrix. -/
theorem systemDesign_memLp_two_of_gram_integrable_coordinates
    {X0 : Ω → Matrix m k ℝ}
    (hX : ∀ a c, AEStronglyMeasurable (fun ω => X0 ω a c) μ)
    (hGram : Integrable (fun ω => (X0 ω)ᵀ * X0 ω) μ) :
    MemLp X0 2 μ := by
  have hcoord : ∀ a c, MemLp (fun ω => X0 ω a c) 2 μ := by
    intro a c
    have hdiag : Integrable (fun ω => ((X0 ω)ᵀ * X0 ω) c c) μ :=
      Integrable.eval (Integrable.eval hGram c) c
    have hsq : Integrable (fun ω => (X0 ω a c) ^ 2) μ := by
      have hmeas : AEStronglyMeasurable (fun ω => (X0 ω a c) ^ 2) μ := by
        simpa [pow_two] using (hX a c).mul (hX a c)
      refine hdiag.mono' hmeas (ae_of_all μ fun ω => ?_)
      have hle : (X0 ω a c) ^ 2 ≤ ((X0 ω)ᵀ * X0 ω) c c := by
        simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using
          (Finset.single_le_sum
            (fun b _ => sq_nonneg (X0 ω b c)) (Finset.mem_univ a))
      calc
        ‖(X0 ω a c) ^ 2‖ = (X0 ω a c) ^ 2 := by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
        _ ≤ ((X0 ω)ᵀ * X0 ω) c c := hle
    exact (memLp_two_iff_integrable_sq (hX a c)).2 hsq
  exact MemLp.of_eval (fun a => MemLp.of_eval (fun c => hcoord a c))

namespace SystemAssumption72PrimitiveRow

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- A primitive row-iid Assumption 7.2 package supplies the split
`SystemAssumption72` fields used by the Chapter 11 proof engine. -/
theorem toSystemAssumption72
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72PrimitiveRow μ X e) :
    SystemAssumption72 μ X e where
  gram_integrable := h.gram_integrable
  gram_independent := by
    let f : Matrix m k ℝ × (m → ℝ) → Matrix k k ℝ := fun row => row.1ᵀ * row.1
    have hf : Measurable f := measurable_system_pair_gram (m := m) (k := k)
    have hgram : iIndepFun (fun i ω => (X i ω)ᵀ * X i ω) μ := by
      simpa [Function.comp_def] using
        h.row_iIndep.comp (fun _ => f) (fun _ => hf)
    intro i j hij
    exact hgram.indepFun hij
  gram_identDistrib := by
    intro i
    let f : Matrix m k ℝ × (m → ℝ) → Matrix k k ℝ := fun row => row.1ᵀ * row.1
    have hf : Measurable f := measurable_system_pair_gram (m := m) (k := k)
    simpa [Function.comp_def] using
      (h.row_identDistrib i).comp hf
  score_memLp := h.score_memLp
  score_iIndep := by
    let f : Matrix m k ℝ × (m → ℝ) → k → ℝ := fun row => systemScore row.1 row.2
    have hf : Measurable f := measurable_system_row_score (m := m) (k := k)
    simpa [Function.comp_def] using
      h.row_iIndep.comp (fun _ => f) (fun _ => hf)
  score_identDistrib := by
    intro i
    let f : Matrix m k ℝ × (m → ℝ) → k → ℝ := fun row => systemScore row.1 row.2
    have hf : Measurable f := measurable_system_row_score (m := m) (k := k)
    simpa [Function.comp_def] using
      (h.row_identDistrib i).comp hf
  score_mean_zero := h.score_mean_zero
  gram_nonsing := h.gram_nonsing

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- The primitive row package supplies a.e. strong measurability of the
baseline observation row. -/
theorem row_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72PrimitiveRow μ X e) :
    AEStronglyMeasurable (fun ω => (X 0 ω, e 0 ω)) μ :=
  (h.row_identDistrib 0).aestronglyMeasurable_fst

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- The primitive row package supplies a.e. strong measurability of every
observation row. -/
theorem row_aestronglyMeasurable_at
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72PrimitiveRow μ X e) (i : ℕ) :
    AEStronglyMeasurable (fun ω => (X i ω, e i ω)) μ :=
  (h.row_identDistrib i).aestronglyMeasurable_fst

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- The primitive row package supplies a.e. strong measurability of the
baseline system design. -/
theorem x_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72PrimitiveRow μ X e) :
    AEStronglyMeasurable (X 0) μ :=
  h.row_aestronglyMeasurable.fst

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- The primitive row package supplies a.e. strong measurability of every
system design row. -/
theorem x_aestronglyMeasurable_at
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72PrimitiveRow μ X e) (i : ℕ) :
    AEStronglyMeasurable (X i) μ :=
  (h.row_aestronglyMeasurable_at i).fst

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- The primitive row package supplies a.e. strong measurability of the
baseline system error vector. -/
theorem e_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72PrimitiveRow μ X e) :
    AEStronglyMeasurable (e 0) μ :=
  h.row_aestronglyMeasurable.snd

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- The primitive row package supplies a.e. strong measurability of every
system error row. -/
theorem e_aestronglyMeasurable_at
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72PrimitiveRow μ X e) (i : ℕ) :
    AEStronglyMeasurable (e i) μ :=
  (h.row_aestronglyMeasurable_at i).snd

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- The primitive row package derives the system-design `L²` moment from
Assumption 7.2's Gram integrability. -/
theorem design_memLp_two
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72PrimitiveRow μ X e) :
    MemLp (X 0) 2 μ :=
  systemDesign_memLp_two_of_gram_integrable
    (μ := μ) h.x_aestronglyMeasurable h.gram_integrable

end SystemAssumption72PrimitiveRow

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq k] [DecidableEq q] [Fintype m]
  [DecidableEq m] in
/-- Row measurability of the system linear model implies row measurability of
the observed outcome vector. -/
theorem systemOutcome_aestronglyMeasurable_of_linear_model
    [Finite m]
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    ∀ i, AEStronglyMeasurable (Y i) μ := by
  classical
  letI := Fintype.ofFinite m
  intro i
  rw [aestronglyMeasurable_iff_aemeasurable]
  rw [aemeasurable_pi_iff]
  intro j
  have hXj : AEStronglyMeasurable (fun ω => X i ω j) μ :=
    (continuous_apply j).comp_aestronglyMeasurable (hX i)
  have hdot : AEStronglyMeasurable (fun ω => (X i ω j) ⬝ᵥ β) μ := by
    simpa [dotProduct] using
      Finset.aestronglyMeasurable_fun_sum Finset.univ
        (fun c _ =>
          (((continuous_apply c).comp_aestronglyMeasurable hXj).mul_const (β c)))
  have hej : AEStronglyMeasurable (fun ω => e i ω j) μ :=
    (continuous_apply j).comp_aestronglyMeasurable (he i)
  exact ((hdot.add hej).congr
    (ae_of_all μ fun ω => (hmodel i ω j).symm)).aemeasurable

namespace SystemAssumption72

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
/-- The Hansen scaling `√n ĝₙ` equals the centered iid-vector-CLT scaling when
the score mean is zero. -/
theorem sqrt_smul_systemScoreMean_eq_inv_sqrt_sum
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hzero : meanVec μ (fun ω => systemScore (X 0 ω) (e 0 ω)) = 0)
    (n : ℕ) (ω : Ω) :
    Real.sqrt (n : ℝ) •
        systemScoreMean (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) =
      (Real.sqrt (n : ℝ))⁻¹ •
        (∑ i ∈ Finset.range n, systemScore (X i ω) (e i ω) -
          (n : ℝ) • meanVec μ (fun ω => systemScore (X 0 ω) (e 0 ω))) := by
  have hsum :
      (∑ i : Fin n, systemScore (X i.val ω) (e i.val ω)) =
        ∑ i ∈ Finset.range n, systemScore (X i ω) (e i ω) :=
    Fin.sum_univ_eq_sum_range (fun i => systemScore (X i ω) (e i ω)) n
  rw [hzero, smul_zero, sub_zero]
  unfold systemScoreMean
  simp only [Fintype.card_fin]
  rw [hsum]
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hnpos
    have hscale : Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ = (Real.sqrt (n : ℝ))⁻¹ := by
      have hsqr_mul : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt hnpos.le
      calc
        Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ =
            Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ))⁻¹ := by
              rw [hsqr_mul]
        _ = (Real.sqrt (n : ℝ))⁻¹ := by
              field_simp [hsqrt_ne]
    rw [smul_smul]
    exact congrArg (fun c : ℝ => c • ∑ i ∈ Finset.range n, systemScore (X i ω) (e i ω))
      hscale

end SystemAssumption72

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Linearized Hansen Theorem 11.1 at the observation-system level.

If `Q̂ →p Q` and the system score mean obeys the vector CLT with covariance
`Ω`, then the feasible linearized statistic `Q̂⁻¹√n ĝ` has the Gaussian limit
with covariance `Q⁻¹ΩQ⁻¹`. -/
theorem systemLinearizedScore_tendstoInDistribution
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹ *ᵥ
          (Real.sqrt (t : ℝ) •
            systemScoreMean (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω)))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (systemAsymptoticVariance Q Omega)) := by
  have hQinv : TendstoInMeasure μ
      (fun (t : ℕ) ω => (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹)
      atTop (fun _ => Q⁻¹) :=
    tendstoInMeasure_matrix_inv h.gram_meas h.gram_tendsto (fun _ => h.gram_nonsing)
  have hQinv_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => (systemNormalizedGram (fun i : Fin n => X i.val ω))⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (h.gram_meas n)
  have hlin :=
    randomMatrix_mulVec_tendstoInDistribution_multivariateGaussian
      (Ahat := fun (t : ℕ) ω => (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹)
      (A := Q⁻¹) (S := Omega)
      (T := fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          systemScoreMean (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω))
      h.score_cov_posSemidef hQinv_meas hQinv h.score_limit
  simpa [systemAsymptoticVariance, h.gram_inv_transpose] using hlin

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- The sample system Gram is singular with asymptotically vanishing probability
whenever `Q̂ →ₚ Q` and the population Gram is nonsingular. -/
theorem measure_systemNormalizedGram_singular_tendsto_zero
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) :
    Tendsto
      (fun n => μ {ω |
        ¬ IsUnit (systemNormalizedGram (fun i : Fin n => X i.val ω)).det})
      atTop (𝓝 0) := by
  have hDet : TendstoInMeasure μ
      (fun n ω => (systemNormalizedGram (fun i : Fin n => X i.val ω)).det)
      atTop (fun _ => Q.det) :=
    tendstoInMeasure_continuous_comp h.gram_meas h.gram_tendsto
      (Continuous.matrix_det continuous_id)
  have hqne : Q.det ≠ 0 := h.gram_nonsing.ne_zero
  set ε : ℝ := |Q.det| / 2 with hε_def
  have hε_pos : 0 < ε := half_pos (abs_pos.mpr hqne)
  have hε_le : ε ≤ |Q.det| := by
    rw [hε_def]
    linarith [abs_nonneg Q.det]
  have hmeas_eps := hDet (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε_pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmeas_eps
    (fun _ => zero_le _) (fun n => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq, isUnit_iff_ne_zero, not_not] at hω
  simp only [Set.mem_setOf_eq, hω, edist_dist, Real.dist_eq, zero_sub, abs_neg]
  exact ENNReal.ofReal_le_ofReal hε_le

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Hansen-facing system least-squares CLT from a proved system linearization.

The theorem is stated for observation-level system regressors and vector
outcomes. The remaining proof obligation is exactly the finite-sample/asymptotic
linearization of the chosen totalized estimator around `Q̂⁻¹√n ĝ`; once that is
available, the Gaussian limit follows from `systemLinearizedScore_tendstoInDistribution`. -/
theorem systemLeastSquaresBetaStarObs_tendstoInDistribution_of_linearization
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) (β : k → ℝ)
    (hlinearization : TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              systemScoreMean (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0))
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (systemAsymptoticVariance Q Omega)) := by
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (t : ℕ) ω =>
      (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹ *ᵥ
        (Real.sqrt (t : ℝ) •
          systemScoreMean (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω)))
    (Y := fun (t : ℕ) ω =>
      Real.sqrt (t : ℝ) •
        (systemLeastSquaresBetaStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
    (Z := fun z : EuclideanSpace ℝ k => z.ofLp)
    (systemLinearizedScore_tendstoInDistribution (μ := μ) h)
    hlinearization hmeas

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Exact Chapter 11.1 Star-estimator linearization on nonsingular sample Grams.

The normalized finite-sample identity in `Systems.lean` leaves only the
totalized singular-design remainder
`(Q̂ₙ⁻¹ Q̂ₙ - I) β`. On samples where `Q̂ₙ` is nonsingular this remainder is
exactly zero, so the scaled estimator error equals the linearized score. -/
theorem systemLeastSquaresBetaStarObs_linearization_of_nonsingular
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hQhat_unit : ∀ t ω,
      IsUnit (systemNormalizedGram (fun i : Fin t => X i.val ω)).det) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              systemScoreMean (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0) := by
  have hzero :
      TendstoInMeasure μ (fun _ : ℕ => fun _ : Ω => (0 : k → ℝ)) atTop
        (fun _ => 0) := by
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ (fun _ => tendsto_const_nhds))
  refine TendstoInMeasure.congr (fun t => ?_) EventuallyEq.rfl hzero
  filter_upwards with ω
  let Xt : Fin t → Matrix m k ℝ := fun i => X i.val ω
  let et : Fin t → m → ℝ := fun i => e i.val ω
  let Yt : Fin t → m → ℝ := fun i => Y i.val ω
  let Qhat : Matrix k k ℝ := systemNormalizedGram Xt
  let ghat : k → ℝ := systemScoreMean Xt et
  let betaHat : k → ℝ := systemLeastSquaresBetaStarObs Xt Yt
  have hid :
      betaHat - β - Qhat⁻¹ *ᵥ ghat =
        ((Qhat)⁻¹ * Qhat - 1) *ᵥ β := by
    simpa [betaHat, Qhat, ghat, Xt, et, Yt] using
      systemLeastSquaresBetaStarObs_sub_identity_normalized
        (X := Xt) (e := et) (Y := Yt) (β := β)
        (by intro i j; exact hmodel i.val ω j)
  have hlin0 : betaHat - β - Qhat⁻¹ *ᵥ ghat = 0 := by
    rw [hid, Matrix.nonsing_inv_mul Qhat (by simpa [Qhat, Xt] using hQhat_unit t ω)]
    simp
  ext a
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply]
  have hcoord := congrArg (fun v : k → ℝ => v a) hlin0
  simp only [Pi.sub_apply, Pi.zero_apply] at hcoord
  rw [Matrix.mulVec_smul]
  simp only [Pi.smul_apply]
  symm
  change Real.sqrt (t : ℝ) * (betaHat a - β a) -
      Real.sqrt (t : ℝ) * (Qhat⁻¹ *ᵥ ghat) a = 0
  calc
    Real.sqrt (t : ℝ) * (betaHat a - β a) -
        Real.sqrt (t : ℝ) * (Qhat⁻¹ *ᵥ ghat) a =
          Real.sqrt (t : ℝ) *
            (betaHat a - β a - (Qhat⁻¹ *ᵥ ghat) a) := by ring
    _ = 0 := by rw [hcoord, mul_zero]

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Hansen Theorem 11.1 wrapper when sample normalized Grams are nonsingular.

This theorem composes the exact nonsingular finite-sample linearization with
the Chapter 11 system-score CLT package. It is stronger than the pure
linearization-interface theorem, while keeping the nonsingularity side
condition explicit rather than hiding it inside Assumption 7.2. -/
theorem systemLeastSquaresBetaStarObs_tendstoInDistribution_of_nonsingular
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hQhat_unit : ∀ t ω,
      IsUnit (systemNormalizedGram (fun i : Fin t => X i.val ω)).det)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (systemAsymptoticVariance Q Omega)) :=
  systemLeastSquaresBetaStarObs_tendstoInDistribution_of_linearization
    (μ := μ) h β
    (systemLeastSquaresBetaStarObs_linearization_of_nonsingular
      (μ := μ) (X := X) (e := e) (Y := Y) β hmodel hQhat_unit)
    hmeas

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Exact Chapter 11.1 Star-estimator linearization with the singular-design
remainder handled by a high-probability argument.

This removes the global sample-Gram nonsingularity side condition from
`systemLeastSquaresBetaStarObs_linearization_of_nonsingular`: on nonsingular
samples the residual is exactly zero, and the singular event has probability
tending to zero by `measure_systemNormalizedGram_singular_tendsto_zero`. -/
theorem systemLeastSquaresBetaStarObs_linearization
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    TendstoInMeasure μ
      ((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              systemScoreMean (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω)))
      atTop (fun _ => 0) := by
  have hsingular := measure_systemNormalizedGram_singular_tendsto_zero h
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsingular
    (fun _ => zero_le _) (fun t => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro hunit
  let Xt : Fin t → Matrix m k ℝ := fun i => X i.val ω
  let et : Fin t → m → ℝ := fun i => e i.val ω
  let Yt : Fin t → m → ℝ := fun i => Y i.val ω
  let Qhat : Matrix k k ℝ := systemNormalizedGram Xt
  let ghat : k → ℝ := systemScoreMean Xt et
  let betaHat : k → ℝ := systemLeastSquaresBetaStarObs Xt Yt
  have hid :
      betaHat - β - Qhat⁻¹ *ᵥ ghat =
        ((Qhat)⁻¹ * Qhat - 1) *ᵥ β := by
    simpa [betaHat, Qhat, ghat, Xt, et, Yt] using
      systemLeastSquaresBetaStarObs_sub_identity_normalized
        (X := Xt) (e := et) (Y := Yt) (β := β)
        (by intro i j; exact hmodel i.val ω j)
  have hlin0 : betaHat - β - Qhat⁻¹ *ᵥ ghat = 0 := by
    rw [hid, Matrix.nonsing_inv_mul Qhat (by simpa [Qhat, Xt] using hunit)]
    simp
  have hzero :
      Real.sqrt (t : ℝ) • (betaHat - β) -
        Qhat⁻¹ *ᵥ (Real.sqrt (t : ℝ) • ghat) = 0 := by
    rw [Matrix.mulVec_smul, ← smul_sub, hlin0, smul_zero]
  change ε ≤ edist
    (((fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) -
        fun (t : ℕ) ω =>
          (systemNormalizedGram (fun i : Fin t => X i.val ω))⁻¹ *ᵥ
            (Real.sqrt (t : ℝ) •
              systemScoreMean (fun i : Fin t => X i.val ω) (fun i : Fin t => e i.val ω)))
        t ω) 0 at hω
  have hω0 : ε = 0 := by
    simpa [Xt, et, Yt, Qhat, ghat, betaHat, hzero] using hω
  exact hε.ne' hω0

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Hansen Theorem 11.1 at the system-score interface, with sample singularity
handled by the totalized Star estimator and the high-probability Gram argument. -/
theorem systemLeastSquaresBetaStarObs_tendstoInDistribution
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (systemAsymptoticVariance Q Omega)) :=
  systemLeastSquaresBetaStarObs_tendstoInDistribution_of_linearization
    (μ := μ) h β
    (systemLeastSquaresBetaStarObs_linearization
      (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel)
    hmeas

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- The Chapter 11.1 system LS CLT implies the scaled system coefficient
error is `Oₚ(1)`. This is the stochastic boundedness input for Hansen
Theorem 11.2. -/
theorem systemLeastSquaresBetaStarObs_sqrt_sub_boundedInProbabilityNorm
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ) :
    BoundedInProbabilityNorm μ
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) := by
  exact BoundedInProbabilityNorm.of_tendstoInDistribution
    (systemLeastSquaresBetaStarObs_tendstoInDistribution
      (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel hmeas)

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Consistency of the Chapter 11 system Star estimator as a corollary of the
system LS CLT. -/
theorem systemLeastSquaresBetaStarObs_tendstoInMeasure_beta
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInMeasure μ
      (fun t ω =>
        systemLeastSquaresBetaStarObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) := by
  let βhat : ℕ → Ω → k → ℝ := fun t ω =>
    systemLeastSquaresBetaStarObs
      (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)
  have hbounded : BoundedInProbabilityNorm μ
      (fun (t : ℕ) ω => Real.sqrt (t : ℝ) • (βhat t ω - β)) := by
    simpa [βhat] using
      systemLeastSquaresBetaStarObs_sqrt_sub_boundedInProbabilityNorm
        (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel hmeas
  have hinv_sqrt : Tendsto (fun t : ℕ => (Real.sqrt (t : ℝ))⁻¹)
      atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hscaled :
      TendstoInMeasure μ
        (fun (t : ℕ) (ω : Ω) => ((Real.sqrt (t : ℝ))⁻¹) •
          ((Real.sqrt (t : ℝ)) • (βhat t ω - β)))
        atTop (fun _ => (0 : k → ℝ)) :=
    hbounded.tendstoInMeasure_const_smul_zero hinv_sqrt
  have hdiff : TendstoInMeasure μ (fun t ω => βhat t ω - β)
      atTop (fun _ => (0 : k → ℝ)) := by
    refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hscaled
    filter_upwards [eventually_atTop.2 ⟨1, fun t ht => ht⟩] with t ht
    exact ae_of_all μ (fun ω => by
      have htpos_nat : 0 < t := lt_of_lt_of_le Nat.zero_lt_one ht
      have htpos : 0 < (t : ℝ) := Nat.cast_pos.mpr htpos_nat
      have hsqrt_ne : Real.sqrt (t : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr htpos
      ext a
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hsqrt_ne, one_mul])
  have hconst : TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => β)
      atTop (fun _ => β) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all μ (fun _ => tendsto_const_nhds))
  exact TendstoInMeasure.of_sub_tendsto_zero_vector hdiff hconst

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Textbook-facing OrZero consistency of the Chapter 11 system estimator.

This is the OrZero counterpart of
`systemLeastSquaresBetaStarObs_tendstoInMeasure_beta`, transported through the
shared pointwise Star/OrZero bridge. -/
theorem systemLeastSquaresBetaOrZeroObs_tendstoInMeasure_beta
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} {Q Omega : Matrix k k ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInMeasure μ
      (fun t ω =>
        systemLeastSquaresBetaOrZeroObs
          (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω))
      atTop (fun _ => β) := by
  have hmeas_star : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ := by
    intro t
    convert hmeas t using 1
    ext ω
    rw [systemLeastSquaresBetaOrZeroObs_eq_star]
  simpa [systemLeastSquaresBetaOrZeroObs_eq_star] using
    systemLeastSquaresBetaStarObs_tendstoInMeasure_beta
      (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel hmeas_star

/-- Scalar-response support lemma for the Chapter 11 system CLT.

This is the `m = 1` Chapter 7 OLS specialization, not Hansen's joint
observation-level Theorem 11.1. The covariance is restated using Chapter 11's
`systemAsymptoticVariance` notation for reuse in scalar corollaries. -/
theorem scalarResponseSystemLeastSquaresBetaStar_tendstoInDistribution
    {X : ℕ → Ω → k → ℝ} {e y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) •
        (systemLeastSquaresBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e))) := by
  simpa [systemLeastSquaresBetaStar, systemAsymptoticVariance, heteroAsymCov] using
    olsBetaStar_vector_tendstoInDistribution_heteroAsymCov
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel

/-- Fixed-derivative transform of the scalar-response support CLT.

The full observation-level Hansen Theorem 11.2 is exposed separately below;
this lemma only transports the preceding `m = 1` specialization. -/
theorem scalarResponseSystemLeastSquaresBetaStar_linearTransform_tendstoInDistribution
    {X : ℕ → Ω → k → ℝ} {e y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ) (R : Matrix k q ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) •
        (Rᵀ *ᵥ systemLeastSquaresBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) -
          Rᵀ *ᵥ β))
      atTop (fun z : EuclideanSpace ℝ q => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemDeltaVariance
          (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e)) R)) := by
  let T : ℕ → Ω → k → ℝ := fun n ω =>
    Real.sqrt (n : ℝ) •
      (systemLeastSquaresBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)
  let Te : ℕ → Ω → EuclideanSpace ℝ k := fun n ω => WithLp.toLp 2 (T n ω)
  have hT := scalarResponseSystemLeastSquaresBetaStar_tendstoInDistribution
    (μ := μ) (X := X) (e := e) (y := y) h β hmodel
  have hTe :
      TendstoInDistribution Te atTop (fun z : EuclideanSpace ℝ k => z)
        (fun _ => μ)
        (multivariateGaussian 0
          (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e))) := by
    have hmap := hT.continuous_comp (PiLp.continuous_toLp 2 (fun _ : k => ℝ))
    simpa [T, Te, Function.comp_def] using hmap
  have hS : (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e)).PosSemidef := by
    simpa [systemAsymptoticVariance, heteroAsymCov] using
      heteroAsymCov_posSemidef (μ := μ) (X := X) (e := e) h
  have hlin :
      TendstoInDistribution
        (fun n => matrixContinuousLinearMap Rᵀ ∘ Te n)
        atTop (matrixContinuousLinearMap Rᵀ ∘ fun z : EuclideanSpace ℝ k => z)
        (fun _ => μ)
        (multivariateGaussian 0
          (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e))) :=
    hTe.continuous_comp (matrixContinuousLinearMap Rᵀ).continuous
  have hLaw :
      HasLaw (fun z : EuclideanSpace ℝ k => matrixContinuousLinearMap Rᵀ z)
        (multivariateGaussian 0
          (systemDeltaVariance
            (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e)) R))
        (multivariateGaussian 0
          (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e))) := by
    simpa [systemDeltaVariance, matrixContinuousLinearMap,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      hasLaw_multivariateGaussian_zero_linearMap (n := k) (q := q) hS Rᵀ
  have htargetE :
      TendstoInDistribution
        (fun n ω => matrixContinuousLinearMap Rᵀ (Te n ω))
        atTop (fun z : EuclideanSpace ℝ q => z)
        (fun _ => μ)
        (multivariateGaussian 0
          (systemDeltaVariance
            (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e)) R)) := by
    simpa [Function.comp_def] using
      tendstoInDistribution_id_of_hasLaw_limit (E := EuclideanSpace ℝ q) hlin hLaw
  have htarget := htargetE.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : q => ℝ))
  simpa [T, Te, Function.comp_def, matrixContinuousLinearMap_apply] using htarget

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [Fintype m] [DecidableEq m] in
/-- Hansen Assumption 7.3/Chapter 11.2 deterministic smoothness package for a
function of the system coefficient vector.

The derivative of `r` at `β` is represented by Hansen's matrix `R`, with
linear action `v ↦ Rᵀv`. The stochastic Taylor-remainder negligibility needed
for Theorem 11.2 is intentionally kept outside this deterministic package. -/
structure SystemDeltaAssumption73
    (r : (k → ℝ) → (q → ℝ)) (β : k → ℝ) (R : Matrix k q ℝ)
    extends SmoothFunctionAssumption73 r β R

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [Fintype m] [DecidableEq m] in
/-- Measurable companion to `SystemDeltaAssumption73`.

Local differentiability at `β` supplies Hansen's Taylor remainder, but it does
not by itself make every plug-in sample transform measurable. This package adds
the exact measurable-transform field used to discharge the transformed-target
measurability premises in theorem-facing wrappers. -/
structure SystemDeltaAssumption73Measurable
    (r : (k → ℝ) → (q → ℝ)) (β : k → ℝ) (R : Matrix k q ℝ)
    extends SystemDeltaAssumption73 r β R where
  measurable : Measurable r

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [Fintype m] [DecidableEq m] in
/-- Literal `ContDiffAt` surface for Hansen Assumption 7.3.

The `ContDiffAt` field records Hansen's continuously differentiable-at-the-true
parameter assumption. The derivative representation, full-rank condition, and
measurability are the additional finite-dimensional data needed by the current
Lean theorem route. -/
structure SystemDeltaAssumption73ContDiffAt
    (r : (k → ℝ) → (q → ℝ)) (β : k → ℝ) (R : Matrix k q ℝ)
    extends SmoothFunctionAssumption73 r β R where
  contDiffAt : ContDiffAt ℝ 1 r β
  measurable : Measurable r

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [Fintype m] [DecidableEq m] in
/-- Deterministic Taylor remainder for Hansen Theorem 11.2:
`r(b) - r(β) - Rᵀ(b - β)`. -/
noncomputable def systemDeltaTaylorRemainder
    (r : (k → ℝ) → (q → ℝ)) (β : k → ℝ) (R : Matrix k q ℝ) :
    (k → ℝ) → (q → ℝ) :=
  fun b => r b - r β - Rᵀ *ᵥ (b - β)

namespace SystemDeltaAssumption73

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq q]
  [Fintype m] [DecidableEq m] in
/-- Reuse the generic Chapter 7/Delta-method Assumption 7.3 package at the
Chapter 11 system layer. -/
def of_smoothFunctionAssumption73
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h73 : SmoothFunctionAssumption73 r β R) :
    SystemDeltaAssumption73 r β R where
  toSmoothFunctionAssumption73 := h73

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq q]
  [Fintype m] [DecidableEq m] in
/-- Assumption 7.3 supplies the deterministic little-o Taylor remainder. -/
theorem taylorRemainder_isLittleO
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h73 : SystemDeltaAssumption73 r β R) :
    systemDeltaTaylorRemainder r β R =o[𝓝 β] (fun b => b - β) := by
  simpa [systemDeltaTaylorRemainder, h73.derivative_apply] using
    deltaMethod_remainder_isLittleO h73.differentiable_at

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq q]
  [Fintype m] [DecidableEq m] in
/-- Algebraic form of the Taylor expansion around `β`. -/
theorem taylorExpansion_eq_linear_plus_remainder
    {r : (k → ℝ) → (q → ℝ)} {β b : k → ℝ} {R : Matrix k q ℝ}
    (_h73 : SystemDeltaAssumption73 r β R) :
    r b - r β =
      Rᵀ *ᵥ (b - β) + systemDeltaTaylorRemainder r β R b := by
  ext j
  simp [systemDeltaTaylorRemainder]

end SystemDeltaAssumption73

namespace SystemDeltaAssumption73Measurable

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq q]
  [Fintype m] [DecidableEq m] in
/-- Add the measurable-transform field to an existing Chapter 11 Assumption 7.3
package. This is the direct constructor for call sites that already proved the
derivative representation and full-rank condition in `SystemDeltaAssumption73`. -/
def of_systemDeltaAssumption73
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (hr : Measurable r) (h73 : SystemDeltaAssumption73 r β R) :
    SystemDeltaAssumption73Measurable r β R where
  toSystemDeltaAssumption73 := h73
  measurable := hr

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq q]
  [Fintype m] [DecidableEq m] in
/-- Measurable Chapter 11 wrapper around the generic smooth-function
Assumption 7.3 package. -/
def of_smoothFunctionAssumption73
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (hr : Measurable r) (h73 : SmoothFunctionAssumption73 r β R) :
    SystemDeltaAssumption73Measurable r β R where
  toSystemDeltaAssumption73 :=
    SystemDeltaAssumption73.of_smoothFunctionAssumption73 h73
  measurable := hr

end SystemDeltaAssumption73Measurable

namespace SystemDeltaAssumption73ContDiffAt

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq q]
  [Fintype m] [DecidableEq m] in
/-- The literal `ContDiffAt` package supplies the measurable Chapter 11
Assumption 7.3 surface. -/
def toSystemDeltaAssumption73Measurable
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h73 : SystemDeltaAssumption73ContDiffAt r β R) :
    SystemDeltaAssumption73Measurable r β R where
  toSystemDeltaAssumption73 :=
    { derivative := h73.derivative
      differentiable_at := h73.differentiable_at
      derivative_apply := h73.derivative_apply
      fullRank := h73.fullRank }
  measurable := h73.measurable

end SystemDeltaAssumption73ContDiffAt

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq q] in
/-- Hansen Theorem 11.2 Taylor-remainder bridge.

If the coefficient estimator is consistent and its scaled coefficient error is
`Oₚ(1)`, Assumption 7.3's deterministic little-o Taylor remainder is negligible
after the same scaling. -/
theorem systemDelta_scaled_taylor_remainder_tendstoInMeasure_of_consistency_bounded
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h73 : SystemDeltaAssumption73 r β R)
    (root : ℕ → ℝ) (βhat : ℕ → Ω → k → ℝ)
    (hβ : TendstoInMeasure μ βhat atTop (fun _ => β))
    (hTβ : BoundedInProbabilityNorm μ
      (fun n ω => root n • (βhat n ω - β))) :
    TendstoInMeasure μ
      (fun n ω => root n • systemDeltaTaylorRemainder r β R (βhat n ω))
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hβ ⊢
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  have hδ2 : 0 < δ / 2 := ENNReal.div_pos hδ.ne' ENNReal.ofNat_ne_top
  obtain ⟨M, hMpos, hMev⟩ := hTβ (δ / 2) hδ2
  let η : ℝ := ε / M
  have hηpos : 0 < η := div_pos hε hMpos
  have hnear :
      ∀ᶠ b in 𝓝 β,
        ‖systemDeltaTaylorRemainder r β R b‖ ≤ η * ‖b - β‖ :=
    (SystemDeltaAssumption73.taylorRemainder_isLittleO h73).def hηpos
  rcases Metric.mem_nhds_iff.1 hnear with ⟨ρ, hρpos, hρsub⟩
  have hβev := (hβ ρ hρpos).eventually_lt_const hδ2
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hMev.and hβev)
  refine ⟨N, fun n hnN => ?_⟩
  have hnM : μ {ω | M ≤ ‖root n • (βhat n ω - β)‖} ≤ δ / 2 := (hN n hnN).1
  have hnβ : μ {ω | ρ ≤ dist (βhat n ω) β} < δ / 2 := (hN n hnN).2
  have hnβ_le : μ {ω | ρ ≤ dist (βhat n ω) β} ≤ δ / 2 := le_of_lt hnβ
  have hcover :
      {ω | ε ≤ dist
        (root n • systemDeltaTaylorRemainder r β R (βhat n ω)) 0} ⊆
        {ω | M ≤ ‖root n • (βhat n ω - β)‖} ∪
          {ω | ρ ≤ dist (βhat n ω) β} := by
    intro ω hω
    by_cases hTbig : M ≤ ‖root n • (βhat n ω - β)‖
    · exact Or.inl hTbig
    right
    by_contra hβbig
    have hTsmall : ‖root n • (βhat n ω - β)‖ < M := not_le.mp hTbig
    have hβsmall : dist (βhat n ω) β < ρ := not_le.mp hβbig
    have hbmem : βhat n ω ∈ Metric.ball β ρ := by
      simpa [Metric.mem_ball, dist_comm] using hβsmall
    have hrem_bound :
        ‖systemDeltaTaylorRemainder r β R (βhat n ω)‖ ≤
          η * ‖βhat n ω - β‖ :=
      hρsub hbmem
    have hscaled_bound :
        ‖root n • systemDeltaTaylorRemainder r β R (βhat n ω)‖ ≤
          η * ‖root n • (βhat n ω - β)‖ := by
      calc
        ‖root n • systemDeltaTaylorRemainder r β R (βhat n ω)‖
            = ‖root n‖ * ‖systemDeltaTaylorRemainder r β R (βhat n ω)‖ :=
              norm_smul _ _
        _ ≤ ‖root n‖ * (η * ‖βhat n ω - β‖) :=
              mul_le_mul_of_nonneg_left hrem_bound (norm_nonneg _)
        _ = η * (‖root n‖ * ‖βhat n ω - β‖) := by ring
        _ = η * ‖root n • (βhat n ω - β)‖ := by rw [norm_smul]
    have hscaled_lt : ‖root n • systemDeltaTaylorRemainder r β R (βhat n ω)‖ < ε := by
      calc
        ‖root n • systemDeltaTaylorRemainder r β R (βhat n ω)‖
            ≤ η * ‖root n • (βhat n ω - β)‖ := hscaled_bound
        _ < η * M := mul_lt_mul_of_pos_left hTsmall hηpos
        _ = ε := div_mul_cancel₀ ε hMpos.ne'
    have hdist_lt :
        dist (root n • systemDeltaTaylorRemainder r β R (βhat n ω)) 0 < ε := by
      simpa [dist_eq_norm] using hscaled_lt
    exact (not_le_of_gt hdist_lt) hω
  calc
    μ {ω | ε ≤ dist
        (root n • systemDeltaTaylorRemainder r β R (βhat n ω)) 0}
        ≤ μ ({ω | M ≤ ‖root n • (βhat n ω - β)‖} ∪
          {ω | ρ ≤ dist (βhat n ω) β}) := measure_mono hcover
    _ ≤ μ {ω | M ≤ ‖root n • (βhat n ω - β)‖} +
          μ {ω | ρ ≤ dist (βhat n ω) β} := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hnM hnβ_le
    _ = δ := ENNReal.add_halves δ

/-- Stable nonlinear-delta linearization interface for Hansen Theorem 11.2.

`Tβ` is the scaled coefficient statistic and `Tθ` is the scaled statistic for a
smooth function of the coefficients. The expansion records the Assumption 7.3
Taylor remainder: `Tθ = Rᵀ Tβ + oₚ(1)`. -/
structure SystemDeltaLinearization
    (μ : Measure Ω)
    (Tθ : ℕ → Ω → q → ℝ) (R : Matrix k q ℝ) (Tβ : ℕ → Ω → k → ℝ) : Prop where
  scaled_measurable : ∀ n, AEMeasurable (Tθ n) μ
  expansion : TendstoInMeasure μ
    (Tθ - fun n ω => Rᵀ *ᵥ Tβ n ω) atTop (fun _ => 0)

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq q] [Fintype m] [DecidableEq m] in
/-- Constructor for the Chapter 11 nonlinear-delta interface from the scaled Taylor
remainder associated with `SystemDeltaAssumption73`. -/
theorem systemDeltaLinearization_of_scaled_taylor_remainder
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (_h73 : SystemDeltaAssumption73 r β R)
    (root : ℕ → ℝ) (βhat : ℕ → Ω → k → ℝ)
    (hscaled_meas : ∀ n,
      AEMeasurable (fun ω => root n • (r (βhat n ω) - r β)) μ)
    (hrem : TendstoInMeasure μ
      (fun n ω => root n • systemDeltaTaylorRemainder r β R (βhat n ω))
      atTop (fun _ => 0)) :
    SystemDeltaLinearization μ
      (fun n ω => root n • (r (βhat n ω) - r β)) R
      (fun n ω => root n • (βhat n ω - β)) where
  scaled_measurable := hscaled_meas
  expansion := by
    have heq :
        ((fun n ω => root n • (r (βhat n ω) - r β)) -
            fun n ω => Rᵀ *ᵥ (root n • (βhat n ω - β))) =
          fun n ω => root n • systemDeltaTaylorRemainder r β R (βhat n ω) := by
      funext n ω
      ext j
      simp [systemDeltaTaylorRemainder, sub_eq_add_neg, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_neg, smul_neg, smul_eq_mul]
      ring_nf
    simpa [heq] using hrem

/-- Hansen Theorem 11.2 at the stable nonlinear-delta interface.

Once a coefficient statistic has covariance `Vβ` and the smooth target has the
linearization `RᵀTβ + oₚ(1)`, the smooth target has covariance `RᵀVβR`. -/
theorem systemDelta_tendstoInDistribution_multivariateGaussian_of_linearization
    (Tθ : ℕ → Ω → q → ℝ) (R : Matrix k q ℝ) (Tβ : ℕ → Ω → k → ℝ)
    (Vβ : Matrix k k ℝ) (hVβ : Vβ.PosSemidef)
    (hTβ : TendstoInDistribution Tβ atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 Vβ))
    (hlinear : SystemDeltaLinearization μ Tθ R Tβ) :
    TendstoInDistribution Tθ atTop (fun z : EuclideanSpace ℝ q => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (systemDeltaVariance Vβ R)) := by
  let Tβe : ℕ → Ω → EuclideanSpace ℝ k := fun n ω => WithLp.toLp 2 (Tβ n ω)
  have hTβe :
      TendstoInDistribution Tβe atTop (fun z : EuclideanSpace ℝ k => z)
        (fun _ => μ) (multivariateGaussian 0 Vβ) := by
    have hmap := hTβ.continuous_comp (PiLp.continuous_toLp 2 (fun _ : k => ℝ))
    simpa [Tβe, Function.comp_def] using hmap
  have hlinE :
      TendstoInDistribution
        (fun n => matrixContinuousLinearMap Rᵀ ∘ Tβe n)
        atTop (matrixContinuousLinearMap Rᵀ ∘ fun z : EuclideanSpace ℝ k => z)
        (fun _ => μ) (multivariateGaussian 0 Vβ) :=
    hTβe.continuous_comp (matrixContinuousLinearMap Rᵀ).continuous
  have hLaw : HasLaw (fun z : EuclideanSpace ℝ k => matrixContinuousLinearMap Rᵀ z)
      (multivariateGaussian 0 (systemDeltaVariance Vβ R)) (multivariateGaussian 0 Vβ) := by
    simpa [systemDeltaVariance, matrixContinuousLinearMap,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      hasLaw_multivariateGaussian_zero_linearMap (n := k) (q := q) hVβ Rᵀ
  have htargetE :
      TendstoInDistribution
        (fun n ω => matrixContinuousLinearMap Rᵀ (Tβe n ω))
        atTop (fun z : EuclideanSpace ℝ q => z)
        (fun _ => μ) (multivariateGaussian 0 (systemDeltaVariance Vβ R)) := by
    simpa [Function.comp_def] using
      tendstoInDistribution_id_of_hasLaw_limit (E := EuclideanSpace ℝ q) hlinE hLaw
  have htarget := htargetE.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : q => ℝ))
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n ω => Rᵀ *ᵥ Tβ n ω) (Y := Tθ)
    (Z := fun z : EuclideanSpace ℝ q => z.ofLp)
    (by
      simpa [Tβe, Function.comp_def, matrixContinuousLinearMap_apply] using htarget)
    hlinear.expansion hlinear.scaled_measurable

/-- Hansen Theorem 11.2 from the Chapter 11 Gaussian-limit interface and a
stable nonlinear-delta linearization. -/
theorem systemDelta_tendstoInDistribution_multivariateGaussian_of_gaussianLimit
    (Tθ : ℕ → Ω → q → ℝ) (R : Matrix k q ℝ) (Tβ : ℕ → Ω → k → ℝ)
    (Vβ : Matrix k k ℝ)
    (hTβ : GaussianLimit μ Tβ Vβ)
    (hlinear : SystemDeltaLinearization μ Tθ R Tβ) :
    TendstoInDistribution Tθ atTop (fun z : EuclideanSpace ℝ q => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (systemDeltaVariance Vβ R)) :=
  systemDelta_tendstoInDistribution_multivariateGaussian_of_linearization
    Tθ R Tβ Vβ hTβ.covariance_posSemidef hTβ.limit hlinear

omit [DecidableEq m] in
/-- Hansen Theorem 11.2, concrete system least-squares Delta-method wrapper.

Combines the system LS CLT from Theorem 11.1, the derived consistency and
`Oₚ(1)` scaled coefficient error, and Assumption 7.3's Taylor remainder to
obtain the Gaussian limit for `√n (r(β̂ₙ) - r(β))`. -/
theorem systemDelta_systemLeastSquaresBetaStarObs_tendstoInDistribution
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ} {Q Omega : Matrix k k ℝ}
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h : SystemScoreCLTConditions μ X e Q Omega)
    (h73 : SystemDeltaAssumption73 r β R)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hmeasβ : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ)
    (hmeasθ : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (r (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) - r β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (r (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) - r β))
      atTop (fun z : EuclideanSpace ℝ q => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemDeltaVariance (systemAsymptoticVariance Q Omega) R)) := by
  let βhat : ℕ → Ω → k → ℝ := fun t ω =>
    systemLeastSquaresBetaStarObs
      (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)
  have hβclt : TendstoInDistribution
      (fun (t : ℕ) ω => Real.sqrt (t : ℝ) • (βhat t ω - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (systemAsymptoticVariance Q Omega)) := by
    simpa [βhat] using
      systemLeastSquaresBetaStarObs_tendstoInDistribution
        (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel hmeasβ
  have hβbounded : BoundedInProbabilityNorm μ
      (fun (t : ℕ) ω => Real.sqrt (t : ℝ) • (βhat t ω - β)) := by
    simpa [βhat] using
      systemLeastSquaresBetaStarObs_sqrt_sub_boundedInProbabilityNorm
        (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel hmeasβ
  have hβcons : TendstoInMeasure μ βhat atTop (fun _ => β) := by
    simpa [βhat] using
      systemLeastSquaresBetaStarObs_tendstoInMeasure_beta
        (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel hmeasβ
  have hrem : TendstoInMeasure μ
      (fun (t : ℕ) (ω : Ω) => Real.sqrt (t : ℝ) •
        systemDeltaTaylorRemainder r β R (βhat t ω))
      atTop (fun _ => (0 : q → ℝ)) :=
    systemDelta_scaled_taylor_remainder_tendstoInMeasure_of_consistency_bounded
      (μ := μ) h73 (fun t : ℕ => Real.sqrt (t : ℝ)) βhat hβcons hβbounded
  have hlinear : SystemDeltaLinearization μ
      (fun t ω => Real.sqrt (t : ℝ) • (r (βhat t ω) - r β)) R
      (fun t ω => Real.sqrt (t : ℝ) • (βhat t ω - β)) :=
    systemDeltaLinearization_of_scaled_taylor_remainder
      (μ := μ) h73 (fun t : ℕ => Real.sqrt (t : ℝ)) βhat
      (by simpa [βhat] using hmeasθ) hrem
  have hV : (systemAsymptoticVariance Q Omega).PosSemidef :=
    systemAsymptoticVariance_posSemidef h.score_cov_posSemidef h.gram_inv_transpose
  exact systemDelta_tendstoInDistribution_multivariateGaussian_of_linearization
    (μ := μ)
    (Tθ := fun t ω => Real.sqrt (t : ℝ) • (r (βhat t ω) - r β))
    (R := R)
    (Tβ := fun t ω => Real.sqrt (t : ℝ) • (βhat t ω - β))
    (Vβ := systemAsymptoticVariance Q Omega)
    hV hβclt hlinear

omit [DecidableEq k] in
/-- Interface projection for delta-method asymptotic normality of smooth
functions of multiple-equation coefficients. -/
theorem systemDelta_gaussianLimit_from_interface
    (Tθ : ℕ → Ω → q → ℝ) (Vβ : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hTθ : GaussianLimit μ Tθ (systemDeltaVariance Vβ R)) :
    GaussianLimit μ Tθ (systemDeltaVariance Vβ R) :=
  hTθ

omit [DecidableEq k] in
/-- Distributional face of `systemDelta_gaussianLimit_from_interface`. -/
theorem systemDelta_tendstoInDistribution_from_interface
    (Tθ : ℕ → Ω → q → ℝ) (Vβ : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hTθ : GaussianLimit μ Tθ (systemDeltaVariance Vβ R)) :
    TendstoInDistribution Tθ atTop (fun z : EuclideanSpace ℝ q => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 (systemDeltaVariance Vβ R)) :=
  hTθ.limit

omit [IsProbabilityMeasure μ] [DecidableEq k] in
/-- Interface projection for a pair of system least-squares covariance
consistency statements. -/
theorem systemCovariance_consistent_from_interfaces
    (Vhat Vhat0 : ℕ → Ω → Matrix k k ℝ) (Vβ Vβ0 : Matrix k k ℝ)
    (hV : CovarianceEstimatorConsistent μ Vhat Vβ)
    (hV0 : CovarianceEstimatorConsistent μ Vhat0 Vβ0) :
    CovarianceEstimatorConsistent μ Vhat Vβ ∧
      CovarianceEstimatorConsistent μ Vhat0 Vβ0 :=
  ⟨hV, hV0⟩

omit [DecidableEq k] [DecidableEq m] in
/-- **System moment WLLN for Hansen Chapter 11.**

The normalized system Gram matrix `n⁻¹∑ Xᵢ'Xᵢ` converges to its population
counterpart under the Banach-valued WLLN hypotheses. -/
theorem systemNormalizedGram_tendstoInMeasure
    {X : ℕ → Ω → Matrix m k ℝ}
    (hint : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => (X i ω)ᵀ * X i ω)))
    (hident : ∀ i,
      IdentDistrib (fun ω => (X i ω)ᵀ * X i ω)
        (fun ω => (X 0 ω)ᵀ * X 0 ω) μ μ) :
    TendstoInMeasure μ
      (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
      atTop (fun _ => μ[fun ω => (X 0 ω)ᵀ * X 0 ω]) := by
  have h :
      TendstoInMeasure μ
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, (X i ω)ᵀ * X i ω))
        atTop (fun _ => μ[fun ω => (X 0 ω)ᵀ * X 0 ω]) :=
    tendstoInMeasure_wlln
      (μ := μ) (fun i ω => (X i ω)ᵀ * X i ω) hint hindep hident
  have hfun_eq :
      (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω)) =
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, (X i ω)ᵀ * X i ω)) := by
    funext n ω
    have hsum :
        (∑ i : Fin n, (X i.val ω)ᵀ * X i.val ω) =
          ∑ i ∈ Finset.range n, (X i ω)ᵀ * X i ω :=
      Fin.sum_univ_eq_sum_range (fun i => (X i ω)ᵀ * X i ω) n
    simp only [systemNormalizedGram, Fintype.card_fin]
    rw [hsum]
  rw [hfun_eq]
  exact h

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq m] in
/-- Measurability of the normalized system Gram under the corresponding
identical-distribution moment hypotheses. -/
theorem systemNormalizedGram_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ}
    (hint : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hident : ∀ i,
      IdentDistrib (fun ω => (X i ω)ᵀ * X i ω)
        (fun ω => (X 0 ω)ᵀ * X 0 ω) μ μ) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω => systemNormalizedGram (fun i : Fin n => X i.val ω)) μ := by
  simp only [systemNormalizedGram]
  refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card (Fin n) : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact ((hident i.val).integrable_iff.mpr hint).aestronglyMeasurable

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Measurability of the normalized system score mean under Assumption 7.2. -/
theorem systemScoreMean_aestronglyMeasurable_of_assumption72
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72 μ X e) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω => systemScoreMean (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω))
      μ := by
  simp only [systemScoreMean]
  refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card (Fin n) : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact ((h.score_identDistrib i.val).memLp_iff.mpr h.score_memLp).aestronglyMeasurable

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Measurability of Hansen's observation-level system LS estimator under
Assumption 7.2 and the system linear model.

The proof rewrites `β̂ₙ` as `Q̂ₙ⁻¹ (Q̂ₙβ + ĝₙ)` and reuses the Gram/score
measurability fields derived from Assumption 7.2. -/
theorem systemLeastSquaresBetaStarObs_aestronglyMeasurable_of_assumption72
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        systemLeastSquaresBetaStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω)) μ := by
  have hGram : AEStronglyMeasurable
      (fun ω => systemNormalizedGram (fun i : Fin n => X i.val ω)) μ :=
    systemNormalizedGram_aestronglyMeasurable
      (μ := μ) (X := X) h.gram_integrable h.gram_identDistrib n
  have hScore : AEStronglyMeasurable
      (fun ω => systemScoreMean (fun i : Fin n => X i.val ω)
        (fun i : Fin n => e i.val ω)) μ :=
    systemScoreMean_aestronglyMeasurable_of_assumption72
      (μ := μ) (X := X) (e := e) h n
  have hInv : AEStronglyMeasurable
      (fun ω => (systemNormalizedGram (fun i : Fin n => X i.val ω))⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hGram
  have hGramBeta : AEStronglyMeasurable
      (fun ω => systemNormalizedGram (fun i : Fin n => X i.val ω) *ᵥ β) μ :=
    (Continuous.matrix_mulVec continuous_id continuous_const).comp_aestronglyMeasurable hGram
  have hMiddle : AEStronglyMeasurable
      (fun ω =>
        systemNormalizedGram (fun i : Fin n => X i.val ω) *ᵥ β +
          systemScoreMean (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω)) μ :=
    hGramBeta.add hScore
  have hRhs : AEStronglyMeasurable
      (fun ω =>
        (systemNormalizedGram (fun i : Fin n => X i.val ω))⁻¹ *ᵥ
          (systemNormalizedGram (fun i : Fin n => X i.val ω) *ᵥ β +
            systemScoreMean (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω))) μ := by
    exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hInv.prodMk hMiddle)
  refine hRhs.congr (ae_of_all μ (fun ω => ?_))
  let Xt : Fin n → Matrix m k ℝ := fun i => X i.val ω
  let et : Fin n → m → ℝ := fun i => e i.val ω
  let Yt : Fin n → m → ℝ := fun i => Y i.val ω
  change
    (systemNormalizedGram Xt)⁻¹ *ᵥ
      (systemNormalizedGram Xt *ᵥ β + systemScoreMean Xt et) =
        systemLeastSquaresBetaStarObs Xt Yt
  rw [← systemScoreMean_outcomes_linear_model Xt et Yt β
    (by intro i j; exact hmodel i.val ω j),
    ← systemLeastSquaresBetaStarObs_eq_normalized_moments Xt Yt]

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Finite-sample measurability of the observation-level system residual row,
derived from measurability of the observations and the Star coefficient
estimator. -/
theorem systemResidualStarObs_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (n : ℕ) (i : Fin n) :
    AEStronglyMeasurable
      (fun ω => systemResidualStarObs
        (fun r : Fin n => X r.val ω) (fun r : Fin n => Y r.val ω) i) μ := by
  have hBeta : AEStronglyMeasurable
      (fun ω => systemLeastSquaresBetaStarObs
        (fun r : Fin n => X r.val ω) (fun r : Fin n => Y r.val ω)) μ := by
    have hGram : AEStronglyMeasurable
        (fun ω => systemNormalizedGram (fun r : Fin n => X r.val ω)) μ := by
      simp only [systemNormalizedGram]
      refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card (Fin n) : ℝ)⁻¹)
      refine Finset.aestronglyMeasurable_fun_sum _ (fun r _ => ?_)
      have hXi := hX r.val
      have hXiT := (continuous_id.matrix_transpose).comp_aestronglyMeasurable hXi
      exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hXiT.prodMk hXi)
    have hScore : AEStronglyMeasurable
        (fun ω => systemScoreMean
          (fun r : Fin n => X r.val ω) (fun r : Fin n => Y r.val ω)) μ := by
      simp only [systemScoreMean, systemScore]
      refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card (Fin n) : ℝ)⁻¹)
      refine Finset.aestronglyMeasurable_fun_sum _ (fun r _ => ?_)
      have hXiT := (continuous_id.matrix_transpose).comp_aestronglyMeasurable (hX r.val)
      exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hXiT.prodMk (hY r.val))
    have hInv := aestronglyMeasurable_matrix_inv hGram
    have hMul := (Continuous.matrix_mulVec continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable (hInv.prodMk hScore)
    simpa only [systemLeastSquaresBetaStarObs_eq_normalized_moments] using hMul
  rw [aestronglyMeasurable_iff_aemeasurable, aemeasurable_pi_iff]
  intro a
  have hYia : AEStronglyMeasurable (fun ω => Y i.val ω a) μ :=
    (continuous_apply a).comp_aestronglyMeasurable (hY i.val)
  have hXia : AEStronglyMeasurable (fun ω => X i.val ω a) μ :=
    (continuous_apply a).comp_aestronglyMeasurable (hX i.val)
  have hfit : AEStronglyMeasurable
      (fun ω => X i.val ω a ⬝ᵥ systemLeastSquaresBetaStarObs
        (fun r : Fin n => X r.val ω) (fun r : Fin n => Y r.val ω)) μ :=
    (Continuous.dotProduct continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXia.prodMk hBeta)
  exact ((hYia.sub hfit).congr (ae_of_all μ fun ω => by
    rw [systemResidualStarObs_apply]
    rfl)).aemeasurable

omit [IsProbabilityMeasure μ] [Fintype k] [Fintype q] [DecidableEq k]
  [DecidableEq q] [DecidableEq m] in
private theorem systemRobustMiddleTerm_aestronglyMeasurable_of_pair
    {X : Ω → Matrix m k ℝ} {e : Ω → m → ℝ}
    (hX : AEStronglyMeasurable X μ) (he : AEStronglyMeasurable e μ) :
    AEStronglyMeasurable (fun ω => systemRobustMiddleTerm (X ω) (e ω)) μ := by
  have hXt : AEStronglyMeasurable (fun ω => (X ω)ᵀ) μ :=
    continuous_id.matrix_transpose.comp_aestronglyMeasurable hX
  have hScore : AEStronglyMeasurable (fun ω => systemScore (X ω) (e ω)) μ := by
    simpa only [systemScore] using
      (Continuous.matrix_mulVec continuous_fst continuous_snd)
        |>.comp_aestronglyMeasurable (hXt.prodMk he)
  have hOuter : AEStronglyMeasurable
      (fun ω => Matrix.vecMulVec (systemScore (X ω) (e ω))
        (systemScore (X ω) (e ω))) μ :=
    (Continuous.matrix_vecMulVec continuous_id continuous_id)
      |>.comp_aestronglyMeasurable hScore
  exact hOuter.congr (ae_of_all μ fun ω =>
    (systemRobustMiddleTerm_eq_vecMulVec_score (X ω) (e ω)).symm)

omit [IsProbabilityMeasure μ] [Fintype m] [Fintype q] [DecidableEq k]
  [DecidableEq q] [DecidableEq m] in
/-- A finite residual covariance is measurable when each residual row is
measurable. -/
theorem systemSigmaHat_aestronglyMeasurable_of_rows
    {r : Type*} [Fintype r]
    {ehat : r → Ω → m → ℝ}
    (hehat : ∀ i, AEStronglyMeasurable (ehat i) μ) :
    AEStronglyMeasurable (fun ω => systemSigmaHat (fun i => ehat i ω)) μ := by
  classical
  simp only [systemSigmaHat]
  refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card r : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ => ?_)
  exact (Continuous.matrix_vecMulVec continuous_id continuous_id)
    |>.comp_aestronglyMeasurable (hehat i)

omit [IsProbabilityMeasure μ] [Fintype k] [Fintype q] [DecidableEq k]
  [DecidableEq q] [DecidableEq m] in
/-- A finite homoskedastic middle matrix is measurable when each design row
and the estimated covariance are measurable. -/
theorem systemHomoskedasticMiddle_aestronglyMeasurable_of_rows
    {r : Type*} [Fintype r]
    {X : r → Ω → Matrix m k ℝ} {SigmaHat : Ω → Matrix m m ℝ}
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hSigma : AEStronglyMeasurable SigmaHat μ) :
    AEStronglyMeasurable
      (fun ω => systemHomoskedasticMiddle (fun i => X i ω) (SigmaHat ω)) μ := by
  classical
  simp only [systemHomoskedasticMiddle]
  refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card r : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ => ?_)
  have hXi := hX i
  have hXiT := (continuous_id.matrix_transpose).comp_aestronglyMeasurable hXi
  have hLeft := (Continuous.matrix_mul continuous_fst continuous_snd)
    |>.comp_aestronglyMeasurable (hXiT.prodMk hSigma)
  simpa only [systemMiddleTerm, Matrix.mul_assoc] using
    (Continuous.matrix_mul continuous_fst continuous_snd)
      |>.comp_aestronglyMeasurable (hLeft.prodMk hXi)

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Scaled system-estimator measurability needed by Hansen Theorem 11.1,
derived from Assumption 7.2 instead of left as a theorem premise. -/
theorem systemLeastSquaresBetaStarObs_scaled_aemeasurable_of_assumption72
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) (n : ℕ) :
    AEMeasurable
      (fun ω =>
        Real.sqrt (n : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) - β)) μ := by
  exact ((systemLeastSquaresBetaStarObs_aestronglyMeasurable_of_assumption72
      (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel n).sub
      aestronglyMeasurable_const).const_smul (Real.sqrt (n : ℝ)) |>.aemeasurable

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Scaled OrZero system-estimator measurability, transported through the
Star/OrZero bridge. -/
theorem systemLeastSquaresBetaOrZeroObs_scaled_aemeasurable_of_assumption72
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) (n : ℕ) :
    AEMeasurable
      (fun ω =>
        Real.sqrt (n : ℝ) •
          (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) - β)) μ := by
  convert systemLeastSquaresBetaStarObs_scaled_aemeasurable_of_assumption72
    (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel n using 1
  ext ω
  rw [systemLeastSquaresBetaOrZeroObs_eq_star]

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Transformed-target measurability for Hansen Theorem 11.2 when the
smooth transform is explicitly measurable. -/
theorem systemDelta_systemLeastSquaresBetaStarObs_scaled_aemeasurable_of_assumption72
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ}
    (h : SystemAssumption72 μ X e) (hr : Measurable r)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) (n : ℕ) :
    AEMeasurable
      (fun ω =>
        Real.sqrt (n : ℝ) •
          (r (systemLeastSquaresBetaStarObs
            (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω)) - r β)) μ := by
  have hβhat : AEStronglyMeasurable
      (fun ω =>
        systemLeastSquaresBetaStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω)) μ :=
    systemLeastSquaresBetaStarObs_aestronglyMeasurable_of_assumption72
      (μ := μ) (X := X) (e := e) (Y := Y) h β hmodel n
  exact ((hr.comp_aemeasurable hβhat.aemeasurable).sub aemeasurable_const).const_smul
    (Real.sqrt (n : ℝ))

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- OrZero transformed-target measurability for Hansen Theorem 11.2, transported
through the Star/OrZero bridge. -/
theorem systemDelta_systemLeastSquaresBetaOrZeroObs_scaled_aemeasurable_of_assumption72
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ}
    (h : SystemAssumption72 μ X e) (hr : Measurable r)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) (n : ℕ) :
    AEMeasurable
      (fun ω =>
        Real.sqrt (n : ℝ) •
          (r (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω)) - r β)) μ := by
  convert systemDelta_systemLeastSquaresBetaStarObs_scaled_aemeasurable_of_assumption72
    (μ := μ) (X := X) (e := e) (Y := Y) (r := r) (β := β) h hr hmodel n using 1
  ext ω
  rw [systemLeastSquaresBetaOrZeroObs_eq_star]

namespace SystemAssumption72

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- A Chapter 11 Assumption 7.2 package supplies the lower-level
`SystemScoreCLTConditions` consumed by the existing system-LS proof engine. -/
theorem toSystemScoreCLTConditions
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72 μ X e) :
    SystemScoreCLTConditions μ X e
      (systemPopulationGram μ X) (systemPopulationScoreCovariance μ X e) where
  gram_meas :=
    fun n => systemNormalizedGram_aestronglyMeasurable
      (μ := μ) (X := X) h.gram_integrable h.gram_identDistrib n
  gram_tendsto := by
    simpa [systemPopulationGram] using
      systemNormalizedGram_tendstoInMeasure
        (μ := μ) (X := X) h.gram_integrable h.gram_independent h.gram_identDistrib
  gram_nonsing := h.gram_nonsing
  gram_inv_transpose :=
    systemPopulationGram_inv_transpose (μ := μ) (X := X) h.gram_integrable
  score_limit := by
    let Yscore : ℕ → Ω → k → ℝ := fun i ω => systemScore (X i ω) (e i ω)
    have hcltE :
        TendstoInDistribution
          (fun (n : ℕ) ω =>
            WithLp.toLp 2
              ((Real.sqrt (n : ℝ))⁻¹ •
                (∑ i ∈ Finset.range n, Yscore i ω -
                  (n : ℝ) • meanVec μ (Yscore 0))))
          atTop (fun z : EuclideanSpace ℝ k => z) (fun _ => μ)
          (multivariateGaussian 0 (covMat μ (Yscore 0))) :=
      iidVectorCLT_tendstoInDistribution_multivariateGaussian
        (μ := μ) (Y := Yscore) h.score_memLp h.score_iIndep h.score_identDistrib
    have hraw :
        TendstoInDistribution
          (fun (n : ℕ) ω =>
            (Real.sqrt (n : ℝ))⁻¹ •
              (∑ i ∈ Finset.range n, Yscore i ω -
                (n : ℝ) • meanVec μ (Yscore 0)))
          atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
          (multivariateGaussian 0 (covMat μ (Yscore 0))) := by
      have hmap := hcltE.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : k => ℝ))
      simpa [Yscore, Function.comp_def] using hmap
    have hscore :
        TendstoInDistribution
          (fun (n : ℕ) ω =>
            Real.sqrt (n : ℝ) •
              systemScoreMean (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω))
          atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
          (multivariateGaussian 0 (covMat μ (Yscore 0))) := by
      refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hraw
      intro n
      exact ae_of_all μ (fun ω => by
        simpa [Yscore] using
          (sqrt_smul_systemScoreMean_eq_inv_sqrt_sum
            (μ := μ) (X := X) (e := e) h.score_mean_zero n ω).symm)
    simpa [Yscore,
      systemScore_covMat_eq_populationScoreCovariance
        (μ := μ) (X := X) (e := e) h.score_memLp h.score_mean_zero] using hscore
  score_cov_posSemidef := by
    simpa [
      systemScore_covMat_eq_populationScoreCovariance
        (μ := μ) (X := X) (e := e) h.score_memLp h.score_mean_zero] using
      covMat_posSemidef (μ := μ) (Y := fun ω => systemScore (X 0 ω) (e 0 ω))
        h.score_memLp

omit [DecidableEq m] in
/-- Assumption 7.2's square-integrable system score makes the true-error robust
middle integrable because `Xᵢ'eᵢeᵢ'Xᵢ` is the score outer product. -/
theorem robustMiddleTerm_integrable
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72 μ X e) :
    Integrable (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ := by
  classical
  have houter :
      Integrable
        (fun ω =>
          Matrix.vecMulVec (systemScore (X 0 ω) (e 0 ω))
            (systemScore (X 0 ω) (e 0 ω))) μ := by
    refine Integrable.of_eval ?_
    intro a
    refine Integrable.of_eval ?_
    intro b
    simpa [Matrix.vecMulVec_apply] using
      (h.score_memLp.eval a).integrable_mul (h.score_memLp.eval b)
  simpa [systemRobustMiddleTerm_eq_vecMulVec_score] using houter

omit [DecidableEq m] in
/-- Assumption 7.2's independent score sequence induces independence of the
true-error robust middle sequence. -/
theorem robustMiddleTerm_independent
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72 μ X e) :
    Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemRobustMiddleTerm (X i ω) (e i ω))) := by
  classical
  have hout : iIndepFun
      (fun i ω =>
        Matrix.vecMulVec (systemScore (X i ω) (e i ω))
          (systemScore (X i ω) (e i ω))) μ := by
    simpa [Function.comp] using
      h.score_iIndep.comp (fun _ z => Matrix.vecMulVec z z)
        (fun _ => measurable_vecMulVec_self (k := k))
  intro i j hij
  simpa [systemRobustMiddleTerm_eq_vecMulVec_score] using hout.indepFun hij

omit [DecidableEq m] in
/-- Assumption 7.2's identically distributed score sequence induces identical
distribution of the true-error robust middle sequence. -/
theorem robustMiddleTerm_identDistrib
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72 μ X e) (i : ℕ) :
    IdentDistrib (fun ω => systemRobustMiddleTerm (X i ω) (e i ω))
      (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ μ := by
  classical
  have hi := (h.score_identDistrib i).comp (measurable_vecMulVec_self (k := k))
  simpa [Function.comp, systemRobustMiddleTerm_eq_vecMulVec_score] using hi

omit [DecidableEq m] in
/-- Assumption 7.2 supplies the true-error robust middle WLLN used by Hansen
Theorem 11.3. The remaining robust feasible step is only residual substitution. -/
theorem robustMiddle_ideal_tendstoInMeasure
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72 μ X e) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω))
      atTop (fun _ => systemPopulationScoreCovariance μ X e) := by
  have hraw :
      TendstoInMeasure μ
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
          (∑ i ∈ Finset.range n, systemRobustMiddleTerm (X i ω) (e i ω)))
        atTop (fun _ => μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)]) :=
    tendstoInMeasure_wlln
      (μ := μ) (fun i ω => systemRobustMiddleTerm (X i ω) (e i ω))
      (robustMiddleTerm_integrable (μ := μ) h)
      (robustMiddleTerm_independent (μ := μ) h)
      (robustMiddleTerm_identDistrib (μ := μ) h)
  have hfun_eq :
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω)) =
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
          (∑ i ∈ Finset.range n, systemRobustMiddleTerm (X i ω) (e i ω))) := by
    funext n ω
    have hsum :
        (∑ i : Fin n, systemRobustMiddleTerm (X i.val ω) (e i.val ω)) =
          ∑ i ∈ Finset.range n, systemRobustMiddleTerm (X i ω) (e i ω) :=
      Fin.sum_univ_eq_sum_range
        (fun i => systemRobustMiddleTerm (X i ω) (e i ω)) n
    simp only [systemRobustMiddle, Fintype.card_fin]
    rw [hsum]
  rw [hfun_eq]
  simpa [systemPopulationScoreCovariance] using hraw

omit [DecidableEq m] in
/-- Measurability of the true-error robust middle follows from the
`SystemAssumption72` score-outer integrability and identical-distribution
projections. -/
theorem robustMiddle_ideal_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (h : SystemAssumption72 μ X e) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω)) μ :=
by
  simp only [systemRobustMiddle]
  refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card (Fin n) : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact ((robustMiddleTerm_identDistrib (μ := μ) h i.val).integrable_iff.mpr
    (robustMiddleTerm_integrable (μ := μ) h)).aestronglyMeasurable

end SystemAssumption72

/-- The theorem-facing residual/covariance inputs for Hansen Theorem 11.3.

`SystemAssumption72` supplies the system Gram WLLN and nonsingularity.  The two
remaining fields are exactly the feasible-residual middle convergence premises
needed for the displayed robust and homoskedastic covariance estimators.  They
are kept explicit here so the public theorem does not pretend to derive the
residual perturbation bounds from Assumption 7.2 before those bounds exist. -/
structure SystemCovarianceTheorem113Conditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Matrix m k ℝ) (e : ℕ → Ω → m → ℝ)
    (Y : ℕ → Ω → m → ℝ) (Omega0 : Matrix k k ℝ) : Prop where
  assumption72 : SystemAssumption72 μ X e
  robust_middle_measurable : ∀ n,
    AEStronglyMeasurable
      (fun ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω)
          (systemResidualStarObs (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))) μ
  robust_middle_consistent : TendstoInMeasure μ
    (fun n ω =>
      systemRobustMiddle (fun i : Fin n => X i.val ω)
        (systemResidualStarObs (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω)))
    atTop (fun _ => systemPopulationScoreCovariance μ X e)
  homoskedastic_middle_measurable : ∀ n,
    AEStronglyMeasurable
      (fun ω =>
        systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
          (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))) μ
  homoskedastic_middle_consistent : TendstoInMeasure μ
    (fun n ω =>
      systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
        (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω)))
    atTop (fun _ => Omega0)

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Hansen Theorem 11.1 from the Chapter 11 observation-level Assumption 7.2
package. This theorem derives the score CLT and Gram WLLN from the primitive
system package, then reuses the existing high-probability Star-estimator
linearization. -/
theorem systemLeastSquaresBetaStarObs_tendstoInDistribution_of_assumption72
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    (h72 : SystemAssumption72 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemAsymptoticVariance
          (systemPopulationGram μ X) (systemPopulationScoreCovariance μ X e))) :=
  systemLeastSquaresBetaStarObs_tendstoInDistribution
    (μ := μ) (X := X) (e := e) (Y := Y)
    h72.toSystemScoreCLTConditions β hmodel hmeas

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Textbook-facing OrZero version of Hansen Theorem 11.1.

The proof is a pointwise transport across
`systemLeastSquaresBetaOrZeroObs_eq_star`, so the public endpoint reuses the
Star proof engine without duplicating the CLT argument. -/
theorem systemLeastSquaresBetaOrZeroObs_tendstoInDistribution_of_assumption72
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    (h72 : SystemAssumption72 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hmeas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemAsymptoticVariance
          (systemPopulationGram μ X) (systemPopulationScoreCovariance μ X e))) := by
  simpa [systemLeastSquaresBetaOrZeroObs_eq_star] using
    systemLeastSquaresBetaStarObs_tendstoInDistribution_of_assumption72
      (μ := μ) (X := X) (e := e) (Y := Y) h72 β hmodel
      (fun t => by
        convert hmeas t using 1
        ext ω
        rw [systemLeastSquaresBetaOrZeroObs_eq_star])

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Hansen Theorem 11.1 with the scaled-estimator measurability discharged
from `SystemAssumption72`. -/
theorem systemLeastSquaresBetaStarObs_tendstoInDistribution_of_assumption72_auto_measurable
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    (h72 : SystemAssumption72 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemAsymptoticVariance
          (systemPopulationGram μ X) (systemPopulationScoreCovariance μ X e))) :=
  systemLeastSquaresBetaStarObs_tendstoInDistribution_of_assumption72
    (μ := μ) (X := X) (e := e) (Y := Y) h72 β hmodel
    (fun t =>
      systemLeastSquaresBetaStarObs_scaled_aemeasurable_of_assumption72
        (μ := μ) (X := X) (e := e) (Y := Y) h72 β hmodel t)

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Textbook-facing OrZero Hansen Theorem 11.1 with estimator measurability
derived from `SystemAssumption72`. -/
theorem systemLeastSquaresBetaOrZeroObs_tendstoInDistribution_of_assumption72_auto_measurable
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    (h72 : SystemAssumption72 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemAsymptoticVariance
          (systemPopulationGram μ X) (systemPopulationScoreCovariance μ X e))) :=
  systemLeastSquaresBetaOrZeroObs_tendstoInDistribution_of_assumption72
    (μ := μ) (X := X) (e := e) (Y := Y) h72 β hmodel
    (fun t =>
      systemLeastSquaresBetaOrZeroObs_scaled_aemeasurable_of_assumption72
        (μ := μ) (X := X) (e := e) (Y := Y) h72 β hmodel t)

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Hansen Theorem 11.1 from the literal row-iid Assumption 7.2 surface. -/
theorem systemLeastSquaresBetaOrZeroObs_tendstoInDistribution_of_primitive_row_assumption72
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    (h72 : SystemAssumption72PrimitiveRow μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemAsymptoticVariance
          (systemPopulationGram μ X) (systemPopulationScoreCovariance μ X e))) :=
  systemLeastSquaresBetaOrZeroObs_tendstoInDistribution_of_assumption72_auto_measurable
    (μ := μ) (X := X) (e := e) (Y := Y)
    h72.toSystemAssumption72 β hmodel

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- **Hansen Theorem 11.1** from literal observed-row Assumption 7.2.

The residual-row iid, Gram WLLN, score CLT, and population nonsingularity
inputs are derived from observed `(Xᵢ,Yᵢ)` iid rows, Hansen's fourth moments,
orthogonality, and positive definiteness of `Q`. -/
theorem systemLeastSquaresBetaOrZeroObs_tendstoInDistribution_of_observed_assumption72
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h72 : SystemAssumption72ObservedResponseFourthConditions μ X e Y β) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemAsymptoticVariance
          (systemPopulationGram μ X) (systemPopulationScoreCovariance μ X e))) :=
  systemLeastSquaresBetaOrZeroObs_tendstoInDistribution_of_primitive_row_assumption72
    (μ := μ) (X := X) (e := e) (Y := Y)
    h72.toSystemAssumption72PrimitiveRow β h72.model

omit [DecidableEq m] in
/-- Hansen Theorem 11.2 from the Chapter 11 observation-level Assumption 7.2
package and the deterministic Assumption 7.3 smoothness package. -/
theorem systemDelta_systemLeastSquaresBetaStarObs_tendstoInDistribution_of_assumptions72_73
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h72 : SystemAssumption72 μ X e)
    (h73 : SystemDeltaAssumption73 r β R)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hmeasβ : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ)
    (hmeasθ : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (r (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) - r β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (r (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) - r β))
      atTop (fun z : EuclideanSpace ℝ q => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemDeltaVariance
          (systemAsymptoticVariance
            (systemPopulationGram μ X) (systemPopulationScoreCovariance μ X e)) R)) :=
  systemDelta_systemLeastSquaresBetaStarObs_tendstoInDistribution
    (μ := μ) (X := X) (e := e) (Y := Y)
    h72.toSystemScoreCLTConditions h73 hmodel hmeasβ hmeasθ

omit [DecidableEq m] in
/-- Textbook-facing OrZero version of Hansen Theorem 11.2.

This transports the Star delta-method endpoint across the pointwise OrZero/Star
bridge for system least squares. -/
theorem systemDelta_systemLeastSquaresBetaOrZeroObs_tendstoInDistribution_of_assumptions72_73
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h72 : SystemAssumption72 μ X e)
    (h73 : SystemDeltaAssumption73 r β R)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hmeasβ : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ)
    (hmeasθ : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (r (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) - r β)) μ) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (r (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) - r β))
      atTop (fun z : EuclideanSpace ℝ q => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemDeltaVariance
          (systemAsymptoticVariance
            (systemPopulationGram μ X) (systemPopulationScoreCovariance μ X e)) R)) := by
  simpa [systemLeastSquaresBetaOrZeroObs_eq_star] using
    systemDelta_systemLeastSquaresBetaStarObs_tendstoInDistribution_of_assumptions72_73
      (μ := μ) (X := X) (e := e) (Y := Y) h72 h73 hmodel
      (fun t => by
        convert hmeasβ t using 1
        ext ω
        rw [systemLeastSquaresBetaOrZeroObs_eq_star])
      (fun t => by
        convert hmeasθ t using 1
        ext ω
        rw [systemLeastSquaresBetaOrZeroObs_eq_star])

omit [DecidableEq m] in
/-- Hansen Theorem 11.2 with both scaled coefficient and transformed-target
measurability discharged from `SystemAssumption72` and a measurable
Assumption 7.3 package. -/
theorem systemDelta_betaStarObs_tendstoInDistribution_of_assumptions72_73_measurable
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h72 : SystemAssumption72 μ X e)
    (h73 : SystemDeltaAssumption73Measurable r β R)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (r (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) - r β))
      atTop (fun z : EuclideanSpace ℝ q => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemDeltaVariance
          (systemAsymptoticVariance
            (systemPopulationGram μ X) (systemPopulationScoreCovariance μ X e)) R)) :=
  systemDelta_systemLeastSquaresBetaStarObs_tendstoInDistribution_of_assumptions72_73
    (μ := μ) (X := X) (e := e) (Y := Y)
    h72 h73.toSystemDeltaAssumption73 hmodel
    (fun t =>
      systemLeastSquaresBetaStarObs_scaled_aemeasurable_of_assumption72
        (μ := μ) (X := X) (e := e) (Y := Y) h72 β hmodel t)
    (fun t =>
      systemDelta_systemLeastSquaresBetaStarObs_scaled_aemeasurable_of_assumption72
        (μ := μ) (X := X) (e := e) (Y := Y) (r := r) (β := β)
        h72 h73.measurable hmodel t)

omit [DecidableEq m] in
/-- Textbook-facing OrZero Hansen Theorem 11.2 with measurability discharged
from the primitive theorem packages. -/
theorem systemDelta_betaOrZeroObs_tendstoInDistribution_of_assumptions72_73_measurable
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h72 : SystemAssumption72 μ X e)
    (h73 : SystemDeltaAssumption73Measurable r β R)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (r (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) - r β))
      atTop (fun z : EuclideanSpace ℝ q => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemDeltaVariance
          (systemAsymptoticVariance
            (systemPopulationGram μ X) (systemPopulationScoreCovariance μ X e)) R)) := by
  simpa [systemLeastSquaresBetaOrZeroObs_eq_star] using
    systemDelta_betaStarObs_tendstoInDistribution_of_assumptions72_73_measurable
      (μ := μ) (X := X) (e := e) (Y := Y)
      h72 h73 hmodel

omit [DecidableEq m] in
/-- Hansen Theorem 11.2 from the literal row-iid Assumption 7.2 surface and
the measurable Assumption 7.3 surface. -/
theorem systemDelta_betaOrZeroObs_tendstoInDistribution_of_primitive_row_assumptions72_73
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h72 : SystemAssumption72PrimitiveRow μ X e)
    (h73 : SystemDeltaAssumption73Measurable r β R)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (r (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) - r β))
      atTop (fun z : EuclideanSpace ℝ q => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemDeltaVariance
          (systemAsymptoticVariance
            (systemPopulationGram μ X) (systemPopulationScoreCovariance μ X e)) R)) :=
  systemDelta_betaOrZeroObs_tendstoInDistribution_of_assumptions72_73_measurable
    (μ := μ) (X := X) (e := e) (Y := Y)
    h72.toSystemAssumption72 h73 hmodel

omit [DecidableEq m] in
/-- **Hansen Theorem 11.2** from literal observed-row Assumption 7.2 and the
measurable Assumption 7.3 smooth-function package. -/
theorem systemDelta_betaOrZeroObs_tendstoInDistribution_of_observed_assumptions72_73
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h72 : SystemAssumption72ObservedResponseFourthConditions μ X e Y β)
    (h73 : SystemDeltaAssumption73Measurable r β R) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (r (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) - r β))
      atTop (fun z : EuclideanSpace ℝ q => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemDeltaVariance
          (systemAsymptoticVariance
            (systemPopulationGram μ X) (systemPopulationScoreCovariance μ X e)) R)) :=
  systemDelta_betaOrZeroObs_tendstoInDistribution_of_primitive_row_assumptions72_73
    (μ := μ) (X := X) (e := e) (Y := Y)
    h72.toSystemAssumption72PrimitiveRow h73 h72.model

set_option linter.style.longLine false in
omit [DecidableEq m] in
/-- Hansen Theorem 11.2 from the literal row-iid Assumption 7.2 surface and
the generic Chapter 7 smooth-function Assumption 7.3 package, with transform
measurability stated separately. -/
theorem systemDelta_betaOrZeroObs_tendstoInDistribution_of_primitive_row_assumptions72_smoothFunction73
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h72 : SystemAssumption72PrimitiveRow μ X e)
    (hr : Measurable r)
    (h73 : SmoothFunctionAssumption73 r β R)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (r (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) - r β))
      atTop (fun z : EuclideanSpace ℝ q => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemDeltaVariance
          (systemAsymptoticVariance
            (systemPopulationGram μ X) (systemPopulationScoreCovariance μ X e)) R)) :=
  systemDelta_betaOrZeroObs_tendstoInDistribution_of_primitive_row_assumptions72_73
    (μ := μ) (X := X) (e := e) (Y := Y)
    h72 (SystemDeltaAssumption73Measurable.of_smoothFunctionAssumption73 hr h73)
    hmodel

omit [DecidableEq m] in
/-- Hansen Theorem 11.2 from the literal `ContDiffAt` Assumption 7.3 surface
and the row-iid Assumption 7.2 system package.

The `ContDiffAt` package still records the measurable-transform field needed by
the current plug-in estimator measurability route. -/
theorem systemDelta_betaOrZeroObs_tendstoInDistribution_of_primitive_row_assumptions72_contDiffAt
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    {Y : ℕ → Ω → m → ℝ}
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h72 : SystemAssumption72PrimitiveRow μ X e)
    (h73 : SystemDeltaAssumption73ContDiffAt r β R)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (r (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) - r β))
      atTop (fun z : EuclideanSpace ℝ q => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemDeltaVariance
          (systemAsymptoticVariance
            (systemPopulationGram μ X) (systemPopulationScoreCovariance μ X e)) R)) :=
  systemDelta_betaOrZeroObs_tendstoInDistribution_of_primitive_row_assumptions72_73
    (μ := μ) (X := X) (e := e) (Y := Y)
    h72 h73.toSystemDeltaAssumption73Measurable hmodel

omit [DecidableEq m] in
/-- **Hansen Theorem 11.2** from literal observed-row Assumption 7.2 and the
literal `ContDiffAt` Assumption 7.3 surface. -/
theorem systemDelta_betaOrZeroObs_tendstoInDistribution_of_observed_assumptions72_contDiffAt
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {R : Matrix k q ℝ}
    (h72 : SystemAssumption72ObservedResponseFourthConditions μ X e Y β)
    (h73 : SystemDeltaAssumption73ContDiffAt r β R) :
    TendstoInDistribution
      (fun (t : ℕ) ω =>
        Real.sqrt (t : ℝ) •
          (r (systemLeastSquaresBetaOrZeroObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω)) - r β))
      atTop (fun z : EuclideanSpace ℝ q => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (systemDeltaVariance
          (systemAsymptoticVariance
            (systemPopulationGram μ X) (systemPopulationScoreCovariance μ X e)) R)) :=
  systemDelta_betaOrZeroObs_tendstoInDistribution_of_primitive_row_assumptions72_contDiffAt
    (μ := μ) (X := X) (e := e) (Y := Y)
    h72.toSystemAssumption72PrimitiveRow h73 h72.model

omit [DecidableEq k] [DecidableEq m] in
/-- **Ideal robust system-middle WLLN for Hansen Chapter 11.**

The normalized middle matrix `n⁻¹∑ Xᵢ'eᵢeᵢ'Xᵢ` converges to its population
counterpart under the Banach-valued WLLN hypotheses. This is the true-error
middle layer; replacing `eᵢ` by least-squares residuals is a separate feasible
residual-substitution step. -/
theorem systemRobustMiddle_ideal_tendstoInMeasure
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hint : Integrable (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemRobustMiddleTerm (X i ω) (e i ω))))
    (hident : ∀ i,
      IdentDistrib (fun ω => systemRobustMiddleTerm (X i ω) (e i ω))
        (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ μ) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω))
      atTop (fun _ => μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)]) := by
  have h :
      TendstoInMeasure μ
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
          (∑ i ∈ Finset.range n, systemRobustMiddleTerm (X i ω) (e i ω)))
        atTop (fun _ => μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)]) :=
    tendstoInMeasure_wlln
      (μ := μ) (fun i ω => systemRobustMiddleTerm (X i ω) (e i ω))
      hint hindep hident
  have hfun_eq :
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω)) =
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
          (∑ i ∈ Finset.range n, systemRobustMiddleTerm (X i ω) (e i ω))) := by
    funext n ω
    have hsum :
        (∑ i : Fin n, systemRobustMiddleTerm (X i.val ω) (e i.val ω)) =
          ∑ i ∈ Finset.range n, systemRobustMiddleTerm (X i ω) (e i ω) :=
      Fin.sum_univ_eq_sum_range
        (fun i => systemRobustMiddleTerm (X i ω) (e i ω)) n
    simp only [systemRobustMiddle, Fintype.card_fin]
    rw [hsum]
  rw [hfun_eq]
  exact h

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq m] in
/-- Measurability of the true-error robust system middle matrix under the
corresponding identical-distribution moment hypotheses. -/
theorem systemRobustMiddle_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hint : Integrable (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ)
    (hident : ∀ i,
      IdentDistrib (fun ω => systemRobustMiddleTerm (X i ω) (e i ω))
        (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ μ) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω)) μ := by
  simp only [systemRobustMiddle]
  refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card (Fin n) : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact ((hident i.val).integrable_iff.mpr hint).aestronglyMeasurable

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq m] in
/-- Feasible-residual perturbation target for Hansen Theorem 11.3.

If replacing the true vector errors by feasible residuals changes the exact
system robust middle matrix by `o_p(1)`, then the feasible middle has the same
probability limit as the true-error middle. -/
theorem systemRobustMiddle_feasible_tendstoInMeasure_of_substitution
    {X : ℕ → Ω → Matrix m k ℝ} {e ehat : ℕ → Ω → m → ℝ}
    {Omega : Matrix k k ℝ}
    (hideal : TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω))
      atTop (fun _ => Omega))
    (hsub : TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => ehat i.val ω) -
          systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => ehat i.val ω))
      atTop (fun _ => Omega) :=
  TendstoInMeasure.of_sub_tendsto_zero_matrix hsub hideal

omit [Fintype q] [DecidableEq q] [IsProbabilityMeasure μ] in
/-- Empirical cross weight for Hansen Theorem 11.3 robust residual substitution.

For coefficient error `d = β̂ - β`, the linear part of
`Xᵢ'(eᵢ-Xᵢd)(eᵢ-Xᵢd)'Xᵢ - Xᵢ'eᵢeᵢ'Xᵢ` is a finite sum of
`d l` times these third-order design-error averages. -/
noncomputable def systemRobustMiddleCrossWeight
    {n : Type*} [Fintype n]
    (X : n → Matrix m k ℝ) (e : n → m → ℝ)
    (a b : m) (c d l : k) : ℝ :=
  ∑ i : n, (Fintype.card n : ℝ)⁻¹ *
    ((e i a * X i b l + X i a l * e i b) * X i a c * X i b d)

omit [Fintype q] [DecidableEq q] [IsProbabilityMeasure μ] in
/-- Empirical quadratic weight for Hansen Theorem 11.3 robust residual substitution.

This is the fourth-order design average multiplying two coordinates of
`β̂ - β` in the quadratic part of the robust middle perturbation. -/
noncomputable def systemRobustMiddleQuadraticWeight
    {n : Type*} [Fintype n]
    (X : n → Matrix m k ℝ) (a b : m) (c d l r : k) : ℝ :=
  ∑ i : n, (Fintype.card n : ℝ)⁻¹ *
    (X i a l * X i b r * X i a c * X i b d)

omit [Fintype q] [DecidableEq q] [DecidableEq m] [IsProbabilityMeasure μ] in
/-- Exact finite-sample residual algebra behind Hansen Theorem 11.3.

Under the system linear model, replacing the true errors by Star residuals in
the robust middle is the corresponding substitution
`eᵢ ↦ eᵢ - Xᵢ(β̂ - β)` in every robust-middle summand. This is the
finite-sample residual algebra; expanding the two dot products gives the
pre-existing scalar cross and quadratic weights. -/
theorem systemRobustMiddle_residualStarObs_sub_apply_eq_dot_sums
    {n : Type*} [Fintype n]
    (X : n → Matrix m k ℝ) (e Y : n → m → ℝ) (β : k → ℝ)
    (hmodel : ∀ i j, Y i j = (X i j) ⬝ᵥ β + e i j) (c d : k) :
    (systemRobustMiddle X (systemResidualStarObs X Y) -
        systemRobustMiddle X e) c d =
      ∑ i : n, ∑ a : m, ∑ b : m,
        (Fintype.card n : ℝ)⁻¹ *
          (X i a c *
            (((e i a - X i a ⬝ᵥ (systemLeastSquaresBetaStarObs X Y - β)) *
                (e i b - X i b ⬝ᵥ (systemLeastSquaresBetaStarObs X Y - β))) -
              e i a * e i b) *
            X i b d) := by
  classical
  let r : k → ℝ := systemLeastSquaresBetaStarObs X Y - β
  have hres : ∀ i a, systemResidualStarObs X Y i a = e i a - X i a ⬝ᵥ r := by
    intro i a
    simpa [r] using
      systemResidualStarObs_linear_model_apply X e Y β i a hmodel
  simp only [systemRobustMiddle, systemRobustMiddleTerm, systemMiddleTerm,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.vecMulVec_apply, Matrix.transpose_apply, hres, smul_eq_mul]
  rw [← mul_sub]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_sub]
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  simp [r]
  ring_nf

omit [Fintype q] [DecidableEq q] [DecidableEq m] [IsProbabilityMeasure μ] in
/-- Scalar cross/quadratic expansion of the finite-sample residual substitution
identity behind Hansen Theorem 11.3.

This is the exact coordinate form consumed by the feasible robust-middle
consistency proof: the linear residual-substitution terms are the empirical
cross weights and the quadratic terms are the empirical fourth-order weights. -/
theorem systemRobustMiddle_residualStarObs_sub_apply_eq_scalar_weights
    {n : Type*} [Fintype n]
    (X : n → Matrix m k ℝ) (e Y : n → m → ℝ) (β : k → ℝ)
    (hmodel : ∀ i j, Y i j = (X i j) ⬝ᵥ β + e i j) (c d : k) :
    (systemRobustMiddle X (systemResidualStarObs X Y) -
        systemRobustMiddle X e) c d =
      -∑ a : m, ∑ b : m, ∑ l : k,
        (systemLeastSquaresBetaStarObs X Y - β) l *
          systemRobustMiddleCrossWeight X e a b c d l +
        ∑ a : m, ∑ b : m, ∑ l : k, ∑ r : k,
          (systemLeastSquaresBetaStarObs X Y - β) l *
            (systemLeastSquaresBetaStarObs X Y - β) r *
            systemRobustMiddleQuadraticWeight X a b c d l r := by
  classical
  let r : k → ℝ := systemLeastSquaresBetaStarObs X Y - β
  let cardInv : ℝ := (Fintype.card n : ℝ)⁻¹
  let crossTerm : n → m → m → k → ℝ := fun i a b l =>
    cardInv * ((e i a * X i b l + X i a l * e i b) * X i a c * X i b d) * r l
  let quadTerm : n → m → m → k → k → ℝ := fun i a b l s =>
    cardInv * (X i a s * X i b l * X i a c * X i b d) * r s * r l
  let crossExpanded : ℝ := ∑ i : n, ∑ a : m, ∑ b : m, ∑ l : k,
    crossTerm i a b l
  let quadExpanded : ℝ := ∑ i : n, ∑ a : m, ∑ b : m, ∑ l : k, ∑ s : k,
    quadTerm i a b l s
  have hcross :
      (∑ a : m, ∑ b : m, ∑ l : k,
        r l * systemRobustMiddleCrossWeight X e a b c d l) = crossExpanded := by
    unfold systemRobustMiddleCrossWeight
    calc
      (∑ a : m, ∑ b : m, ∑ l : k,
        r l * ∑ i : n, cardInv *
          ((e i a * X i b l + X i a l * e i b) * X i a c * X i b d)) =
          ∑ a : m, ∑ b : m, ∑ l : k, ∑ i : n,
            r l * (cardInv *
              ((e i a * X i b l + X i a l * e i b) *
                X i a c * X i b d)) := by
            simp [Finset.mul_sum]
      _ = ∑ a : m, ∑ b : m, ∑ i : n, ∑ l : k,
            r l * (cardInv *
              ((e i a * X i b l + X i a l * e i b) *
                X i a c * X i b d)) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_comm]
      _ = ∑ a : m, ∑ i : n, ∑ b : m, ∑ l : k,
            r l * (cardInv *
              ((e i a * X i b l + X i a l * e i b) *
                X i a c * X i b d)) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_comm]
      _ = ∑ i : n, ∑ a : m, ∑ b : m, ∑ l : k,
            r l * (cardInv *
              ((e i a * X i b l + X i a l * e i b) *
                X i a c * X i b d)) := by
            rw [Finset.sum_comm]
      _ = crossExpanded := by
            simp [crossExpanded, crossTerm, mul_assoc, mul_left_comm, mul_comm]
  have hquad :
      (∑ a : m, ∑ b : m, ∑ l : k, ∑ s : k,
        r l * r s * systemRobustMiddleQuadraticWeight X a b c d l s) = quadExpanded := by
    unfold systemRobustMiddleQuadraticWeight
    calc
      (∑ a : m, ∑ b : m, ∑ l : k, ∑ s : k,
        r l * r s * ∑ i : n, cardInv *
          (X i a l * X i b s * X i a c * X i b d)) =
          ∑ a : m, ∑ b : m, ∑ l : k, ∑ s : k, ∑ i : n,
            r l * r s * (cardInv *
              (X i a l * X i b s * X i a c * X i b d)) := by
            simp [Finset.mul_sum]
      _ = ∑ a : m, ∑ b : m, ∑ l : k, ∑ i : n, ∑ s : k,
            r l * r s * (cardInv *
              (X i a l * X i b s * X i a c * X i b d)) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.sum_comm]
      _ = ∑ a : m, ∑ b : m, ∑ i : n, ∑ l : k, ∑ s : k,
            r l * r s * (cardInv *
              (X i a l * X i b s * X i a c * X i b d)) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_comm]
      _ = ∑ a : m, ∑ i : n, ∑ b : m, ∑ l : k, ∑ s : k,
            r l * r s * (cardInv *
              (X i a l * X i b s * X i a c * X i b d)) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_comm]
      _ = ∑ i : n, ∑ a : m, ∑ b : m, ∑ l : k, ∑ s : k,
            r l * r s * (cardInv *
              (X i a l * X i b s * X i a c * X i b d)) := by
            rw [Finset.sum_comm]
      _ = ∑ i : n, ∑ a : m, ∑ b : m, ∑ s : k, ∑ l : k,
            r s * r l * (cardInv *
              (X i a s * X i b l * X i a c * X i b d)) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_comm]
      _ = ∑ i : n, ∑ a : m, ∑ b : m, ∑ l : k, ∑ s : k,
            cardInv * (X i a s * X i b l * X i a c * X i b d) * r s * r l := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.sum_comm]
            simp [mul_assoc, mul_left_comm, mul_comm]
      _ = quadExpanded := by
            simp [quadExpanded, quadTerm]
  have hsummand : ∀ i : n, ∀ a b : m,
      cardInv *
          (X i a c *
            (((e i a - X i a ⬝ᵥ r) *
                (e i b - X i b ⬝ᵥ r)) -
              e i a * e i b) *
            X i b d) =
        -∑ l : k, crossTerm i a b l + ∑ l : k, ∑ s : k, quadTerm i a b l s := by
    intro i a b
    simp [crossTerm, quadTerm, cardInv, dotProduct, mul_assoc, mul_left_comm, mul_comm]
    ring_nf
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    ring_nf
    simp_rw [Finset.sum_add_distrib]
    ring_nf
    abel_nf
    ring_nf
    simp [mul_assoc, mul_left_comm, mul_comm]
    abel_nf
  calc
    (systemRobustMiddle X (systemResidualStarObs X Y) -
        systemRobustMiddle X e) c d =
      ∑ i : n, ∑ a : m, ∑ b : m,
        cardInv *
          (X i a c *
            (((e i a - X i a ⬝ᵥ r) *
                (e i b - X i b ⬝ᵥ r)) -
              e i a * e i b) *
            X i b d) := by
          simpa [r] using
            systemRobustMiddle_residualStarObs_sub_apply_eq_dot_sums
              X e Y β hmodel c d
    _ =
      -crossExpanded + quadExpanded := by
          calc
            ∑ i : n, ∑ a : m, ∑ b : m,
              cardInv *
                (X i a c *
                  (((e i a - X i a ⬝ᵥ r) *
                      (e i b - X i b ⬝ᵥ r)) -
                    e i a * e i b) *
                  X i b d)
                =
              ∑ i : n, ∑ a : m, ∑ b : m,
                (-∑ l : k, crossTerm i a b l + ∑ l : k, ∑ s : k,
                  quadTerm i a b l s) := by
                apply Finset.sum_congr rfl
                intro i _
                apply Finset.sum_congr rfl
                intro a _
                apply Finset.sum_congr rfl
                intro b _
                exact hsummand i a b
            _ = -crossExpanded + quadExpanded := by
                dsimp [crossExpanded, quadExpanded]
                simp_rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ =
      -∑ a : m, ∑ b : m, ∑ l : k,
        r l * systemRobustMiddleCrossWeight X e a b c d l +
        ∑ a : m, ∑ b : m, ∑ l : k, ∑ s : k,
          r l * r s * systemRobustMiddleQuadraticWeight X a b c d l s := by
          rw [← hcross, ← hquad]
    _ =
      -∑ a : m, ∑ b : m, ∑ l : k,
        (systemLeastSquaresBetaStarObs X Y - β) l *
          systemRobustMiddleCrossWeight X e a b c d l +
        ∑ a : m, ∑ b : m, ∑ l : k, ∑ s : k,
          (systemLeastSquaresBetaStarObs X Y - β) l *
            (systemLeastSquaresBetaStarObs X Y - β) s *
            systemRobustMiddleQuadraticWeight X a b c d l s := by
          simp [r]

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m]
  [IsProbabilityMeasure μ] in
private lemma measurable_system_joint_row_X (a : m) (c : k) :
    Measurable (fun row : Matrix m k ℝ × (m → ℝ) => row.1 a c) := by
  have hfst : Continuous (fun row : Matrix m k ℝ × (m → ℝ) => row.1) :=
    continuous_fst
  have hrow : Continuous (fun row : Matrix m k ℝ × (m → ℝ) => row.1 a) :=
    (continuous_apply a).comp hfst
  exact ((continuous_apply c).comp hrow).measurable

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m]
  [IsProbabilityMeasure μ] in
private lemma measurable_system_joint_row_e (a : m) :
    Measurable (fun row : Matrix m k ℝ × (m → ℝ) => row.2 a) := by
  have hsnd : Continuous (fun row : Matrix m k ℝ × (m → ℝ) => row.2) :=
    continuous_snd
  exact ((continuous_apply a).comp hsnd).measurable

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m]
  [IsProbabilityMeasure μ] in
private lemma measurable_system_joint_middle (Sigma : Matrix m m ℝ) :
    Measurable (fun row : Matrix m k ℝ × (m → ℝ) =>
      systemMiddleTerm row.1 Sigma) := by
  have hX : Continuous (fun row : Matrix m k ℝ × (m → ℝ) => row.1) :=
    continuous_fst
  have hXt : Continuous (fun row : Matrix m k ℝ × (m → ℝ) => row.1ᵀ) :=
    (continuous_id.matrix_transpose).comp hX
  have hLeft : Continuous (fun row : Matrix m k ℝ × (m → ℝ) =>
      row.1ᵀ * Sigma) :=
    Continuous.matrix_mul hXt continuous_const
  exact (Continuous.matrix_mul hLeft hX).measurable

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m]
  [IsProbabilityMeasure μ] in
private lemma measurable_system_joint_design_weight (a b : m) (c d : k) :
    Measurable (fun row : Matrix m k ℝ × (m → ℝ) =>
      row.1 a c * row.1 b d) :=
  (measurable_system_joint_row_X (m := m) a c).mul
    (measurable_system_joint_row_X (m := m) b d)

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m]
  [IsProbabilityMeasure μ] in
private lemma measurable_system_joint_cross_weight (a b : m) (c d l : k) :
    Measurable (fun row : Matrix m k ℝ × (m → ℝ) =>
      (row.2 a * row.1 b l + row.1 a l * row.2 b) *
        row.1 a c * row.1 b d) :=
  ((((measurable_system_joint_row_e (m := m) a).mul
      (measurable_system_joint_row_X (m := m) b l)).add
      ((measurable_system_joint_row_X (m := m) a l).mul
        (measurable_system_joint_row_e (m := m) b))).mul
      (measurable_system_joint_row_X (m := m) a c)).mul
      (measurable_system_joint_row_X (m := m) b d)

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m]
  [IsProbabilityMeasure μ] in
private lemma measurable_system_joint_quadratic_weight (a b : m) (c d l r : k) :
    Measurable (fun row : Matrix m k ℝ × (m → ℝ) =>
      row.1 a l * row.1 b r * row.1 a c * row.1 b d) :=
  ((((measurable_system_joint_row_X (m := m) a l).mul
      (measurable_system_joint_row_X (m := m) b r)).mul
      (measurable_system_joint_row_X (m := m) a c)).mul
      (measurable_system_joint_row_X (m := m) b d))

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m]
  [IsProbabilityMeasure μ] in
private lemma measurable_system_joint_error_outer :
    Measurable (fun row : Matrix m k ℝ × (m → ℝ) =>
      Matrix.vecMulVec row.2 row.2) :=
  (Continuous.matrix_vecMulVec continuous_snd continuous_snd).measurable

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m]
  [IsProbabilityMeasure μ] in
private lemma measurable_system_joint_sigma_cross_weight (a b : m) (l : k) :
    Measurable (fun row : Matrix m k ℝ × (m → ℝ) =>
      row.2 a * row.1 b l + row.1 a l * row.2 b) :=
  ((measurable_system_joint_row_e (m := m) a).mul
      (measurable_system_joint_row_X (m := m) b l)).add
    ((measurable_system_joint_row_X (m := m) a l).mul
      (measurable_system_joint_row_e (m := m) b))

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
private theorem systemCovariance113_designCoordinate_memLp_two
    {X0 : Ω → Matrix m k ℝ} (hX : MemLp X0 2 μ) (a : m) (c : k) :
    MemLp (fun ω => X0 ω a c) 2 μ :=
  (hX.eval a).eval c

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
/-- Coordinate design products used by the Theorem 11.3 homoskedastic middle
and residual-covariance perturbation are integrable when the system design row
has a finite second moment. -/
theorem systemCovariance113_designWeight_integrable_of_design_memLp_two
    {X : ℕ → Ω → Matrix m k ℝ}
    (hX : MemLp (X 0) 2 μ) (a b : m) (c d : k) :
    Integrable (fun ω => X 0 ω a c * X 0 ω b d) μ :=
  (systemCovariance113_designCoordinate_memLp_two (μ := μ) hX a c).integrable_mul
    (systemCovariance113_designCoordinate_memLp_two (μ := μ) hX b d)

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
/-- The fixed homoskedastic middle contribution `X'WX` is integrable when the
system design row has a finite second moment. -/
theorem systemCovariance113_middleTerm_integrable_of_design_memLp_two
    {X : ℕ → Ω → Matrix m k ℝ} (W : Matrix m m ℝ)
    (hX : MemLp (X 0) 2 μ) :
    Integrable (fun ω => systemMiddleTerm (X 0 ω) W) μ := by
  refine Integrable.of_eval ?_
  intro c
  refine Integrable.of_eval ?_
  intro d
  have hterm : Integrable
      (fun ω => ∑ a : m, ∑ b : m, W b a * (X 0 ω a d * X 0 ω b c)) μ := by
    refine integrable_finset_sum _ (fun a _ => ?_)
    refine integrable_finset_sum _ (fun b _ => ?_)
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      ((systemCovariance113_designWeight_integrable_of_design_memLp_two
        (μ := μ) (X := X) hX a b d c).const_mul (W b a))
  simpa [systemMiddleTerm, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hterm

omit [Fintype q] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
private theorem systemCovariance113_matrix_entry_abs_le_norm
    (A : Matrix m k ℝ) (a : m) (c : k) :
    |A a c| ≤ ‖A‖ := by
  have hcoord : |A a c| ≤ ‖A a‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (A a) c
  exact hcoord.trans (norm_le_pi_norm A a)

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
private theorem systemCovariance113_vector_entry_abs_le_norm
    (v : m → ℝ) (a : m) :
    |v a| ≤ ‖v‖ := by
  simpa [Real.norm_eq_abs] using norm_le_pi_norm v a

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
/-- Compact mixed moment sufficient condition for the robust-middle cross
weights in Hansen Theorem 11.3. -/
theorem systemCovariance113_robustCross_integrable_of_errorNorm_designNorm_cubed
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (he0 : AEStronglyMeasurable (e 0) μ)
    (hMixed : Integrable (fun ω => ‖e 0 ω‖ * ‖X 0 ω‖ ^ 3) μ)
    (a b : m) (c d l : k) :
    Integrable
      (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
        X 0 ω a c * X 0 ω b d) μ := by
  have hea : AEStronglyMeasurable (fun ω => e 0 ω a) μ :=
    (continuous_apply a).comp_aestronglyMeasurable he0
  have heb : AEStronglyMeasurable (fun ω => e 0 ω b) μ :=
    (continuous_apply b).comp_aestronglyMeasurable he0
  have hXb : AEStronglyMeasurable (fun ω => X 0 ω b) μ :=
    (continuous_apply b).comp_aestronglyMeasurable hX0
  have hXa : AEStronglyMeasurable (fun ω => X 0 ω a) μ :=
    (continuous_apply a).comp_aestronglyMeasurable hX0
  have hXbl : AEStronglyMeasurable (fun ω => X 0 ω b l) μ :=
    (continuous_apply l).comp_aestronglyMeasurable hXb
  have hXal : AEStronglyMeasurable (fun ω => X 0 ω a l) μ :=
    (continuous_apply l).comp_aestronglyMeasurable hXa
  have hXac : AEStronglyMeasurable (fun ω => X 0 ω a c) μ :=
    (continuous_apply c).comp_aestronglyMeasurable hXa
  have hXbd : AEStronglyMeasurable (fun ω => X 0 ω b d) μ :=
    (continuous_apply d).comp_aestronglyMeasurable hXb
  have hf : AEStronglyMeasurable
      (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
        X 0 ω a c * X 0 ω b d) μ :=
    (((hea.mul hXbl).add (hXal.mul heb)).mul hXac).mul hXbd
  refine (hMixed.const_mul 2).mono' hf (ae_of_all μ fun ω => ?_)
  have hea_le := systemCovariance113_vector_entry_abs_le_norm (e 0 ω) a
  have heb_le := systemCovariance113_vector_entry_abs_le_norm (e 0 ω) b
  have hXbl_le := systemCovariance113_matrix_entry_abs_le_norm (X 0 ω) b l
  have hXal_le := systemCovariance113_matrix_entry_abs_le_norm (X 0 ω) a l
  have hXac_le := systemCovariance113_matrix_entry_abs_le_norm (X 0 ω) a c
  have hXbd_le := systemCovariance113_matrix_entry_abs_le_norm (X 0 ω) b d
  have hsum :
      |e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b| ≤
        2 * ‖e 0 ω‖ * ‖X 0 ω‖ := by
    calc
      |e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b| ≤
          |e 0 ω a * X 0 ω b l| + |X 0 ω a l * e 0 ω b| :=
            abs_add_le _ _
      _ = |e 0 ω a| * |X 0 ω b l| + |X 0 ω a l| * |e 0 ω b| := by
            rw [abs_mul, abs_mul]
      _ ≤ ‖e 0 ω‖ * ‖X 0 ω‖ + ‖X 0 ω‖ * ‖e 0 ω‖ := by
            gcongr
      _ = 2 * ‖e 0 ω‖ * ‖X 0 ω‖ := by ring
  calc
    ‖(e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
        X 0 ω a c * X 0 ω b d‖ =
        |e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b| *
          |X 0 ω a c| * |X 0 ω b d| := by
          simp [Real.norm_eq_abs, mul_assoc]
    _ ≤ (2 * ‖e 0 ω‖ * ‖X 0 ω‖) * ‖X 0 ω‖ * ‖X 0 ω‖ := by
          gcongr
    _ = 2 * (‖e 0 ω‖ * ‖X 0 ω‖ ^ 3) := by ring

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
/-- Compact fourth-row-moment sufficient condition for the robust-middle
quadratic weights in Hansen Theorem 11.3. -/
theorem systemCovariance113_robustQuadratic_integrable_of_designNorm_fourth
    {X : ℕ → Ω → Matrix m k ℝ}
    (hX0 : AEStronglyMeasurable (X 0) μ)
    (hFourth : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ)
    (a b : m) (c d l r : k) :
    Integrable (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ := by
  have hXa : AEStronglyMeasurable (fun ω => X 0 ω a) μ :=
    (continuous_apply a).comp_aestronglyMeasurable hX0
  have hXb : AEStronglyMeasurable (fun ω => X 0 ω b) μ :=
    (continuous_apply b).comp_aestronglyMeasurable hX0
  have hXal : AEStronglyMeasurable (fun ω => X 0 ω a l) μ :=
    (continuous_apply l).comp_aestronglyMeasurable hXa
  have hXbr : AEStronglyMeasurable (fun ω => X 0 ω b r) μ :=
    (continuous_apply r).comp_aestronglyMeasurable hXb
  have hXac : AEStronglyMeasurable (fun ω => X 0 ω a c) μ :=
    (continuous_apply c).comp_aestronglyMeasurable hXa
  have hXbd : AEStronglyMeasurable (fun ω => X 0 ω b d) μ :=
    (continuous_apply d).comp_aestronglyMeasurable hXb
  have hf : AEStronglyMeasurable
      (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ :=
    ((hXal.mul hXbr).mul hXac).mul hXbd
  refine hFourth.mono' hf (ae_of_all μ fun ω => ?_)
  have hXal_le := systemCovariance113_matrix_entry_abs_le_norm (X 0 ω) a l
  have hXbr_le := systemCovariance113_matrix_entry_abs_le_norm (X 0 ω) b r
  have hXac_le := systemCovariance113_matrix_entry_abs_le_norm (X 0 ω) a c
  have hXbd_le := systemCovariance113_matrix_entry_abs_le_norm (X 0 ω) b d
  calc
    ‖X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d‖ =
        |X 0 ω a l| * |X 0 ω b r| * |X 0 ω a c| * |X 0 ω b d| := by
          simp [Real.norm_eq_abs, mul_assoc]
    _ ≤ ‖X 0 ω‖ * ‖X 0 ω‖ * ‖X 0 ω‖ * ‖X 0 ω‖ := by
          gcongr
    _ = ‖X 0 ω‖ ^ 4 := by ring

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
/-- Compact second-error-moment sufficient condition for the true-error
outer-product integrability in Hansen Theorem 11.3. -/
theorem systemCovariance113_errorOuter_integrable_of_errorNorm_sq
    {e : ℕ → Ω → m → ℝ}
    (he0 : AEStronglyMeasurable (e 0) μ)
    (hErrorSq : Integrable (fun ω => ‖e 0 ω‖ ^ 2) μ) :
    Integrable (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ := by
  classical
  refine Integrable.of_eval ?_
  intro a
  refine Integrable.of_eval ?_
  intro b
  have hea : AEStronglyMeasurable (fun ω => e 0 ω a) μ :=
    (continuous_apply a).comp_aestronglyMeasurable he0
  have heb : AEStronglyMeasurable (fun ω => e 0 ω b) μ :=
    (continuous_apply b).comp_aestronglyMeasurable he0
  refine hErrorSq.mono' (hea.mul heb) (ae_of_all μ fun ω => ?_)
  have hea_le := systemCovariance113_vector_entry_abs_le_norm (e 0 ω) a
  have heb_le := systemCovariance113_vector_entry_abs_le_norm (e 0 ω) b
  calc
    ‖Matrix.vecMulVec (e 0 ω) (e 0 ω) a b‖ =
        |e 0 ω a| * |e 0 ω b| := by
          simp [Matrix.vecMulVec_apply, Real.norm_eq_abs]
    _ ≤ ‖e 0 ω‖ * ‖e 0 ω‖ := by
          gcongr
    _ = ‖e 0 ω‖ ^ 2 := by ring

omit [IsProbabilityMeasure μ] [Fintype q] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
/-- Compact `L²(e₀)` and `L²(X₀)` sufficient condition for the residual
covariance cross weights in Hansen Theorem 11.3. -/
theorem systemCovariance113_sigmaCross_integrable_of_errorNorm_sq_design_memLp_two
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hX : MemLp (X 0) 2 μ)
    (he0 : AEStronglyMeasurable (e 0) μ)
    (hErrorSq : Integrable (fun ω => ‖e 0 ω‖ ^ 2) μ)
    (a b : m) (l : k) :
    Integrable (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ := by
  have he_memLp : MemLp (e 0) 2 μ :=
    (memLp_two_iff_integrable_sq_norm he0).2 hErrorSq
  exact
    ((he_memLp.eval a).integrable_mul
      ((hX.eval b).eval l)).add
    (((hX.eval a).eval l).integrable_mul
      (he_memLp.eval b))

omit [Fintype q] [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
/-- Scalar WLLN bridge for the robust-middle cross weights in Hansen
Theorem 11.3. -/
theorem systemRobustMiddleCrossWeight_boundedInProbability_of_wlln
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (a b : m) (c d l : k)
    (hint : Integrable
      (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
        X 0 ω a c * X 0 ω b d) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => (e i ω a * X i ω b l + X i ω a l * e i ω b) *
        X i ω a c * X i ω b d)))
    (hident : ∀ i,
      IdentDistrib
        (fun ω => (e i ω a * X i ω b l + X i ω a l * e i ω b) *
          X i ω a c * X i ω b d)
        (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
          X 0 ω a c * X 0 ω b d) μ μ) :
    BoundedInProbability μ
      (fun n ω =>
        systemRobustMiddleCrossWeight
          (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b c d l) := by
  let W : ℕ → Ω → ℝ := fun i ω =>
    (e i ω a * X i ω b l + X i ω a l * e i ω b) * X i ω a c * X i ω b d
  have hWLLN : TendstoInMeasure μ
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, W i ω)
      atTop (fun _ => μ[W 0]) :=
    tendstoInMeasure_wlln W hint hindep hident
  have hWeight : TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddleCrossWeight
          (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b c d l)
      atTop (fun _ => μ[W 0]) := by
    refine hWLLN.congr_left (fun n => ae_of_all μ (fun ω => ?_))
    have hsum :
        (∑ i : Fin n,
            (e i.val ω a * X i.val ω b l + X i.val ω a l * e i.val ω b) *
              X i.val ω a c * X i.val ω b d) =
          ∑ i ∈ Finset.range n,
            (e i ω a * X i ω b l + X i ω a l * e i ω b) *
              X i ω a c * X i ω b d :=
      Fin.sum_univ_eq_sum_range
        (fun i =>
          (e i ω a * X i ω b l + X i ω a l * e i ω b) *
            X i ω a c * X i ω b d) n
    calc
      (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, W i ω)
          = (n : ℝ)⁻¹ * ∑ i : Fin n,
              (e i.val ω a * X i.val ω b l + X i.val ω a l * e i.val ω b) *
                X i.val ω a c * X i.val ω b d := by
                rw [← hsum]
                simp [smul_eq_mul]
      _ = ∑ i : Fin n, (n : ℝ)⁻¹ *
              ((e i.val ω a * X i.val ω b l + X i.val ω a l * e i.val ω b) *
                X i.val ω a c * X i.val ω b d) := by
                rw [Finset.mul_sum]
      _ = systemRobustMiddleCrossWeight
            (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b c d l := by
                rw [systemRobustMiddleCrossWeight]
                simp only [Fintype.card_fin]
  exact BoundedInProbability.of_tendstoInMeasure_const hWeight

omit [Fintype q] [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
/-- Scalar WLLN bridge for the robust-middle quadratic weights in Hansen
Theorem 11.3. -/
theorem systemRobustMiddleQuadraticWeight_boundedInProbability_of_wlln
    {X : ℕ → Ω → Matrix m k ℝ}
    (a b : m) (c d l r : k)
    (hint : Integrable
      (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => X i ω a l * X i ω b r * X i ω a c * X i ω b d)))
    (hident : ∀ i,
      IdentDistrib
        (fun ω => X i ω a l * X i ω b r * X i ω a c * X i ω b d)
        (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ μ) :
    BoundedInProbability μ
      (fun n ω =>
        systemRobustMiddleQuadraticWeight
          (fun i : Fin n => X i.val ω) a b c d l r) := by
  let W : ℕ → Ω → ℝ := fun i ω =>
    X i ω a l * X i ω b r * X i ω a c * X i ω b d
  have hWLLN : TendstoInMeasure μ
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, W i ω)
      atTop (fun _ => μ[W 0]) :=
    tendstoInMeasure_wlln W hint hindep hident
  have hWeight : TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddleQuadraticWeight
          (fun i : Fin n => X i.val ω) a b c d l r)
      atTop (fun _ => μ[W 0]) := by
    refine hWLLN.congr_left (fun n => ae_of_all μ (fun ω => ?_))
    have hsum :
        (∑ i : Fin n,
            X i.val ω a l * X i.val ω b r * X i.val ω a c * X i.val ω b d) =
          ∑ i ∈ Finset.range n,
            X i ω a l * X i ω b r * X i ω a c * X i ω b d :=
      Fin.sum_univ_eq_sum_range
        (fun i => X i ω a l * X i ω b r * X i ω a c * X i ω b d) n
    calc
      (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, W i ω)
          = (n : ℝ)⁻¹ * ∑ i : Fin n,
              X i.val ω a l * X i.val ω b r * X i.val ω a c * X i.val ω b d := by
                rw [← hsum]
                simp [smul_eq_mul]
      _ = ∑ i : Fin n, (n : ℝ)⁻¹ *
              (X i.val ω a l * X i.val ω b r * X i.val ω a c * X i.val ω b d) := by
                rw [Finset.mul_sum]
      _ = systemRobustMiddleQuadraticWeight
            (fun i : Fin n => X i.val ω) a b c d l r := by
                rw [systemRobustMiddleQuadraticWeight]
                simp only [Fintype.card_fin]
  exact BoundedInProbability.of_tendstoInMeasure_const hWeight

omit [Fintype q] [DecidableEq q] [DecidableEq m] [IsProbabilityMeasure μ] in
/-- Coefficient consistency plus bounded empirical robust-middle weights imply
Hansen Theorem 11.3's feasible residual-substitution premise.

This is the sample-specific Star residual result:
`n⁻¹∑ Xᵢ'êᵢêᵢ'Xᵢ - n⁻¹∑ Xᵢ'eᵢeᵢ'Xᵢ = oₚ(1)`, with `êᵢ` the actual
observation-level Star system residuals. -/
theorem systemRobustMiddle_sub_tendstoInMeasure_zero_of_beta_bounded_weights
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (_hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hBeta : TendstoInMeasure μ
      (fun n ω =>
        systemLeastSquaresBetaStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω))
      atTop (fun _ => β))
    (hCrossWeight : ∀ a b : m, ∀ c d l : k,
      BoundedInProbability μ
        (fun n ω =>
          systemRobustMiddleCrossWeight
            (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b c d l))
    (hQuadraticWeight : ∀ a b : m, ∀ c d l r : k,
      BoundedInProbability μ
        (fun n ω =>
          systemRobustMiddleQuadraticWeight
            (fun i : Fin n => X i.val ω) a b c d l r))
    (hdecomp : ∀ n ω c d,
      (systemRobustMiddle (fun i : Fin n => X i.val ω)
          (systemResidualStarObs (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω)) -
        systemRobustMiddle (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω)) c d =
        -∑ a : m, ∑ b : m, ∑ l : k,
          (systemLeastSquaresBetaStarObs
              (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) - β) l *
            systemRobustMiddleCrossWeight
              (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b c d l +
          ∑ a : m, ∑ b : m, ∑ l : k, ∑ s : k,
            (systemLeastSquaresBetaStarObs
                (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) - β) l *
              (systemLeastSquaresBetaStarObs
                (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) - β) s *
              systemRobustMiddleQuadraticWeight
                (fun i : Fin n => X i.val ω) a b c d l s) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω)) -
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (fun i : Fin n => e i.val ω))
      atTop (fun _ => 0) := by
  classical
  let βhat : ℕ → Ω → k → ℝ := fun n ω =>
    systemLeastSquaresBetaStarObs
      (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω)
  let r : ℕ → Ω → k → ℝ := fun n ω => βhat n ω - β
  have hr : ∀ l : k, TendstoInMeasure μ (fun n ω => r n ω l) atTop (fun _ => 0) := by
    intro l
    have hl := TendstoInMeasure.pi_apply hBeta l
    simpa [r, βhat, Pi.sub_apply] using TendstoInMeasure.sub_limit_zero_real hl
  refine tendstoInMeasure_pi (μ := μ) (fun c => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun d => ?_)
  let cross : ℕ → Ω → ℝ := fun n ω =>
    ∑ a : m, ∑ b : m, ∑ l : k,
      r n ω l *
        systemRobustMiddleCrossWeight
          (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b c d l
  let quad : ℕ → Ω → ℝ := fun n ω =>
    ∑ a : m, ∑ b : m, ∑ l : k, ∑ s : k,
      r n ω l * r n ω s *
        systemRobustMiddleQuadraticWeight
          (fun i : Fin n => X i.val ω) a b c d l s
  have hcross : TendstoInMeasure μ cross atTop (fun _ => 0) := by
    have hA : ∀ a ∈ (Finset.univ : Finset m),
        TendstoInMeasure μ
          (fun n ω => ∑ b : m, ∑ l : k,
            r n ω l *
              systemRobustMiddleCrossWeight
                (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b c d l)
          atTop (fun _ => 0) := by
      intro a _
      have hB : ∀ b ∈ (Finset.univ : Finset m),
          TendstoInMeasure μ
            (fun n ω => ∑ l : k,
              r n ω l *
                systemRobustMiddleCrossWeight
                  (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b c d l)
            atTop (fun _ => 0) := by
        intro b _
        have hL : ∀ l ∈ (Finset.univ : Finset k),
            TendstoInMeasure μ
              (fun n ω =>
                r n ω l *
                  systemRobustMiddleCrossWeight
                    (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω)
                    a b c d l)
              atTop (fun _ => 0) := by
          intro l _
          exact TendstoInMeasure.mul_boundedInProbability (hr l) (hCrossWeight a b c d l)
        simpa using tendstoInMeasure_finset_sum_zero_real (μ := μ)
          (s := (Finset.univ : Finset k))
          (X := fun l n ω =>
            r n ω l *
              systemRobustMiddleCrossWeight
                (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b c d l)
          hL
      simpa using tendstoInMeasure_finset_sum_zero_real (μ := μ)
        (s := (Finset.univ : Finset m))
        (X := fun b n ω => ∑ l : k,
          r n ω l *
            systemRobustMiddleCrossWeight
              (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b c d l)
        hB
    simpa [cross] using tendstoInMeasure_finset_sum_zero_real (μ := μ)
      (s := (Finset.univ : Finset m))
      (X := fun a n ω => ∑ b : m, ∑ l : k,
        r n ω l *
          systemRobustMiddleCrossWeight
            (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b c d l)
      hA
  have hquad : TendstoInMeasure μ quad atTop (fun _ => 0) := by
    have hA : ∀ a ∈ (Finset.univ : Finset m),
        TendstoInMeasure μ
          (fun n ω => ∑ b : m, ∑ l : k, ∑ s : k,
            r n ω l * r n ω s *
              systemRobustMiddleQuadraticWeight
                (fun i : Fin n => X i.val ω) a b c d l s)
          atTop (fun _ => 0) := by
      intro a _
      have hB : ∀ b ∈ (Finset.univ : Finset m),
          TendstoInMeasure μ
            (fun n ω => ∑ l : k, ∑ s : k,
              r n ω l * r n ω s *
                systemRobustMiddleQuadraticWeight
                  (fun i : Fin n => X i.val ω) a b c d l s)
            atTop (fun _ => 0) := by
        intro b _
        have hL : ∀ l ∈ (Finset.univ : Finset k),
            TendstoInMeasure μ
              (fun n ω => ∑ s : k,
                r n ω l * r n ω s *
                  systemRobustMiddleQuadraticWeight
                    (fun i : Fin n => X i.val ω) a b c d l s)
              atTop (fun _ => 0) := by
          intro l _
          have hS : ∀ s ∈ (Finset.univ : Finset k),
              TendstoInMeasure μ
                (fun n ω =>
                  r n ω l * r n ω s *
                    systemRobustMiddleQuadraticWeight
                      (fun i : Fin n => X i.val ω) a b c d l s)
                atTop (fun _ => 0) := by
            intro s _
            have hprod := TendstoInMeasure.mul_zero_real (hr l) (hr s)
            exact TendstoInMeasure.mul_boundedInProbability hprod
              (hQuadraticWeight a b c d l s)
          simpa using tendstoInMeasure_finset_sum_zero_real (μ := μ)
            (s := (Finset.univ : Finset k))
            (X := fun s n ω =>
              r n ω l * r n ω s *
                systemRobustMiddleQuadraticWeight
                  (fun i : Fin n => X i.val ω) a b c d l s)
            hS
        simpa using tendstoInMeasure_finset_sum_zero_real (μ := μ)
          (s := (Finset.univ : Finset k))
          (X := fun l n ω => ∑ s : k,
            r n ω l * r n ω s *
              systemRobustMiddleQuadraticWeight
                (fun i : Fin n => X i.val ω) a b c d l s)
          hL
      simpa using tendstoInMeasure_finset_sum_zero_real (μ := μ)
        (s := (Finset.univ : Finset m))
        (X := fun b n ω => ∑ l : k, ∑ s : k,
          r n ω l * r n ω s *
            systemRobustMiddleQuadraticWeight
              (fun i : Fin n => X i.val ω) a b c d l s)
        hB
    simpa [quad] using tendstoInMeasure_finset_sum_zero_real (μ := μ)
      (s := (Finset.univ : Finset m))
      (X := fun a n ω => ∑ b : m, ∑ l : k, ∑ s : k,
        r n ω l * r n ω s *
          systemRobustMiddleQuadraticWeight
            (fun i : Fin n => X i.val ω) a b c d l s)
      hA
  have hformula : TendstoInMeasure μ (fun n ω => -cross n ω + quad n ω)
      atTop (fun _ => 0) :=
    TendstoInMeasure.add_zero_real (TendstoInMeasure.neg_zero_real hcross) hquad
  refine hformula.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  symm
  simpa [cross, quad, r, βhat] using hdecomp n ω c d

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Coefficient consistency plus scalar WLLNs for the robust-middle residual
weights imply Hansen Theorem 11.3's feasible residual-substitution premise. -/
theorem systemRobustMiddle_sub_tendstoInMeasure_zero_of_beta_weight_wlln
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hBeta : TendstoInMeasure μ
      (fun n ω =>
        systemLeastSquaresBetaStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω))
      atTop (fun _ => β))
    (hdecomp : ∀ n ω c d,
      (systemRobustMiddle (fun i : Fin n => X i.val ω)
          (systemResidualStarObs (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω)) -
        systemRobustMiddle (fun i : Fin n => X i.val ω)
          (fun i : Fin n => e i.val ω)) c d =
        -∑ a : m, ∑ b : m, ∑ l : k,
          (systemLeastSquaresBetaStarObs
              (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) - β) l *
            systemRobustMiddleCrossWeight
              (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b c d l +
          ∑ a : m, ∑ b : m, ∑ l : k, ∑ s : k,
            (systemLeastSquaresBetaStarObs
                (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) - β) l *
              (systemLeastSquaresBetaStarObs
                (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) - β) s *
              systemRobustMiddleQuadraticWeight
                (fun i : Fin n => X i.val ω) a b c d l s)
    (hCross_int : ∀ a b : m, ∀ c d l : k,
      Integrable
        (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
          X 0 ω a c * X 0 ω b d) μ)
    (hCross_indep : ∀ a b : m, ∀ c d l : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => (e i ω a * X i ω b l + X i ω a l * e i ω b) *
          X i ω a c * X i ω b d)))
    (hCross_ident : ∀ a b : m, ∀ c d l : k, ∀ i,
      IdentDistrib
        (fun ω => (e i ω a * X i ω b l + X i ω a l * e i ω b) *
          X i ω a c * X i ω b d)
        (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
          X 0 ω a c * X 0 ω b d) μ μ)
    (hQuadratic_int : ∀ a b : m, ∀ c d l r : k,
      Integrable (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ)
    (hQuadratic_indep : ∀ a b : m, ∀ c d l r : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => X i ω a l * X i ω b r * X i ω a c * X i ω b d)))
    (hQuadratic_ident : ∀ a b : m, ∀ c d l r : k, ∀ i,
      IdentDistrib
        (fun ω => X i ω a l * X i ω b r * X i ω a c * X i ω b d)
        (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ μ) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω)) -
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (fun i : Fin n => e i.val ω))
      atTop (fun _ => 0) :=
  systemRobustMiddle_sub_tendstoInMeasure_zero_of_beta_bounded_weights
    (μ := μ) (X := X) (e := e) (Y := Y) hmodel hBeta
    (fun a b c d l =>
      systemRobustMiddleCrossWeight_boundedInProbability_of_wlln
        (μ := μ) (X := X) (e := e) a b c d l
        (hCross_int a b c d l) (hCross_indep a b c d l)
        (hCross_ident a b c d l))
    (fun a b c d l r =>
      systemRobustMiddleQuadraticWeight_boundedInProbability_of_wlln
        (μ := μ) (X := X) a b c d l r
        (hQuadratic_int a b c d l r) (hQuadratic_indep a b c d l r)
        (hQuadratic_ident a b c d l r))
    hdecomp

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Coefficient consistency plus scalar WLLNs for the robust-middle residual
weights imply the feasible residual-substitution premise, with the exact
finite-sample scalar decomposition discharged from the system linear model.

This closes the residual-algebra input of Hansen Theorem 11.3: callers provide
the coefficient consistency and the cross/quadratic WLLN premises, while
`systemRobustMiddle_residualStarObs_sub_apply_eq_scalar_weights` supplies the
finite-sample expansion. -/
theorem systemRobustMiddle_sub_tendstoInMeasure_zero_of_beta_weight_wlln_of_linear_model
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hBeta : TendstoInMeasure μ
      (fun n ω =>
        systemLeastSquaresBetaStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω))
      atTop (fun _ => β))
    (hCross_int : ∀ a b : m, ∀ c d l : k,
      Integrable
        (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
          X 0 ω a c * X 0 ω b d) μ)
    (hCross_indep : ∀ a b : m, ∀ c d l : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => (e i ω a * X i ω b l + X i ω a l * e i ω b) *
          X i ω a c * X i ω b d)))
    (hCross_ident : ∀ a b : m, ∀ c d l : k, ∀ i,
      IdentDistrib
        (fun ω => (e i ω a * X i ω b l + X i ω a l * e i ω b) *
          X i ω a c * X i ω b d)
        (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
          X 0 ω a c * X 0 ω b d) μ μ)
    (hQuadratic_int : ∀ a b : m, ∀ c d l r : k,
      Integrable (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ)
    (hQuadratic_indep : ∀ a b : m, ∀ c d l r : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => X i ω a l * X i ω b r * X i ω a c * X i ω b d)))
    (hQuadratic_ident : ∀ a b : m, ∀ c d l r : k, ∀ i,
      IdentDistrib
        (fun ω => X i ω a l * X i ω b r * X i ω a c * X i ω b d)
        (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ μ) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω)) -
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (fun i : Fin n => e i.val ω))
      atTop (fun _ => 0) :=
  systemRobustMiddle_sub_tendstoInMeasure_zero_of_beta_weight_wlln
    (μ := μ) (X := X) (e := e) (Y := Y) hmodel hBeta
    (fun n ω c d => by
      simpa using
        systemRobustMiddle_residualStarObs_sub_apply_eq_scalar_weights
          (X := fun i : Fin n => X i.val ω)
          (e := fun i : Fin n => e i.val ω)
          (Y := fun i : Fin n => Y i.val ω)
          (β := β)
          (fun i j => hmodel i.val ω j) c d)
    hCross_int hCross_indep hCross_ident
    hQuadratic_int hQuadratic_indep hQuadratic_ident

omit [DecidableEq k] [DecidableEq q] [DecidableEq m] in
/-- **Ideal residual-covariance WLLN for Hansen Chapter 11.**

The true-error covariance average `n⁻¹∑ eᵢeᵢ'` converges to its population
matrix under the Banach-valued WLLN hypotheses. Feasible residual covariance
consistency is obtained by combining this theorem with a residual-substitution
bound for `êᵢêᵢ' - eᵢeᵢ'`. -/
theorem systemSigmaHat_ideal_tendstoInMeasure
    {e : ℕ → Ω → m → ℝ}
    (hint : Integrable (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => Matrix.vecMulVec (e i ω) (e i ω))))
    (hident : ∀ i,
      IdentDistrib (fun ω => Matrix.vecMulVec (e i ω) (e i ω))
        (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ μ) :
    TendstoInMeasure μ
      (fun n ω => systemSigmaHat (fun i : Fin n => e i.val ω))
      atTop (fun _ => μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)]) := by
  have h :
      TendstoInMeasure μ
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
          (∑ i ∈ Finset.range n, Matrix.vecMulVec (e i ω) (e i ω)))
        atTop (fun _ => μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)]) :=
    tendstoInMeasure_wlln
      (μ := μ) (fun i ω => Matrix.vecMulVec (e i ω) (e i ω))
      hint hindep hident
  have hfun_eq :
      (fun n ω => systemSigmaHat (fun i : Fin n => e i.val ω)) =
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
          (∑ i ∈ Finset.range n, Matrix.vecMulVec (e i ω) (e i ω))) := by
    funext n ω
    have hsum :
        (∑ i : Fin n, Matrix.vecMulVec (e i.val ω) (e i.val ω)) =
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (e i ω) (e i ω) :=
      Fin.sum_univ_eq_sum_range (fun i => Matrix.vecMulVec (e i ω) (e i ω)) n
    simp only [systemSigmaHat, Fintype.card_fin]
    rw [hsum]
  rw [hfun_eq]
  exact h

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
/-- Measurability of the true-error residual covariance average. -/
theorem systemSigmaHat_ideal_aestronglyMeasurable
    {e : ℕ → Ω → m → ℝ}
    (hint : Integrable (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ)
    (hident : ∀ i,
      IdentDistrib (fun ω => Matrix.vecMulVec (e i ω) (e i ω))
        (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ μ) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω => systemSigmaHat (fun i : Fin n => e i.val ω)) μ := by
  simp only [systemSigmaHat]
  refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card (Fin n) : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact ((hident i.val).integrable_iff.mpr hint).aestronglyMeasurable

omit [IsProbabilityMeasure μ] [DecidableEq m] in
/-- Residual-covariance consistency from a true-error covariance WLLN plus a
feasible-residual covariance substitution.

This is the homoskedastic covariance input for Hansen Theorem 11.3:
`Σ̂(ê) - Σ̂(e) = oₚ(1)` transfers the true-error covariance limit to the
actual Star residual covariance surface used by
`systemHomoskedasticCovarianceStarObs`. -/
theorem systemSigmaHatStarObs_tendstoInMeasure_of_true_error_substitution
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Sigma : Matrix m m ℝ}
    (hideal : TendstoInMeasure μ
      (fun n ω => systemSigmaHat (fun i : Fin n => e i.val ω))
      atTop (fun _ => Sigma))
    (hsub : TendstoInMeasure μ
      (fun n ω =>
        systemSigmaHatStarObs
            (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) -
          systemSigmaHat (fun i : Fin n => e i.val ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        systemSigmaHatStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω))
      atTop (fun _ => Sigma) :=
  TendstoInMeasure.of_sub_tendsto_zero_matrix hsub hideal

omit [Fintype q] [DecidableEq q] [IsProbabilityMeasure μ] in
/-- Empirical cross weight for the feasible residual-covariance substitution in
Hansen Theorem 11.3.

For coefficient error `d = β̂ - β`, the linear part of
`n⁻¹∑(eᵢ-Xᵢd)(eᵢ-Xᵢd)' - n⁻¹∑eᵢeᵢ'` is a finite sum of `d l` times these
second-order error/design averages. -/
noncomputable def systemSigmaHatCrossWeight
    {n : Type*} [Fintype n]
    (X : n → Matrix m k ℝ) (e : n → m → ℝ) (a b : m) (l : k) : ℝ :=
  ∑ i : n, (Fintype.card n : ℝ)⁻¹ *
    (e i a * X i b l + X i a l * e i b)

omit [Fintype q] [DecidableEq q] [IsProbabilityMeasure μ] in
/-- Empirical quadratic weight for the feasible residual-covariance substitution
in Hansen Theorem 11.3.

This is the second-order design average multiplying two coordinates of
`β̂ - β` in the quadratic part of `Σ̂(ê)-Σ̂(e)`. -/
noncomputable def systemSigmaHatQuadraticWeight
    {n : Type*} [Fintype n]
    (X : n → Matrix m k ℝ) (a b : m) (l r : k) : ℝ :=
  ∑ i : n, (Fintype.card n : ℝ)⁻¹ * (X i a l * X i b r)

omit [Fintype q] [DecidableEq q] [DecidableEq m] [IsProbabilityMeasure μ] in
/-- Exact finite-sample residual-covariance algebra behind Hansen Theorem 11.3.

Under the system linear model, replacing true errors by Star residuals in
`systemSigmaHat` is the substitution `eᵢ ↦ eᵢ - Xᵢ(β̂ - β)` in each
outer-product summand. -/
theorem systemSigmaHatStarObs_sub_apply_eq_dot_sums
    {n : Type*} [Fintype n]
    (X : n → Matrix m k ℝ) (e Y : n → m → ℝ) (β : k → ℝ)
    (hmodel : ∀ i j, Y i j = (X i j) ⬝ᵥ β + e i j) (a b : m) :
    (systemSigmaHatStarObs X Y - systemSigmaHat e) a b =
      ∑ i : n, (Fintype.card n : ℝ)⁻¹ *
        (((e i a - X i a ⬝ᵥ (systemLeastSquaresBetaStarObs X Y - β)) *
            (e i b - X i b ⬝ᵥ (systemLeastSquaresBetaStarObs X Y - β))) -
          e i a * e i b) := by
  classical
  let r : k → ℝ := systemLeastSquaresBetaStarObs X Y - β
  have hres : ∀ i j, systemResidualStarObs X Y i j = e i j - X i j ⬝ᵥ r := by
    intro i j
    simpa [r] using
      systemResidualStarObs_linear_model_apply X e Y β i j hmodel
  simp only [systemSigmaHatStarObs, systemSigmaHat, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, hres, smul_eq_mul]
  rw [← mul_sub]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]

omit [Fintype q] [DecidableEq q] [DecidableEq m] [IsProbabilityMeasure μ] in
/-- Scalar cross/quadratic expansion of the feasible residual-covariance
substitution identity behind Hansen Theorem 11.3. -/
theorem systemSigmaHatStarObs_sub_apply_eq_scalar_weights
    {n : Type*} [Fintype n]
    (X : n → Matrix m k ℝ) (e Y : n → m → ℝ) (β : k → ℝ)
    (hmodel : ∀ i j, Y i j = (X i j) ⬝ᵥ β + e i j) (a b : m) :
    (systemSigmaHatStarObs X Y - systemSigmaHat e) a b =
      -∑ l : k,
        (systemLeastSquaresBetaStarObs X Y - β) l *
          systemSigmaHatCrossWeight X e a b l +
        ∑ l : k, ∑ r : k,
          (systemLeastSquaresBetaStarObs X Y - β) l *
            (systemLeastSquaresBetaStarObs X Y - β) r *
            systemSigmaHatQuadraticWeight X a b l r := by
  classical
  let r : k → ℝ := systemLeastSquaresBetaStarObs X Y - β
  let cardInv : ℝ := (Fintype.card n : ℝ)⁻¹
  let crossTerm : n → k → ℝ := fun i l =>
    cardInv * (e i a * X i b l + X i a l * e i b) * r l
  let quadTerm : n → k → k → ℝ := fun i l s =>
    cardInv * (X i a l * X i b s) * r l * r s
  let crossExpanded : ℝ := ∑ i : n, ∑ l : k, crossTerm i l
  let quadExpanded : ℝ := ∑ i : n, ∑ l : k, ∑ s : k, quadTerm i l s
  have hcross :
      (∑ l : k, r l * systemSigmaHatCrossWeight X e a b l) =
        crossExpanded := by
    unfold systemSigmaHatCrossWeight
    calc
      (∑ l : k, r l *
          ∑ i : n, cardInv * (e i a * X i b l + X i a l * e i b)) =
          ∑ l : k, ∑ i : n,
            r l * (cardInv * (e i a * X i b l + X i a l * e i b)) := by
            simp [Finset.mul_sum]
      _ = ∑ i : n, ∑ l : k,
            r l * (cardInv * (e i a * X i b l + X i a l * e i b)) := by
            rw [Finset.sum_comm]
      _ = crossExpanded := by
            simp [crossExpanded, crossTerm, mul_assoc, mul_comm]
  have hquad :
      (∑ l : k, ∑ s : k,
        r l * r s * systemSigmaHatQuadraticWeight X a b l s) =
        quadExpanded := by
    unfold systemSigmaHatQuadraticWeight
    calc
      (∑ l : k, ∑ s : k,
        r l * r s * ∑ i : n, cardInv * (X i a l * X i b s)) =
          ∑ l : k, ∑ s : k, ∑ i : n,
            r l * r s * (cardInv * (X i a l * X i b s)) := by
            simp [Finset.mul_sum]
      _ = ∑ l : k, ∑ i : n, ∑ s : k,
            r l * r s * (cardInv * (X i a l * X i b s)) := by
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.sum_comm]
      _ = ∑ i : n, ∑ l : k, ∑ s : k,
            r l * r s * (cardInv * (X i a l * X i b s)) := by
            rw [Finset.sum_comm]
      _ = quadExpanded := by
            simp [quadExpanded, quadTerm, mul_assoc, mul_comm]
  have hsummand : ∀ i : n,
      cardInv *
          (((e i a - X i a ⬝ᵥ r) * (e i b - X i b ⬝ᵥ r)) -
            e i a * e i b) =
        -∑ l : k, crossTerm i l + ∑ l : k, ∑ s : k, quadTerm i l s := by
    intro i
    simp [crossTerm, quadTerm, cardInv, dotProduct, mul_assoc, mul_comm]
    ring_nf
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    ring_nf
    simp_rw [Finset.sum_add_distrib]
    ring_nf
    abel_nf
    ring_nf
    simp only [mul_assoc, mul_left_comm, mul_comm]
    rw [Finset.sum_comm]
    simp [mul_comm]
  calc
    (systemSigmaHatStarObs X Y - systemSigmaHat e) a b =
      ∑ i : n, cardInv *
        (((e i a - X i a ⬝ᵥ r) * (e i b - X i b ⬝ᵥ r)) -
          e i a * e i b) := by
          simpa [r, cardInv] using
            systemSigmaHatStarObs_sub_apply_eq_dot_sums
              X e Y β hmodel a b
    _ = ∑ i : n, (-∑ l : k, crossTerm i l + ∑ l : k, ∑ s : k,
          quadTerm i l s) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hsummand i
    _ = -crossExpanded + quadExpanded := by
          dsimp [crossExpanded, quadExpanded]
          simp_rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = -∑ l : k,
          (systemLeastSquaresBetaStarObs X Y - β) l *
            systemSigmaHatCrossWeight X e a b l +
        ∑ l : k, ∑ s : k,
          (systemLeastSquaresBetaStarObs X Y - β) l *
          (systemLeastSquaresBetaStarObs X Y - β) s *
            systemSigmaHatQuadraticWeight X a b l s := by
          rw [← hcross, ← hquad]

omit [Fintype q] [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
/-- Scalar WLLN bridge for the residual-covariance cross weights in Hansen
Theorem 11.3. -/
theorem systemSigmaHatCrossWeight_boundedInProbability_of_wlln
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (a b : m) (l : k)
    (hint : Integrable
      (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => e i ω a * X i ω b l + X i ω a l * e i ω b)))
    (hident : ∀ i,
      IdentDistrib
        (fun ω => e i ω a * X i ω b l + X i ω a l * e i ω b)
        (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ μ) :
    BoundedInProbability μ
      (fun n ω =>
        systemSigmaHatCrossWeight
          (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b l) := by
  let W : ℕ → Ω → ℝ := fun i ω =>
    e i ω a * X i ω b l + X i ω a l * e i ω b
  have hWLLN : TendstoInMeasure μ
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, W i ω)
      atTop (fun _ => μ[W 0]) :=
    tendstoInMeasure_wlln W hint hindep hident
  have hWeight : TendstoInMeasure μ
      (fun n ω =>
        systemSigmaHatCrossWeight
          (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b l)
      atTop (fun _ => μ[W 0]) := by
    refine hWLLN.congr_left (fun n => ae_of_all μ (fun ω => ?_))
    have hsum :
        (∑ i : Fin n,
            (e i.val ω a * X i.val ω b l + X i.val ω a l * e i.val ω b)) =
          ∑ i ∈ Finset.range n,
            (e i ω a * X i ω b l + X i ω a l * e i ω b) :=
      Fin.sum_univ_eq_sum_range
        (fun i => e i ω a * X i ω b l + X i ω a l * e i ω b) n
    calc
      (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, W i ω)
          = (n : ℝ)⁻¹ * ∑ i : Fin n,
              (e i.val ω a * X i.val ω b l +
                X i.val ω a l * e i.val ω b) := by
                rw [← hsum]
                simp [smul_eq_mul]
      _ = ∑ i : Fin n, (n : ℝ)⁻¹ *
              (e i.val ω a * X i.val ω b l +
                X i.val ω a l * e i.val ω b) := by
                rw [Finset.mul_sum]
      _ = systemSigmaHatCrossWeight
            (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b l := by
                rw [systemSigmaHatCrossWeight]
                simp only [Fintype.card_fin]
  exact BoundedInProbability.of_tendstoInMeasure_const hWeight

omit [Fintype q] [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq q]
  [DecidableEq m] in
/-- Scalar WLLN bridge for the residual-covariance quadratic weights in Hansen
Theorem 11.3. -/
theorem systemSigmaHatQuadraticWeight_boundedInProbability_of_wlln
    {X : ℕ → Ω → Matrix m k ℝ}
    (a b : m) (l r : k)
    (hint : Integrable (fun ω => X 0 ω a l * X 0 ω b r) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => X i ω a l * X i ω b r)))
    (hident : ∀ i,
      IdentDistrib (fun ω => X i ω a l * X i ω b r)
        (fun ω => X 0 ω a l * X 0 ω b r) μ μ) :
    BoundedInProbability μ
      (fun n ω =>
        systemSigmaHatQuadraticWeight
          (fun i : Fin n => X i.val ω) a b l r) := by
  let W : ℕ → Ω → ℝ := fun i ω => X i ω a l * X i ω b r
  have hWLLN : TendstoInMeasure μ
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, W i ω)
      atTop (fun _ => μ[W 0]) :=
    tendstoInMeasure_wlln W hint hindep hident
  have hWeight : TendstoInMeasure μ
      (fun n ω =>
        systemSigmaHatQuadraticWeight
          (fun i : Fin n => X i.val ω) a b l r)
      atTop (fun _ => μ[W 0]) := by
    refine hWLLN.congr_left (fun n => ae_of_all μ (fun ω => ?_))
    have hsum :
        (∑ i : Fin n, X i.val ω a l * X i.val ω b r) =
          ∑ i ∈ Finset.range n, X i ω a l * X i ω b r :=
      Fin.sum_univ_eq_sum_range
        (fun i => X i ω a l * X i ω b r) n
    calc
      (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, W i ω)
          = (n : ℝ)⁻¹ * ∑ i : Fin n, X i.val ω a l * X i.val ω b r := by
                rw [← hsum]
                simp [smul_eq_mul]
      _ = ∑ i : Fin n, (n : ℝ)⁻¹ * (X i.val ω a l * X i.val ω b r) := by
                rw [Finset.mul_sum]
      _ = systemSigmaHatQuadraticWeight
            (fun i : Fin n => X i.val ω) a b l r := by
                rw [systemSigmaHatQuadraticWeight]
                simp only [Fintype.card_fin]
  exact BoundedInProbability.of_tendstoInMeasure_const hWeight

omit [Fintype q] [DecidableEq q] [DecidableEq m] [IsProbabilityMeasure μ] in
/-- Coefficient consistency plus bounded empirical residual-covariance weights
imply Hansen Theorem 11.3's feasible residual-covariance substitution premise. -/
theorem systemSigmaHatStarObs_sub_tendstoInMeasure_zero_of_beta_bounded_weights
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (_hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hBeta : TendstoInMeasure μ
      (fun n ω =>
        systemLeastSquaresBetaStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω))
      atTop (fun _ => β))
    (hCrossWeight : ∀ a b : m, ∀ l : k,
      BoundedInProbability μ
        (fun n ω =>
          systemSigmaHatCrossWeight
            (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b l))
    (hQuadraticWeight : ∀ a b : m, ∀ l r : k,
      BoundedInProbability μ
        (fun n ω =>
          systemSigmaHatQuadraticWeight
            (fun i : Fin n => X i.val ω) a b l r))
    (hdecomp : ∀ n ω a b,
      (systemSigmaHatStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) -
        systemSigmaHat (fun i : Fin n => e i.val ω)) a b =
        -∑ l : k,
          (systemLeastSquaresBetaStarObs
              (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) - β) l *
            systemSigmaHatCrossWeight
              (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b l +
          ∑ l : k, ∑ r : k,
            (systemLeastSquaresBetaStarObs
                (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) - β) l *
              (systemLeastSquaresBetaStarObs
                (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) - β) r *
              systemSigmaHatQuadraticWeight
                (fun i : Fin n => X i.val ω) a b l r) :
    TendstoInMeasure μ
      (fun n ω =>
        systemSigmaHatStarObs
            (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) -
          systemSigmaHat (fun i : Fin n => e i.val ω))
      atTop (fun _ => 0) := by
  classical
  let βhat : ℕ → Ω → k → ℝ := fun n ω =>
    systemLeastSquaresBetaStarObs
      (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω)
  let r : ℕ → Ω → k → ℝ := fun n ω => βhat n ω - β
  have hr : ∀ l : k, TendstoInMeasure μ (fun n ω => r n ω l) atTop (fun _ => 0) := by
    intro l
    have hl := TendstoInMeasure.pi_apply hBeta l
    simpa [r, βhat, Pi.sub_apply] using TendstoInMeasure.sub_limit_zero_real hl
  refine tendstoInMeasure_pi (μ := μ) (fun a => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun b => ?_)
  let cross : ℕ → Ω → ℝ := fun n ω =>
    ∑ l : k,
      r n ω l *
        systemSigmaHatCrossWeight
          (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b l
  let quad : ℕ → Ω → ℝ := fun n ω =>
    ∑ l : k, ∑ s : k,
      r n ω l * r n ω s *
        systemSigmaHatQuadraticWeight
          (fun i : Fin n => X i.val ω) a b l s
  have hcross : TendstoInMeasure μ cross atTop (fun _ => 0) := by
    have hL : ∀ l ∈ (Finset.univ : Finset k),
        TendstoInMeasure μ
          (fun n ω =>
            r n ω l *
              systemSigmaHatCrossWeight
                (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b l)
          atTop (fun _ => 0) := by
      intro l _
      exact TendstoInMeasure.mul_boundedInProbability (hr l) (hCrossWeight a b l)
    simpa [cross] using tendstoInMeasure_finset_sum_zero_real (μ := μ)
      (s := (Finset.univ : Finset k))
      (X := fun l n ω =>
        r n ω l *
          systemSigmaHatCrossWeight
            (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b l)
      hL
  have hquad : TendstoInMeasure μ quad atTop (fun _ => 0) := by
    have hL : ∀ l ∈ (Finset.univ : Finset k),
        TendstoInMeasure μ
          (fun n ω => ∑ s : k,
            r n ω l * r n ω s *
              systemSigmaHatQuadraticWeight
                (fun i : Fin n => X i.val ω) a b l s)
          atTop (fun _ => 0) := by
      intro l _
      have hS : ∀ s ∈ (Finset.univ : Finset k),
          TendstoInMeasure μ
            (fun n ω =>
              r n ω l * r n ω s *
                systemSigmaHatQuadraticWeight
                  (fun i : Fin n => X i.val ω) a b l s)
            atTop (fun _ => 0) := by
        intro s _
        have hprod := TendstoInMeasure.mul_zero_real (hr l) (hr s)
        exact TendstoInMeasure.mul_boundedInProbability hprod
          (hQuadraticWeight a b l s)
      simpa using tendstoInMeasure_finset_sum_zero_real (μ := μ)
        (s := (Finset.univ : Finset k))
        (X := fun s n ω =>
          r n ω l * r n ω s *
            systemSigmaHatQuadraticWeight
              (fun i : Fin n => X i.val ω) a b l s)
        hS
    simpa [quad] using tendstoInMeasure_finset_sum_zero_real (μ := μ)
      (s := (Finset.univ : Finset k))
      (X := fun l n ω => ∑ s : k,
        r n ω l * r n ω s *
          systemSigmaHatQuadraticWeight
            (fun i : Fin n => X i.val ω) a b l s)
      hL
  have hformula : TendstoInMeasure μ (fun n ω => -cross n ω + quad n ω)
      atTop (fun _ => 0) :=
    TendstoInMeasure.add_zero_real (TendstoInMeasure.neg_zero_real hcross) hquad
  refine hformula.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  symm
  simpa [cross, quad, r, βhat] using hdecomp n ω a b

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Coefficient consistency plus scalar WLLNs for residual-covariance weights
imply Hansen Theorem 11.3's feasible residual-covariance substitution premise. -/
theorem systemSigmaHatStarObs_sub_tendstoInMeasure_zero_of_beta_weight_wlln
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hBeta : TendstoInMeasure μ
      (fun n ω =>
        systemLeastSquaresBetaStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω))
      atTop (fun _ => β))
    (hdecomp : ∀ n ω a b,
      (systemSigmaHatStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) -
        systemSigmaHat (fun i : Fin n => e i.val ω)) a b =
        -∑ l : k,
          (systemLeastSquaresBetaStarObs
              (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) - β) l *
            systemSigmaHatCrossWeight
              (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω) a b l +
          ∑ l : k, ∑ r : k,
            (systemLeastSquaresBetaStarObs
                (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) - β) l *
              (systemLeastSquaresBetaStarObs
                (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) - β) r *
              systemSigmaHatQuadraticWeight
                (fun i : Fin n => X i.val ω) a b l r)
    (hCross_int : ∀ a b : m, ∀ l : k,
      Integrable (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ)
    (hCross_indep : ∀ a b : m, ∀ l : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => e i ω a * X i ω b l + X i ω a l * e i ω b)))
    (hCross_ident : ∀ a b : m, ∀ l : k, ∀ i,
      IdentDistrib
        (fun ω => e i ω a * X i ω b l + X i ω a l * e i ω b)
        (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ μ)
    (hQuadratic_int : ∀ a b : m, ∀ l r : k,
      Integrable (fun ω => X 0 ω a l * X 0 ω b r) μ)
    (hQuadratic_indep : ∀ a b : m, ∀ l r : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => X i ω a l * X i ω b r)))
    (hQuadratic_ident : ∀ a b : m, ∀ l r : k, ∀ i,
      IdentDistrib (fun ω => X i ω a l * X i ω b r)
        (fun ω => X 0 ω a l * X 0 ω b r) μ μ) :
    TendstoInMeasure μ
      (fun n ω =>
        systemSigmaHatStarObs
            (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) -
          systemSigmaHat (fun i : Fin n => e i.val ω))
      atTop (fun _ => 0) :=
  systemSigmaHatStarObs_sub_tendstoInMeasure_zero_of_beta_bounded_weights
    (μ := μ) (X := X) (e := e) (Y := Y) hmodel hBeta
    (fun a b l =>
      systemSigmaHatCrossWeight_boundedInProbability_of_wlln
        (μ := μ) (X := X) (e := e) a b l
        (hCross_int a b l) (hCross_indep a b l) (hCross_ident a b l))
    (fun a b l r =>
      systemSigmaHatQuadraticWeight_boundedInProbability_of_wlln
        (μ := μ) (X := X) a b l r
        (hQuadratic_int a b l r) (hQuadratic_indep a b l r)
        (hQuadratic_ident a b l r))
    hdecomp

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- Coefficient consistency plus scalar WLLNs for residual-covariance weights
imply the feasible residual-covariance substitution premise, with the
finite-sample decomposition discharged from the system linear model. -/
theorem systemSigmaHatStarObs_sub_tendstoInMeasure_zero_of_beta_weight_wlln_of_linear_model
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hBeta : TendstoInMeasure μ
      (fun n ω =>
        systemLeastSquaresBetaStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω))
      atTop (fun _ => β))
    (hCross_int : ∀ a b : m, ∀ l : k,
      Integrable (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ)
    (hCross_indep : ∀ a b : m, ∀ l : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => e i ω a * X i ω b l + X i ω a l * e i ω b)))
    (hCross_ident : ∀ a b : m, ∀ l : k, ∀ i,
      IdentDistrib
        (fun ω => e i ω a * X i ω b l + X i ω a l * e i ω b)
        (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ μ)
    (hQuadratic_int : ∀ a b : m, ∀ l r : k,
      Integrable (fun ω => X 0 ω a l * X 0 ω b r) μ)
    (hQuadratic_indep : ∀ a b : m, ∀ l r : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => X i ω a l * X i ω b r)))
    (hQuadratic_ident : ∀ a b : m, ∀ l r : k, ∀ i,
      IdentDistrib (fun ω => X i ω a l * X i ω b r)
        (fun ω => X 0 ω a l * X 0 ω b r) μ μ) :
    TendstoInMeasure μ
      (fun n ω =>
        systemSigmaHatStarObs
            (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) -
          systemSigmaHat (fun i : Fin n => e i.val ω))
      atTop (fun _ => 0) :=
  systemSigmaHatStarObs_sub_tendstoInMeasure_zero_of_beta_weight_wlln
    (μ := μ) (X := X) (e := e) (Y := Y) hmodel hBeta
    (fun n ω a b => by
      simpa using
        systemSigmaHatStarObs_sub_apply_eq_scalar_weights
          (X := fun i : Fin n => X i.val ω)
          (e := fun i : Fin n => e i.val ω)
          (Y := fun i : Fin n => Y i.val ω)
          (β := β)
          (fun i j => hmodel i.val ω j) a b)
    hCross_int hCross_indep hCross_ident
    hQuadratic_int hQuadratic_indep hQuadratic_ident

omit [DecidableEq k] [DecidableEq m] in
/-- **Fixed-covariance homoskedastic system-middle WLLN for Hansen Chapter 11.**

For a fixed error covariance matrix `Σ`, the normalized middle matrix
`n⁻¹∑ Xᵢ'ΣXᵢ` converges to its population counterpart under the Banach-valued
WLLN hypotheses. -/
theorem systemHomoskedasticMiddle_fixed_tendstoInMeasure
    {X : ℕ → Ω → Matrix m k ℝ} (Sigma : Matrix m m ℝ)
    (hint : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma)))
    (hident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ μ) :
    TendstoInMeasure μ
      (fun n ω => systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) Sigma)
      atTop (fun _ => μ[fun ω => systemMiddleTerm (X 0 ω) Sigma]) := by
  have h :
      TendstoInMeasure μ
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
          (∑ i ∈ Finset.range n, systemMiddleTerm (X i ω) Sigma))
        atTop (fun _ => μ[fun ω => systemMiddleTerm (X 0 ω) Sigma]) :=
    tendstoInMeasure_wlln
      (μ := μ) (fun i ω => systemMiddleTerm (X i ω) Sigma)
      hint hindep hident
  have hfun_eq :
      (fun n ω => systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) Sigma) =
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
          (∑ i ∈ Finset.range n, systemMiddleTerm (X i ω) Sigma)) := by
    funext n ω
    have hsum :
        (∑ i : Fin n, systemMiddleTerm (X i.val ω) Sigma) =
          ∑ i ∈ Finset.range n, systemMiddleTerm (X i ω) Sigma :=
      Fin.sum_univ_eq_sum_range (fun i => systemMiddleTerm (X i ω) Sigma) n
    simp only [systemHomoskedasticMiddle, Fintype.card_fin]
    rw [hsum]
  rw [hfun_eq]
  exact h

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq m] in
/-- Measurability of the fixed-covariance homoskedastic system middle matrix. -/
theorem systemHomoskedasticMiddle_fixed_aestronglyMeasurable
    {X : ℕ → Ω → Matrix m k ℝ} (Sigma : Matrix m m ℝ)
    (hint : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ μ) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω => systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) Sigma) μ := by
  simp only [systemHomoskedasticMiddle]
  refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card (Fin n) : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact ((hident i.val).integrable_iff.mpr hint).aestronglyMeasurable

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq m] in
/-- Estimated-covariance perturbation target for Hansen's homoskedastic system
middle matrix.

If replacing a fixed covariance matrix by an estimated matrix changes
`n⁻¹∑ Xᵢ'ΣXᵢ` by `o_p(1)`, then the estimated middle has the same probability
limit as the fixed-covariance middle. -/
theorem systemHomoskedasticMiddle_feasible_tendstoInMeasure_of_substitution
    {X : ℕ → Ω → Matrix m k ℝ} {Sigma : Matrix m m ℝ}
    {SigmaHat : ℕ → Ω → Matrix m m ℝ} {Omega : Matrix k k ℝ}
    (hfixed : TendstoInMeasure μ
      (fun n ω => systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) Sigma)
      atTop (fun _ => Omega))
    (hsub : TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) (SigmaHat n ω) -
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) Sigma)
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) (SigmaHat n ω))
      atTop (fun _ => Omega) :=
  TendstoInMeasure.of_sub_tendsto_zero_matrix hsub hfixed

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq m] in
/-- Bounded empirical design weights turn covariance-matrix consistency into
Hansen's homoskedastic system-middle substitution step.

This is the reusable perturbation engine behind feasible SUR covariance:
`Σ̂ ->p Σ` and `n⁻¹∑ Xᵢa Xᵢb = Oₚ(1)` for every coordinate imply
`n⁻¹∑ Xᵢ'(Σ̂-Σ)Xᵢ = oₚ(1)`. -/
theorem systemHomoskedasticMiddle_sub_tendstoInMeasure_zero_of_covariance_bounded_weights
    {X : ℕ → Ω → Matrix m k ℝ}
    {SigmaHat : ℕ → Ω → Matrix m m ℝ} {Sigma : Matrix m m ℝ}
    (hSigma : TendstoInMeasure μ SigmaHat atTop (fun _ => Sigma))
    (hWeight : ∀ a b : m, ∀ c d : k,
      BoundedInProbability μ
        (fun n ω =>
          systemHomoskedasticMiddleWeight
            (fun i : Fin n => X i.val ω) a b c d)) :
    TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) (SigmaHat n ω) -
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) Sigma)
      atTop (fun _ => 0) := by
  refine tendstoInMeasure_pi (μ := μ) (fun c => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun d => ?_)
  have hOuter : ∀ a ∈ (Finset.univ : Finset m),
      TendstoInMeasure μ
        (fun n ω => ∑ b : m,
          (SigmaHat n ω a b - Sigma a b) *
            systemHomoskedasticMiddleWeight
              (fun i : Fin n => X i.val ω) a b c d)
        atTop (fun _ => 0) := by
    intro a _
    have hInner : ∀ b ∈ (Finset.univ : Finset m),
        TendstoInMeasure μ
          (fun n ω =>
            (SigmaHat n ω a b - Sigma a b) *
              systemHomoskedasticMiddleWeight
                (fun i : Fin n => X i.val ω) a b c d)
          atTop (fun _ => 0) := by
      intro b _
      have hSigma_ab : TendstoInMeasure μ
          (fun n ω => SigmaHat n ω a b) atTop (fun _ => Sigma a b) := by
        simpa using TendstoInMeasure.pi_apply
          (TendstoInMeasure.pi_apply hSigma a) b
      have hdiff_ab : TendstoInMeasure μ
          (fun n ω => SigmaHat n ω a b - Sigma a b)
          atTop (fun _ => 0) :=
        TendstoInMeasure.sub_limit_zero_real hSigma_ab
      exact TendstoInMeasure.mul_boundedInProbability hdiff_ab (hWeight a b c d)
    simpa using tendstoInMeasure_finset_sum_zero_real (μ := μ)
      (s := (Finset.univ : Finset m))
      (X := fun b n ω =>
        (SigmaHat n ω a b - Sigma a b) *
          systemHomoskedasticMiddleWeight
            (fun i : Fin n => X i.val ω) a b c d)
      hInner
  have hsum := tendstoInMeasure_finset_sum_zero_real (μ := μ)
    (s := (Finset.univ : Finset m))
    (X := fun a n ω => ∑ b : m,
      (SigmaHat n ω a b - Sigma a b) *
        systemHomoskedasticMiddleWeight
          (fun i : Fin n => X i.val ω) a b c d)
    hOuter
  refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  exact (systemHomoskedasticMiddle_sub_apply_eq_sum_weight
    (fun i : Fin n => X i.val ω) (SigmaHat n ω) Sigma c d).symm

omit [IsProbabilityMeasure μ] [DecidableEq k] [DecidableEq m] in
/-- Covariance consistency and bounded empirical design weights discharge the
homoskedastic system-middle substitution premise used by the CMT wrappers. -/
theorem systemHomoskedasticMiddle_feasible_tendstoInMeasure_of_covariance_bounded_weights
    {X : ℕ → Ω → Matrix m k ℝ} {Sigma : Matrix m m ℝ}
    {SigmaHat : ℕ → Ω → Matrix m m ℝ} {Omega : Matrix k k ℝ}
    (hfixed : TendstoInMeasure μ
      (fun n ω => systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) Sigma)
      atTop (fun _ => Omega))
    (hSigma : TendstoInMeasure μ SigmaHat atTop (fun _ => Sigma))
    (hWeight : ∀ a b : m, ∀ c d : k,
      BoundedInProbability μ
        (fun n ω =>
          systemHomoskedasticMiddleWeight
            (fun i : Fin n => X i.val ω) a b c d)) :
    TendstoInMeasure μ
      (fun n ω => systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) (SigmaHat n ω))
      atTop (fun _ => Omega) :=
  systemHomoskedasticMiddle_feasible_tendstoInMeasure_of_substitution hfixed
    (systemHomoskedasticMiddle_sub_tendstoInMeasure_zero_of_covariance_bounded_weights
      (μ := μ) (X := X) (SigmaHat := SigmaHat) (Sigma := Sigma) hSigma hWeight)

omit [Fintype q] [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq q] [DecidableEq m] in
/-- Scalar WLLN bridge for the empirical design weights in Hansen's
homoskedastic system-middle perturbation. -/
theorem systemHomoskedasticMiddleWeight_boundedInProbability_of_wlln
    {X : ℕ → Ω → Matrix m k ℝ} (a b : m) (c d : k)
    (hint : Integrable (fun ω => X 0 ω a c * X 0 ω b d) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => X i ω a c * X i ω b d)))
    (hident : ∀ i,
      IdentDistrib (fun ω => X i ω a c * X i ω b d)
        (fun ω => X 0 ω a c * X 0 ω b d) μ μ) :
    BoundedInProbability μ
      (fun n ω =>
        systemHomoskedasticMiddleWeight
          (fun i : Fin n => X i.val ω) a b c d) := by
  have hWeight :
      TendstoInMeasure μ
        (fun n ω =>
          systemHomoskedasticMiddleWeight
            (fun i : Fin n => X i.val ω) a b c d)
        atTop (fun _ => μ[fun ω => X 0 ω a c * X 0 ω b d]) := by
    have hraw :
        TendstoInMeasure μ
          (fun (n : ℕ) ω =>
            (n : ℝ)⁻¹ •
              (∑ i ∈ Finset.range n, X i ω a c * X i ω b d))
          atTop (fun _ => μ[fun ω => X 0 ω a c * X 0 ω b d]) :=
      tendstoInMeasure_wlln
        (μ := μ) (fun i ω => X i ω a c * X i ω b d) hint hindep hident
    have hfun_eq :
        (fun n ω =>
          systemHomoskedasticMiddleWeight
            (fun i : Fin n => X i.val ω) a b c d) =
          (fun (n : ℕ) ω =>
            (n : ℝ)⁻¹ •
              (∑ i ∈ Finset.range n, X i ω a c * X i ω b d)) := by
      funext n ω
      have hsum :
          (∑ i : Fin n, X i.val ω a c * X i.val ω b d) =
            ∑ i ∈ Finset.range n, X i ω a c * X i ω b d :=
        Fin.sum_univ_eq_sum_range (fun i => X i ω a c * X i ω b d) n
      simp only [systemHomoskedasticMiddleWeight, Fintype.card_fin]
      rw [hsum]
    rw [hfun_eq]
    exact hraw
  exact BoundedInProbability.of_tendstoInMeasure_const hWeight

namespace SystemCovarianceTheorem113Conditions

omit [DecidableEq m] in
/-- Constructor for Hansen Theorem 11.3 from residual and covariance
perturbation bounds.

`SystemAssumption72` supplies the Gram WLLN and the true-error robust middle
WLLN. The remaining robust input is the feasible-residual substitution
`Ω̂(ê)-Ω̂(e)=oₚ(1)`. The homoskedastic input is split into a fixed-covariance
WLLN plus consistency of `Σ̂`, with bounded empirical design weights handling
the covariance substitution. -/
theorem of_substitution_and_covariance_bounded_weights
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    (h72 : SystemAssumption72 μ X e) (Sigma : Matrix m m ℝ)
    (hrobust_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hrobust_sub : TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω)) -
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (fun i : Fin n => e i.val ω))
      atTop (fun _ => 0))
    (hfixed_int : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hfixed_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma)))
    (hfixed_ident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ μ)
    (hhomoskedastic_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
            (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hSigma : TendstoInMeasure μ
      (fun n ω =>
        systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω))
      atTop (fun _ => Sigma))
    (hWeight : ∀ a b : m, ∀ c d : k,
      BoundedInProbability μ
        (fun n ω =>
          systemHomoskedasticMiddleWeight
            (fun i : Fin n => X i.val ω) a b c d)) :
    SystemCovarianceTheorem113Conditions μ X e Y
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma]) where
  assumption72 := h72
  robust_middle_measurable := hrobust_meas
  robust_middle_consistent :=
    TendstoInMeasure.of_sub_tendsto_zero_matrix
      hrobust_sub
      (SystemAssumption72.robustMiddle_ideal_tendstoInMeasure h72)
  homoskedastic_middle_measurable := hhomoskedastic_meas
  homoskedastic_middle_consistent :=
    systemHomoskedasticMiddle_feasible_tendstoInMeasure_of_covariance_bounded_weights
      (μ := μ) (X := X) (Sigma := Sigma)
      (SigmaHat := fun n ω =>
        systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω))
      (Omega := μ[fun ω => systemMiddleTerm (X 0 ω) Sigma])
      (systemHomoskedasticMiddle_fixed_tendstoInMeasure
        (μ := μ) (X := X) Sigma hfixed_int hfixed_indep hfixed_ident)
      hSigma hWeight

omit [DecidableEq m] in
/-- Variant of `of_substitution_and_covariance_bounded_weights` whose
homoskedastic design-weight boundedness is derived from scalar WLLN premises. -/
theorem of_substitution_and_covariance_weight_wlln
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    (h72 : SystemAssumption72 μ X e) (Sigma : Matrix m m ℝ)
    (hrobust_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hrobust_sub : TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω)) -
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (fun i : Fin n => e i.val ω))
      atTop (fun _ => 0))
    (hfixed_int : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hfixed_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma)))
    (hfixed_ident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ μ)
    (hhomoskedastic_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
            (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hSigma : TendstoInMeasure μ
      (fun n ω =>
        systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω))
      atTop (fun _ => Sigma))
    (hWeight_int : ∀ a b : m, ∀ c d : k,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d) μ)
    (hWeight_indep : ∀ a b : m, ∀ c d : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => X i ω a c * X i ω b d)))
    (hWeight_ident : ∀ a b : m, ∀ c d : k, ∀ i,
      IdentDistrib (fun ω => X i ω a c * X i ω b d)
        (fun ω => X 0 ω a c * X 0 ω b d) μ μ) :
    SystemCovarianceTheorem113Conditions μ X e Y
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma]) :=
  of_substitution_and_covariance_bounded_weights
    (μ := μ) (X := X) (e := e) (Y := Y) h72 Sigma
    hrobust_meas hrobust_sub
    hfixed_int hfixed_indep hfixed_ident
    hhomoskedastic_meas hSigma
    (fun a b c d =>
      systemHomoskedasticMiddleWeight_boundedInProbability_of_wlln
        (μ := μ) (X := X) a b c d
        (hWeight_int a b c d) (hWeight_indep a b c d)
        (hWeight_ident a b c d))

omit [DecidableEq m] in
/-- Constructor for Hansen Theorem 11.3 from Assumption 7.2, coefficient
consistency, and scalar residual-perturbation WLLNs.

This is the theorem-facing route that derives both displayed middle
consistencies. `SystemAssumption72` supplies the ideal robust WLLN and the
coefficient consistency used in the feasible-residual perturbation. The
cross/quadratic scalar WLLNs control the robust residual substitution, while
`Σ̂ ->p Σ` plus scalar design-weight WLLNs control the homoskedastic middle. -/
theorem of_beta_weight_wlln_and_covariance_weight_wlln
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h72 : SystemAssumption72 μ X e) (Sigma : Matrix m m ℝ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hbeta_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrobust_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hCross_int : ∀ a b : m, ∀ c d l : k,
      Integrable
        (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
          X 0 ω a c * X 0 ω b d) μ)
    (hCross_indep : ∀ a b : m, ∀ c d l : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => (e i ω a * X i ω b l + X i ω a l * e i ω b) *
          X i ω a c * X i ω b d)))
    (hCross_ident : ∀ a b : m, ∀ c d l : k, ∀ i,
      IdentDistrib
        (fun ω => (e i ω a * X i ω b l + X i ω a l * e i ω b) *
          X i ω a c * X i ω b d)
        (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
          X 0 ω a c * X 0 ω b d) μ μ)
    (hQuadratic_int : ∀ a b : m, ∀ c d l r : k,
      Integrable (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ)
    (hQuadratic_indep : ∀ a b : m, ∀ c d l r : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => X i ω a l * X i ω b r * X i ω a c * X i ω b d)))
    (hQuadratic_ident : ∀ a b : m, ∀ c d l r : k, ∀ i,
      IdentDistrib
        (fun ω => X i ω a l * X i ω b r * X i ω a c * X i ω b d)
        (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ μ)
    (hfixed_int : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hfixed_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma)))
    (hfixed_ident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ μ)
    (hhomoskedastic_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
            (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hSigma : TendstoInMeasure μ
      (fun n ω =>
        systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω))
      atTop (fun _ => Sigma))
    (hWeight_int : ∀ a b : m, ∀ c d : k,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d) μ)
    (hWeight_indep : ∀ a b : m, ∀ c d : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => X i ω a c * X i ω b d)))
    (hWeight_ident : ∀ a b : m, ∀ c d : k, ∀ i,
      IdentDistrib (fun ω => X i ω a c * X i ω b d)
        (fun ω => X 0 ω a c * X 0 ω b d) μ μ) :
    SystemCovarianceTheorem113Conditions μ X e Y
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma]) :=
  of_substitution_and_covariance_weight_wlln
    (μ := μ) (X := X) (e := e) (Y := Y) h72 Sigma hrobust_meas
    (systemRobustMiddle_sub_tendstoInMeasure_zero_of_beta_weight_wlln_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) hmodel
      (systemLeastSquaresBetaStarObs_tendstoInMeasure_beta
        (μ := μ) (X := X) (e := e) (Y := Y)
        h72.toSystemScoreCLTConditions β hmodel hbeta_meas)
      hCross_int hCross_indep hCross_ident
      hQuadratic_int hQuadratic_indep hQuadratic_ident)
    hfixed_int hfixed_indep hfixed_ident hhomoskedastic_meas hSigma
    hWeight_int hWeight_indep hWeight_ident

omit [DecidableEq m] in
/-- Joint observation iid constructor for Hansen Theorem 11.3.

This theorem-facing route derives the scalar independence and identical-distribution
fields for the robust cross weights, robust quadratic weights, homoskedastic
design weights, and fixed-`Σ` homoskedastic middle from iid rows `(Xᵢ,eᵢ)`.
The remaining analytic premises are the displayed mixed-moment integrability
fields and consistency of the feasible residual covariance; the finite-sample
residual algebra is discharged by the scalar expansion theorem above. -/
theorem of_beta_weight_wlln_and_covariance_joint_iid
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h72 : SystemAssumption72 μ X e) (Sigma : Matrix m m ℝ)
    (hjoint : iIndepFun (fun i ω => (X i ω, e i ω)) μ)
    (hident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω))
        (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hbeta_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrobust_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hCross_int : ∀ a b : m, ∀ c d l : k,
      Integrable
        (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
          X 0 ω a c * X 0 ω b d) μ)
    (hQuadratic_int : ∀ a b : m, ∀ c d l r : k,
      Integrable (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ)
    (hfixed_int : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hhomoskedastic_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
            (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hSigma : TendstoInMeasure μ
      (fun n ω =>
        systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω))
      atTop (fun _ => Sigma))
    (hWeight_int : ∀ a b : m, ∀ c d : k,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d) μ) :
    SystemCovarianceTheorem113Conditions μ X e Y
      (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma]) :=
  of_beta_weight_wlln_and_covariance_weight_wlln
    (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
    h72 Sigma hmodel hbeta_meas hrobust_meas
    hCross_int
    (fun a b c d l =>
      let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row =>
        (row.2 a * row.1 b l + row.1 a l * row.2 b) * row.1 a c * row.1 b d
      have hind : iIndepFun (fun i ω => f (X i ω, e i ω)) μ := by
        simpa [f, Function.comp_def] using
          hjoint.comp (fun _ => f)
            (fun _ => measurable_system_joint_cross_weight (m := m) a b c d l)
      fun i j hij => hind.indepFun hij)
    (fun a b c d l i =>
      let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row =>
        (row.2 a * row.1 b l + row.1 a l * row.2 b) * row.1 a c * row.1 b d
      have hi := (hident i).comp
        (measurable_system_joint_cross_weight (m := m) a b c d l)
      by
        simpa [f, Function.comp_def] using hi)
    hQuadratic_int
    (fun a b c d l r =>
      let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row =>
        row.1 a l * row.1 b r * row.1 a c * row.1 b d
      have hind : iIndepFun (fun i ω => f (X i ω, e i ω)) μ := by
        simpa [f, Function.comp_def] using
          hjoint.comp (fun _ => f)
            (fun _ => measurable_system_joint_quadratic_weight (m := m) a b c d l r)
      fun i j hij => hind.indepFun hij)
    (fun a b c d l r i =>
      let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row =>
        row.1 a l * row.1 b r * row.1 a c * row.1 b d
      have hi := (hident i).comp
        (measurable_system_joint_quadratic_weight (m := m) a b c d l r)
      by
        simpa [f, Function.comp_def] using hi)
    hfixed_int
    (by
      have hind : iIndepFun (fun i ω => systemMiddleTerm (X i ω) Sigma) μ := by
        simpa [Function.comp_def] using
          hjoint.comp (fun _ => fun row : Matrix m k ℝ × (m → ℝ) =>
            systemMiddleTerm row.1 Sigma)
            (fun _ => measurable_system_joint_middle (m := m) Sigma)
      exact fun i j hij => hind.indepFun hij)
    (fun i => by
      have hi := (hident i).comp
        (measurable_system_joint_middle (m := m) Sigma)
      simpa [Function.comp_def] using hi)
    hhomoskedastic_meas hSigma hWeight_int
    (fun a b c d =>
      let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row => row.1 a c * row.1 b d
      have hind : iIndepFun (fun i ω => f (X i ω, e i ω)) μ := by
        simpa [f, Function.comp_def] using
          hjoint.comp (fun _ => f)
            (fun _ => measurable_system_joint_design_weight (m := m) a b c d)
      fun i j hij => hind.indepFun hij)
    (fun a b c d i =>
      let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row => row.1 a c * row.1 b d
      have hi := (hident i).comp
        (measurable_system_joint_design_weight (m := m) a b c d)
      by
        simpa [f, Function.comp_def] using hi)

omit [DecidableEq m] in
/-- Constructor for Hansen Theorem 11.3 that derives feasible residual
covariance consistency from true-error covariance and residual-substitution
WLLNs.

Compared with `of_beta_weight_wlln_and_covariance_weight_wlln`, this wrapper no
longer takes `Σ̂(ê) ->p Σ` as a primitive. The covariance target is the literal
true-error covariance `E[eᵢeᵢ']`, and the feasible `systemSigmaHatStarObs`
consistency is assembled internally from the true-error outer-product WLLN plus
the residual-covariance cross/quadratic WLLNs. -/
theorem of_beta_weight_wlln_and_true_error_covariance_weight_wlln
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h72 : SystemAssumption72 μ X e)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hbeta_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrobust_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hRobustCross_int : ∀ a b : m, ∀ c d l : k,
      Integrable
        (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
          X 0 ω a c * X 0 ω b d) μ)
    (hRobustCross_indep : ∀ a b : m, ∀ c d l : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => (e i ω a * X i ω b l + X i ω a l * e i ω b) *
          X i ω a c * X i ω b d)))
    (hRobustCross_ident : ∀ a b : m, ∀ c d l : k, ∀ i,
      IdentDistrib
        (fun ω => (e i ω a * X i ω b l + X i ω a l * e i ω b) *
          X i ω a c * X i ω b d)
        (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
          X 0 ω a c * X 0 ω b d) μ μ)
    (hRobustQuadratic_int : ∀ a b : m, ∀ c d l r : k,
      Integrable (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ)
    (hRobustQuadratic_indep : ∀ a b : m, ∀ c d l r : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => X i ω a l * X i ω b r * X i ω a c * X i ω b d)))
    (hRobustQuadratic_ident : ∀ a b : m, ∀ c d l r : k, ∀ i,
      IdentDistrib
        (fun ω => X i ω a l * X i ω b r * X i ω a c * X i ω b d)
        (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ μ)
    (hErrorOuter_int : Integrable (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ)
    (hErrorOuter_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => Matrix.vecMulVec (e i ω) (e i ω))))
    (hErrorOuter_ident : ∀ i,
      IdentDistrib (fun ω => Matrix.vecMulVec (e i ω) (e i ω))
        (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ μ)
    (hSigmaCross_int : ∀ a b : m, ∀ l : k,
      Integrable (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ)
    (hSigmaCross_indep : ∀ a b : m, ∀ l : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => e i ω a * X i ω b l + X i ω a l * e i ω b)))
    (hSigmaCross_ident : ∀ a b : m, ∀ l : k, ∀ i,
      IdentDistrib
        (fun ω => e i ω a * X i ω b l + X i ω a l * e i ω b)
        (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ μ)
    (hSigmaQuadratic_int : ∀ a b : m, ∀ l r : k,
      Integrable (fun ω => X 0 ω a l * X 0 ω b r) μ)
    (hSigmaQuadratic_indep : ∀ a b : m, ∀ l r : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => X i ω a l * X i ω b r)))
    (hSigmaQuadratic_ident : ∀ a b : m, ∀ l r : k, ∀ i,
      IdentDistrib (fun ω => X i ω a l * X i ω b r)
        (fun ω => X 0 ω a l * X 0 ω b r) μ μ)
    (hfixed_int : Integrable
      (fun ω => systemMiddleTerm (X 0 ω)
        (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)])) μ)
    (hfixed_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω)
        (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)]))))
    (hfixed_ident : ∀ i,
      IdentDistrib
        (fun ω => systemMiddleTerm (X i ω)
          (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)]))
        (fun ω => systemMiddleTerm (X 0 ω)
          (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)])) μ μ)
    (hhomoskedastic_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
            (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hWeight_int : ∀ a b : m, ∀ c d : k,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d) μ)
    (hWeight_indep : ∀ a b : m, ∀ c d : k,
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => X i ω a c * X i ω b d)))
    (hWeight_ident : ∀ a b : m, ∀ c d : k, ∀ i,
      IdentDistrib (fun ω => X i ω a c * X i ω b d)
        (fun ω => X 0 ω a c * X 0 ω b d) μ μ) :
    SystemCovarianceTheorem113Conditions μ X e Y
      (μ[fun ω => systemMiddleTerm (X 0 ω)
        (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)])]) := by
  let Sigma : Matrix m m ℝ := μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)]
  have hBeta : TendstoInMeasure μ
      (fun n ω =>
        systemLeastSquaresBetaStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω))
      atTop (fun _ => β) :=
    systemLeastSquaresBetaStarObs_tendstoInMeasure_beta
      (μ := μ) (X := X) (e := e) (Y := Y)
      h72.toSystemScoreCLTConditions β hmodel hbeta_meas
  have hSigmaIdeal : TendstoInMeasure μ
      (fun n ω => systemSigmaHat (fun i : Fin n => e i.val ω))
      atTop (fun _ => Sigma) := by
    simpa [Sigma] using
      systemSigmaHat_ideal_tendstoInMeasure
        (μ := μ) (e := e)
        hErrorOuter_int hErrorOuter_indep hErrorOuter_ident
  have hSigmaSub : TendstoInMeasure μ
      (fun n ω =>
        systemSigmaHatStarObs
            (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω) -
          systemSigmaHat (fun i : Fin n => e i.val ω))
      atTop (fun _ => 0) :=
    systemSigmaHatStarObs_sub_tendstoInMeasure_zero_of_beta_weight_wlln_of_linear_model
      (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
      hmodel hBeta hSigmaCross_int hSigmaCross_indep hSigmaCross_ident
      hSigmaQuadratic_int hSigmaQuadratic_indep hSigmaQuadratic_ident
  have hSigma : TendstoInMeasure μ
      (fun n ω =>
        systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
          (fun i : Fin n => Y i.val ω))
      atTop (fun _ => Sigma) :=
    systemSigmaHatStarObs_tendstoInMeasure_of_true_error_substitution
      (μ := μ) (X := X) (e := e) (Y := Y) hSigmaIdeal hSigmaSub
  exact of_beta_weight_wlln_and_covariance_weight_wlln
    (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
    h72 Sigma hmodel hbeta_meas hrobust_meas
    hRobustCross_int hRobustCross_indep hRobustCross_ident
    hRobustQuadratic_int hRobustQuadratic_indep hRobustQuadratic_ident
    hfixed_int hfixed_indep hfixed_ident hhomoskedastic_meas hSigma
    hWeight_int hWeight_indep hWeight_ident

omit [DecidableEq m] in
/-- Joint observation iid constructor for Hansen Theorem 11.3 with feasible
residual covariance consistency derived internally.

This derives all independence and identical-distribution fields for the robust
middle, true-error covariance, residual-covariance substitution, homoskedastic
middle, and design-weight WLLNs from iid rows `(Xᵢ,eᵢ)`. Integrability fields
remain explicit here because they encode the exact mixed moments consumed by
the scalar WLLNs. -/
theorem of_beta_weight_wlln_and_true_error_covariance_joint_iid
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h72 : SystemAssumption72 μ X e)
    (hjoint : iIndepFun (fun i ω => (X i ω, e i ω)) μ)
    (hident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω))
        (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hbeta_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrobust_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hRobustCross_int : ∀ a b : m, ∀ c d l : k,
      Integrable
        (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
          X 0 ω a c * X 0 ω b d) μ)
    (hRobustQuadratic_int : ∀ a b : m, ∀ c d l r : k,
      Integrable (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ)
    (hErrorOuter_int : Integrable (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ)
    (hSigmaCross_int : ∀ a b : m, ∀ l : k,
      Integrable (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ)
    (hSigmaQuadratic_int : ∀ a b : m, ∀ l r : k,
      Integrable (fun ω => X 0 ω a l * X 0 ω b r) μ)
    (hfixed_int : Integrable
      (fun ω => systemMiddleTerm (X 0 ω)
        (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)])) μ)
    (hhomoskedastic_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
            (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hWeight_int : ∀ a b : m, ∀ c d : k,
      Integrable (fun ω => X 0 ω a c * X 0 ω b d) μ) :
    SystemCovarianceTheorem113Conditions μ X e Y
      (μ[fun ω => systemMiddleTerm (X 0 ω)
        (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)])]) :=
  of_beta_weight_wlln_and_true_error_covariance_weight_wlln
    (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
    h72 hmodel hbeta_meas hrobust_meas
    hRobustCross_int
    (fun a b c d l =>
      let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row =>
        (row.2 a * row.1 b l + row.1 a l * row.2 b) * row.1 a c * row.1 b d
      have hind : iIndepFun (fun i ω => f (X i ω, e i ω)) μ := by
        simpa [f, Function.comp_def] using
          hjoint.comp (fun _ => f)
            (fun _ => measurable_system_joint_cross_weight (m := m) a b c d l)
      fun i j hij => hind.indepFun hij)
    (fun a b c d l i =>
      let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row =>
        (row.2 a * row.1 b l + row.1 a l * row.2 b) * row.1 a c * row.1 b d
      have hi := (hident i).comp
        (measurable_system_joint_cross_weight (m := m) a b c d l)
      by
        simpa [f, Function.comp_def] using hi)
    hRobustQuadratic_int
    (fun a b c d l r =>
      let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row =>
        row.1 a l * row.1 b r * row.1 a c * row.1 b d
      have hind : iIndepFun (fun i ω => f (X i ω, e i ω)) μ := by
        simpa [f, Function.comp_def] using
          hjoint.comp (fun _ => f)
            (fun _ => measurable_system_joint_quadratic_weight (m := m) a b c d l r)
      fun i j hij => hind.indepFun hij)
    (fun a b c d l r i =>
      let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row =>
        row.1 a l * row.1 b r * row.1 a c * row.1 b d
      have hi := (hident i).comp
        (measurable_system_joint_quadratic_weight (m := m) a b c d l r)
      by
        simpa [f, Function.comp_def] using hi)
    hErrorOuter_int
    (by
      have hind : iIndepFun
          (fun i ω => Matrix.vecMulVec (e i ω) (e i ω)) μ := by
        simpa [Function.comp_def] using
          hjoint.comp (fun _ => fun row : Matrix m k ℝ × (m → ℝ) =>
            Matrix.vecMulVec row.2 row.2)
            (fun _ => measurable_system_joint_error_outer (m := m))
      exact fun i j hij => hind.indepFun hij)
    (fun i => by
      have hi := (hident i).comp
        (measurable_system_joint_error_outer (m := m))
      simpa [Function.comp_def] using hi)
    hSigmaCross_int
    (fun a b l =>
      let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row =>
        row.2 a * row.1 b l + row.1 a l * row.2 b
      have hind : iIndepFun (fun i ω => f (X i ω, e i ω)) μ := by
        simpa [f, Function.comp_def] using
          hjoint.comp (fun _ => f)
            (fun _ => measurable_system_joint_sigma_cross_weight (m := m) a b l)
      fun i j hij => hind.indepFun hij)
    (fun a b l i =>
      let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row =>
        row.2 a * row.1 b l + row.1 a l * row.2 b
      have hi := (hident i).comp
        (measurable_system_joint_sigma_cross_weight (m := m) a b l)
      by
        simpa [f, Function.comp_def] using hi)
    hSigmaQuadratic_int
    (fun a b l r =>
      let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row => row.1 a l * row.1 b r
      have hind : iIndepFun (fun i ω => f (X i ω, e i ω)) μ := by
        simpa [f, Function.comp_def] using
          hjoint.comp (fun _ => f)
            (fun _ => measurable_system_joint_design_weight (m := m) a b l r)
      fun i j hij => hind.indepFun hij)
    (fun a b l r i =>
      let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row => row.1 a l * row.1 b r
      have hi := (hident i).comp
        (measurable_system_joint_design_weight (m := m) a b l r)
      by
        simpa [f, Function.comp_def] using hi)
    hfixed_int
    (by
      have hind : iIndepFun
          (fun i ω => systemMiddleTerm (X i ω)
            (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)])) μ := by
        simpa [Function.comp_def] using
          hjoint.comp (fun _ => fun row : Matrix m k ℝ × (m → ℝ) =>
            systemMiddleTerm row.1 (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)]))
            (fun _ => measurable_system_joint_middle (m := m)
              (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)]))
      exact fun i j hij => hind.indepFun hij)
    (fun i => by
      have hi := (hident i).comp
        (measurable_system_joint_middle (m := m)
          (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)]))
      simpa [Function.comp_def] using hi)
    hhomoskedastic_meas hWeight_int
    (fun a b c d =>
      let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row => row.1 a c * row.1 b d
      have hind : iIndepFun (fun i ω => f (X i ω, e i ω)) μ := by
        simpa [f, Function.comp_def] using
          hjoint.comp (fun _ => f)
            (fun _ => measurable_system_joint_design_weight (m := m) a b c d)
      fun i j hij => hind.indepFun hij)
    (fun a b c d i =>
      let f : Matrix m k ℝ × (m → ℝ) → ℝ := fun row => row.1 a c * row.1 b d
      have hi := (hident i).comp
        (measurable_system_joint_design_weight (m := m) a b c d)
      by
        simpa [f, Function.comp_def] using hi)

omit [DecidableEq m] in
/-- Joint-row Theorem 11.3 constructor with finite design second moment.

This version derives the residual-covariance quadratic integrability, fixed
homoskedastic middle integrability, and homoskedastic design-weight
integrability from `MemLp (X 0) 2 μ`. The robust-middle third/fourth mixed
moments and the residual-covariance cross moments remain explicit because they
are the exact higher mixed moments Hansen's feasible robust covariance proof
uses. -/
theorem of_beta_weight_wlln_and_true_error_covariance_joint_iid_design_memLp
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h72 : SystemAssumption72 μ X e)
    (hjoint : iIndepFun (fun i ω => (X i ω, e i ω)) μ)
    (hident : ∀ i,
      IdentDistrib (fun ω => (X i ω, e i ω))
        (fun ω => (X 0 ω, e 0 ω)) μ μ)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hbeta_meas : ∀ t : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (t : ℝ) •
          (systemLeastSquaresBetaStarObs
            (fun i : Fin t => X i.val ω) (fun i : Fin t => Y i.val ω) - β)) μ)
    (hrobust_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hX_memLp : MemLp (X 0) 2 μ)
    (hRobustCross_int : ∀ a b : m, ∀ c d l : k,
      Integrable
        (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
          X 0 ω a c * X 0 ω b d) μ)
    (hRobustQuadratic_int : ∀ a b : m, ∀ c d l r : k,
      Integrable (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ)
    (hErrorOuter_int : Integrable (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ)
    (hSigmaCross_int : ∀ a b : m, ∀ l : k,
      Integrable (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ)
    (hhomoskedastic_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
            (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ) :
    SystemCovarianceTheorem113Conditions μ X e Y
      (μ[fun ω => systemMiddleTerm (X 0 ω)
        (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)])]) :=
  of_beta_weight_wlln_and_true_error_covariance_joint_iid
    (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
    h72 hjoint hident hmodel hbeta_meas hrobust_meas
    hRobustCross_int hRobustQuadratic_int hErrorOuter_int hSigmaCross_int
    (fun a b l r =>
      systemCovariance113_designWeight_integrable_of_design_memLp_two
        (μ := μ) (X := X) hX_memLp a b l r)
    (systemCovariance113_middleTerm_integrable_of_design_memLp_two
      (μ := μ) (X := X)
      (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)]) hX_memLp)
    hhomoskedastic_meas
    (fun a b c d =>
      systemCovariance113_designWeight_integrable_of_design_memLp_two
        (μ := μ) (X := X) hX_memLp a b c d)

omit [DecidableEq m] in
/-- Primitive row-iid Theorem 11.3 constructor with finite design second moment.

The split `SystemAssumption72`, scaled-estimator measurability, and all iid
composition fields are derived from `SystemAssumption72PrimitiveRow`. The
remaining explicit assumptions are the higher mixed moments that are not yet
encoded in the current primitive-row Assumption 7.2 facade and the
measurability of the two displayed feasible middle surfaces. -/
theorem of_primitive_row_true_error_covariance_joint_iid_design_memLp
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h72 : SystemAssumption72PrimitiveRow μ X e)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hrobust_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hX_memLp : MemLp (X 0) 2 μ)
    (hRobustCross_int : ∀ a b : m, ∀ c d l : k,
      Integrable
        (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
          X 0 ω a c * X 0 ω b d) μ)
    (hRobustQuadratic_int : ∀ a b : m, ∀ c d l r : k,
      Integrable (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ)
    (hErrorOuter_int : Integrable (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ)
    (hSigmaCross_int : ∀ a b : m, ∀ l : k,
      Integrable (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ)
    (hhomoskedastic_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
            (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ) :
    SystemCovarianceTheorem113Conditions μ X e Y
      (μ[fun ω => systemMiddleTerm (X 0 ω)
        (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)])]) :=
  of_beta_weight_wlln_and_true_error_covariance_joint_iid_design_memLp
    (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
    h72.toSystemAssumption72 h72.row_iIndep h72.row_identDistrib hmodel
    (fun t =>
      systemLeastSquaresBetaStarObs_scaled_aemeasurable_of_assumption72
        (μ := μ) (X := X) (e := e) (Y := Y)
        h72.toSystemAssumption72 β hmodel t)
    hrobust_meas hX_memLp hRobustCross_int hRobustQuadratic_int
    hErrorOuter_int hSigmaCross_int hhomoskedastic_meas

omit [DecidableEq m] in
/-- Primitive row-iid Theorem 11.3 constructor deriving the finite design
second moment from Assumption 7.2's Gram integrability. -/
theorem of_primitive_row_true_error_covariance_joint_iid_gram
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h72 : SystemAssumption72PrimitiveRow μ X e)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hrobust_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hRobustCross_int : ∀ a b : m, ∀ c d l : k,
      Integrable
        (fun ω => (e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) *
          X 0 ω a c * X 0 ω b d) μ)
    (hRobustQuadratic_int : ∀ a b : m, ∀ c d l r : k,
      Integrable (fun ω => X 0 ω a l * X 0 ω b r * X 0 ω a c * X 0 ω b d) μ)
    (hErrorOuter_int : Integrable (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ)
    (hSigmaCross_int : ∀ a b : m, ∀ l : k,
      Integrable (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ)
    (hhomoskedastic_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
            (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ) :
    SystemCovarianceTheorem113Conditions μ X e Y
      (μ[fun ω => systemMiddleTerm (X 0 ω)
        (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)])]) :=
  of_primitive_row_true_error_covariance_joint_iid_design_memLp
    (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
    h72 hmodel hrobust_meas h72.design_memLp_two
    hRobustCross_int hRobustQuadratic_int hErrorOuter_int hSigmaCross_int
    hhomoskedastic_meas

omit [DecidableEq m] in
/-- Primitive row-iid Theorem 11.3 constructor with compact higher-moment
sufficient conditions for the robust-middle perturbation.

The scalar robust cross/quadratic integrability fields are derived from
`E[‖e₀‖‖X₀‖³] < ∞` and `E[‖X₀‖⁴] < ∞`; the remaining explicit residual
covariance fields are the error outer-product and the simpler residual
cross-weight moments. -/
theorem of_primitive_row_true_error_covariance_joint_iid_compact_moments
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h72 : SystemAssumption72PrimitiveRow μ X e)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hrobust_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hX_memLp : MemLp (X 0) 2 μ)
    (he0_meas : AEStronglyMeasurable (e 0) μ)
    (hMixed : Integrable (fun ω => ‖e 0 ω‖ * ‖X 0 ω‖ ^ 3) μ)
    (hFourth : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ)
    (hErrorOuter_int : Integrable (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ)
    (hSigmaCross_int : ∀ a b : m, ∀ l : k,
      Integrable (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ)
    (hhomoskedastic_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
            (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ) :
    SystemCovarianceTheorem113Conditions μ X e Y
      (μ[fun ω => systemMiddleTerm (X 0 ω)
        (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)])]) :=
  of_primitive_row_true_error_covariance_joint_iid_design_memLp
    (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
    h72 hmodel hrobust_meas hX_memLp
    (fun a b c d l =>
      systemCovariance113_robustCross_integrable_of_errorNorm_designNorm_cubed
        (μ := μ) (X := X) (e := e)
        hX_memLp.aestronglyMeasurable he0_meas hMixed a b c d l)
    (fun a b c d l r =>
      systemCovariance113_robustQuadratic_integrable_of_designNorm_fourth
        (μ := μ) (X := X)
        hX_memLp.aestronglyMeasurable hFourth a b c d l r)
    hErrorOuter_int hSigmaCross_int hhomoskedastic_meas

omit [DecidableEq m] in
/-- Primitive row-iid Theorem 11.3 compact-moment constructor deriving both
the design `L²` moment and error measurability from the primitive row package. -/
theorem of_primitive_row_true_error_covariance_joint_iid_compact_moments_of_gram
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h72 : SystemAssumption72PrimitiveRow μ X e)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hrobust_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hMixed : Integrable (fun ω => ‖e 0 ω‖ * ‖X 0 ω‖ ^ 3) μ)
    (hFourth : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ)
    (hErrorOuter_int : Integrable (fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)) μ)
    (hSigmaCross_int : ∀ a b : m, ∀ l : k,
      Integrable (fun ω => e 0 ω a * X 0 ω b l + X 0 ω a l * e 0 ω b) μ)
    (hhomoskedastic_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
            (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ) :
    SystemCovarianceTheorem113Conditions μ X e Y
      (μ[fun ω => systemMiddleTerm (X 0 ω)
        (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)])]) :=
  of_primitive_row_true_error_covariance_joint_iid_compact_moments
    (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
    h72 hmodel hrobust_meas h72.design_memLp_two h72.e_aestronglyMeasurable
    hMixed hFourth hErrorOuter_int hSigmaCross_int hhomoskedastic_meas

omit [DecidableEq m] in
/-- Primitive row-iid Theorem 11.3 compact-moment constructor deriving the
true-error covariance and residual-covariance cross integrability from compact
norm moments.

This is the tightest current Assumption-7.2-facing route for Hansen Theorem
11.3: the primitive row package supplies iid, Gram, score, and design `L²`
fields; `E‖e₀‖²`, `E‖e₀‖‖X₀‖³`, and `E‖X₀‖⁴` supply the remaining covariance
perturbation moments. -/
theorem of_primitive_row_true_error_covariance_joint_iid_compact_norm_moments_of_gram
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ} {β : k → ℝ}
    (h72 : SystemAssumption72PrimitiveRow μ X e)
    (hmodel : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j)
    (hrobust_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hErrorSq : Integrable (fun ω => ‖e 0 ω‖ ^ 2) μ)
    (hMixed : Integrable (fun ω => ‖e 0 ω‖ * ‖X 0 ω‖ ^ 3) μ)
    (hFourth : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ)
    (hhomoskedastic_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
            (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ) :
    SystemCovarianceTheorem113Conditions μ X e Y
      (μ[fun ω => systemMiddleTerm (X 0 ω)
        (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)])]) :=
  of_primitive_row_true_error_covariance_joint_iid_compact_moments_of_gram
    (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
    h72 hmodel hrobust_meas hMixed hFourth
    (systemCovariance113_errorOuter_integrable_of_errorNorm_sq
      (μ := μ) (e := e) h72.e_aestronglyMeasurable hErrorSq)
    (fun a b l =>
      systemCovariance113_sigmaCross_integrable_of_errorNorm_sq_design_memLp_two
        (μ := μ) (X := X) (e := e)
        h72.design_memLp_two h72.e_aestronglyMeasurable hErrorSq a b l)
    hhomoskedastic_meas

end SystemCovarianceTheorem113Conditions

/-- Theorem-facing primitive-row Assumption 7.2 facade for Hansen Theorem 11.3.

This extends the Chapter 11 row-iid Assumption 7.2 package with the compact
norm moments used to prove feasible robust and homoskedastic covariance
consistency:
`E‖e₀‖²`, `E[‖e₀‖‖X₀‖³]`, and `E‖X₀‖⁴`. The two displayed finite-sample
measurability fields are formal side conditions for the exact feasible
covariance surfaces; they are not stochastic convergence assumptions. -/
structure SystemCovarianceTheorem113CompactPrimitiveRowConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Matrix m k ℝ) (e Y : ℕ → Ω → m → ℝ)
    (β : k → ℝ) : Prop
    extends SystemAssumption72PrimitiveRow μ X e where
  /-- System linear model, observation by observation and equation by equation. -/
  model : ∀ i ω j, Y i ω j = (X i ω j) ⬝ᵥ β + e i ω j
  /-- Compact finite second moment for the system error vector. -/
  error_norm_sq_integrable : Integrable (fun ω => ‖e 0 ω‖ ^ 2) μ
  /-- Compact mixed moment controlling the feasible robust-middle cross term. -/
  error_design_norm_cubed_integrable :
    Integrable (fun ω => ‖e 0 ω‖ * ‖X 0 ω‖ ^ 3) μ
  /-- Compact finite fourth moment for the system design row. -/
  design_norm_fourth_integrable : Integrable (fun ω => ‖X 0 ω‖ ^ 4) μ
  /-- Measurability of Hansen's feasible robust middle surface. -/
  robust_middle_measurable : ∀ n,
    AEStronglyMeasurable
      (fun ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω)
          (systemResidualStarObs (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))) μ
  /-- Measurability of Hansen's feasible homoskedastic middle surface. -/
  homoskedastic_middle_measurable : ∀ n,
    AEStronglyMeasurable
      (fun ω =>
        systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
          (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω))) μ

namespace SystemCovarianceTheorem113CompactPrimitiveRowConditions

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- The compact primitive-row Assumption 7.2 facade supplies the theorem-facing
Hansen 11.3 covariance condition package. -/
theorem toSystemCovarianceTheorem113Conditions
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {β : k → ℝ}
    (h : SystemCovarianceTheorem113CompactPrimitiveRowConditions μ X e Y β) :
    SystemCovarianceTheorem113Conditions μ X e Y
      (μ[fun ω => systemMiddleTerm (X 0 ω)
        (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)])]) :=
  open SystemCovarianceTheorem113Conditions in
  of_primitive_row_true_error_covariance_joint_iid_compact_norm_moments_of_gram
      (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
      h.toSystemAssumption72PrimitiveRow h.model
      h.robust_middle_measurable
      h.error_norm_sq_integrable
      h.error_design_norm_cubed_integrable
      h.design_norm_fourth_integrable
      h.homoskedastic_middle_measurable

end SystemCovarianceTheorem113CompactPrimitiveRowConditions

/-- Continuous-mapping theorem for the normalized Chapter 11 sandwich covariance
`Q̂⁻¹Ω̂Q̂⁻¹`. -/
theorem systemSandwichCovariance_tendstoInMeasure
    {Qhat Omegahat : ℕ → Ω → Matrix k k ℝ} {Q Omega : Matrix k k ℝ}
    (hQ_meas : ∀ n, AEStronglyMeasurable (Qhat n) μ)
    (hOmega_meas : ∀ n, AEStronglyMeasurable (Omegahat n) μ)
    (hQ : TendstoInMeasure μ Qhat atTop (fun _ => Q))
    (hOmega : TendstoInMeasure μ Omegahat atTop (fun _ => Omega))
    (hQ_unit : IsUnit Q.det) :
    TendstoInMeasure μ
      (fun n ω => systemSandwichCovariance (Qhat n ω) (Omegahat n ω))
      atTop (fun _ => systemAsymptoticVariance Q Omega) := by
  have hQinv : TendstoInMeasure μ
      (fun n ω => (Qhat n ω)⁻¹) atTop (fun _ => Q⁻¹) :=
    tendstoInMeasure_matrix_inv hQ_meas hQ (fun _ => hQ_unit)
  have hQinv_meas : ∀ n, AEStronglyMeasurable (fun ω => (Qhat n ω)⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (hQ_meas n)
  have hLeft : TendstoInMeasure μ
      (fun n ω => (Qhat n ω)⁻¹ * Omegahat n ω)
      atTop (fun _ => Q⁻¹ * Omega) :=
    tendstoInMeasure_matrix_mul hQinv_meas hOmega_meas hQinv hOmega
  have hLeft_meas : ∀ n,
      AEStronglyMeasurable (fun ω => (Qhat n ω)⁻¹ * Omegahat n ω) μ := by
    intro n
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hQinv_meas n).prodMk (hOmega_meas n))
  have hFull : TendstoInMeasure μ
      (fun n ω => ((Qhat n ω)⁻¹ * Omegahat n ω) * (Qhat n ω)⁻¹)
      atTop (fun _ => (Q⁻¹ * Omega) * Q⁻¹) :=
    tendstoInMeasure_matrix_mul hLeft_meas hQinv_meas hLeft hQinv
  simpa [systemSandwichCovariance, systemAsymptoticVariance, Matrix.mul_assoc] using hFull

omit [DecidableEq m] in
/-- Moment-convergence route for the exact normalized robust system covariance
`Q̂⁻¹Ω̂Q̂⁻¹`. This is the CMT layer used by Hansen Theorem 11.3 after the
feasible residual middle matrix has been shown to converge. -/
theorem systemRobustCovariance_tendstoInMeasure_of_moment_convergence
    {X : ℕ → Ω → Matrix m k ℝ} {ehat : ℕ → Ω → m → ℝ}
    {Q Omega : Matrix k k ℝ}
    (hQ_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => systemNormalizedGram (fun i : Fin n => X i.val ω)) μ)
    (hOmega_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => ehat i.val ω)) μ)
    (hQ : TendstoInMeasure μ
      (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
      atTop (fun _ => Q))
    (hOmega : TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => ehat i.val ω))
      atTop (fun _ => Omega))
    (hQ_unit : IsUnit Q.det) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustCovariance (fun i : Fin n => X i.val ω) (fun i : Fin n => ehat i.val ω))
      atTop (fun _ => systemAsymptoticVariance Q Omega) :=
  systemSandwichCovariance_tendstoInMeasure
    (μ := μ)
    (Qhat := fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
    (Omegahat := fun n ω =>
      systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => ehat i.val ω))
    hQ_meas hOmega_meas hQ hOmega hQ_unit

omit [DecidableEq m] in
/-- Displayed feasible-residual route for Hansen Theorem 11.3.

This specializes the sandwich CMT layer to the actual Star residual covariance
estimator `systemRobustCovarianceStarObs`, so callers only need to prove
convergence of Hansen's middle matrix
`n⁻¹∑ Xᵢ' êᵢ êᵢ' Xᵢ` rather than introduce an auxiliary residual array. -/
theorem systemRobustCovarianceStarObs_tendstoInMeasure_of_moment_convergence
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    {Q Omega : Matrix k k ℝ}
    (hQ_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => systemNormalizedGram (fun i : Fin n => X i.val ω)) μ)
    (hOmega_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (systemResidualStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hQ : TendstoInMeasure μ
      (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
      atTop (fun _ => Q))
    (hOmega : TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω)
          (systemResidualStarObs (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω)))
      atTop (fun _ => Omega))
    (hQ_unit : IsUnit Q.det) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustCovarianceStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω))
      atTop (fun _ => systemAsymptoticVariance Q Omega) := by
  simpa [systemRobustCovarianceStarObs, systemRobustCovariance] using
    systemSandwichCovariance_tendstoInMeasure
      (μ := μ)
      (Qhat := fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
      (Omegahat := fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω)
          (systemResidualStarObs (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω)))
      (Q := Q) (Omega := Omega)
      hQ_meas hOmega_meas hQ hOmega hQ_unit

omit [DecidableEq m] in
/-- WLLN plus CMT route for the exact true-error robust system covariance
`Q̂⁻¹Ω̂Q̂⁻¹`. This proves the Hansen 11.3 sandwich shape for the ideal middle
matrix `n⁻¹∑ Xᵢ'eᵢeᵢ'Xᵢ`; feasible residual substitution is the remaining
separate step for `êᵢ`. -/
theorem systemRobustCovariance_tendstoInMeasure_of_ideal_wlln
    {X : ℕ → Ω → Matrix m k ℝ} {e : ℕ → Ω → m → ℝ}
    (hQ_int : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hQ_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => (X i ω)ᵀ * X i ω)))
    (hQ_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω)ᵀ * X i ω)
        (fun ω => (X 0 ω)ᵀ * X 0 ω) μ μ)
    (hOmega_int : Integrable (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ)
    (hOmega_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemRobustMiddleTerm (X i ω) (e i ω))))
    (hOmega_ident : ∀ i,
      IdentDistrib (fun ω => systemRobustMiddleTerm (X i ω) (e i ω))
        (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ μ)
    (hQ_unit : IsUnit (μ[fun ω => (X 0 ω)ᵀ * X 0 ω]).det) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustCovariance (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω))
      atTop
      (fun _ => systemAsymptoticVariance
        (μ[fun ω => (X 0 ω)ᵀ * X 0 ω])
        (μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)])) :=
  systemRobustCovariance_tendstoInMeasure_of_moment_convergence
    (μ := μ)
    (X := X) (ehat := e)
    (Q := μ[fun ω => (X 0 ω)ᵀ * X 0 ω])
    (Omega := μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)])
    (fun n => systemNormalizedGram_aestronglyMeasurable hQ_int hQ_ident n)
    (fun n => systemRobustMiddle_aestronglyMeasurable hOmega_int hOmega_ident n)
    (systemNormalizedGram_tendstoInMeasure hQ_int hQ_indep hQ_ident)
    (systemRobustMiddle_ideal_tendstoInMeasure hOmega_int hOmega_indep hOmega_ident)
    hQ_unit

omit [DecidableEq m] in
/-- Feasible-residual robust covariance route for Hansen Theorem 11.3.

This combines the exact true-error WLLN with a residual-substitution bound
`Ω̂_HC(ê) - Ω̂_HC(e) = o_p(1)`. It is the vector-system analogue of the
Chapter 7 HC covariance assembly, stated at the exact matrix level Hansen uses. -/
theorem systemRobustCovariance_tendstoInMeasure_of_feasible_wlln_substitution
    {X : ℕ → Ω → Matrix m k ℝ} {e ehat : ℕ → Ω → m → ℝ}
    (hQ_int : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hQ_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => (X i ω)ᵀ * X i ω)))
    (hQ_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω)ᵀ * X i ω)
        (fun ω => (X 0 ω)ᵀ * X 0 ω) μ μ)
    (hOmega_int : Integrable (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ)
    (hOmega_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemRobustMiddleTerm (X i ω) (e i ω))))
    (hOmega_ident : ∀ i,
      IdentDistrib (fun ω => systemRobustMiddleTerm (X i ω) (e i ω))
        (fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)) μ μ)
    (hOmega_hat_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (fun i : Fin n => ehat i.val ω)) μ)
    (hsub : TendstoInMeasure μ
      (fun n ω =>
        systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => ehat i.val ω) -
          systemRobustMiddle (fun i : Fin n => X i.val ω) (fun i : Fin n => e i.val ω))
      atTop (fun _ => 0))
    (hQ_unit : IsUnit (μ[fun ω => (X 0 ω)ᵀ * X 0 ω]).det) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustCovariance (fun i : Fin n => X i.val ω)
          (fun i : Fin n => ehat i.val ω))
      atTop
      (fun _ => systemAsymptoticVariance
        (μ[fun ω => (X 0 ω)ᵀ * X 0 ω])
        (μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)])) := by
  have hQ :
      TendstoInMeasure μ
        (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
        atTop (fun _ => μ[fun ω => (X 0 ω)ᵀ * X 0 ω]) :=
    systemNormalizedGram_tendstoInMeasure hQ_int hQ_indep hQ_ident
  have hOmegaIdeal :
      TendstoInMeasure μ
        (fun n ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (fun i : Fin n => e i.val ω))
        atTop (fun _ => μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)]) :=
    systemRobustMiddle_ideal_tendstoInMeasure hOmega_int hOmega_indep hOmega_ident
  have hOmegaHat :
      TendstoInMeasure μ
        (fun n ω =>
          systemRobustMiddle (fun i : Fin n => X i.val ω)
            (fun i : Fin n => ehat i.val ω))
        atTop (fun _ => μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)]) :=
    systemRobustMiddle_feasible_tendstoInMeasure_of_substitution hOmegaIdeal hsub
  exact systemRobustCovariance_tendstoInMeasure_of_moment_convergence
    (μ := μ)
    (X := X) (ehat := ehat)
    (Q := μ[fun ω => (X 0 ω)ᵀ * X 0 ω])
    (Omega := μ[fun ω => systemRobustMiddleTerm (X 0 ω) (e 0 ω)])
    (fun n => systemNormalizedGram_aestronglyMeasurable hQ_int hQ_ident n)
    hOmega_hat_meas hQ hOmegaHat hQ_unit

omit [DecidableEq m] in
/-- Moment-convergence route for the exact normalized homoskedastic system
covariance `Q̂⁻¹Ω̂₀Q̂⁻¹`. -/
theorem systemHomoskedasticCovariance_tendstoInMeasure_of_moment_convergence
    {X : ℕ → Ω → Matrix m k ℝ} {SigmaHat : ℕ → Ω → Matrix m m ℝ}
    {Q Omega : Matrix k k ℝ}
    (hQ_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => systemNormalizedGram (fun i : Fin n => X i.val ω)) μ)
    (hOmega_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle
            (fun i : Fin n => X i.val ω) (SigmaHat n ω)) μ)
    (hQ : TendstoInMeasure μ
      (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
      atTop (fun _ => Q))
    (hOmega : TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticMiddle
          (fun i : Fin n => X i.val ω) (SigmaHat n ω))
      atTop (fun _ => Omega))
    (hQ_unit : IsUnit Q.det) :
    TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticCovariance
          (fun i : Fin n => X i.val ω) (SigmaHat n ω))
      atTop (fun _ => systemAsymptoticVariance Q Omega) :=
  systemSandwichCovariance_tendstoInMeasure
    (μ := μ)
    (Qhat := fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
    (Omegahat := fun n ω =>
      systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) (SigmaHat n ω))
    hQ_meas hOmega_meas hQ hOmega hQ_unit

omit [DecidableEq m] in
/-- Displayed feasible homoskedastic covariance route for Hansen Theorem 11.3.

This specializes the sandwich CMT layer to
`systemHomoskedasticCovarianceStarObs`, whose middle matrix uses the actual
Star residual covariance `Σ̂ = n⁻¹∑ êᵢ êᵢ'`. -/
theorem systemHomoskedasticCovarianceStarObs_tendstoInMeasure_of_moment_convergence
    {X : ℕ → Ω → Matrix m k ℝ} {Y : ℕ → Ω → m → ℝ}
    {Q Omega : Matrix k k ℝ}
    (hQ_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => systemNormalizedGram (fun i : Fin n => X i.val ω)) μ)
    (hOmega_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
            (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
              (fun i : Fin n => Y i.val ω))) μ)
    (hQ : TendstoInMeasure μ
      (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
      atTop (fun _ => Q))
    (hOmega : TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
          (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω)))
      atTop (fun _ => Omega))
    (hQ_unit : IsUnit Q.det) :
    TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticCovarianceStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω))
      atTop (fun _ => systemAsymptoticVariance Q Omega) := by
  simpa [systemHomoskedasticCovarianceStarObs, systemHomoskedasticCovariance] using
    systemSandwichCovariance_tendstoInMeasure
      (μ := μ)
      (Qhat := fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
      (Omegahat := fun n ω =>
        systemHomoskedasticMiddle (fun i : Fin n => X i.val ω)
          (systemSigmaHatStarObs (fun i : Fin n => X i.val ω)
            (fun i : Fin n => Y i.val ω)))
      (Q := Q) (Omega := Omega)
      hQ_meas hOmega_meas hQ hOmega hQ_unit

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- **Hansen Theorem 11.3**, displayed system covariance estimators.

This is the theorem-facing endpoint for the actual Star residual covariance
surfaces.  `SystemAssumption72` supplies the system Gram WLLN and nonsingularity;
the robust and homoskedastic residual/covariance middle consistency premises
are carried explicitly by `SystemCovarianceTheorem113Conditions`. -/
theorem systemCovariances_theorem11_3_of_middle_consistency
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {Omega0 : Matrix k k ℝ}
    (h : SystemCovarianceTheorem113Conditions μ X e Y Omega0) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustCovarianceStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω))
      atTop
      (fun _ =>
        systemAsymptoticVariance (systemPopulationGram μ X)
          (systemPopulationScoreCovariance μ X e)) ∧
    TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticCovarianceStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω))
      atTop
      (fun _ => systemAsymptoticVariance (systemPopulationGram μ X) Omega0) := by
  have hQ_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω => systemNormalizedGram (fun i : Fin n => X i.val ω)) μ :=
    fun n => systemNormalizedGram_aestronglyMeasurable
      (μ := μ) (X := X)
      h.assumption72.gram_integrable h.assumption72.gram_identDistrib n
  have hQ : TendstoInMeasure μ
      (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
      atTop (fun _ => systemPopulationGram μ X) := by
    simpa [systemPopulationGram] using
      systemNormalizedGram_tendstoInMeasure
        (μ := μ) (X := X)
        h.assumption72.gram_integrable
        h.assumption72.gram_independent
        h.assumption72.gram_identDistrib
  constructor
  · exact systemRobustCovarianceStarObs_tendstoInMeasure_of_moment_convergence
      (μ := μ) (X := X) (Y := Y)
      (Q := systemPopulationGram μ X)
      (Omega := systemPopulationScoreCovariance μ X e)
      hQ_meas h.robust_middle_measurable hQ h.robust_middle_consistent
      h.assumption72.gram_nonsing
  · exact systemHomoskedasticCovarianceStarObs_tendstoInMeasure_of_moment_convergence
      (μ := μ) (X := X) (Y := Y)
      (Q := systemPopulationGram μ X) (Omega := Omega0)
      hQ_meas h.homoskedastic_middle_measurable hQ
      h.homoskedastic_middle_consistent h.assumption72.gram_nonsing

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- **Hansen Theorem 11.3**, displayed covariance estimators from the
primitive row-iid Assumption 7.2 facade plus compact covariance moments.

This is the preferred theorem-facing endpoint: it derives the feasible robust
and homoskedastic middle consistency package internally and then reuses
`systemCovariances_theorem11_3_of_middle_consistency`. -/
theorem systemCovariances_theorem11_3_of_primitive_row_compact_assumption72
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {β : k → ℝ}
    (h : SystemCovarianceTheorem113CompactPrimitiveRowConditions μ X e Y β) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustCovarianceStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω))
      atTop
      (fun _ =>
        systemAsymptoticVariance (systemPopulationGram μ X)
          (systemPopulationScoreCovariance μ X e)) ∧
    TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticCovarianceStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω))
      atTop
      (fun _ =>
        systemAsymptoticVariance (systemPopulationGram μ X)
          (μ[fun ω => systemMiddleTerm (X 0 ω)
            (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)])])) :=
  systemCovariances_theorem11_3_of_middle_consistency
    (μ := μ) (X := X) (e := e) (Y := Y)
    h.toSystemCovarianceTheorem113Conditions

omit [Fintype q] [DecidableEq q] [DecidableEq m] in
/-- **Hansen Theorem 11.3** from literal observed-row Assumption 7.2.

The observed-row fourth moments derive all residual-substitution moments in
the compact covariance package. Measurability of both displayed feasible
middle matrices is derived from the observed rows and the Star estimator. -/
theorem systemCovariances_theorem11_3_of_observed_assumption72
    {X : ℕ → Ω → Matrix m k ℝ} {e Y : ℕ → Ω → m → ℝ}
    {β : k → ℝ}
    (h : SystemAssumption72ObservedResponseFourthConditions μ X e Y β) :
    TendstoInMeasure μ
      (fun n ω =>
        systemRobustCovarianceStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω))
      atTop
      (fun _ =>
        systemAsymptoticVariance (systemPopulationGram μ X)
          (systemPopulationScoreCovariance μ X e)) ∧
    TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticCovarianceStarObs
          (fun i : Fin n => X i.val ω) (fun i : Fin n => Y i.val ω))
      atTop
      (fun _ =>
        systemAsymptoticVariance (systemPopulationGram μ X)
          (μ[fun ω => systemMiddleTerm (X 0 ω)
            (μ[fun ω => Matrix.vecMulVec (e 0 ω) (e 0 ω)])])) := by
  apply systemCovariances_theorem11_3_of_primitive_row_compact_assumption72
    (μ := μ) (X := X) (e := e) (Y := Y) (β := β)
  exact
    { toSystemAssumption72PrimitiveRow := h.toSystemAssumption72PrimitiveRow
      model := h.model
      error_norm_sq_integrable := h.error_norm_sq_integrable
      error_design_norm_cubed_integrable := h.error_design_norm_cubed_integrable
      design_norm_fourth_integrable := h.design_norm_fourth_integrable
      robust_middle_measurable := fun n => by
        simp only [systemRobustMiddle]
        refine AEStronglyMeasurable.const_smul ?_ ((Fintype.card (Fin n) : ℝ)⁻¹)
        refine Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ => ?_)
        exact systemRobustMiddleTerm_aestronglyMeasurable_of_pair
          (h.x_aestronglyMeasurable_at i.val)
          (systemResidualStarObs_aestronglyMeasurable
            (μ := μ) (X := X) (Y := Y)
            h.x_aestronglyMeasurable_at h.y_aestronglyMeasurable_at n i)
      homoskedastic_middle_measurable := fun n => by
        have hResidual : ∀ i : Fin n, AEStronglyMeasurable
            (fun ω => systemResidualStarObs
              (fun r : Fin n => X r.val ω) (fun r : Fin n => Y r.val ω) i) μ :=
          fun i => systemResidualStarObs_aestronglyMeasurable
            (μ := μ) (X := X) (Y := Y)
            h.x_aestronglyMeasurable_at h.y_aestronglyMeasurable_at n i
        have hSigmaRaw := systemSigmaHat_aestronglyMeasurable_of_rows
          (μ := μ)
          (ehat := fun i : Fin n => fun ω => systemResidualStarObs
            (fun r : Fin n => X r.val ω) (fun r : Fin n => Y r.val ω) i)
          hResidual
        have hSigma : AEStronglyMeasurable
            (fun ω => systemSigmaHatStarObs
              (fun r : Fin n => X r.val ω) (fun r : Fin n => Y r.val ω)) μ := by
          simpa only [systemSigmaHatStarObs] using hSigmaRaw
        exact systemHomoskedasticMiddle_aestronglyMeasurable_of_rows
          (μ := μ) (X := fun i : Fin n => X i.val)
          (SigmaHat := fun ω => systemSigmaHatStarObs
            (fun r : Fin n => X r.val ω) (fun r : Fin n => Y r.val ω))
          (fun i => h.x_aestronglyMeasurable_at i.val) hSigma }

omit [DecidableEq m] in
/-- Fixed-covariance WLLN plus CMT route for the homoskedastic system covariance
`Q̂⁻¹Ω̂₀Q̂⁻¹`. -/
theorem systemHomoskedasticCovariance_tendstoInMeasure_of_fixed_wlln
    {X : ℕ → Ω → Matrix m k ℝ} (Sigma : Matrix m m ℝ)
    (hQ_int : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hQ_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => (X i ω)ᵀ * X i ω)))
    (hQ_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω)ᵀ * X i ω)
        (fun ω => (X 0 ω)ᵀ * X 0 ω) μ μ)
    (hOmega_int : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hOmega_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma)))
    (hOmega_ident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ μ)
    (hQ_unit : IsUnit (μ[fun ω => (X 0 ω)ᵀ * X 0 ω]).det) :
    TendstoInMeasure μ
      (fun n ω => systemHomoskedasticCovariance (fun i : Fin n => X i.val ω) Sigma)
      atTop
      (fun _ => systemAsymptoticVariance
        (μ[fun ω => (X 0 ω)ᵀ * X 0 ω])
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma])) :=
  systemHomoskedasticCovariance_tendstoInMeasure_of_moment_convergence
    (μ := μ)
    (X := X) (SigmaHat := fun _ _ => Sigma)
    (Q := μ[fun ω => (X 0 ω)ᵀ * X 0 ω])
    (Omega := μ[fun ω => systemMiddleTerm (X 0 ω) Sigma])
    (fun n => systemNormalizedGram_aestronglyMeasurable hQ_int hQ_ident n)
    (fun n => systemHomoskedasticMiddle_fixed_aestronglyMeasurable Sigma
      hOmega_int hOmega_ident n)
    (systemNormalizedGram_tendstoInMeasure hQ_int hQ_indep hQ_ident)
    (systemHomoskedasticMiddle_fixed_tendstoInMeasure Sigma
      hOmega_int hOmega_indep hOmega_ident)
    hQ_unit

omit [DecidableEq m] in
/-- Estimated-covariance homoskedastic covariance route for Hansen Theorems
11.3 and 11.6.

This combines the fixed-covariance WLLN with a perturbation bound showing that
the estimated covariance middle matrix differs from the fixed-covariance middle
by `o_p(1)`. -/
theorem systemHomoskedasticCovariance_tendstoInMeasure_of_feasible_wlln_substitution
    {X : ℕ → Ω → Matrix m k ℝ} (Sigma : Matrix m m ℝ)
    {SigmaHat : ℕ → Ω → Matrix m m ℝ}
    (hQ_int : Integrable (fun ω => (X 0 ω)ᵀ * X 0 ω) μ)
    (hQ_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => (X i ω)ᵀ * X i ω)))
    (hQ_ident : ∀ i,
      IdentDistrib (fun ω => (X i ω)ᵀ * X i ω)
        (fun ω => (X 0 ω)ᵀ * X 0 ω) μ μ)
    (hOmega_int : Integrable (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ)
    (hOmega_indep : Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => systemMiddleTerm (X i ω) Sigma)))
    (hOmega_ident : ∀ i,
      IdentDistrib (fun ω => systemMiddleTerm (X i ω) Sigma)
        (fun ω => systemMiddleTerm (X 0 ω) Sigma) μ μ)
    (hOmega_hat_meas : ∀ n,
      AEStronglyMeasurable
        (fun ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) (SigmaHat n ω)) μ)
    (hsub : TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) (SigmaHat n ω) -
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) Sigma)
      atTop (fun _ => 0))
    (hQ_unit : IsUnit (μ[fun ω => (X 0 ω)ᵀ * X 0 ω]).det) :
    TendstoInMeasure μ
      (fun n ω =>
        systemHomoskedasticCovariance (fun i : Fin n => X i.val ω) (SigmaHat n ω))
      atTop
      (fun _ => systemAsymptoticVariance
        (μ[fun ω => (X 0 ω)ᵀ * X 0 ω])
        (μ[fun ω => systemMiddleTerm (X 0 ω) Sigma])) := by
  have hQ :
      TendstoInMeasure μ
        (fun n ω => systemNormalizedGram (fun i : Fin n => X i.val ω))
        atTop (fun _ => μ[fun ω => (X 0 ω)ᵀ * X 0 ω]) :=
    systemNormalizedGram_tendstoInMeasure hQ_int hQ_indep hQ_ident
  have hOmegaFixed :
      TendstoInMeasure μ
        (fun n ω => systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) Sigma)
        atTop (fun _ => μ[fun ω => systemMiddleTerm (X 0 ω) Sigma]) :=
    systemHomoskedasticMiddle_fixed_tendstoInMeasure Sigma
      hOmega_int hOmega_indep hOmega_ident
  have hOmegaHat :
      TendstoInMeasure μ
        (fun n ω =>
          systemHomoskedasticMiddle (fun i : Fin n => X i.val ω) (SigmaHat n ω))
        atTop (fun _ => μ[fun ω => systemMiddleTerm (X 0 ω) Sigma]) :=
    systemHomoskedasticMiddle_feasible_tendstoInMeasure_of_substitution hOmegaFixed hsub
  exact systemHomoskedasticCovariance_tendstoInMeasure_of_moment_convergence
    (μ := μ)
    (X := X) (SigmaHat := SigmaHat)
    (Q := μ[fun ω => (X 0 ω)ᵀ * X 0 ω])
    (Omega := μ[fun ω => systemMiddleTerm (X 0 ω) Sigma])
    (fun n => systemNormalizedGram_aestronglyMeasurable hQ_int hQ_ident n)
    hOmega_hat_meas hQ hOmegaHat hQ_unit

/-- **Stacked-scalar support for Hansen Theorem 11.3.**

For the stacked system, the Chapter 7 HC0 and homoskedastic Star covariance
consistency results apply directly to the system least-squares design. This
theorem assembles those convergence and measurability results into Chapter 8's
covariance-estimator interface, restating the HC0 limit with the Chapter 11
`systemAsymptoticVariance` notation. Hansen's displayed multivariate system
middle matrices are exposed separately by `systemRobustMiddle` and
`systemRobustCovariance`. -/
theorem systemCovariance_consistent_of_iidRobustFeasibleHCMomentConditions
    {X : ℕ → Ω → k → ℝ} {e y : ℕ → Ω → ℝ}
    (β : k → ℝ) (hm : IidRobustFeasibleHCMomentConditions μ X e y β) :
    CovarianceEstimatorConsistent μ
        (fun n ω =>
          olsHetCovStar (stackRegressors X n ω) (stackOutcomes y n ω))
        (systemAsymptoticVariance (popGram μ X) (scoreCovMat μ X e)) ∧
      CovarianceEstimatorConsistent μ
        (fun n ω =>
          olsHomoCovStar (stackRegressors X n ω) (stackOutcomes y n ω))
        (homoAsymCov μ X e) := by
  constructor
  · refine covarianceEstimatorConsistent_of_tendstoInMeasure _ _ ?hV_meas ?hV
    · exact olsHetCovStar_stack_aestronglyMeasurable_components
        (μ := μ) (X := X) (e := e) (y := y)
        hm.toRobustCovarianceConsistencyConditions.toSampleMomentAssumption71
        β hm.model hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable
    · simpa [systemAsymptoticVariance, heteroAsymCov] using
        olsHetCovStar_tendstoInMeasure_of_iidRobustFeasibleHCMomentConditions
          (μ := μ) (X := X) (e := e) (y := y) β hm
  · refine covarianceEstimatorConsistent_of_tendstoInMeasure _ _ ?hV0_meas ?hV0
    · exact olsHomoskedasticCovStar_stack_aestronglyMeasurable_components
        (μ := μ) (X := X) (e := e) (y := y)
        hm.toErrorVarianceConsistencyConditions.toSampleMomentAssumption71
        β hm.model hm.x_aestronglyMeasurable hm.e_aestronglyMeasurable
    · exact olsHomoCovStar_tendstoInMeasure_of_iidRobustFeasibleHCMomentConditions
        (μ := μ) (X := X) (e := e) (y := y) β hm

omit [IsProbabilityMeasure μ] [DecidableEq q] in
/-- Covariance consistency for smooth functions of system coefficients. -/
theorem systemDeltaCovariance_consistent
    (Vθhat : ℕ → Ω → Matrix q q ℝ) (Vθ : Matrix q q ℝ)
    (hVθ : CovarianceEstimatorConsistent μ Vθhat Vθ) :
    CovarianceEstimatorConsistent μ Vθhat Vθ :=
  hVθ

end HansenEconometrics
