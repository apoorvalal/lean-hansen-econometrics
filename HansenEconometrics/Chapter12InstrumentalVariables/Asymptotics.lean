import HansenEconometrics.AsymptoticUtils.DeltaMethod
import HansenEconometrics.Chapter8Asymptotics
import HansenEconometrics.Chapter12InstrumentalVariables.Basic
import HansenEconometrics.Chapter12InstrumentalVariables.GeneratedRegressors

/-!
# Chapter 12 - asymptotic instrumental-variables interfaces

This file records support interfaces for the 2SLS consistency,
asymptotic-normality, covariance, and smooth-function routes. The projection
lemmas below expose reusable convergence facts, but they are not proofs of
Hansen Theorems 12.1--12.5 from Assumptions 12.1--12.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Function Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Omega k l q : Type*}
variable [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
variable [Fintype k] [Fintype l] [Fintype q]
variable [DecidableEq k] [DecidableEq l] [DecidableEq q]

omit [MeasurableSpace Omega] [IsProbabilityMeasure mu] [Fintype q]
    [DecidableEq k] [DecidableEq l] [DecidableEq q] in
@[reducible]
private noncomputable def matrixBorelMeasurableSpaceInst
    (r c : Type*) [Fintype r] [Fintype c] : MeasurableSpace (Matrix r c ℝ) :=
  matrixBorelMeasurableSpace r c

attribute [local instance] matrixBorelMeasurableSpaceInst

omit [MeasurableSpace Omega] [IsProbabilityMeasure mu] [Fintype q]
    [DecidableEq k] [DecidableEq l] [DecidableEq q] in
private lemma matrixBorelSpaceInst
    (r c : Type*) [Fintype r] [Fintype c] : BorelSpace (Matrix r c ℝ) :=
  matrixBorelSpace r c

attribute [local instance] matrixBorelSpaceInst

omit [MeasurableSpace Omega] [Fintype k] [Fintype l] [Fintype q]
    [DecidableEq k] [DecidableEq l] [DecidableEq q] in
/-- Unnormalized rectangular stacked cross moment `Z'X` as a finite sum. -/
theorem stackInstruments_transpose_mul_stackRegressors_eq_sum
    (Z : ℕ → Omega → l → ℝ) (X : ℕ → Omega → k → ℝ) (n : ℕ) (ω : Omega) :
    (stackRegressors Z n ω)ᵀ * stackRegressors X n ω =
      ∑ i : Fin n, Matrix.vecMulVec (Z i.val ω) (X i.val ω) := by
  ext a b
  simp [stackRegressors, Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]

omit [MeasurableSpace Omega] [Fintype k] [Fintype l] [Fintype q]
    [DecidableEq k] [DecidableEq l] [DecidableEq q] in
/-- Hansen's normalized stacked IV cross moment is the sample average of
rectangular rank-one moments `Zᵢ Xᵢ'`. -/
@[simp]
theorem ivNormalizedCrossMoment_stack_eq_avg
    (Z : ℕ → Omega → l → ℝ) (X : ℕ → Omega → k → ℝ) (n : ℕ) (ω : Omega) :
    ivNormalizedCrossMoment (stackRegressors Z n ω) (stackRegressors X n ω) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, Matrix.vecMulVec (Z i.val ω) (X i.val ω) := by
  unfold ivNormalizedCrossMoment
  rw [stackInstruments_transpose_mul_stackRegressors_eq_sum]
  simp [Fintype.card_fin]

omit [MeasurableSpace Omega] [Fintype k] [Fintype l] [Fintype q]
    [DecidableEq k] [DecidableEq l] [DecidableEq q] in
/-- Bridge `Fin n` summation to `Finset.range n` summation for rectangular IV
cross moments. -/
@[simp]
theorem sum_fin_eq_sum_range_vecMulVec_rect
    (Z : ℕ → Omega → l → ℝ) (X : ℕ → Omega → k → ℝ) (n : ℕ) (ω : Omega) :
    (∑ i : Fin n, Matrix.vecMulVec (Z i.val ω) (X i.val ω)) =
      ∑ i ∈ Finset.range n, Matrix.vecMulVec (Z i ω) (X i ω) :=
  Fin.sum_univ_eq_sum_range (fun i => Matrix.vecMulVec (Z i ω) (X i ω)) n

omit [MeasurableSpace Omega] [Fintype l] [Fintype q]
    [DecidableEq k] [DecidableEq l] [DecidableEq q] in
/-- Hansen's normalized stacked IV score moment is the sample average of
`Zᵢ eᵢ`. -/
@[simp]
theorem ivNormalizedScore_stack_eq_avg
    (Z : ℕ → Omega → l → ℝ) (e : ℕ → Omega → ℝ) (n : ℕ) (ω : Omega) :
    ivNormalizedScore (stackRegressors Z n ω) (stackErrors e n ω) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, e i.val ω • Z i.val ω := by
  unfold ivNormalizedScore
  rw [stackRegressors_transpose_mulVec_stackErrors_eq_sum]
  simp [Fintype.card_fin]

/-- Population instrument moment `Q_ZZ = E[Z Z']`. -/
noncomputable def ivPopInstrumentMoment
    (mu : Measure Omega) (Z : ℕ → Omega → l → ℝ) : Matrix l l ℝ :=
  mu[fun ω => Matrix.vecMulVec (Z 0 ω) (Z 0 ω)]

/-- Population instrument/regressor cross moment `Q_ZX = E[Z X']`. -/
noncomputable def ivPopCrossMoment
    (mu : Measure Omega) (Z : ℕ → Omega → l → ℝ) (X : ℕ → Omega → k → ℝ) :
    Matrix l k ℝ :=
  mu[fun ω => Matrix.vecMulVec (Z 0 ω) (X 0 ω)]

/-- Population instrument/error moment `E[Z e]`. -/
noncomputable def ivPopScoreMoment
    (mu : Measure Omega) (Z : ℕ → Omega → l → ℝ) (e : ℕ → Omega → ℝ) : l → ℝ :=
  mu[fun ω => e 0 ω • Z 0 ω]

/-- Moment-level proof package for the WLLN part of Hansen Assumption 12.1.

This records the transformed iid/integrability hypotheses used to prove
convergence of `n⁻¹Z'Z`, `n⁻¹Z'X`, and `n⁻¹Z'e`. Hansen's raw iid and finite
second-moment assumptions imply these fields; they are kept explicit here so
the Chapter 12 proof can reuse the existing Banach-valued WLLN. -/
structure IVSampleMomentAssumption12_1
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : ℕ → Omega → k → ℝ) (Z : ℕ → Omega → l → ℝ) (e : ℕ → Omega → ℝ) where
  indep_ZZ :
    Pairwise ((· ⟂ᵢ[mu] ·) on (fun i ω => Matrix.vecMulVec (Z i ω) (Z i ω)))
  ident_ZZ : ∀ i,
    IdentDistrib (fun ω => Matrix.vecMulVec (Z i ω) (Z i ω))
      (fun ω => Matrix.vecMulVec (Z 0 ω) (Z 0 ω)) mu mu
  int_ZZ : Integrable (fun ω => Matrix.vecMulVec (Z 0 ω) (Z 0 ω)) mu
  indep_ZX :
    Pairwise ((· ⟂ᵢ[mu] ·) on (fun i ω => Matrix.vecMulVec (Z i ω) (X i ω)))
  ident_ZX : ∀ i,
    IdentDistrib (fun ω => Matrix.vecMulVec (Z i ω) (X i ω))
      (fun ω => Matrix.vecMulVec (Z 0 ω) (X 0 ω)) mu mu
  int_ZX : Integrable (fun ω => Matrix.vecMulVec (Z 0 ω) (X 0 ω)) mu
  indep_Ze : Pairwise ((· ⟂ᵢ[mu] ·) on (fun i ω => e i ω • Z i ω))
  ident_Ze : ∀ i,
    IdentDistrib (fun ω => e i ω • Z i ω) (fun ω => e 0 ω • Z 0 ω) mu mu
  int_Ze : Integrable (fun ω => e 0 ω • Z 0 ω) mu
  QZZ_nonsing : IsUnit (ivPopInstrumentMoment mu Z).det
  bread_nonsing :
    IsUnit ((ivPopCrossMoment mu Z X)ᵀ *
      (ivPopInstrumentMoment mu Z)⁻¹ * ivPopCrossMoment mu Z X).det
  orthogonality : ivPopScoreMoment mu Z e = 0

/-- WLLN for Hansen's normalized sample instrument moment `n⁻¹Z'Z`. -/
theorem ivNormalizedInstrumentMoment_stack_tendstoInMeasure_pop
    {X : ℕ → Omega → k → ℝ} {Z : ℕ → Omega → l → ℝ} {e : ℕ → Omega → ℝ}
    (h : IVSampleMomentAssumption12_1 mu X Z e) :
    TendstoInMeasure mu
      (fun n ω => ivNormalizedInstrumentMoment (stackRegressors Z n ω))
      atTop (fun _ => ivPopInstrumentMoment mu Z) := by
  simp only [ivNormalizedInstrumentMoment, stackRegressors_transpose_mul_self_eq_sum,
    Fintype.card_fin, sum_fin_eq_sum_range_vecMulVec]
  exact tendstoInMeasure_wlln
    (fun i ω => Matrix.vecMulVec (Z i ω) (Z i ω))
    h.int_ZZ h.indep_ZZ h.ident_ZZ

/-- Measurability of Hansen's normalized sample instrument moment. -/
theorem ivNormalizedInstrumentMoment_stack_aestronglyMeasurable
    {X : ℕ → Omega → k → ℝ} {Z : ℕ → Omega → l → ℝ} {e : ℕ → Omega → ℝ}
    (h : IVSampleMomentAssumption12_1 mu X Z e) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω => ivNormalizedInstrumentMoment (stackRegressors Z n ω)) mu := by
  simp only [ivNormalizedInstrumentMoment, stackRegressors_transpose_mul_self_eq_sum,
    Fintype.card_fin, sum_fin_eq_sum_range_vecMulVec]
  refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact ((h.ident_ZZ i).integrable_iff.mpr h.int_ZZ).aestronglyMeasurable

/-- WLLN for Hansen's normalized sample IV cross moment `n⁻¹Z'X`. -/
theorem ivNormalizedCrossMoment_stack_tendstoInMeasure_pop
    {X : ℕ → Omega → k → ℝ} {Z : ℕ → Omega → l → ℝ} {e : ℕ → Omega → ℝ}
    (h : IVSampleMomentAssumption12_1 mu X Z e) :
    TendstoInMeasure mu
      (fun n ω => ivNormalizedCrossMoment (stackRegressors Z n ω) (stackRegressors X n ω))
      atTop (fun _ => ivPopCrossMoment mu Z X) := by
  simp only [ivNormalizedCrossMoment_stack_eq_avg, sum_fin_eq_sum_range_vecMulVec_rect]
  exact tendstoInMeasure_wlln
    (fun i ω => Matrix.vecMulVec (Z i ω) (X i ω))
    h.int_ZX h.indep_ZX h.ident_ZX

/-- Measurability of Hansen's normalized sample IV cross moment. -/
theorem ivNormalizedCrossMoment_stack_aestronglyMeasurable
    {X : ℕ → Omega → k → ℝ} {Z : ℕ → Omega → l → ℝ} {e : ℕ → Omega → ℝ}
    (h : IVSampleMomentAssumption12_1 mu X Z e) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω => ivNormalizedCrossMoment (stackRegressors Z n ω) (stackRegressors X n ω)) mu := by
  simp only [ivNormalizedCrossMoment_stack_eq_avg, sum_fin_eq_sum_range_vecMulVec_rect]
  refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact ((h.ident_ZX i).integrable_iff.mpr h.int_ZX).aestronglyMeasurable

/-- WLLN for Hansen's normalized sample IV score moment `n⁻¹Z'e`. -/
theorem ivNormalizedScore_stack_tendstoInMeasure_zero
    {X : ℕ → Omega → k → ℝ} {Z : ℕ → Omega → l → ℝ} {e : ℕ → Omega → ℝ}
    (h : IVSampleMomentAssumption12_1 mu X Z e) :
    TendstoInMeasure mu
      (fun n ω => ivNormalizedScore (stackRegressors Z n ω) (stackErrors e n ω))
      atTop (fun _ => (0 : l → ℝ)) := by
  simp only [ivNormalizedScore_stack_eq_avg, sum_fin_eq_sum_range_smul]
  rw [show (fun _ : Omega => (0 : l → ℝ)) =
      (fun _ : Omega => ivPopScoreMoment mu Z e) by rw [h.orthogonality]]
  exact tendstoInMeasure_wlln
    (fun i ω => e i ω • Z i ω)
    h.int_Ze h.indep_Ze h.ident_Ze

/-- Measurability of Hansen's normalized sample IV score moment. -/
theorem ivNormalizedScore_stack_aestronglyMeasurable
    {X : ℕ → Omega → k → ℝ} {Z : ℕ → Omega → l → ℝ} {e : ℕ → Omega → ℝ}
    (h : IVSampleMomentAssumption12_1 mu X Z e) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω => ivNormalizedScore (stackRegressors Z n ω) (stackErrors e n ω)) mu := by
  simp only [ivNormalizedScore_stack_eq_avg, sum_fin_eq_sum_range_smul]
  refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact ((h.ident_Ze i).integrable_iff.mpr h.int_Ze).aestronglyMeasurable

set_option maxHeartbeats 500000 in
-- Product-space and additive CMT synthesis for rectangular IV moments is expensive here.
/-- WLLN for Hansen's normalized sample IV outcome moment under the structural
equation `Yᵢ = Xᵢ'β + eᵢ`.

This is the theorem-facing bridge that turns the primitive WLLNs for `n⁻¹Z'X`
and `n⁻¹Z'e` into the population moment restriction
`plim n⁻¹Z'Y = Q_ZX β`. -/
theorem ivNormalizedOutcomeMoment_stack_tendstoInMeasure_structural
    {X : ℕ → Omega → k → ℝ} {Z : ℕ → Omega → l → ℝ}
    {e y : ℕ → Omega → ℝ} (β : k → ℝ)
    (h : IVSampleMomentAssumption12_1 mu X Z e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure mu
      (fun n ω => ivNormalizedOutcomeMoment (stackRegressors Z n ω) (stackOutcomes y n ω))
      atTop (fun _ => ivPopCrossMoment mu Z X *ᵥ β) := by
  have hCross := ivNormalizedCrossMoment_stack_tendstoInMeasure_pop h
  have hCrossMeas : ∀ n, AEStronglyMeasurable
      (fun ω => ivNormalizedCrossMoment (stackRegressors Z n ω) (stackRegressors X n ω)) mu :=
    fun n => ivNormalizedCrossMoment_stack_aestronglyMeasurable h n
  have hCrossBetaMeas : ∀ n, AEStronglyMeasurable
      (fun ω => ivNormalizedCrossMoment (stackRegressors Z n ω) (stackRegressors X n ω) *ᵥ β)
      mu := by
    intro n
    exact (Continuous.matrix_mulVec continuous_id continuous_const).comp_aestronglyMeasurable
      (hCrossMeas n)
  have hCrossBeta : TendstoInMeasure mu
      (fun n ω => ivNormalizedCrossMoment (stackRegressors Z n ω)
        (stackRegressors X n ω) *ᵥ β)
      atTop (fun _ => ivPopCrossMoment mu Z X *ᵥ β) :=
    tendstoInMeasure_continuous_comp hCrossMeas hCross
      (Continuous.matrix_mulVec continuous_id continuous_const)
  have hScore := ivNormalizedScore_stack_tendstoInMeasure_zero h
  have hScoreMeas : ∀ n, AEStronglyMeasurable
      (fun ω => ivNormalizedScore (stackRegressors Z n ω) (stackErrors e n ω)) mu :=
    fun n => ivNormalizedScore_stack_aestronglyMeasurable h n
  have hSum := tendstoInMeasure_add hCrossBetaMeas hScoreMeas hCrossBeta hScore
  simp only [add_zero] at hSum
  refine hSum.congr_left (fun n => ae_of_all mu (fun ω => ?_))
  symm
  change ivNormalizedOutcomeMoment (stackRegressors Z n ω) (stackOutcomes y n ω) =
    ivNormalizedCrossMoment (stackRegressors Z n ω) (stackRegressors X n ω) *ᵥ β +
      ivNormalizedScore (stackRegressors Z n ω) (stackErrors e n ω)
  rw [stack_linear_model X e y β hmodel n ω]
  exact ivNormalizedOutcomeMoment_linear_model
    (stackRegressors X n ω) (stackRegressors Z n ω) β (stackErrors e n ω)

/-- High-level consistency interface used by the Chapter 12 2SLS route. -/
structure IVConsistencyInterface
    (betahat : ℕ → Omega → k → ℝ) (beta : k → ℝ) : Prop where
  consistent : TendstoInMeasure mu betahat atTop (fun _ => beta)

/-- High-level Gaussian-limit interface used by the Chapter 12 2SLS route. -/
structure IVGaussianLimitInterface
    (T : ℕ → Omega → k → ℝ) (QZX : Matrix l k ℝ) (QZZ OmegaMat : Matrix l l ℝ) :
    Prop where
  gaussian_limit : GaussianLimit mu T (tslsAsymptoticVariance QZX QZZ OmegaMat)

omit [IsProbabilityMeasure mu] [DecidableEq k] in
/-- Interface projection for 2SLS consistency. -/
theorem twoStageLeastSquares_consistent_from_interface
    (betahat : ℕ → Omega → k → ℝ) (beta : k → ℝ)
    (h : IVConsistencyInterface (mu := mu) betahat beta) :
    TendstoInMeasure mu betahat atTop (fun _ => beta) :=
  h.consistent

omit [IsProbabilityMeasure mu] in
/-- **Hansen Theorem 12.1, population-moment identification layer.**

Once an estimator is known to converge to the population moment-form 2SLS map,
the moment restriction `Q_ZY = Q_ZX β` and nonsingularity of
`Q_ZX' Q_ZZ⁻¹ Q_ZX` identify the probability limit as `β`. Raw sample-moment
constructors should target the premise of this theorem. -/
theorem twoStageLeastSquares_consistent_from_population_moment_limit
    (betahat : ℕ → Omega → k → ℝ)
    (QZX : Matrix l k ℝ) (QZZ : Matrix l l ℝ) (QZY : l → ℝ) (beta : k → ℝ)
    (hlim : TendstoInMeasure mu betahat atTop
      (fun _ => twoStageLeastSquaresMomentBeta QZX QZZ QZY))
    (hQZY : QZY = QZX *ᵥ beta)
    (hunit : IsUnit (QZXᵀ * QZZ⁻¹ * QZX).det) :
    TendstoInMeasure mu betahat atTop (fun _ => beta) := by
  simpa [twoStageLeastSquaresMomentBeta_eq_beta QZX QZZ QZY beta hQZY hunit] using hlim

set_option maxHeartbeats 800000 in
-- Measurability through nested finite-dimensional matrix inverses and products is expensive here.
omit [IsProbabilityMeasure mu] [Fintype q] [DecidableEq q] in
/-- The moment-form 2SLS map is a.e. strongly measurable whenever its sample
moment inputs are. -/
theorem twoStageLeastSquaresMomentBeta_aestronglyMeasurable
    (QZXseq : Omega → Matrix l k ℝ) (QZZseq : Omega → Matrix l l ℝ)
    (QZYseq : Omega → l → ℝ)
    (hQZX : AEStronglyMeasurable QZXseq mu)
    (hQZZ : AEStronglyMeasurable QZZseq mu)
    (hQZY : AEStronglyMeasurable QZYseq mu) :
    AEStronglyMeasurable
      (fun ω => twoStageLeastSquaresMomentBeta (QZXseq ω) (QZZseq ω) (QZYseq ω)) mu := by
  have hQZXt : AEStronglyMeasurable (fun ω => (QZXseq ω)ᵀ) mu :=
    continuous_id.matrix_transpose.comp_aestronglyMeasurable hQZX
  have hQZZinv : AEStronglyMeasurable (fun ω => (QZZseq ω)⁻¹) mu :=
    aestronglyMeasurable_matrix_inv hQZZ
  have hLeft : AEStronglyMeasurable (fun ω => (QZXseq ω)ᵀ * (QZZseq ω)⁻¹) mu := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hQZXt.prodMk hQZZinv)
  have hBread : AEStronglyMeasurable
      (fun ω => (QZXseq ω)ᵀ * (QZZseq ω)⁻¹ * QZXseq ω) mu := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hLeft.prodMk hQZX)
  have hBreadInv : AEStronglyMeasurable
      (fun ω => ((QZXseq ω)ᵀ * (QZZseq ω)⁻¹ * QZXseq ω)⁻¹) mu :=
    aestronglyMeasurable_matrix_inv hBread
  have hNumerator : AEStronglyMeasurable
      (fun ω => ((QZXseq ω)ᵀ * (QZZseq ω)⁻¹) *ᵥ QZYseq ω) mu := by
    exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hLeft.prodMk hQZY)
  unfold twoStageLeastSquaresMomentBeta
  exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
    (hBreadInv.prodMk hNumerator)

set_option maxHeartbeats 800000 in
-- Continuity through nested finite-dimensional matrix inverses and products is expensive here.
omit [Fintype q] [DecidableEq q] in
/-- The moment-form 2SLS map is continuous at population moments with
nonsingular instrument moment matrix and nonsingular 2SLS bread matrix. -/
theorem twoStageLeastSquaresMomentBeta_continuousAt
    (QZX : Matrix l k ℝ) (QZZ : Matrix l l ℝ) (QZY : l → ℝ)
    (hQZZ : IsUnit QZZ.det)
    (hBread : IsUnit (QZXᵀ * QZZ⁻¹ * QZX).det) :
    ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × (l → ℝ) =>
        twoStageLeastSquaresMomentBeta p.1.1 p.1.2 p.2)
      ((QZX, QZZ), QZY) := by
  let B : Matrix k k ℝ := QZXᵀ * QZZ⁻¹ * QZX
  have hQZXc : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × (l → ℝ) => p.1.1)
      ((QZX, QZZ), QZY) :=
    continuousAt_fst.comp continuousAt_fst
  have hQZZc : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × (l → ℝ) => p.1.2)
      ((QZX, QZZ), QZY) :=
    continuousAt_snd.comp continuousAt_fst
  have hQZYc : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × (l → ℝ) => p.2)
      ((QZX, QZZ), QZY) :=
    continuousAt_snd
  have hQZXt : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × (l → ℝ) => p.1.1ᵀ)
      ((QZX, QZZ), QZY) :=
    continuous_id.matrix_transpose.continuousAt.comp hQZXc
  have hQZZinv : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × (l → ℝ) => p.1.2⁻¹)
      ((QZX, QZZ), QZY) := by
    have hcontInv : ContinuousAt Inv.inv QZZ := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hQZZ.ne_zero
    exact hcontInv.comp hQZZc
  have hLeft : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × (l → ℝ) => p.1.1ᵀ * p.1.2⁻¹)
      ((QZX, QZZ), QZY) :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hQZXt.prodMk hQZZinv)
  have hBreadc : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × (l → ℝ) => p.1.1ᵀ * p.1.2⁻¹ * p.1.1)
      ((QZX, QZZ), QZY) :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hLeft.prodMk hQZXc)
  have hBreadInv : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × (l → ℝ) =>
        (p.1.1ᵀ * p.1.2⁻¹ * p.1.1)⁻¹)
      ((QZX, QZZ), QZY) := by
    have hcontInv : ContinuousAt Inv.inv B := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hBread.ne_zero
    simpa [B] using hcontInv.comp hBreadc
  have hNumerator : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × (l → ℝ) =>
        (p.1.1ᵀ * p.1.2⁻¹) *ᵥ p.2)
      ((QZX, QZZ), QZY) :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).continuousAt.comp
      (hLeft.prodMk hQZYc)
  unfold twoStageLeastSquaresMomentBeta
  exact (Continuous.matrix_mulVec continuous_fst continuous_snd).continuousAt.comp
    (hBreadInv.prodMk hNumerator)

set_option maxHeartbeats 800000 in
-- Product-space CMT for the 2SLS moment map carries finite-dimensional matrix topology.
omit [Fintype q] [DecidableEq q] in
/-- **Hansen Theorem 12.1, sample-moment continuous-mapping layer.**

If the sample 2SLS moments converge to the corresponding population moments,
then the moment-form 2SLS estimator converges to the population moment-form
2SLS map. -/
theorem twoStageLeastSquaresMomentBeta_tendstoInMeasure_of_moments
    {QZXhat : ℕ → Omega → Matrix l k ℝ} {QZZhat : ℕ → Omega → Matrix l l ℝ}
    {QZYhat : ℕ → Omega → l → ℝ}
    {QZX : Matrix l k ℝ} {QZZ : Matrix l l ℝ} {QZY : l → ℝ}
    (hQZX_meas : ∀ n, AEStronglyMeasurable (QZXhat n) mu)
    (hQZZ_meas : ∀ n, AEStronglyMeasurable (QZZhat n) mu)
    (hQZY_meas : ∀ n, AEStronglyMeasurable (QZYhat n) mu)
    (hQZX : TendstoInMeasure mu QZXhat atTop (fun _ => QZX))
    (hQZZ : TendstoInMeasure mu QZZhat atTop (fun _ => QZZ))
    (hQZY : TendstoInMeasure mu QZYhat atTop (fun _ => QZY))
    (hQZZunit : IsUnit QZZ.det)
    (hBread : IsUnit (QZXᵀ * QZZ⁻¹ * QZX).det) :
    TendstoInMeasure mu
      (fun n ω => twoStageLeastSquaresMomentBeta (QZXhat n ω) (QZZhat n ω) (QZYhat n ω))
      atTop (fun _ => twoStageLeastSquaresMomentBeta QZX QZZ QZY) := by
  have hpair : TendstoInMeasure mu
      (fun n ω => (QZXhat n ω, QZZhat n ω)) atTop
      (fun _ : Omega => (QZX, QZZ)) :=
    tendstoInMeasure_prodMk hQZX hQZZ
  have htriple : TendstoInMeasure mu
      (fun n ω => ((QZXhat n ω, QZZhat n ω), QZYhat n ω)) atTop
      (fun _ : Omega => ((QZX, QZZ), QZY)) :=
    tendstoInMeasure_prodMk hpair hQZY
  exact tendstoInMeasure_continuousAt_const_comp
    (fun n => ((hQZX_meas n).prodMk (hQZZ_meas n)).prodMk (hQZY_meas n))
    (fun n => twoStageLeastSquaresMomentBeta_aestronglyMeasurable
      (QZXhat n) (QZZhat n) (QZYhat n) (hQZX_meas n) (hQZZ_meas n) (hQZY_meas n))
    htriple (twoStageLeastSquaresMomentBeta_continuousAt QZX QZZ QZY hQZZunit hBread)

set_option maxHeartbeats 800000 in
-- Reusing the sample-moment CMT layer keeps the Hansen-facing consistency corollary direct.
omit [Fintype q] [DecidableEq q] in
/-- **Hansen Theorem 12.1, moment-convergence consistency layer.**

This composes the sample-moment continuous mapping result with the population
identification identity `Q_ZY = Q_ZX β`. -/
theorem twoStageLeastSquares_consistent_from_moment_convergence
    {QZXhat : ℕ → Omega → Matrix l k ℝ} {QZZhat : ℕ → Omega → Matrix l l ℝ}
    {QZYhat : ℕ → Omega → l → ℝ}
    {QZX : Matrix l k ℝ} {QZZ : Matrix l l ℝ} {QZY : l → ℝ} {beta : k → ℝ}
    (hQZX_meas : ∀ n, AEStronglyMeasurable (QZXhat n) mu)
    (hQZZ_meas : ∀ n, AEStronglyMeasurable (QZZhat n) mu)
    (hQZY_meas : ∀ n, AEStronglyMeasurable (QZYhat n) mu)
    (hQZX : TendstoInMeasure mu QZXhat atTop (fun _ => QZX))
    (hQZZ : TendstoInMeasure mu QZZhat atTop (fun _ => QZZ))
    (hQZYhat : TendstoInMeasure mu QZYhat atTop (fun _ => QZY))
    (hQZY : QZY = QZX *ᵥ beta)
    (hQZZunit : IsUnit QZZ.det)
    (hBread : IsUnit (QZXᵀ * QZZ⁻¹ * QZX).det) :
    TendstoInMeasure mu
      (fun n ω => twoStageLeastSquaresMomentBeta (QZXhat n ω) (QZZhat n ω) (QZYhat n ω))
      atTop (fun _ => beta) := by
  have hlim : TendstoInMeasure mu
      (fun n ω => twoStageLeastSquaresMomentBeta (QZXhat n ω) (QZZhat n ω) (QZYhat n ω))
      atTop (fun _ => twoStageLeastSquaresMomentBeta QZX QZZ QZY) :=
    twoStageLeastSquaresMomentBeta_tendstoInMeasure_of_moments
      hQZX_meas hQZZ_meas hQZY_meas hQZX hQZZ hQZYhat hQZZunit hBread
  exact twoStageLeastSquares_consistent_from_population_moment_limit
    (fun n ω => twoStageLeastSquaresMomentBeta (QZXhat n ω) (QZZhat n ω) (QZYhat n ω))
    QZX QZZ QZY beta hlim hQZY hBread

set_option maxHeartbeats 800000 in
-- This theorem composes three finite-dimensional WLLNs with the existing 2SLS moment-map CMT.
/-- **Hansen Theorem 12.1, moment-form 2SLS consistency from Assumption 12.1.**

Under the Chapter 12 moment-level assumption package and the structural equation
`Yᵢ = Xᵢ'β + eᵢ`, the normalized-moment 2SLS map converges in probability to
the structural coefficient. -/
theorem twoStageLeastSquaresMomentBeta_stack_consistent_structural
    {X : ℕ → Omega → k → ℝ} {Z : ℕ → Omega → l → ℝ}
    {e y : ℕ → Omega → ℝ} (β : k → ℝ)
    (h : IVSampleMomentAssumption12_1 mu X Z e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure mu
      (fun n ω => twoStageLeastSquaresMomentBeta
        (ivNormalizedCrossMoment (stackRegressors Z n ω) (stackRegressors X n ω))
        (ivNormalizedInstrumentMoment (stackRegressors Z n ω))
        (ivNormalizedOutcomeMoment (stackRegressors Z n ω) (stackOutcomes y n ω)))
      atTop (fun _ => β) := by
  have hQZX_meas : ∀ n, AEStronglyMeasurable
      (fun ω => ivNormalizedCrossMoment (stackRegressors Z n ω) (stackRegressors X n ω)) mu :=
    fun n => ivNormalizedCrossMoment_stack_aestronglyMeasurable h n
  have hQZZ_meas : ∀ n, AEStronglyMeasurable
      (fun ω => ivNormalizedInstrumentMoment (stackRegressors Z n ω)) mu :=
    fun n => ivNormalizedInstrumentMoment_stack_aestronglyMeasurable h n
  have hQZY_meas : ∀ n, AEStronglyMeasurable
      (fun ω => ivNormalizedOutcomeMoment (stackRegressors Z n ω) (stackOutcomes y n ω)) mu := by
    intro n
    have hCrossBeta : AEStronglyMeasurable
        (fun ω => ivNormalizedCrossMoment (stackRegressors Z n ω) (stackRegressors X n ω) *ᵥ β)
        mu :=
      (Continuous.matrix_mulVec continuous_id continuous_const).comp_aestronglyMeasurable
        (hQZX_meas n)
    have hScore : AEStronglyMeasurable
        (fun ω => ivNormalizedScore (stackRegressors Z n ω) (stackErrors e n ω)) mu :=
      ivNormalizedScore_stack_aestronglyMeasurable h n
    refine (hCrossBeta.add hScore).congr (ae_of_all mu (fun ω => ?_))
    symm
    change ivNormalizedOutcomeMoment (stackRegressors Z n ω) (stackOutcomes y n ω) =
      ivNormalizedCrossMoment (stackRegressors Z n ω) (stackRegressors X n ω) *ᵥ β +
        ivNormalizedScore (stackRegressors Z n ω) (stackErrors e n ω)
    rw [stack_linear_model X e y β hmodel n ω]
    exact ivNormalizedOutcomeMoment_linear_model
      (stackRegressors X n ω) (stackRegressors Z n ω) β (stackErrors e n ω)
  exact twoStageLeastSquares_consistent_from_moment_convergence
    hQZX_meas hQZZ_meas hQZY_meas
    (ivNormalizedCrossMoment_stack_tendstoInMeasure_pop h)
    (ivNormalizedInstrumentMoment_stack_tendstoInMeasure_pop h)
    (ivNormalizedOutcomeMoment_stack_tendstoInMeasure_structural β h hmodel)
    rfl h.QZZ_nonsing h.bread_nonsing

set_option maxHeartbeats 800000 in
-- The proof reindexes the normalized moment-map theorem and then applies the finite-sample bridge.
/-- **Hansen Theorem 12.1, shifted finite-sample 2SLS consistency layer.**

For samples of size `n + 1`, the displayed total 2SLS estimator equals the
normalized moment-form estimator and therefore converges in probability to the
structural coefficient under the Chapter 12 moment-level assumptions. The shift
only excludes the empty-sample normalization corner. -/
theorem twoStageLeastSquaresBeta_stack_succ_consistent_structural
    {X : ℕ → Omega → k → ℝ} {Z : ℕ → Omega → l → ℝ}
    {e y : ℕ → Omega → ℝ} (β : k → ℝ)
    (h : IVSampleMomentAssumption12_1 mu X Z e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure mu
      (fun n ω => twoStageLeastSquaresBeta
        (stackRegressors X (n + 1) ω)
        (stackRegressors Z (n + 1) ω)
        (stackOutcomes y (n + 1) ω))
      atTop (fun _ => β) := by
  have hMoment :=
    twoStageLeastSquaresMomentBeta_stack_consistent_structural β h hmodel
  have hShift : TendstoInMeasure mu
      ((fun n ω => twoStageLeastSquaresMomentBeta
        (ivNormalizedCrossMoment (stackRegressors Z n ω) (stackRegressors X n ω))
        (ivNormalizedInstrumentMoment (stackRegressors Z n ω))
        (ivNormalizedOutcomeMoment (stackRegressors Z n ω) (stackOutcomes y n ω))) ∘
          (fun n => n + 1))
      atTop (fun _ => β) :=
    hMoment.comp (tendsto_add_atTop_nat 1)
  refine hShift.congr_left (fun n => ae_of_all mu (fun ω => ?_))
  change twoStageLeastSquaresMomentBeta
      (ivNormalizedCrossMoment (stackRegressors Z (n + 1) ω) (stackRegressors X (n + 1) ω))
      (ivNormalizedInstrumentMoment (stackRegressors Z (n + 1) ω))
      (ivNormalizedOutcomeMoment (stackRegressors Z (n + 1) ω) (stackOutcomes y (n + 1) ω)) =
    twoStageLeastSquaresBeta
      (stackRegressors X (n + 1) ω)
      (stackRegressors Z (n + 1) ω)
      (stackOutcomes y (n + 1) ω)
  exact (twoStageLeastSquaresBeta_eq_normalizedSampleMoments
    (stackRegressors X (n + 1) ω)
    (stackRegressors Z (n + 1) ω)
    (stackOutcomes y (n + 1) ω)).symm

/-- Interface projection for 2SLS asymptotic normality. -/
theorem twoStageLeastSquares_gaussianLimit_from_interface
    (T : ℕ → Omega → k → ℝ) (QZX : Matrix l k ℝ) (QZZ OmegaMat : Matrix l l ℝ)
    (h : IVGaussianLimitInterface (mu := mu) T QZX QZZ OmegaMat) :
    GaussianLimit mu T (tslsAsymptoticVariance QZX QZZ OmegaMat) :=
  h.gaussian_limit

/-- Distributional face of `twoStageLeastSquares_gaussianLimit_from_interface`. -/
theorem twoStageLeastSquares_tendstoInDistribution_from_interface
    (T : ℕ → Omega → k → ℝ) (QZX : Matrix l k ℝ) (QZZ OmegaMat : Matrix l l ℝ)
    (h : IVGaussianLimitInterface (mu := mu) T QZX QZZ OmegaMat) :
    TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => mu) (multivariateGaussian 0 (tslsAsymptoticVariance QZX QZZ OmegaMat)) :=
  h.gaussian_limit.limit

/-- **Hansen Theorem 12.2, IV score CLT layer.**

The instrument score `√n n⁻¹ Z'e` is exactly Chapter 7's score process with
the instrument vector used as the regressor vector. -/
theorem ivScore_tendstoInDistribution_multivariateGaussian
    {Z : ℕ → Omega → l → ℝ} {e : ℕ → Omega → ℝ}
    (h : ScoreCLTConditions mu Z e) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          ivNormalizedScore (stackRegressors Z n ω) (stackErrors e n ω))
      atTop
      (fun z : EuclideanSpace ℝ l => z.ofLp)
      (fun _ => mu)
      (multivariateGaussian 0 (scoreCovMat mu Z e)) := by
  simpa [ivNormalizedScore, sampleCrossMoment] using
    scoreVector_sampleCrossMoment_tendstoInDistribution_multivariateGaussian
      (μ := mu) (X := Z) (e := e) h

/-- Gaussian-limit packaging of the IV score CLT. -/
theorem ivScore_gaussianLimit
    {Z : ℕ → Omega → l → ℝ} {e : ℕ → Omega → ℝ}
    (h : ScoreCLTConditions mu Z e) :
    GaussianLimit mu
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          ivNormalizedScore (stackRegressors Z n ω) (stackErrors e n ω))
      (scoreCovMat mu Z e) :=
  gaussianLimit_of_tendstoInDistribution
    (fun (n : ℕ) ω =>
      Real.sqrt (n : ℝ) •
        ivNormalizedScore (stackRegressors Z n ω) (stackErrors e n ω))
    (scoreCovMat mu Z e)
    (scoreCovMat_posSemidef (μ := mu) (X := Z) (e := e) h.toSampleCLTAssumption72)
    (ivScore_tendstoInDistribution_multivariateGaussian (mu := mu) (Z := Z) (e := e) h)

/-- **Hansen Theorem 12.2, influence-function Slutsky layer.**

If a scaled 2SLS coefficient error has the influence expansion
`A · √n n⁻¹Z'e + oₚ(1)`, where
`A = (Q_ZX' Q_ZZ⁻¹ Q_ZX)⁻¹ Q_ZX' Q_ZZ⁻¹`, and the score has a Gaussian
limit, then the scaled error is asymptotically Gaussian with the linear-image
covariance. -/
theorem twoStageLeastSquares_tendstoInDistribution_from_score_linearization
    (scaledError : ℕ → Omega → k → ℝ) (score : ℕ → Omega → l → ℝ)
    (QZX : Matrix l k ℝ) (QZZ OmegaMat : Matrix l l ℝ)
    (hlinear : TendstoInMeasure mu
      (scaledError - fun n ω => tslsInfluenceMatrix QZX QZZ *ᵥ score n ω)
      atTop (fun _ => 0))
    (hmeas : ∀ n, AEMeasurable (scaledError n) mu)
    (hScore : GaussianLimit mu score OmegaMat) :
    TendstoInDistribution scaledError atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0
        (tslsInfluenceMatrix QZX QZZ * OmegaMat * (tslsInfluenceMatrix QZX QZZ)ᵀ)) := by
  have hlin :=
    (gaussianLimit_linearMap score OmegaMat (tslsInfluenceMatrix QZX QZZ) hScore).limit
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n ω => tslsInfluenceMatrix QZX QZZ *ᵥ score n ω)
    (Y := scaledError)
    (Z := fun z : EuclideanSpace ℝ k => z.ofLp)
    hlin hlinear hmeas

/-- **Hansen Theorem 12.2, Chapter 7 score-CLT specialization.**

This specializes the influence-function Slutsky layer to the IV score CLT
discharged by Chapter 7's `ScoreCLTConditions` applied to the instruments. -/
theorem twoStageLeastSquares_tendstoInDistribution_from_ivScore_linearization
    (scaledError : ℕ → Omega → k → ℝ)
    (QZX : Matrix l k ℝ) (QZZ : Matrix l l ℝ)
    {Z : ℕ → Omega → l → ℝ} {e : ℕ → Omega → ℝ}
    (hclt : ScoreCLTConditions mu Z e)
    (hlinear : TendstoInMeasure mu
      (scaledError - fun (n : ℕ) ω =>
        tslsInfluenceMatrix QZX QZZ *ᵥ
          (Real.sqrt (n : ℝ) •
            ivNormalizedScore (stackRegressors Z n ω) (stackErrors e n ω)))
      atTop (fun _ => 0))
    (hmeas : ∀ n, AEMeasurable (scaledError n) mu) :
    TendstoInDistribution scaledError atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => mu)
      (multivariateGaussian 0
        (tslsInfluenceMatrix QZX QZZ * scoreCovMat mu Z e *
          (tslsInfluenceMatrix QZX QZZ)ᵀ)) :=
  twoStageLeastSquares_tendstoInDistribution_from_score_linearization
    scaledError
    (fun (n : ℕ) ω =>
      Real.sqrt (n : ℝ) •
        ivNormalizedScore (stackRegressors Z n ω) (stackErrors e n ω))
    QZX QZZ (scoreCovMat mu Z e) hlinear hmeas (ivScore_gaussianLimit hclt)

set_option maxHeartbeats 1200000 in
-- Measurability through the 2SLS sandwich map has several matrix inverse/product layers.
omit [IsProbabilityMeasure mu] [Fintype q] [DecidableEq q] in
/-- The 2SLS sandwich variance map is a.e. strongly measurable whenever its
sample moment inputs are. -/
theorem tslsAsymptoticVariance_aestronglyMeasurable
    (QZXseq : Omega → Matrix l k ℝ) (QZZseq OmegaSeq : Omega → Matrix l l ℝ)
    (hQZX : AEStronglyMeasurable QZXseq mu)
    (hQZZ : AEStronglyMeasurable QZZseq mu)
    (hOmega : AEStronglyMeasurable OmegaSeq mu) :
    AEStronglyMeasurable
      (fun ω => tslsAsymptoticVariance (QZXseq ω) (QZZseq ω) (OmegaSeq ω)) mu := by
  have hQZXt : AEStronglyMeasurable (fun ω => (QZXseq ω)ᵀ) mu :=
    continuous_id.matrix_transpose.comp_aestronglyMeasurable hQZX
  have hQZZinv : AEStronglyMeasurable (fun ω => (QZZseq ω)⁻¹) mu :=
    aestronglyMeasurable_matrix_inv hQZZ
  have hLeft : AEStronglyMeasurable (fun ω => (QZXseq ω)ᵀ * (QZZseq ω)⁻¹) mu := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hQZXt.prodMk hQZZinv)
  have hBreadMat : AEStronglyMeasurable
      (fun ω => (QZXseq ω)ᵀ * (QZZseq ω)⁻¹ * QZXseq ω) mu := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hLeft.prodMk hQZX)
  have hBread : AEStronglyMeasurable
      (fun ω => ((QZXseq ω)ᵀ * (QZZseq ω)⁻¹ * QZXseq ω)⁻¹) mu :=
    aestronglyMeasurable_matrix_inv hBreadMat
  have hLeftOmega : AEStronglyMeasurable
      (fun ω => (QZXseq ω)ᵀ * (QZZseq ω)⁻¹ * OmegaSeq ω) mu := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hLeft.prodMk hOmega)
  have hLeftOmegaInv : AEStronglyMeasurable
      (fun ω => (QZXseq ω)ᵀ * (QZZseq ω)⁻¹ * OmegaSeq ω * (QZZseq ω)⁻¹) mu := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hLeftOmega.prodMk hQZZinv)
  have hMeat : AEStronglyMeasurable
      (fun ω => (QZXseq ω)ᵀ * (QZZseq ω)⁻¹ * OmegaSeq ω * (QZZseq ω)⁻¹ * QZXseq ω)
      mu := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hLeftOmegaInv.prodMk hQZX)
  have hBreadMeat : AEStronglyMeasurable
      (fun ω =>
        ((QZXseq ω)ᵀ * (QZZseq ω)⁻¹ * QZXseq ω)⁻¹ *
          ((QZXseq ω)ᵀ * (QZZseq ω)⁻¹ * OmegaSeq ω * (QZZseq ω)⁻¹ * QZXseq ω))
      mu := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hBread.prodMk hMeat)
  unfold tslsAsymptoticVariance tslsBread tslsMeat
  exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
    (hBreadMeat.prodMk hBread)

set_option maxHeartbeats 1200000 in
-- Continuity through the 2SLS sandwich map has several matrix inverse/product layers.
omit [Fintype q] [DecidableEq q] in
/-- The 2SLS sandwich variance map is continuous at population moments with
nonsingular instrument moment matrix and nonsingular 2SLS bread matrix. -/
theorem tslsAsymptoticVariance_continuousAt
    (QZX : Matrix l k ℝ) (QZZ OmegaMat : Matrix l l ℝ)
    (hQZZ : IsUnit QZZ.det)
    (hBreadUnit : IsUnit (QZXᵀ * QZZ⁻¹ * QZX).det) :
    ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × Matrix l l ℝ =>
        tslsAsymptoticVariance p.1.1 p.1.2 p.2)
      ((QZX, QZZ), OmegaMat) := by
  let B : Matrix k k ℝ := QZXᵀ * QZZ⁻¹ * QZX
  have hQZXc : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × Matrix l l ℝ => p.1.1)
      ((QZX, QZZ), OmegaMat) :=
    continuousAt_fst.comp continuousAt_fst
  have hQZZc : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × Matrix l l ℝ => p.1.2)
      ((QZX, QZZ), OmegaMat) :=
    continuousAt_snd.comp continuousAt_fst
  have hOmegac : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × Matrix l l ℝ => p.2)
      ((QZX, QZZ), OmegaMat) :=
    continuousAt_snd
  have hQZXt : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × Matrix l l ℝ => p.1.1ᵀ)
      ((QZX, QZZ), OmegaMat) :=
    continuous_id.matrix_transpose.continuousAt.comp hQZXc
  have hQZZinv : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × Matrix l l ℝ => p.1.2⁻¹)
      ((QZX, QZZ), OmegaMat) := by
    have hcontInv : ContinuousAt Inv.inv QZZ := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hQZZ.ne_zero
    exact hcontInv.comp hQZZc
  have hLeft : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × Matrix l l ℝ => p.1.1ᵀ * p.1.2⁻¹)
      ((QZX, QZZ), OmegaMat) :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hQZXt.prodMk hQZZinv)
  have hBreadMat : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × Matrix l l ℝ =>
        p.1.1ᵀ * p.1.2⁻¹ * p.1.1)
      ((QZX, QZZ), OmegaMat) :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hLeft.prodMk hQZXc)
  have hBread : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × Matrix l l ℝ =>
        (p.1.1ᵀ * p.1.2⁻¹ * p.1.1)⁻¹)
      ((QZX, QZZ), OmegaMat) := by
    have hcontInv : ContinuousAt Inv.inv B := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hBreadUnit.ne_zero
    simpa [B] using hcontInv.comp hBreadMat
  have hLeftOmega : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × Matrix l l ℝ =>
        p.1.1ᵀ * p.1.2⁻¹ * p.2)
      ((QZX, QZZ), OmegaMat) :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hLeft.prodMk hOmegac)
  have hLeftOmegaInv : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × Matrix l l ℝ =>
        p.1.1ᵀ * p.1.2⁻¹ * p.2 * p.1.2⁻¹)
      ((QZX, QZZ), OmegaMat) :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hLeftOmega.prodMk hQZZinv)
  have hMeat : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × Matrix l l ℝ =>
        p.1.1ᵀ * p.1.2⁻¹ * p.2 * p.1.2⁻¹ * p.1.1)
      ((QZX, QZZ), OmegaMat) :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hLeftOmegaInv.prodMk hQZXc)
  have hBreadMeat : ContinuousAt
      (fun p : (Matrix l k ℝ × Matrix l l ℝ) × Matrix l l ℝ =>
        (p.1.1ᵀ * p.1.2⁻¹ * p.1.1)⁻¹ *
          (p.1.1ᵀ * p.1.2⁻¹ * p.2 * p.1.2⁻¹ * p.1.1))
      ((QZX, QZZ), OmegaMat) :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hBread.prodMk hMeat)
  unfold tslsAsymptoticVariance tslsBread tslsMeat
  exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
    (hBreadMeat.prodMk hBread)

set_option maxHeartbeats 1200000 in
-- Product-space CMT for the 2SLS sandwich map carries finite-dimensional matrix topology.
omit [Fintype q] [DecidableEq q] in
/-- **Hansen Theorem 12.3, covariance plug-in continuous-mapping layer.**

If the sample `Q_ZX`, `Q_ZZ`, and `Ω` components converge, then the robust
2SLS sandwich covariance plug-in converges to Hansen's asymptotic covariance
matrix. -/
theorem tslsAsymptoticVariance_tendstoInMeasure_of_moments
    {QZXhat : ℕ → Omega → Matrix l k ℝ} {QZZhat Omegahat : ℕ → Omega → Matrix l l ℝ}
    {QZX : Matrix l k ℝ} {QZZ OmegaMat : Matrix l l ℝ}
    (hQZX_meas : ∀ n, AEStronglyMeasurable (QZXhat n) mu)
    (hQZZ_meas : ∀ n, AEStronglyMeasurable (QZZhat n) mu)
    (hOmega_meas : ∀ n, AEStronglyMeasurable (Omegahat n) mu)
    (hQZX : TendstoInMeasure mu QZXhat atTop (fun _ => QZX))
    (hQZZ : TendstoInMeasure mu QZZhat atTop (fun _ => QZZ))
    (hOmega : TendstoInMeasure mu Omegahat atTop (fun _ => OmegaMat))
    (hQZZunit : IsUnit QZZ.det)
    (hBread : IsUnit (QZXᵀ * QZZ⁻¹ * QZX).det) :
    TendstoInMeasure mu
      (fun n ω => tslsAsymptoticVariance (QZXhat n ω) (QZZhat n ω) (Omegahat n ω))
      atTop (fun _ => tslsAsymptoticVariance QZX QZZ OmegaMat) := by
  have hpair : TendstoInMeasure mu
      (fun n ω => (QZXhat n ω, QZZhat n ω)) atTop
      (fun _ : Omega => (QZX, QZZ)) :=
    tendstoInMeasure_prodMk hQZX hQZZ
  have htriple : TendstoInMeasure mu
      (fun n ω => ((QZXhat n ω, QZZhat n ω), Omegahat n ω)) atTop
      (fun _ : Omega => ((QZX, QZZ), OmegaMat)) :=
    tendstoInMeasure_prodMk hpair hOmega
  exact tendstoInMeasure_continuousAt_const_comp
    (fun n => ((hQZX_meas n).prodMk (hQZZ_meas n)).prodMk (hOmega_meas n))
    (fun n => tslsAsymptoticVariance_aestronglyMeasurable
      (QZXhat n) (QZZhat n) (Omegahat n)
      (hQZX_meas n) (hQZZ_meas n) (hOmega_meas n))
    htriple (tslsAsymptoticVariance_continuousAt QZX QZZ OmegaMat hQZZunit hBread)

set_option maxHeartbeats 1200000 in
-- Constructor wrapper over the sandwich-map CMT.
omit [Fintype q] [DecidableEq q] in
/-- Stable covariance-consistency constructor for a robust 2SLS sandwich plug-in
whose moment components are consistent. -/
theorem tslsCovarianceEstimatorConsistent_of_moment_convergence
    {QZXhat : ℕ → Omega → Matrix l k ℝ} {QZZhat Omegahat : ℕ → Omega → Matrix l l ℝ}
    {QZX : Matrix l k ℝ} {QZZ OmegaMat : Matrix l l ℝ}
    (hQZX_meas : ∀ n, AEStronglyMeasurable (QZXhat n) mu)
    (hQZZ_meas : ∀ n, AEStronglyMeasurable (QZZhat n) mu)
    (hOmega_meas : ∀ n, AEStronglyMeasurable (Omegahat n) mu)
    (hQZX : TendstoInMeasure mu QZXhat atTop (fun _ => QZX))
    (hQZZ : TendstoInMeasure mu QZZhat atTop (fun _ => QZZ))
    (hOmega : TendstoInMeasure mu Omegahat atTop (fun _ => OmegaMat))
    (hQZZunit : IsUnit QZZ.det)
    (hBread : IsUnit (QZXᵀ * QZZ⁻¹ * QZX).det) :
    CovarianceEstimatorConsistent mu
      (fun n ω => tslsAsymptoticVariance (QZXhat n ω) (QZZhat n ω) (Omegahat n ω))
      (tslsAsymptoticVariance QZX QZZ OmegaMat) :=
  covarianceEstimatorConsistent_of_tendstoInMeasure
    (fun n ω => tslsAsymptoticVariance (QZXhat n ω) (QZZhat n ω) (Omegahat n ω))
    (tslsAsymptoticVariance QZX QZZ OmegaMat)
    (fun n => tslsAsymptoticVariance_aestronglyMeasurable
      (QZXhat n) (QZZhat n) (Omegahat n)
      (hQZX_meas n) (hQZZ_meas n) (hOmega_meas n))
    (tslsAsymptoticVariance_tendstoInMeasure_of_moments
      hQZX_meas hQZZ_meas hOmega_meas hQZX hQZZ hOmega hQZZunit hBread)

omit [IsProbabilityMeasure mu] [DecidableEq k] in
/-- Interface projection for 2SLS covariance-matrix estimator consistency. -/
theorem twoStageLeastSquares_covariance_consistent_from_interface
    (Vhat : ℕ → Omega → Matrix k k ℝ) (Vbeta : Matrix k k ℝ)
    (hV : CovarianceEstimatorConsistent mu Vhat Vbeta) :
    CovarianceEstimatorConsistent mu Vhat Vbeta :=
  hV

omit [IsProbabilityMeasure mu] [DecidableEq q] in
/-- Interface projection for consistency of smooth functions of 2SLS parameters. -/
theorem twoStageLeastSquares_function_consistent_from_interface
    (thetahat : ℕ → Omega → q → ℝ) (theta : q → ℝ)
    (hTheta : TendstoInMeasure mu thetahat atTop (fun _ => theta)) :
    TendstoInMeasure mu thetahat atTop (fun _ => theta) :=
  hTheta

omit [DecidableEq k] [DecidableEq q] in
/-- **Hansen Theorem 12.4, continuous-mapping layer.**

If the 2SLS coefficient estimator is consistent and `r` is continuous at the
population coefficient `beta`, then `r(betahat)` is consistent for `r(beta)`.
This is the Chapter 12 specialization of the reusable smooth-function
consistency theorem from the asymptotic utilities. -/
theorem twoStageLeastSquares_function_consistent_of_continuous
    (betahat : ℕ → Omega → k → ℝ) (beta : k → ℝ)
    (rfun : (k → ℝ) → q → ℝ)
    (h : IVConsistencyInterface (mu := mu) betahat beta)
    (hβ_meas : ∀ n, AEStronglyMeasurable (betahat n) mu)
    (hrβ_meas : ∀ n, AEStronglyMeasurable (fun ω => rfun (betahat n ω)) mu)
    (hr : ContinuousAt rfun beta) :
    TendstoInMeasure mu (fun n ω => rfun (betahat n ω)) atTop (fun _ => rfun beta) :=
  smoothFunction_consistency hβ_meas hrβ_meas h.consistent hr

omit [DecidableEq k] in
/-- Interface projection for delta-method asymptotic normality of functions of 2SLS. -/
theorem twoStageLeastSquares_function_gaussianLimit_from_interface
    (Ttheta : ℕ → Omega → q → ℝ) (Vbeta : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hTheta : GaussianLimit mu Ttheta (tslsDeltaVariance Vbeta R)) :
    GaussianLimit mu Ttheta (tslsDeltaVariance Vbeta R) :=
  hTheta

omit [DecidableEq k] in
/-- Distributional face of `twoStageLeastSquares_function_gaussianLimit_from_interface`. -/
theorem twoStageLeastSquares_function_tendstoInDistribution_from_interface
    (Ttheta : ℕ → Omega → q → ℝ) (Vbeta : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hTheta : GaussianLimit mu Ttheta (tslsDeltaVariance Vbeta R)) :
    TendstoInDistribution Ttheta atTop (fun z : EuclideanSpace ℝ q => z.ofLp)
      (fun _ => mu) (multivariateGaussian 0 (tslsDeltaVariance Vbeta R)) :=
  hTheta.limit

omit [DecidableEq k] [DecidableEq q] in
/-- **Hansen Theorem 12.5, fixed-derivative covariance layer.**

If the 2SLS coefficient covariance estimator is consistent, then the fixed
delta-method covariance plug-in `R' Vhat R` is consistent. This is the
Chapter 12 notation wrapper around the Chapter 7 linear covariance CMT. -/
theorem tslsDeltaCovarianceConsistent_of_fixedDerivative
    (Vhat : ℕ → Omega → Matrix k k ℝ) (Vbeta : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hV : CovarianceEstimatorConsistent mu Vhat Vbeta) :
    CovarianceEstimatorConsistent mu
      (fun n ω => tslsDeltaVariance (Vhat n ω) R)
      (tslsDeltaVariance Vbeta R) :=
  covarianceEstimatorConsistent_of_tendstoInMeasure
    (fun n ω => tslsDeltaVariance (Vhat n ω) R)
    (tslsDeltaVariance Vbeta R)
    (fun n => by
      simpa [tslsDeltaVariance] using
        linMapCov_aestronglyMeasurable (Ω := Omega) (μ := mu) (k := k) (q := q)
          (R := Rᵀ) (hV.covariance_measurable n))
    (by
      have hlim := linMapCov_tendstoInMeasure
        (Ω := Omega) (μ := mu) (k := k) (q := q)
        (R := Rᵀ) hV.covariance_measurable hV.consistent
      simpa [tslsDeltaVariance] using hlim)

set_option maxHeartbeats 800000 in
-- This is a notation bridge from Chapter 7's random linear-map covariance CMT
-- to Chapter 12's `R' V R` delta-variance convention.
omit [DecidableEq k] [DecidableEq q] in
/-- **Hansen Theorem 12.5, estimated-derivative covariance layer.**

If the derivative estimate `Rhat` and 2SLS covariance estimate are consistent,
then the nonlinear delta-method covariance plug-in `Rhat' Vhat Rhat` is
consistent. -/
theorem tslsDeltaCovarianceConsistent_of_estimatedDerivative
    {Rhat : ℕ → Omega → Matrix k q ℝ} {R : Matrix k q ℝ}
    {Vhat : ℕ → Omega → Matrix k k ℝ} {Vbeta : Matrix k k ℝ}
    (hR_meas : ∀ n, AEStronglyMeasurable (Rhat n) mu)
    (hR : TendstoInMeasure mu Rhat atTop (fun _ => R))
    (hV : CovarianceEstimatorConsistent mu Vhat Vbeta) :
    CovarianceEstimatorConsistent mu
      (fun n ω => tslsDeltaVariance (Vhat n ω) (Rhat n ω))
      (tslsDeltaVariance Vbeta R) := by
  have hRt_meas : ∀ n, AEStronglyMeasurable (fun ω => (Rhat n ω)ᵀ) mu :=
    fun n => continuous_id.matrix_transpose.comp_aestronglyMeasurable (hR_meas n)
  have hRt : TendstoInMeasure mu (fun n ω => (Rhat n ω)ᵀ) atTop
      (fun _ : Omega => Rᵀ) :=
    tendstoInMeasure_continuous_comp hR_meas hR continuous_id.matrix_transpose
  refine covarianceEstimatorConsistent_of_tendstoInMeasure
    (fun n ω => tslsDeltaVariance (Vhat n ω) (Rhat n ω))
    (tslsDeltaVariance Vbeta R) ?_ ?_
  · intro n
    have hLeft : AEStronglyMeasurable
        (fun ω => (Rhat n ω)ᵀ * Vhat n ω) mu := by
      exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        ((hRt_meas n).prodMk (hV.covariance_measurable n))
    simpa [tslsDeltaVariance] using
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hLeft.prodMk (hR_meas n))
  · have hlim := randomLinearMapCovariance_tendstoInMeasure
      (Ω := Omega) (μ := mu) (k := k) (q := q)
      (Rhat := fun n ω => (Rhat n ω)ᵀ) (R := Rᵀ)
      (Vhat := Vhat) (V := Vbeta)
      hRt_meas hV.covariance_measurable hRt hV.consistent
    simpa [tslsDeltaVariance] using hlim

end HansenEconometrics
