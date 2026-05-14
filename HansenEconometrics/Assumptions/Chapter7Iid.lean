import HansenEconometrics.Chapter7Asymptotics.SandwichAssembly

/-!
# Chapter 7 IID Assumption Setups

This module provides the clean textbook-facing names for iid Chapter 7 setup
packages. The existing WLLN/CLT/HC condition structures remain backend proof
targets; the theorem methods here convert the iid-facing assumptions into those
targets.
-/

open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Matrix

namespace HansenEconometrics

variable {Ω k : Type*}
variable [MeasurableSpace Ω] [Fintype k] [DecidableEq k]
variable {μ : Measure Ω}

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

omit [DecidableEq k] in
private lemma measurable_iidRowOuter :
    Measurable (fun z : (k → ℝ) × ℝ => Matrix.vecMulVec z.1 z.1) := by
  exact (Continuous.matrix_vecMulVec continuous_fst continuous_fst).measurable

omit [Fintype k] [DecidableEq k] in
private lemma measurable_iidRowCross :
    Measurable (fun z : (k → ℝ) × ℝ => z.2 • z.1) := by
  rw [measurable_pi_iff]
  intro i
  simpa using measurable_snd.mul ((measurable_pi_apply i).comp measurable_fst)

omit [Fintype k] [DecidableEq k] in
private lemma measurable_iidErrorSq :
    Measurable (fun z : (k → ℝ) × ℝ => z.2 ^ 2) := by
  exact measurable_snd.pow_const 2

/-- Textbook-facing iid linear-model rows. -/
structure IidLinearModelRows
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → k → ℝ) (e y : ℕ → Ω → ℝ) (β : k → ℝ) where
  model : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω
  x_aestronglyMeasurable : ∀ i, AEStronglyMeasurable (X i) μ
  e_aestronglyMeasurable : ∀ i, AEStronglyMeasurable (e i) μ
  joint_iIndep : iIndepFun (fun i ω => (X i ω, e i ω)) μ
  joint_identDistrib : ∀ i,
    IdentDistrib (fun ω => (X i ω, e i ω))
      (fun ω => (X 0 ω, e 0 ω)) μ μ

/-- IID linear-model rows with the moment assumptions behind Assumption 7.1. -/
structure IidLinearModelMomentExog
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → k → ℝ) (e y : ℕ → Ω → ℝ) (β : k → ℝ)
    extends IidLinearModelRows μ X e y β where
  int_outer : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ
  int_cross : Integrable (fun ω => e 0 ω • X 0 ω) μ
  Q_nonsing : IsUnit (μ[fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)]).det
  orthogonality : μ[fun ω => e 0 ω • X 0 ω] = 0

/-- Hansen Assumption 7.1 in iid row form. -/
abbrev IidOLSAssumption71
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → k → ℝ) (e y : ℕ → Ω → ℝ) (β : k → ℝ) :=
  IidLinearModelMomentExog μ X e y β

/-- Hansen Assumption 7.4 in iid row form. -/
structure IidOLSAssumption74
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → k → ℝ) (e y : ℕ → Ω → ℝ) (β : k → ℝ)
    extends IidLinearModelMomentExog μ X e y β where
  int_error_sq : Integrable (fun ω => e 0 ω ^ 2) μ

/-- Hansen Assumption 7.2 with a structural-error fourth moment. -/
abbrev IidOLSAssumption72FourthMoment
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → k → ℝ) (e y : ℕ → Ω → ℝ) (β : k → ℝ) :=
  IidAssumption72FourthMomentConditions μ X e y β

/-- Hansen Assumption 7.2 with a response fourth moment. -/
abbrev IidOLSAssumption72ResponseMoment
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → k → ℝ) (e y : ℕ → Ω → ℝ) (β : k → ℝ) :=
  IidAssumption72ResponseMomentConditions μ X e y β

namespace IidLinearModelMomentExog

/-- IID moment-exogeneity assumptions imply the current LLN consistency proof bundle. -/
theorem toLeastSquaresConsistencyConditions
    {X : ℕ → Ω → k → ℝ} {e y : ℕ → Ω → ℝ} {β : k → ℝ}
    [IsProbabilityMeasure μ]
    (h : IidLinearModelMomentExog μ X e y β) :
    LeastSquaresConsistencyConditions μ X e where
  indep_outer := by
    intro i j hij
    simpa [Function.comp_def] using
      (h.joint_iIndep.indepFun hij).comp measurable_iidRowOuter measurable_iidRowOuter
  indep_cross := by
    intro i j hij
    simpa [Function.comp_def, Pi.smul_apply, smul_eq_mul] using
      (h.joint_iIndep.indepFun hij).comp measurable_iidRowCross measurable_iidRowCross
  ident_outer := by
    intro i
    simpa [Function.comp_def] using
      (h.joint_identDistrib i).comp measurable_iidRowOuter
  ident_cross := by
    intro i
    simpa [Function.comp_def, Pi.smul_apply, smul_eq_mul] using
      (h.joint_identDistrib i).comp measurable_iidRowCross
  int_outer := h.int_outer
  int_cross := h.int_cross
  Q_nonsing := h.Q_nonsing
  orthogonality := h.orthogonality

end IidLinearModelMomentExog

namespace IidOLSAssumption71

/-- Hansen Assumption 7.1 rows convert to the current LLN consistency proof bundle. -/
theorem toLeastSquaresConsistencyConditions
    {X : ℕ → Ω → k → ℝ} {e y : ℕ → Ω → ℝ} {β : k → ℝ}
    [IsProbabilityMeasure μ]
    (h : IidOLSAssumption71 μ X e y β) :
    LeastSquaresConsistencyConditions μ X e :=
  IidLinearModelMomentExog.toLeastSquaresConsistencyConditions h

end IidOLSAssumption71

namespace IidOLSAssumption74

/-- Hansen Assumption 7.4 rows convert to the current residual-variance proof bundle. -/
theorem toErrorVarianceConsistencyConditions
    {X : ℕ → Ω → k → ℝ} {e y : ℕ → Ω → ℝ} {β : k → ℝ}
    [IsProbabilityMeasure μ]
    (h : IidOLSAssumption74 μ X e y β) :
    ErrorVarianceConsistencyConditions μ X e where
  toLeastSquaresConsistencyConditions :=
    h.toIidLinearModelMomentExog.toLeastSquaresConsistencyConditions
  indep_error_sq := by
    intro i j hij
    simpa [Function.comp_def] using
      (h.joint_iIndep.indepFun hij).comp measurable_iidErrorSq measurable_iidErrorSq
  ident_error_sq := by
    intro i
    simpa [Function.comp_def] using
      (h.joint_identDistrib i).comp measurable_iidErrorSq
  int_error_sq := h.int_error_sq

end IidOLSAssumption74

namespace IidOLSAssumption72FourthMoment

/-- Structural-error fourth-moment iid rows convert to the existing robust feasible-HC package. -/
theorem toRobustFeasibleHCMomentConditions
    {X : ℕ → Ω → k → ℝ} {e y : ℕ → Ω → ℝ} {β : k → ℝ}
    [IsProbabilityMeasure μ]
    (h : IidOLSAssumption72FourthMoment μ X e y β) :
    RobustFeasibleHCMomentConditions μ X e y β :=
  h.toIidRobustFeasibleHCMomentConditions.toRobustFeasibleHCMomentConditions

end IidOLSAssumption72FourthMoment

namespace IidOLSAssumption72ResponseMoment

/-- Response-fourth-moment iid rows imply the structural-error fourth-moment package. -/
theorem toIidOLSAssumption72FourthMoment
    {X : ℕ → Ω → k → ℝ} {e y : ℕ → Ω → ℝ} {β : k → ℝ}
    [IsProbabilityMeasure μ]
    (h : IidOLSAssumption72ResponseMoment μ X e y β) :
    IidOLSAssumption72FourthMoment μ X e y β :=
  h.toIidAssumption72FourthMomentConditions

/-- Response-fourth-moment iid rows convert to the existing robust feasible-HC package. -/
theorem toRobustFeasibleHCMomentConditions
    {X : ℕ → Ω → k → ℝ} {e y : ℕ → Ω → ℝ} {β : k → ℝ}
    [IsProbabilityMeasure μ]
    (h : IidOLSAssumption72ResponseMoment μ X e y β) :
    RobustFeasibleHCMomentConditions μ X e y β :=
  h.toIidRobustFeasibleHCMomentConditions.toRobustFeasibleHCMomentConditions

end IidOLSAssumption72ResponseMoment

end HansenEconometrics
