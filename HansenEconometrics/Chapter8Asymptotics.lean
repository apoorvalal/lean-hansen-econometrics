import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Analysis.Calculus.FDeriv.Basic
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.AsymptoticUtils.StochasticOrder
import HansenEconometrics.Chapter7Asymptotics.Basic
import HansenEconometrics.Chapter7Asymptotics.Normality

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise ENNReal Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

open Matrix

/-!
# Chapter 8: restricted-estimation asymptotic wrappers

This module adds minimum-distance definitions and current-assumption asymptotic wrappers for Hansen
Theorems 8.6--8.10.  The wrappers compose explicit consistency, CLT, remainder, continuity, PSD, and
factorization inputs rather than assuming theorem conclusions through condition packages.
-/

variable {k q : Type*}
variable [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]

/-- Base minimum-distance estimator with typeclass inverses. -/
noncomputable def mdBeta
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (bhat : k → ℝ)
    [Invertible W] [Invertible (Rᵀ * ⅟W * R)] : k → ℝ :=
  bhat - (⅟W * R * ⅟(Rᵀ * ⅟W * R)) *ᵥ (Rᵀ *ᵥ bhat - c)

/-- The closed-form minimum-distance estimator satisfies the imposed linear restriction. -/
theorem mdBeta_restrict
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (bhat : k → ℝ)
    [Invertible W] [Invertible (Rᵀ * ⅟W * R)] :
    Rᵀ *ᵥ mdBeta W R c bhat = c := by
  unfold mdBeta
  have hleft : Rᵀ * (⅟W * R * ⅟(Rᵀ * ⅟W * R)) = (1 : Matrix q q ℝ) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
    exact mul_invOf_self (Rᵀ * ⅟W * R)
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
  abel

/-- Star minimum-distance estimator using total nonsingular inverses. -/
noncomputable def mdBetaStar
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (bhat : k → ℝ) : k → ℝ :=
  bhat - (W⁻¹ * R * (Rᵀ * W⁻¹ * R)⁻¹) *ᵥ (Rᵀ *ᵥ bhat - c)

/-- On nonsingular inputs, the totalized Star MD estimator agrees with the base estimator. -/
theorem mdBeta_eq_mdBetaStar
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (bhat : k → ℝ)
    [Invertible W] [Invertible (Rᵀ * ⅟W * R)] :
    mdBeta W R c bhat = mdBetaStar W R c bhat := by
  unfold mdBeta mdBetaStar
  rw [← invOf_eq_nonsing_inv W]
  rw [← invOf_eq_nonsing_inv (Rᵀ * ⅟W * R)]

/-- The Star MD estimator satisfies the imposed restriction on nonsingular inputs. -/
theorem mdBetaStar_restrict_of_invertible
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (bhat : k → ℝ)
    [Invertible W] [Invertible (Rᵀ * ⅟W * R)] :
    Rᵀ *ᵥ mdBetaStar W R c bhat = c := by
  rw [← mdBeta_eq_mdBetaStar W R c bhat]
  exact mdBeta_restrict W R c bhat

/-- Star CLS as the minimum-distance specialization with sample Gram weight. -/
noncomputable def clsBetaStar
    {n : Type*} [Fintype n] (X : Matrix n k ℝ) (y : n → ℝ) (R : Matrix k q ℝ)
    (c : q → ℝ) : k → ℝ :=
  mdBetaStar (sampleGram X) R c (olsBetaStar X y)

/-- Fixed linear map in the MD asymptotic distribution. -/
noncomputable def mdLinearMap (W : Matrix k k ℝ) (R : Matrix k q ℝ) : Matrix k k ℝ :=
  1 - W⁻¹ * R * (Rᵀ * W⁻¹ * R)⁻¹ * Rᵀ

/-- MD asymptotic variance. -/
noncomputable def mdAsymptoticVariance
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (V : Matrix k k ℝ) : Matrix k k ℝ :=
  mdLinearMap W R * V * (mdLinearMap W R)ᵀ

set_option maxHeartbeats 800000 in
-- Matrix measurability through nested total inverses and products is expensive here.
/-- The MD linear map is a.e. strongly measurable whenever the weight matrix is. -/
theorem mdLinearMap_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (Wseq : Ω → Matrix k k ℝ) (R : Matrix k q ℝ)
    (hW : AEStronglyMeasurable Wseq μ) :
    AEStronglyMeasurable (fun ω => mdLinearMap (Wseq ω) R) μ := by
  have hWinv : AEStronglyMeasurable (fun ω => (Wseq ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hW
  have hRtWinv : AEStronglyMeasurable (fun ω => Rᵀ * (Wseq ω)⁻¹) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (aestronglyMeasurable_const.prodMk hWinv)
  have hGram : AEStronglyMeasurable (fun ω => Rᵀ * (Wseq ω)⁻¹ * R) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hRtWinv.prodMk aestronglyMeasurable_const)
  have hGramInv : AEStronglyMeasurable (fun ω => (Rᵀ * (Wseq ω)⁻¹ * R)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hGram
  have hWinvR : AEStronglyMeasurable (fun ω => (Wseq ω)⁻¹ * R) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hWinv.prodMk aestronglyMeasurable_const)
  have hB : AEStronglyMeasurable
      (fun ω => (Wseq ω)⁻¹ * R * (Rᵀ * (Wseq ω)⁻¹ * R)⁻¹) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hWinvR.prodMk hGramInv)
  have hA : AEStronglyMeasurable
      (fun ω => (Wseq ω)⁻¹ * R * (Rᵀ * (Wseq ω)⁻¹ * R)⁻¹ * Rᵀ) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hB.prodMk aestronglyMeasurable_const)
  unfold mdLinearMap
  exact aestronglyMeasurable_const.sub hA

set_option maxHeartbeats 800000 in
-- Matrix continuity through nested total inverses and products is expensive here.
/-- The MD linear map is continuous at nonsingular limiting weights whose restriction Gram is
also nonsingular. -/
theorem mdLinearMap_continuousAt_of_nonsingular
    (W : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hW : IsUnit W.det) (hG : IsUnit (Rᵀ * W⁻¹ * R).det) :
    ContinuousAt (fun W' : Matrix k k ℝ => mdLinearMap W' R) W := by
  let G : Matrix q q ℝ := Rᵀ * W⁻¹ * R
  have hWInv : ContinuousAt (fun W' : Matrix k k ℝ => W'⁻¹) W := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hW.ne_zero
  have hRtWinv : ContinuousAt (fun W' : Matrix k k ℝ => Rᵀ * W'⁻¹) W := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (continuousAt_const.prodMk hWInv)
  have hGram : ContinuousAt (fun W' : Matrix k k ℝ => Rᵀ * W'⁻¹ * R) W := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hRtWinv.prodMk continuousAt_const)
  have hGramInv : ContinuousAt (fun W' : Matrix k k ℝ => (Rᵀ * W'⁻¹ * R)⁻¹) W := by
    have hcontInv : ContinuousAt Inv.inv G := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hG.ne_zero
    simpa [G] using hcontInv.comp hGram
  have hWinvR : ContinuousAt (fun W' : Matrix k k ℝ => W'⁻¹ * R) W := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hWInv.prodMk continuousAt_const)
  have hB : ContinuousAt
      (fun W' : Matrix k k ℝ => W'⁻¹ * R * (Rᵀ * W'⁻¹ * R)⁻¹) W := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hWinvR.prodMk hGramInv)
  have hA : ContinuousAt
      (fun W' : Matrix k k ℝ => W'⁻¹ * R * (Rᵀ * W'⁻¹ * R)⁻¹ * Rᵀ) W := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hB.prodMk continuousAt_const)
  unfold mdLinearMap
  exact continuousAt_const.sub hA

set_option maxHeartbeats 800000 in
-- The local CMT instantiation carries the finite-dimensional matrix topology.
/-- Convergence of random MD weights implies convergence of their MD linear maps. -/
theorem mdLinearMap_tendstoInMeasure_of_nonsingular
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (What : ℕ → Ω → Matrix k k ℝ) (W : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) μ)
    (hWhat : TendstoInMeasure μ What atTop (fun _ => W))
    (hW : IsUnit W.det) (hG : IsUnit (Rᵀ * W⁻¹ * R).det) :
    TendstoInMeasure μ (fun n ω => mdLinearMap (What n ω) R) atTop
      (fun _ => mdLinearMap W R) := by
  exact tendstoInMeasure_continuousAt_const_comp
    (f := What) (x := W) (h := fun W' : Matrix k k ℝ => mdLinearMap W' R)
    hWhat_meas
    (fun n => mdLinearMap_aestronglyMeasurable (What n) R (hWhat_meas n))
    hWhat (mdLinearMap_continuousAt_of_nonsingular W R hW hG)

/-- Expanded form of the MD asymptotic variance definition. -/
theorem mdAsymptoticVariance_eq_expanded
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (V : Matrix k k ℝ) :
    mdAsymptoticVariance W R V = mdLinearMap W R * V * (mdLinearMap W R)ᵀ :=
  rfl

/-- Hansen Theorem 8.7, equation (8.24): the compact MD sandwich variance expands to
the four-term textbook formula when the weight matrix is symmetric. -/
theorem mdAsymptoticVariance_eq_hansen_expanded
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (V : Matrix k k ℝ)
    (hWsym : Wᵀ = W) :
    mdAsymptoticVariance W R V =
      V - W⁻¹ * R * (Rᵀ * W⁻¹ * R)⁻¹ * Rᵀ * V
        - V * R * (Rᵀ * W⁻¹ * R)⁻¹ * Rᵀ * W⁻¹
        + W⁻¹ * R * (Rᵀ * W⁻¹ * R)⁻¹ * Rᵀ * V * R *
            (Rᵀ * W⁻¹ * R)⁻¹ * Rᵀ * W⁻¹ := by
  let Winv : Matrix k k ℝ := W⁻¹
  let A : Matrix q q ℝ := (Rᵀ * Winv * R)⁻¹
  have hWinvSym : Winvᵀ = Winv := by
    dsimp [Winv]
    rw [Matrix.transpose_nonsing_inv, hWsym]
  have hGramWsym : (Rᵀ * Winv * R)ᵀ = Rᵀ * Winv * R := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hWinvSym, Matrix.transpose_transpose]
    simp [Matrix.mul_assoc]
  have hAsym : Aᵀ = A := by
    dsimp [A]
    rw [Matrix.transpose_nonsing_inv, hGramWsym]
  unfold mdAsymptoticVariance mdLinearMap
  change (1 - Winv * R * A * Rᵀ) * V * (1 - Winv * R * A * Rᵀ)ᵀ =
      V - Winv * R * A * Rᵀ * V - V * R * A * Rᵀ * Winv +
        Winv * R * A * Rᵀ * V * R * A * Rᵀ * Winv
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_one,
    Matrix.transpose_transpose, hAsym, hWinvSym]
  simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- CLS asymptotic variance is the MD variance with the population Gram weight. -/
noncomputable def clsAsymptoticVariance
    (Q : Matrix k k ℝ) (R : Matrix k q ℝ) (V : Matrix k k ℝ) : Matrix k k ℝ :=
  mdAsymptoticVariance Q R V

/-- Expanded CLS asymptotic variance. -/
theorem clsAsymptoticVariance_eq_expanded
    (Q : Matrix k k ℝ) (R : Matrix k q ℝ) (V : Matrix k k ℝ) :
    clsAsymptoticVariance Q R V = mdLinearMap Q R * V * (mdLinearMap Q R)ᵀ :=
  rfl

/-- Hansen Theorem 8.8: the CLS asymptotic variance is the Theorem 8.7 four-term
minimum-distance formula with the population Gram weight. -/
theorem clsAsymptoticVariance_eq_hansen_expanded
    (Q : Matrix k k ℝ) (R : Matrix k q ℝ) (V : Matrix k k ℝ)
    (hQsym : Qᵀ = Q) :
    clsAsymptoticVariance Q R V =
      V - Q⁻¹ * R * (Rᵀ * Q⁻¹ * R)⁻¹ * Rᵀ * V
        - V * R * (Rᵀ * Q⁻¹ * R)⁻¹ * Rᵀ * Q⁻¹
        + Q⁻¹ * R * (Rᵀ * Q⁻¹ * R)⁻¹ * Rᵀ * V * R *
            (Rᵀ * Q⁻¹ * R)⁻¹ * Rᵀ * Q⁻¹ := by
  simpa [clsAsymptoticVariance] using
    mdAsymptoticVariance_eq_hansen_expanded Q R V hQsym

/-- Efficient MD asymptotic variance. -/
noncomputable def emdAsymptoticVariance
    (R : Matrix k q ℝ) (V : Matrix k k ℝ) : Matrix k k ℝ :=
  V - V * R * (Rᵀ * V * R)⁻¹ * Rᵀ * V

/-- Efficient MD estimator with the efficient weight. -/
noncomputable def emdBetaStar
    (R : Matrix k q ℝ) (c : q → ℝ) (V : Matrix k k ℝ) (bhat : k → ℝ) : k → ℝ :=
  mdBetaStar V⁻¹ R c bhat

/-- Hansen equation (8.25): the efficient-MD estimator is the MD formula with the
efficient weight `V⁻¹`, rewritten using the unrestricted variance matrix `V`. -/
theorem emdBetaStar_eq_hansen
    (R : Matrix k q ℝ) (c : q → ℝ) (V : Matrix k k ℝ) (bhat : k → ℝ)
    (hV : IsUnit V.det) :
    emdBetaStar R c V bhat =
      bhat - (V * R * (Rᵀ * V * R)⁻¹) *ᵥ (Rᵀ *ᵥ bhat - c) := by
  unfold emdBetaStar mdBetaStar
  rw [Matrix.nonsing_inv_nonsing_inv V hV]

/-- Scaled error for a generic constrained estimator. -/
noncomputable def constrainedScaledError
    {Ω : Type*} (root : ℕ → ℝ) (btilde : ℕ → Ω → k → ℝ) (β : k → ℝ) :
    ℕ → Ω → k → ℝ :=
  fun n ω => root n • (btilde n ω - β)

omit [Fintype k] [DecidableEq k] [DecidableEq q] in
/-- The generic constrained-estimator scaled error is a.e. measurable whenever the constrained
estimator sequence is a.e. strongly measurable. -/
theorem constrainedScaledError_aemeasurable
    [Finite k]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (root : ℕ → ℝ) (btilde : ℕ → Ω → k → ℝ) (β : k → ℝ)
    (hbtilde_meas : ∀ n, AEStronglyMeasurable (btilde n) μ) :
    ∀ n, AEMeasurable (constrainedScaledError root btilde β n) μ := by
  let _ := Fintype.ofFinite k
  intro n
  exact (((hbtilde_meas n).sub aestronglyMeasurable_const).const_smul (root n)).aemeasurable

/-- Stable interface for the linearized asymptotic representation of a constrained estimator.

For nonlinear restrictions, the derivative matrix `Rderiv` replaces the fixed linear-restriction
matrix. The interface records the econometric capability used by Theorem 8.10: after scaling, the
constrained estimator equals the MD linear map applied to a score statistic, up to an `o_p(1)`
remainder. -/
structure ConstrainedEstimatorLinearization
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (root : ℕ → ℝ) (btilde : ℕ → Ω → k → ℝ) (β : k → ℝ)
    (W : Matrix k k ℝ) (Rderiv : Matrix k q ℝ) (T : ℕ → Ω → k → ℝ) where
  scaled_measurable : ∀ n, AEMeasurable (constrainedScaledError root btilde β n) μ
  expansion :
    TendstoInMeasure μ
      (constrainedScaledError root btilde β - fun n ω => mdLinearMap W Rderiv *ᵥ T n ω)
      atTop (fun _ => 0)

/-- Hansen Assumption 8.3 for nonlinear restrictions `r(β) = 0`.

The matrix `Rderiv` is Hansen's `R = ∂r(β)' / ∂β`, so the derivative of `r` is
represented by `Rderivᵀ`. This structure deliberately records only the deterministic
restriction, differentiability, and rank content of Assumption 8.3; consistency and optimizer
first-order-condition arguments belong in constructors for `ConstrainedEstimatorLinearization`. -/
structure NonlinearConstraintAssumption83
    (r : (k → ℝ) → (q → ℝ)) (β : k → ℝ) (Rderiv : Matrix k q ℝ) where
  /-- The true parameter satisfies the nonlinear restriction. -/
  constraint : r β = 0
  /-- Fréchet derivative of `r` at `β`. -/
  derivative : (k → ℝ) →L[ℝ] (q → ℝ)
  /-- The restriction map is differentiable at the true parameter. -/
  differentiable_at : HasFDerivAt r derivative β
  /-- The derivative is represented by Hansen's transposed derivative matrix. -/
  derivative_apply : ∀ v : k → ℝ, derivative v = Rderivᵀ *ᵥ v
  /-- Hansen's rank condition `rank(R) = q`, represented as full column rank. -/
  fullRank : Function.Injective Rderiv.mulVec

/-- Deterministic Taylor remainder for the nonlinear restriction map at the true parameter.

For `Rderiv = ∂r(β)' / ∂β`, this is
`r(b) - r(β) - Rderiv' (b - β)`. Assumption 8.3 proves it is little-o of
`b - β`; constrained estimators with `r(b) = 0` turn this into the nonlinear
constraint gap used in the proof of Theorem 8.10. -/
noncomputable def nonlinearConstraintTaylorRemainder
    (r : (k → ℝ) → (q → ℝ)) (β : k → ℝ) (Rderiv : Matrix k q ℝ) :
    (k → ℝ) → (q → ℝ) :=
  fun b => r b - r β - Rderivᵀ *ᵥ (b - β)

/-- Linear map from the unrestricted estimator error to the nonlinear constrained-estimator
error in the finite-sample first-order-condition algebra.

`Rright` is the derivative matrix appearing in the Lagrangian first-order condition, while
`Rleft` is the derivative matrix appearing in the linearized constraint. In the limit both
converge to Hansen's `R`. -/
noncomputable def nonlinearFirstOrderLinearMap
    (W : Matrix k k ℝ) (Rright Rleft : Matrix k q ℝ) : Matrix k k ℝ :=
  1 - W⁻¹ * Rright * (Rleftᵀ * W⁻¹ * Rright)⁻¹ * Rleftᵀ

/-- Correction map multiplying the nonlinear constraint linearization gap in the finite-sample
first-order-condition algebra. -/
noncomputable def nonlinearFirstOrderConstraintCorrection
    (W : Matrix k k ℝ) (Rright Rleft : Matrix k q ℝ) : Matrix k q ℝ :=
  W⁻¹ * Rright * (Rleftᵀ * W⁻¹ * Rright)⁻¹

/-- When the left and right derivative matrices agree, the nonlinear first-order linear map is the
ordinary minimum-distance linear map. -/
theorem nonlinearFirstOrderLinearMap_self_eq_mdLinearMap
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) :
    nonlinearFirstOrderLinearMap W R R = mdLinearMap W R := rfl

set_option maxHeartbeats 1200000 in
-- Matrix measurability through two derivative matrices and nested total inverses is expensive here.
/-- The nonlinear first-order linear map is a.e. strongly measurable whenever the random weight
and derivative matrices are. -/
theorem nonlinearFirstOrderLinearMap_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (Wseq : Ω → Matrix k k ℝ) (Rright Rleft : Ω → Matrix k q ℝ)
    (hW : AEStronglyMeasurable Wseq μ)
    (hRright : AEStronglyMeasurable Rright μ)
    (hRleft : AEStronglyMeasurable Rleft μ) :
    AEStronglyMeasurable
      (fun ω => nonlinearFirstOrderLinearMap (Wseq ω) (Rright ω) (Rleft ω)) μ := by
  have hWinv : AEStronglyMeasurable (fun ω => (Wseq ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hW
  have hRlt : AEStronglyMeasurable (fun ω => (Rleft ω)ᵀ) μ :=
    continuous_id.matrix_transpose.comp_aestronglyMeasurable hRleft
  have hRtWinv : AEStronglyMeasurable (fun ω => (Rleft ω)ᵀ * (Wseq ω)⁻¹) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hRlt.prodMk hWinv)
  have hGram : AEStronglyMeasurable
      (fun ω => (Rleft ω)ᵀ * (Wseq ω)⁻¹ * Rright ω) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hRtWinv.prodMk hRright)
  have hGramInv : AEStronglyMeasurable
      (fun ω => ((Rleft ω)ᵀ * (Wseq ω)⁻¹ * Rright ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hGram
  have hWinvR : AEStronglyMeasurable (fun ω => (Wseq ω)⁻¹ * Rright ω) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hWinv.prodMk hRright)
  have hB : AEStronglyMeasurable
      (fun ω =>
        (Wseq ω)⁻¹ * Rright ω * ((Rleft ω)ᵀ * (Wseq ω)⁻¹ * Rright ω)⁻¹) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hWinvR.prodMk hGramInv)
  have hA : AEStronglyMeasurable
      (fun ω =>
        (Wseq ω)⁻¹ * Rright ω * ((Rleft ω)ᵀ * (Wseq ω)⁻¹ * Rright ω)⁻¹ *
          (Rleft ω)ᵀ) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hB.prodMk hRlt)
  unfold nonlinearFirstOrderLinearMap
  exact aestronglyMeasurable_const.sub hA

set_option maxHeartbeats 1200000 in
-- Matrix measurability through two derivative matrices and nested total inverses is expensive here.
/-- The nonlinear first-order constraint-correction map is a.e. strongly measurable whenever the
random weight and derivative matrices are. -/
theorem nonlinearFirstOrderConstraintCorrection_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (Wseq : Ω → Matrix k k ℝ) (Rright Rleft : Ω → Matrix k q ℝ)
    (hW : AEStronglyMeasurable Wseq μ)
    (hRright : AEStronglyMeasurable Rright μ)
    (hRleft : AEStronglyMeasurable Rleft μ) :
    AEStronglyMeasurable
      (fun ω => nonlinearFirstOrderConstraintCorrection (Wseq ω) (Rright ω) (Rleft ω))
        μ := by
  have hWinv : AEStronglyMeasurable (fun ω => (Wseq ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hW
  have hRlt : AEStronglyMeasurable (fun ω => (Rleft ω)ᵀ) μ :=
    continuous_id.matrix_transpose.comp_aestronglyMeasurable hRleft
  have hRtWinv : AEStronglyMeasurable (fun ω => (Rleft ω)ᵀ * (Wseq ω)⁻¹) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hRlt.prodMk hWinv)
  have hGram : AEStronglyMeasurable
      (fun ω => (Rleft ω)ᵀ * (Wseq ω)⁻¹ * Rright ω) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hRtWinv.prodMk hRright)
  have hGramInv : AEStronglyMeasurable
      (fun ω => ((Rleft ω)ᵀ * (Wseq ω)⁻¹ * Rright ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hGram
  have hWinvR : AEStronglyMeasurable (fun ω => (Wseq ω)⁻¹ * Rright ω) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hWinv.prodMk hRright)
  unfold nonlinearFirstOrderConstraintCorrection
  exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
    (hWinvR.prodMk hGramInv)

set_option maxHeartbeats 1200000 in
-- Continuity through nested total inverses for the random nonlinear FONC map is expensive here.
/-- The nonlinear first-order linear map is continuous at nonsingular limiting weights and
nonsingular limiting mixed restriction Gram matrices. -/
theorem nonlinearFirstOrderLinearMap_continuousAt_of_nonsingular
    (W : Matrix k k ℝ) (Rright Rleft : Matrix k q ℝ)
    (hW : IsUnit W.det) (hG : IsUnit (Rleftᵀ * W⁻¹ * Rright).det) :
    ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ =>
        nonlinearFirstOrderLinearMap p.1.1 p.1.2 p.2)
      ((W, Rright), Rleft) := by
  let G : Matrix q q ℝ := Rleftᵀ * W⁻¹ * Rright
  have hWc : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ => p.1.1)
      ((W, Rright), Rleft) := by
    exact continuousAt_fst.comp continuousAt_fst
  have hRrc : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ => p.1.2)
      ((W, Rright), Rleft) := by
    exact continuousAt_snd.comp continuousAt_fst
  have hRlc : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ => p.2)
      ((W, Rright), Rleft) := by
    exact continuousAt_snd
  have hWinv : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ => p.1.1⁻¹)
      ((W, Rright), Rleft) := by
    have hcontInv : ContinuousAt Inv.inv W := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hW.ne_zero
    exact hcontInv.comp hWc
  have hRlt : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ => p.2ᵀ)
      ((W, Rright), Rleft) := by
    exact continuous_id.matrix_transpose.continuousAt.comp hRlc
  have hRtWinv : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ => p.2ᵀ * p.1.1⁻¹)
      ((W, Rright), Rleft) := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hRlt.prodMk hWinv)
  have hGram : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ =>
        p.2ᵀ * p.1.1⁻¹ * p.1.2)
      ((W, Rright), Rleft) := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hRtWinv.prodMk hRrc)
  have hGramInv : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ =>
        (p.2ᵀ * p.1.1⁻¹ * p.1.2)⁻¹)
      ((W, Rright), Rleft) := by
    have hcontInv : ContinuousAt Inv.inv G := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hG.ne_zero
    simpa [G] using hcontInv.comp hGram
  have hWinvR : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ => p.1.1⁻¹ * p.1.2)
      ((W, Rright), Rleft) := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hWinv.prodMk hRrc)
  have hB : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ =>
        p.1.1⁻¹ * p.1.2 * (p.2ᵀ * p.1.1⁻¹ * p.1.2)⁻¹)
      ((W, Rright), Rleft) := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hWinvR.prodMk hGramInv)
  have hA : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ =>
        p.1.1⁻¹ * p.1.2 * (p.2ᵀ * p.1.1⁻¹ * p.1.2)⁻¹ * p.2ᵀ)
      ((W, Rright), Rleft) := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hB.prodMk hRlt)
  unfold nonlinearFirstOrderLinearMap
  exact continuousAt_const.sub hA

set_option maxHeartbeats 1200000 in
-- Continuity through nested total inverses for the random nonlinear FONC map is expensive here.
/-- The nonlinear first-order constraint-correction map is continuous at nonsingular limiting
weights and nonsingular limiting mixed restriction Gram matrices. -/
theorem nonlinearFirstOrderConstraintCorrection_continuousAt_of_nonsingular
    (W : Matrix k k ℝ) (Rright Rleft : Matrix k q ℝ)
    (hW : IsUnit W.det) (hG : IsUnit (Rleftᵀ * W⁻¹ * Rright).det) :
    ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ =>
        nonlinearFirstOrderConstraintCorrection p.1.1 p.1.2 p.2)
      ((W, Rright), Rleft) := by
  let G : Matrix q q ℝ := Rleftᵀ * W⁻¹ * Rright
  have hWc : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ => p.1.1)
      ((W, Rright), Rleft) := by
    exact continuousAt_fst.comp continuousAt_fst
  have hRrc : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ => p.1.2)
      ((W, Rright), Rleft) := by
    exact continuousAt_snd.comp continuousAt_fst
  have hRlc : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ => p.2)
      ((W, Rright), Rleft) := by
    exact continuousAt_snd
  have hWinv : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ => p.1.1⁻¹)
      ((W, Rright), Rleft) := by
    have hcontInv : ContinuousAt Inv.inv W := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hW.ne_zero
    exact hcontInv.comp hWc
  have hRlt : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ => p.2ᵀ)
      ((W, Rright), Rleft) := by
    exact continuous_id.matrix_transpose.continuousAt.comp hRlc
  have hRtWinv : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ => p.2ᵀ * p.1.1⁻¹)
      ((W, Rright), Rleft) := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hRlt.prodMk hWinv)
  have hGram : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ =>
        p.2ᵀ * p.1.1⁻¹ * p.1.2)
      ((W, Rright), Rleft) := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hRtWinv.prodMk hRrc)
  have hGramInv : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ =>
        (p.2ᵀ * p.1.1⁻¹ * p.1.2)⁻¹)
      ((W, Rright), Rleft) := by
    have hcontInv : ContinuousAt Inv.inv G := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hG.ne_zero
    simpa [G] using hcontInv.comp hGram
  have hWinvR : ContinuousAt
      (fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ => p.1.1⁻¹ * p.1.2)
      ((W, Rright), Rleft) := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hWinv.prodMk hRrc)
  unfold nonlinearFirstOrderConstraintCorrection
  exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
    (hWinvR.prodMk hGramInv)

set_option maxHeartbeats 1200000 in
-- Product-space CMT for the random nonlinear FONC map carries several finite-dimensional
-- topologies at once.
/-- If the random weight and left/right derivative matrices converge in measure, then the
nonlinear first-order linear map converges in measure to its limiting map. -/
theorem nonlinearFirstOrderLinearMap_tendstoInMeasure_of_nonsingular
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (What : ℕ → Ω → Matrix k k ℝ) (Rright Rleft : ℕ → Ω → Matrix k q ℝ)
    (W : Matrix k k ℝ) (Rright0 Rleft0 : Matrix k q ℝ)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) μ)
    (hRright_meas : ∀ n, AEStronglyMeasurable (Rright n) μ)
    (hRleft_meas : ∀ n, AEStronglyMeasurable (Rleft n) μ)
    (hWhat : TendstoInMeasure μ What atTop (fun _ => W))
    (hRright : TendstoInMeasure μ Rright atTop (fun _ => Rright0))
    (hRleft : TendstoInMeasure μ Rleft atTop (fun _ => Rleft0))
    (hW : IsUnit W.det) (hG : IsUnit (Rleft0ᵀ * W⁻¹ * Rright0).det) :
    TendstoInMeasure μ
      (fun n ω => nonlinearFirstOrderLinearMap (What n ω) (Rright n ω) (Rleft n ω))
      atTop (fun _ => nonlinearFirstOrderLinearMap W Rright0 Rleft0) := by
  have hpair : TendstoInMeasure μ (fun n ω => (What n ω, Rright n ω)) atTop
      (fun _ : Ω => (W, Rright0)) :=
    tendstoInMeasure_prodMk hWhat hRright
  have htriple : TendstoInMeasure μ
      (fun n ω => ((What n ω, Rright n ω), Rleft n ω)) atTop
      (fun _ : Ω => ((W, Rright0), Rleft0)) :=
    tendstoInMeasure_prodMk hpair hRleft
  exact tendstoInMeasure_continuousAt_const_comp
    (f := fun n ω => ((What n ω, Rright n ω), Rleft n ω))
    (x := ((W, Rright0), Rleft0))
    (h := fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ =>
      nonlinearFirstOrderLinearMap p.1.1 p.1.2 p.2)
    (fun n => ((hWhat_meas n).prodMk (hRright_meas n)).prodMk (hRleft_meas n))
    (fun n => nonlinearFirstOrderLinearMap_aestronglyMeasurable
      (What n) (Rright n) (Rleft n) (hWhat_meas n) (hRright_meas n) (hRleft_meas n))
    htriple
    (nonlinearFirstOrderLinearMap_continuousAt_of_nonsingular W Rright0 Rleft0 hW hG)

set_option maxHeartbeats 1200000 in
-- Product-space CMT for the random nonlinear FONC correction carries several finite-dimensional
-- topologies at once.
/-- If the random weight and left/right derivative matrices converge in measure, then the
nonlinear first-order constraint-correction map converges in measure to its limiting map. -/
theorem nonlinearFirstOrderConstraintCorrection_tendstoInMeasure_of_nonsingular
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (What : ℕ → Ω → Matrix k k ℝ) (Rright Rleft : ℕ → Ω → Matrix k q ℝ)
    (W : Matrix k k ℝ) (Rright0 Rleft0 : Matrix k q ℝ)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) μ)
    (hRright_meas : ∀ n, AEStronglyMeasurable (Rright n) μ)
    (hRleft_meas : ∀ n, AEStronglyMeasurable (Rleft n) μ)
    (hWhat : TendstoInMeasure μ What atTop (fun _ => W))
    (hRright : TendstoInMeasure μ Rright atTop (fun _ => Rright0))
    (hRleft : TendstoInMeasure μ Rleft atTop (fun _ => Rleft0))
    (hW : IsUnit W.det) (hG : IsUnit (Rleft0ᵀ * W⁻¹ * Rright0).det) :
    TendstoInMeasure μ
      (fun n ω =>
        nonlinearFirstOrderConstraintCorrection (What n ω) (Rright n ω) (Rleft n ω))
      atTop (fun _ => nonlinearFirstOrderConstraintCorrection W Rright0 Rleft0) := by
  have hpair : TendstoInMeasure μ (fun n ω => (What n ω, Rright n ω)) atTop
      (fun _ : Ω => (W, Rright0)) :=
    tendstoInMeasure_prodMk hWhat hRright
  have htriple : TendstoInMeasure μ
      (fun n ω => ((What n ω, Rright n ω), Rleft n ω)) atTop
      (fun _ : Ω => ((W, Rright0), Rleft0)) :=
    tendstoInMeasure_prodMk hpair hRleft
  exact tendstoInMeasure_continuousAt_const_comp
    (f := fun n ω => ((What n ω, Rright n ω), Rleft n ω))
    (x := ((W, Rright0), Rleft0))
    (h := fun p : (Matrix k k ℝ × Matrix k q ℝ) × Matrix k q ℝ =>
      nonlinearFirstOrderConstraintCorrection p.1.1 p.1.2 p.2)
    (fun n => ((hWhat_meas n).prodMk (hRright_meas n)).prodMk (hRleft_meas n))
    (fun n => nonlinearFirstOrderConstraintCorrection_aestronglyMeasurable
      (What n) (Rright n) (Rleft n) (hWhat_meas n) (hRright_meas n) (hRleft_meas n))
    htriple
    (nonlinearFirstOrderConstraintCorrection_continuousAt_of_nonsingular
      W Rright0 Rleft0 hW hG)

/-- Finite-sample algebra behind Hansen's nonlinear constrained-estimator proof.

If the solved first-order condition gives
`bhat - btilde = W⁻¹ Rright λ` and the linearized constraint gives
`Rleft' (btilde - β) = gap`, then the scaled constrained error is the nonlinear
first-order linear map applied to the scaled unrestricted error, plus an explicit correction for
the constraint gap. The theorem is deterministic; stochastic assumptions later make the matrices
converge and the gap negligible. -/
theorem nonlinearFirstOrder_scaledError_eq_linearMap_add_gap
    (root : ℝ) (W : Matrix k k ℝ) (Rright Rleft : Matrix k q ℝ)
    (β bhat btilde : k → ℝ) (lam gap : q → ℝ)
    (hstep : bhat - btilde = (W⁻¹ * Rright) *ᵥ lam)
    (hgap : Rleftᵀ *ᵥ (btilde - β) = gap)
    (hG : IsUnit (Rleftᵀ * W⁻¹ * Rright).det) :
    root • (btilde - β) =
      nonlinearFirstOrderLinearMap W Rright Rleft *ᵥ (root • (bhat - β)) +
        nonlinearFirstOrderConstraintCorrection W Rright Rleft *ᵥ (root • gap) := by
  let G : Matrix q q ℝ := Rleftᵀ * W⁻¹ * Rright
  let B : Matrix k q ℝ := W⁻¹ * Rright * G⁻¹
  have hdiff : bhat - btilde = (bhat - β) - (btilde - β) := by
    ext i
    simp
  have hGlam : G *ᵥ lam = Rleftᵀ *ᵥ (bhat - β) - gap := by
    calc
      G *ᵥ lam = Rleftᵀ *ᵥ ((W⁻¹ * Rright) *ᵥ lam) := by
        dsimp [G]
        rw [Matrix.mulVec_mulVec]
        simp [Matrix.mul_assoc]
      _ = Rleftᵀ *ᵥ (bhat - btilde) := by
        rw [← hstep]
      _ = Rleftᵀ *ᵥ ((bhat - β) - (btilde - β)) := by
        rw [hdiff]
      _ = Rleftᵀ *ᵥ (bhat - β) - Rleftᵀ *ᵥ (btilde - β) := by
        rw [Matrix.mulVec_sub]
      _ = Rleftᵀ *ᵥ (bhat - β) - gap := by
        rw [hgap]
  have hlam : lam = G⁻¹ *ᵥ (Rleftᵀ *ᵥ (bhat - β) - gap) := by
    calc
      lam = (1 : Matrix q q ℝ) *ᵥ lam := by
        simp
      _ = (G⁻¹ * G) *ᵥ lam := by
        rw [Matrix.nonsing_inv_mul G (by simpa [G] using hG)]
      _ = G⁻¹ *ᵥ (G *ᵥ lam) := by
        rw [Matrix.mulVec_mulVec]
      _ = G⁻¹ *ᵥ (Rleftᵀ *ᵥ (bhat - β) - gap) := by
        rw [hGlam]
  have hu : btilde - β = (1 - B * Rleftᵀ) *ᵥ (bhat - β) + B *ᵥ gap := by
    calc
      btilde - β = (bhat - β) - (bhat - btilde) := by
        ext i
        simp
      _ = (bhat - β) - (W⁻¹ * Rright) *ᵥ lam := by
        rw [hstep]
      _ = (bhat - β) -
            (W⁻¹ * Rright) *ᵥ (G⁻¹ *ᵥ (Rleftᵀ *ᵥ (bhat - β) - gap)) := by
        rw [hlam]
      _ = (bhat - β) - B *ᵥ (Rleftᵀ *ᵥ (bhat - β) - gap) := by
        dsimp [B]
        rw [Matrix.mulVec_mulVec]
      _ = (1 - B * Rleftᵀ) *ᵥ (bhat - β) + B *ᵥ gap := by
        rw [Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
        abel
  rw [hu]
  rw [smul_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  rfl

/-- Sequence form of `nonlinearFirstOrder_scaledError_eq_linearMap_add_gap`. This is the
deterministic constructor shape used before applying stochastic convergence of weights,
derivative matrices, and the Taylor constraint gap. -/
theorem nonlinearFirstOrder_scaledError_seq_eq_linearMap_add_gap
    {Ω : Type*} (root : ℕ → ℝ)
    (What : ℕ → Ω → Matrix k k ℝ) (Rright Rleft : ℕ → Ω → Matrix k q ℝ)
    (β : k → ℝ) (bhat btilde : ℕ → Ω → k → ℝ)
    (lam gap : ℕ → Ω → q → ℝ)
    (hstep : ∀ n ω,
      bhat n ω - btilde n ω = ((What n ω)⁻¹ * Rright n ω) *ᵥ lam n ω)
    (hgap : ∀ n ω, (Rleft n ω)ᵀ *ᵥ (btilde n ω - β) = gap n ω)
    (hG : ∀ n ω, IsUnit ((Rleft n ω)ᵀ * (What n ω)⁻¹ * Rright n ω).det) :
    constrainedScaledError root btilde β =
      fun n ω =>
        nonlinearFirstOrderLinearMap (What n ω) (Rright n ω) (Rleft n ω) *ᵥ
            (root n • (bhat n ω - β)) +
          nonlinearFirstOrderConstraintCorrection (What n ω) (Rright n ω) (Rleft n ω) *ᵥ
            (root n • gap n ω) := by
  funext n ω
  exact nonlinearFirstOrder_scaledError_eq_linearMap_add_gap
    (root n) (What n ω) (Rright n ω) (Rleft n ω) β (bhat n ω) (btilde n ω)
    (lam n ω) (gap n ω) (hstep n ω) (hgap n ω) (hG n ω)

/-- A fixed-weight, fixed-derivative first-order-condition constructor for the stable nonlinear
constrained-estimator linearization interface. The deterministic FONC algebra supplies the exact
scaled-error decomposition; the only stochastic input left is that the scaled nonlinear constraint
correction is negligible. -/
theorem constrainedEstimatorLinearization_of_fixed_firstOrder_gap
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (root : ℕ → ℝ) (W : Matrix k k ℝ) (Rderiv : Matrix k q ℝ) (β : k → ℝ)
    (bhat btilde : ℕ → Ω → k → ℝ) (lam gap : ℕ → Ω → q → ℝ)
    (hstep : ∀ n ω, bhat n ω - btilde n ω = (W⁻¹ * Rderiv) *ᵥ lam n ω)
    (hgap : ∀ n ω, Rderivᵀ *ᵥ (btilde n ω - β) = gap n ω)
    (hG : IsUnit (Rderivᵀ * W⁻¹ * Rderiv).det)
    (hscaled_meas : ∀ n, AEMeasurable (constrainedScaledError root btilde β n) μ)
    (hgap_rem : TendstoInMeasure μ
      (fun n ω => nonlinearFirstOrderConstraintCorrection W Rderiv Rderiv *ᵥ
        (root n • gap n ω)) atTop (fun _ => 0)) :
    ConstrainedEstimatorLinearization μ root btilde β W Rderiv
      (fun n ω => root n • (bhat n ω - β)) where
  scaled_measurable := hscaled_meas
  expansion := by
    have hexact := nonlinearFirstOrder_scaledError_seq_eq_linearMap_add_gap
      (root := root) (What := fun _ _ => W) (Rright := fun _ _ => Rderiv)
      (Rleft := fun _ _ => Rderiv) (β := β) (bhat := bhat) (btilde := btilde)
      (lam := lam) (gap := gap) hstep hgap (fun _ _ => hG)
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hgap_rem
    filter_upwards with ω
    funext i
    rw [Pi.sub_apply]
    rw [hexact]
    simp [nonlinearFirstOrderLinearMap_self_eq_mdLinearMap]

namespace NonlinearConstraintAssumption83

omit [DecidableEq k] [DecidableEq q] in
/-- Assumption 8.3 supplies the deterministic Taylor little-o expansion of the nonlinear
restriction map at the true parameter. -/
theorem taylorRemainder_isLittleO
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {Rderiv : Matrix k q ℝ}
    (h83 : NonlinearConstraintAssumption83 r β Rderiv) :
    nonlinearConstraintTaylorRemainder r β Rderiv =o[𝓝 β] (fun b => b - β) := by
  simpa [nonlinearConstraintTaylorRemainder, h83.derivative_apply] using
    h83.differentiable_at.isLittleO

omit [DecidableEq k] [DecidableEq q] in
/-- For any parameter satisfying the nonlinear restriction, the linearized restriction gap is
the negative Taylor remainder. This is the deterministic form of the mean-value/Taylor step in
Hansen's proof of Theorem 8.10. -/
theorem linearizedConstraint_eq_neg_taylorRemainder
    {r : (k → ℝ) → (q → ℝ)} {β b : k → ℝ} {Rderiv : Matrix k q ℝ}
    (h83 : NonlinearConstraintAssumption83 r β Rderiv) (hb : r b = 0) :
    Rderivᵀ *ᵥ (b - β) = -nonlinearConstraintTaylorRemainder r β Rderiv b := by
  ext j
  simp [nonlinearConstraintTaylorRemainder, hb, h83.constraint]

omit [DecidableEq k] [DecidableEq q] in
/-- Sequence form of `linearizedConstraint_eq_neg_taylorRemainder`, useful when the
constrained optimizer enforces `r(β̃ₙ) = 0` pointwise. -/
theorem linearizedConstraint_seq_eq_neg_taylorRemainder
    {Ω : Type*} {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {Rderiv : Matrix k q ℝ}
    (h83 : NonlinearConstraintAssumption83 r β Rderiv)
    (btilde : ℕ → Ω → k → ℝ) (hconstraint : ∀ n ω, r (btilde n ω) = 0) :
    (fun n ω => Rderivᵀ *ᵥ (btilde n ω - β)) =
      fun n ω => -nonlinearConstraintTaylorRemainder r β Rderiv (btilde n ω) := by
  funext n ω
  exact h83.linearizedConstraint_eq_neg_taylorRemainder (hconstraint n ω)

/-- Assumption 8.3 plus fixed-weight/fixed-derivative first-order conditions construct the stable
linearization interface when the scaled Taylor constraint correction is negligible. -/
theorem constrainedEstimatorLinearization_of_fixed_firstOrder
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {Rderiv : Matrix k q ℝ}
    (h83 : NonlinearConstraintAssumption83 r β Rderiv)
    (root : ℕ → ℝ) (W : Matrix k k ℝ)
    (bhat btilde : ℕ → Ω → k → ℝ) (lam : ℕ → Ω → q → ℝ)
    (hbtilde_meas : ∀ n, AEStronglyMeasurable (btilde n) μ)
    (hconstraint : ∀ n ω, r (btilde n ω) = 0)
    (hstep : ∀ n ω, bhat n ω - btilde n ω = (W⁻¹ * Rderiv) *ᵥ lam n ω)
    (hG : IsUnit (Rderivᵀ * W⁻¹ * Rderiv).det)
    (htaylor_rem : TendstoInMeasure μ
      (fun n ω => nonlinearFirstOrderConstraintCorrection W Rderiv Rderiv *ᵥ
        (root n • (-nonlinearConstraintTaylorRemainder r β Rderiv (btilde n ω))))
      atTop (fun _ => 0)) :
    ConstrainedEstimatorLinearization μ root btilde β W Rderiv
      (fun n ω => root n • (bhat n ω - β)) :=
  constrainedEstimatorLinearization_of_fixed_firstOrder_gap root W Rderiv β bhat btilde lam
    (fun n ω => -nonlinearConstraintTaylorRemainder r β Rderiv (btilde n ω)) hstep
    (by
      intro n ω
      exact h83.linearizedConstraint_eq_neg_taylorRemainder (hconstraint n ω))
    hG (constrainedScaledError_aemeasurable root btilde β hbtilde_meas) htaylor_rem

omit [DecidableEq q] in
/-- Assumption 8.3's rank condition and a positive-definite weight imply a positive-definite
nonlinear restriction Gram matrix. -/
theorem restrictionGram_posDef_of_weight_posDef
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {Rderiv : Matrix k q ℝ}
    (h83 : NonlinearConstraintAssumption83 r β Rderiv)
    (W : Matrix k k ℝ) (hW : W.PosDef) :
    (Rderivᵀ * W⁻¹ * Rderiv).PosDef := by
  have hWinv : W⁻¹.PosDef := hW.inv
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hWinv.conjTranspose_mul_mul_same h83.fullRank

/-- Assumption 8.3's rank condition and a positive-definite weight discharge the determinant
side condition for the nonlinear restriction Gram matrix. -/
theorem restrictionGram_det_isUnit_of_weight_posDef
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {Rderiv : Matrix k q ℝ}
    (h83 : NonlinearConstraintAssumption83 r β Rderiv)
    (W : Matrix k k ℝ) (hW : W.PosDef) :
    IsUnit (Rderivᵀ * W⁻¹ * Rderiv).det :=
  isUnit_iff_ne_zero.mpr (h83.restrictionGram_posDef_of_weight_posDef W hW).det_pos.ne'

omit [DecidableEq k] [DecidableEq q] in
/-- Assumption 8.3's rank condition and a positive-definite unrestricted covariance imply
positive definiteness of the efficient nonlinear restriction covariance `R' V R`. -/
theorem efficientRestrictionCov_posDef
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {Rderiv : Matrix k q ℝ}
    (h83 : NonlinearConstraintAssumption83 r β Rderiv)
    (V : Matrix k k ℝ) (hV : V.PosDef) :
    (Rderivᵀ * V * Rderiv).PosDef := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hV.conjTranspose_mul_mul_same h83.fullRank

omit [DecidableEq k] in
/-- The inverse efficient nonlinear restriction covariance is positive semidefinite under
Assumption 8.3 and positive-definite unrestricted covariance. -/
theorem efficientRestrictionCov_inv_posSemidef
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {Rderiv : Matrix k q ℝ}
    (h83 : NonlinearConstraintAssumption83 r β Rderiv)
    (V : Matrix k k ℝ) (hV : V.PosDef) :
    ((Rderivᵀ * V * Rderiv)⁻¹).PosSemidef :=
  (h83.efficientRestrictionCov_posDef V hV).inv.posSemidef

omit [DecidableEq k] in
/-- The efficient nonlinear restriction covariance has a unit determinant under Assumption 8.3
and positive-definite unrestricted covariance. -/
theorem efficientRestrictionCov_det_isUnit
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {Rderiv : Matrix k q ℝ}
    (h83 : NonlinearConstraintAssumption83 r β Rderiv)
    (V : Matrix k k ℝ) (hV : V.PosDef) :
    IsUnit (Rderivᵀ * V * Rderiv).det :=
  isUnit_iff_ne_zero.mpr (h83.efficientRestrictionCov_posDef V hV).det_pos.ne'

end NonlinearConstraintAssumption83

/-- A positive-definite real matrix has a unit determinant. -/
theorem posDef_det_isUnit (M : Matrix k k ℝ) (hM : M.PosDef) : IsUnit M.det := by
  exact isUnit_iff_ne_zero.mpr hM.det_pos.ne'

omit [DecidableEq q] in
/-- If the limiting weight is positive definite and the restriction matrix has full column rank,
then the restriction Gram matrix `Rᵀ W⁻¹ R` is positive definite. -/
theorem restrictionGram_posDef_of_weight_posDef
    (W : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hW : W.PosDef) (hR : Function.Injective R.mulVec) :
    (Rᵀ * W⁻¹ * R).PosDef := by
  have hWinv : W⁻¹.PosDef := hW.inv
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hWinv.conjTranspose_mul_mul_same hR

/-- Positive-definite limiting weights and full-column-rank restrictions discharge the
nonsingular restriction-Gram side condition used by the totalized MD formula. -/
theorem restrictionGram_det_isUnit_of_weight_posDef
    (W : Matrix k k ℝ) (R : Matrix k q ℝ)
    (hW : W.PosDef) (hR : Function.Injective R.mulVec) :
    IsUnit (Rᵀ * W⁻¹ * R).det :=
  posDef_det_isUnit (Rᵀ * W⁻¹ * R) (restrictionGram_posDef_of_weight_posDef W R hW hR)

/-- The population MD map fixes a parameter satisfying the restriction. -/
@[simp]
theorem mdBetaStar_eq_self_of_restrict
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (hrestrict : Rᵀ *ᵥ β = c) :
    mdBetaStar W R c β = β := by
  unfold mdBetaStar
  rw [hrestrict]
  simp

set_option maxHeartbeats 800000 in
-- Finite-dimensional matrix measurability through nested inverses and products is expensive here.
/-- The totalized minimum-distance map is a.e. strongly measurable whenever the
unrestricted estimator and weight matrix are. -/
theorem mdBetaStar_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (Wseq : Ω → Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (bhat : Ω → k → ℝ)
    (hW : AEStronglyMeasurable Wseq μ) (hb : AEStronglyMeasurable bhat μ) :
    AEStronglyMeasurable (fun ω => mdBetaStar (Wseq ω) R c (bhat ω)) μ := by
  have hWinv : AEStronglyMeasurable (fun ω => (Wseq ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hW
  have hRtWinv : AEStronglyMeasurable (fun ω => Rᵀ * (Wseq ω)⁻¹) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (aestronglyMeasurable_const.prodMk hWinv)
  have hGram : AEStronglyMeasurable (fun ω => Rᵀ * (Wseq ω)⁻¹ * R) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hRtWinv.prodMk aestronglyMeasurable_const)
  have hGramInv : AEStronglyMeasurable (fun ω => (Rᵀ * (Wseq ω)⁻¹ * R)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hGram
  have hWinvR : AEStronglyMeasurable (fun ω => (Wseq ω)⁻¹ * R) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hWinv.prodMk aestronglyMeasurable_const)
  have hB : AEStronglyMeasurable
      (fun ω => (Wseq ω)⁻¹ * R * (Rᵀ * (Wseq ω)⁻¹ * R)⁻¹) μ := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hWinvR.prodMk hGramInv)
  have hv : AEStronglyMeasurable (fun ω => Rᵀ *ᵥ bhat ω - c) μ := by
    exact ((Continuous.matrix_mulVec continuous_const continuous_id).comp_aestronglyMeasurable
      hb).sub aestronglyMeasurable_const
  unfold mdBetaStar
  exact hb.sub ((Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
    (hB.prodMk hv))

set_option maxHeartbeats 800000 in
-- Finite-dimensional matrix continuity through nested inverses and products is expensive here.
/-- The totalized minimum-distance map is continuous at nonsingular limiting weights whose
restriction Gram is also nonsingular. This discharges the continuity side condition in the
consistency wrapper from the usual population nonsingularity inputs. -/
theorem mdBetaStar_continuousAt_of_nonsingular
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (hW : IsUnit W.det) (hG : IsUnit (Rᵀ * W⁻¹ * R).det) :
    ContinuousAt (fun p : (k → ℝ) × Matrix k k ℝ => mdBetaStar p.2 R c p.1) (β, W) := by
  let G : Matrix q q ℝ := Rᵀ * W⁻¹ * R
  have hWInv : ContinuousAt (fun p : (k → ℝ) × Matrix k k ℝ => p.2⁻¹) (β, W) := by
    have hcontInv : ContinuousAt Inv.inv W := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hW.ne_zero
    exact hcontInv.comp continuousAt_snd
  have hRtWinv : ContinuousAt (fun p : (k → ℝ) × Matrix k k ℝ => Rᵀ * p.2⁻¹)
      (β, W) := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (continuousAt_const.prodMk hWInv)
  have hGram : ContinuousAt (fun p : (k → ℝ) × Matrix k k ℝ => Rᵀ * p.2⁻¹ * R)
      (β, W) := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hRtWinv.prodMk continuousAt_const)
  have hGramInv :
      ContinuousAt (fun p : (k → ℝ) × Matrix k k ℝ => (Rᵀ * p.2⁻¹ * R)⁻¹)
        (β, W) := by
    have hcontInv : ContinuousAt Inv.inv G := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hG.ne_zero
    simpa [G] using hcontInv.comp hGram
  have hWinvR : ContinuousAt (fun p : (k → ℝ) × Matrix k k ℝ => p.2⁻¹ * R)
      (β, W) := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hWInv.prodMk continuousAt_const)
  have hB : ContinuousAt
      (fun p : (k → ℝ) × Matrix k k ℝ => p.2⁻¹ * R * (Rᵀ * p.2⁻¹ * R)⁻¹)
        (β, W) := by
    exact (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hWinvR.prodMk hGramInv)
  have hv : ContinuousAt (fun p : (k → ℝ) × Matrix k k ℝ => Rᵀ *ᵥ p.1 - c)
      (β, W) := by
    exact (Continuous.matrix_mulVec continuous_const continuous_fst).continuousAt.sub
      continuousAt_const
  have hmulv : ContinuousAt
      (fun p : (k → ℝ) × Matrix k k ℝ =>
        (p.2⁻¹ * R * (Rᵀ * p.2⁻¹ * R)⁻¹) *ᵥ (Rᵀ *ᵥ p.1 - c)) (β, W) := by
    exact (Continuous.matrix_mulVec continuous_fst continuous_snd).continuousAt.comp
      (hB.prodMk hv)
  unfold mdBetaStar
  exact continuousAt_fst.sub hmulv

set_option maxHeartbeats 800000 in
-- Product-space typeclass synthesis for matrix-valued convergence is expensive here.
/-- Hansen Theorem 8.6 current-assumption MD consistency wrapper.

The assumptions are convergence of the unrestricted estimator and the weight matrix plus continuity
of the MD map at the limiting values. -/
theorem mdBeta_tendstoInMeasure_beta
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (bhat : ℕ → Ω → k → ℝ) (What : ℕ → Ω → Matrix k k ℝ)
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (hbhat_meas : ∀ n, AEStronglyMeasurable (bhat n) μ)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) μ)
    (hmd_meas : ∀ n,
      AEStronglyMeasurable (fun ω => mdBetaStar (What n ω) R c (bhat n ω)) μ)
    (hbhat : TendstoInMeasure μ bhat atTop (fun _ => β))
    (hWhat : TendstoInMeasure μ What atTop (fun _ => W))
    (hcont : ContinuousAt (fun p : (k → ℝ) × Matrix k k ℝ => mdBetaStar p.2 R c p.1)
      (β, W))
    (hrestrict : Rᵀ *ᵥ β = c) :
    TendstoInMeasure μ (fun n ω => mdBetaStar (What n ω) R c (bhat n ω)) atTop
      (fun _ => β) := by
  have hprod : TendstoInMeasure μ (fun n ω => (bhat n ω, What n ω)) atTop
      (fun _ => (β, W)) :=
    tendstoInMeasure_prodMk hbhat hWhat
  have hcomp : TendstoInMeasure μ
      (fun n ω => mdBetaStar (What n ω) R c (bhat n ω)) atTop
      (fun _ => mdBetaStar W R c β) :=
    tendstoInMeasure_continuousAt_const_comp
      (fun n => (hbhat_meas n).prodMk (hWhat_meas n)) hmd_meas hprod hcont
  simpa [mdBetaStar_eq_self_of_restrict W R c β hrestrict] using hcomp

set_option maxHeartbeats 800000 in
-- Product-space typeclass synthesis and the derived MD-map lemmas are expensive here.
/-- Hansen Theorem 8.6 consistency wrapper with the MD-map continuity and measurability
side conditions discharged from nonsingularity of the population weight and restriction Gram. -/
theorem mdBeta_tendstoInMeasure_beta_of_nonsingular
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (bhat : ℕ → Ω → k → ℝ) (What : ℕ → Ω → Matrix k k ℝ)
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (hbhat_meas : ∀ n, AEStronglyMeasurable (bhat n) μ)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) μ)
    (hbhat : TendstoInMeasure μ bhat atTop (fun _ => β))
    (hWhat : TendstoInMeasure μ What atTop (fun _ => W))
    (hWunit : IsUnit W.det) (hGunit : IsUnit (Rᵀ * W⁻¹ * R).det)
    (hrestrict : Rᵀ *ᵥ β = c) :
    TendstoInMeasure μ (fun n ω => mdBetaStar (What n ω) R c (bhat n ω)) atTop
      (fun _ => β) := by
  exact mdBeta_tendstoInMeasure_beta bhat What W R c β hbhat_meas hWhat_meas
    (fun n => mdBetaStar_aestronglyMeasurable (What n) R c (bhat n)
      (hWhat_meas n) (hbhat_meas n))
    hbhat hWhat
    (mdBetaStar_continuousAt_of_nonsingular W R c β hWunit hGunit)
    hrestrict

/-- MD scaled-error statistic. -/
noncomputable def mdScaledError
    {Ω : Type*} (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ) (What : ℕ → Ω → Matrix k k ℝ)
    (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ) : ℕ → Ω → k → ℝ :=
  fun n ω => root n • (mdBetaStar (What n ω) R c (bhat n ω) - β)

/-- With the true parameter satisfying the restriction, the fixed-weight MD estimator has the
exact linear expansion around the unrestricted estimator. -/
theorem mdBetaStar_sub_eq_linearMap
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β bhat : k → ℝ)
    (hrestrict : Rᵀ *ᵥ β = c) :
    mdBetaStar W R c bhat - β = mdLinearMap W R *ᵥ (bhat - β) := by
  let B : Matrix k q ℝ := W⁻¹ * R * (Rᵀ * W⁻¹ * R)⁻¹
  let A : Matrix k k ℝ := B * Rᵀ
  unfold mdBetaStar mdLinearMap
  change bhat - B *ᵥ (Rᵀ *ᵥ bhat - c) - β = (1 - A) *ᵥ (bhat - β)
  rw [← hrestrict]
  rw [← Matrix.mulVec_sub]
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.sub_mulVec]
  rw [Matrix.one_mulVec]
  dsimp [A]
  abel

/-- For a fixed MD weight, the MD scaled error is exactly the fixed MD linear map applied to the
unrestricted scaled error. -/
theorem mdScaledError_fixedWeight_eq_linearMap
    {Ω : Type*} (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ)
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (hrestrict : Rᵀ *ᵥ β = c) :
    mdScaledError root bhat (fun _ _ => W) R c β =
      fun n ω => mdLinearMap W R *ᵥ (root n • (bhat n ω - β)) := by
  funext n ω
  unfold mdScaledError
  rw [mdBetaStar_sub_eq_linearMap W R c β (bhat n ω) hrestrict]
  rw [Matrix.mulVec_smul]

/-- With random weights, the MD scaled error is still exactly the random MD linear map applied to
the unrestricted scaled error. -/
theorem mdScaledError_eq_randomLinearMap
    {Ω : Type*} (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ)
    (What : ℕ → Ω → Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (hrestrict : Rᵀ *ᵥ β = c) :
    mdScaledError root bhat What R c β =
      fun n ω => mdLinearMap (What n ω) R *ᵥ (root n • (bhat n ω - β)) := by
  funext n ω
  unfold mdScaledError
  rw [mdBetaStar_sub_eq_linearMap (What n ω) R c β (bhat n ω) hrestrict]
  rw [Matrix.mulVec_smul]

/-- The fixed-weight MD representation has zero linearization remainder. -/
theorem mdFixedWeight_remainder_tendstoInMeasure_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ)
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (hrestrict : Rᵀ *ᵥ β = c) :
    TendstoInMeasure μ
      (mdScaledError root bhat (fun _ _ => W) R c β -
        fun n ω => mdLinearMap W R *ᵥ (root n • (bhat n ω - β)))
      atTop (fun _ => 0) := by
  have hzero :
      TendstoInMeasure μ (fun _ : ℕ => fun _ : Ω => (0 : k → ℝ)) atTop (fun _ => 0) := by
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ (fun _ => tendsto_const_nhds))
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hzero
  filter_upwards with ω
  rw [Pi.sub_apply]
  rw [mdScaledError_fixedWeight_eq_linearMap root bhat W R c β hrestrict]
  simp

/-- CLS scaled-error statistic at the MD abstraction layer, using a supplied CLS weight sequence. -/
noncomputable def clsMDScaledError
    {Ω : Type*} (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ)
    (Qhat : ℕ → Ω → Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ) :
    ℕ → Ω → k → ℝ :=
  mdScaledError root bhat Qhat R c β

/-- Efficient-MD scaled-error statistic. -/
noncomputable def emdScaledError
    {Ω : Type*} (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ)
    (R : Matrix k q ℝ) (c : q → ℝ) (V : Matrix k k ℝ) (β : k → ℝ) :
    ℕ → Ω → k → ℝ :=
  fun n ω => root n • (emdBetaStar R c V (bhat n ω) - β)

set_option maxHeartbeats 800000 in
-- The nested MD estimator measurability lemma plus vector scaling is expensive here.
/-- The scaled MD error is a.e. measurable when the unrestricted estimator and weight process are
a.e. strongly measurable. -/
theorem mdScaledError_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ) (What : ℕ → Ω → Matrix k k ℝ)
    (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (hbhat_meas : ∀ n, AEStronglyMeasurable (bhat n) μ)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) μ) :
    ∀ n, AEMeasurable (mdScaledError root bhat What R c β n) μ := by
  intro n
  have hmd : AEStronglyMeasurable
      (fun ω => mdBetaStar (What n ω) R c (bhat n ω)) μ :=
    mdBetaStar_aestronglyMeasurable (What n) R c (bhat n) (hWhat_meas n)
      (hbhat_meas n)
  exact (AEStronglyMeasurable.const_smul
    (hmd.sub aestronglyMeasurable_const) (root n)).aemeasurable

/-- The scaled CLS-as-MD error is a.e. measurable under the corresponding OLS and Gram
measurability inputs. -/
theorem clsMDScaledError_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ) (Qhat : ℕ → Ω → Matrix k k ℝ)
    (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (hbhat_meas : ∀ n, AEStronglyMeasurable (bhat n) μ)
    (hQhat_meas : ∀ n, AEStronglyMeasurable (Qhat n) μ) :
    ∀ n, AEMeasurable (clsMDScaledError root bhat Qhat R c β n) μ :=
  mdScaledError_aemeasurable root bhat Qhat R c β hbhat_meas hQhat_meas

set_option maxHeartbeats 800000 in
-- The EMD estimator is the MD estimator with a constant efficient weight.
/-- The scaled efficient-MD error is a.e. measurable when the unrestricted estimator is
a.e. strongly measurable. -/
theorem emdScaledError_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ)
    (R : Matrix k q ℝ) (c : q → ℝ) (V : Matrix k k ℝ) (β : k → ℝ)
    (hbhat_meas : ∀ n, AEStronglyMeasurable (bhat n) μ) :
    ∀ n, AEMeasurable (emdScaledError root bhat R c V β n) μ := by
  intro n
  have hmd : AEStronglyMeasurable
      (fun ω => emdBetaStar R c V (bhat n ω)) μ := by
    simpa [emdBetaStar] using
      mdBetaStar_aestronglyMeasurable (fun _ : Ω => V⁻¹) R c (bhat n)
        aestronglyMeasurable_const (hbhat_meas n)
  exact (AEStronglyMeasurable.const_smul
    (hmd.sub aestronglyMeasurable_const) (root n)).aemeasurable

/-- Fixed linear maps preserve centered multivariate Gaussian distributional limits, with the
covariance transformed as `M S Mᵀ`. This is the Gaussian CMT input used by the Chapter 8
minimum-distance Slutsky wrappers. -/
theorem fixedMatrix_mulVec_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M S : Matrix k k ℝ) (hS : S.PosSemidef) (T : ℕ → Ω → k → ℝ)
    (hT : TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 S)) :
    TendstoInDistribution (fun n ω => M *ᵥ T n ω) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (M * S * Mᵀ)) := by
  let Te : ℕ → Ω → EuclideanSpace ℝ k := fun n ω => WithLp.toLp 2 (T n ω)
  have hTe : TendstoInDistribution Te atTop (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ) (multivariateGaussian 0 S) := by
    have hmap := hT.continuous_comp (PiLp.continuous_toLp 2 (fun _ : k => ℝ))
    simpa [Te, Function.comp_def] using hmap
  have hlin : TendstoInDistribution
      (fun n => matrixContinuousLinearMap M ∘ Te n)
      atTop (matrixContinuousLinearMap M ∘ fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ) (multivariateGaussian 0 S) :=
    hTe.continuous_comp (matrixContinuousLinearMap M).continuous
  have hLaw : HasLaw (fun z : EuclideanSpace ℝ k => matrixContinuousLinearMap M z)
      (multivariateGaussian 0 (M * S * Mᵀ)) (multivariateGaussian 0 S) := by
    simpa [matrixContinuousLinearMap, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hasLaw_multivariateGaussian_zero_linearMap (n := k) (q := k) hS M
  have htargetE : TendstoInDistribution
      (fun n ω => matrixContinuousLinearMap M (Te n ω))
      atTop (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ) (multivariateGaussian 0 (M * S * Mᵀ)) := by
    simpa [Function.comp_def] using
      tendstoInDistribution_id_of_hasLaw_limit (E := EuclideanSpace ℝ k) hlin hLaw
  have htarget := htargetE.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : k => ℝ))
  simpa [Te, Function.comp_def, matrixContinuousLinearMap_apply] using htarget

/-- Random matrix-vector Slutsky wrapper for centered multivariate Gaussian limits. If
`Ahatₙ →ₚ A`, then `Ahatₙ Tₙ` has the fixed linear Gaussian image limit. -/
theorem randomMatrix_mulVec_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Ahat : ℕ → Ω → Matrix k k ℝ) (A S : Matrix k k ℝ) (T : ℕ → Ω → k → ℝ)
    (hS : S.PosSemidef)
    (hA_meas : ∀ n, AEStronglyMeasurable (Ahat n) μ)
    (hA : TendstoInMeasure μ Ahat atTop (fun _ => A))
    (hT : TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 S)) :
    TendstoInDistribution (fun n ω => Ahat n ω *ᵥ T n ω) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (A * S * Aᵀ)) := by
  letI : MeasurableSpace (Matrix k k ℝ) := matrixBorelMeasurableSpace k k
  letI : BorelSpace (Matrix k k ℝ) := matrixBorelSpace k k
  let Te : ℕ → Ω → EuclideanSpace ℝ k := fun n ω => WithLp.toLp 2 (T n ω)
  have hTe : TendstoInDistribution Te atTop (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ) (multivariateGaussian 0 S) := by
    have hmap := hT.continuous_comp (PiLp.continuous_toLp 2 (fun _ : k => ℝ))
    simpa [Te, Function.comp_def] using hmap
  have hcont : Continuous
      (fun p : EuclideanSpace ℝ k × Matrix k k ℝ =>
        WithLp.toLp 2 (p.2 *ᵥ p.1.ofLp)) := by
    have hvec : Continuous
        (fun p : EuclideanSpace ℝ k × Matrix k k ℝ => p.2 *ᵥ p.1.ofLp) := by
      exact Continuous.matrix_mulVec continuous_snd
        ((PiLp.continuous_ofLp 2 (fun _ : k => ℝ)).comp continuous_fst)
    exact (PiLp.continuous_toLp 2 (fun _ : k => ℝ)).comp hvec
  have hlin : TendstoInDistribution
      (fun n ω => WithLp.toLp 2 (Ahat n ω *ᵥ T n ω))
      atTop (fun z : EuclideanSpace ℝ k => WithLp.toLp 2 (A *ᵥ z.ofLp))
      (fun _ => μ) (multivariateGaussian 0 S) := by
    have hraw := hTe.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : EuclideanSpace ℝ k × Matrix k k ℝ =>
        WithLp.toLp 2 (p.2 *ᵥ p.1.ofLp))
      hcont hA (fun n => (hA_meas n).aemeasurable)
    simpa [Te, Function.comp_def] using hraw
  have hLaw : HasLaw (fun z : EuclideanSpace ℝ k => WithLp.toLp 2 (A *ᵥ z.ofLp))
      (multivariateGaussian 0 (A * S * Aᵀ)) (multivariateGaussian 0 S) := by
    simpa [matrixContinuousLinearMap, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hasLaw_multivariateGaussian_zero_linearMap (n := k) (q := k) hS A
  have htargetE : TendstoInDistribution
      (fun n ω => WithLp.toLp 2 (Ahat n ω *ᵥ T n ω))
      atTop (fun z : EuclideanSpace ℝ k => z)
      (fun _ => μ) (multivariateGaussian 0 (A * S * Aᵀ)) := by
    simpa using tendstoInDistribution_id_of_hasLaw_limit (E := EuclideanSpace ℝ k) hlin hLaw
  have htarget := htargetE.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : k => ℝ))
  simpa [Function.comp_def] using htarget

/-- Hansen Theorem 8.7 current-assumption MD asymptotic-normality/Slutsky wrapper. -/
theorem mdBeta_tendstoInDistribution_gaussian
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ) (What : ℕ → Ω → Matrix k k ℝ)
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (T : ℕ → Ω → k → ℝ) (Z : Ω' → k → ℝ)
    (hlin : TendstoInDistribution (fun n ω => mdLinearMap W R *ᵥ T n ω)
      atTop Z (fun _ => μ) ν)
    (hrem : TendstoInMeasure μ
      (mdScaledError root bhat What R c β - fun n ω => mdLinearMap W R *ᵥ T n ω)
      atTop (fun _ => 0))
    (hmeas : ∀ n, AEMeasurable (mdScaledError root bhat What R c β n) μ) :
    TendstoInDistribution (mdScaledError root bhat What R c β) atTop Z (fun _ => μ) ν :=
  tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n ω => mdLinearMap W R *ᵥ T n ω)
    (Y := mdScaledError root bhat What R c β) (Z := Z) hlin hrem hmeas

/-- Hansen Theorem 8.7 with scaled-error measurability discharged from measurability of the
unrestricted estimator and weight process. -/
theorem mdBeta_tendstoInDistribution_gaussian_of_measurable
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ) (What : ℕ → Ω → Matrix k k ℝ)
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (T : ℕ → Ω → k → ℝ) (Z : Ω' → k → ℝ)
    (hbhat_meas : ∀ n, AEStronglyMeasurable (bhat n) μ)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) μ)
    (hlin : TendstoInDistribution (fun n ω => mdLinearMap W R *ᵥ T n ω)
      atTop Z (fun _ => μ) ν)
    (hrem : TendstoInMeasure μ
      (mdScaledError root bhat What R c β - fun n ω => mdLinearMap W R *ᵥ T n ω)
      atTop (fun _ => 0)) :
    TendstoInDistribution (mdScaledError root bhat What R c β) atTop Z (fun _ => μ) ν :=
  mdBeta_tendstoInDistribution_gaussian root bhat What W R c β T Z hlin hrem
    (mdScaledError_aemeasurable root bhat What R c β hbhat_meas hWhat_meas)

/-- Hansen Theorem 8.7 with the fixed-linear Gaussian limit and scaled-error measurability
discharged. The remaining statistical input is the MD linearization remainder. -/
theorem mdBeta_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ) (What : ℕ → Ω → Matrix k k ℝ)
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (S : Matrix k k ℝ) (T : ℕ → Ω → k → ℝ)
    (hS : S.PosSemidef)
    (hbhat_meas : ∀ n, AEStronglyMeasurable (bhat n) μ)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) μ)
    (hT : TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 S))
    (hrem : TendstoInMeasure μ
      (mdScaledError root bhat What R c β - fun n ω => mdLinearMap W R *ᵥ T n ω)
      atTop (fun _ => 0)) :
    TendstoInDistribution (mdScaledError root bhat What R c β) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (mdAsymptoticVariance W R S)) := by
  have hlin :=
    fixedMatrix_mulVec_tendstoInDistribution_multivariateGaussian
      (M := mdLinearMap W R) (S := S) hS T hT
  exact mdBeta_tendstoInDistribution_gaussian_of_measurable
    root bhat What W R c β T (fun z : EuclideanSpace ℝ k => z.ofLp)
    hbhat_meas hWhat_meas (by simpa [mdAsymptoticVariance] using hlin) hrem

/-- Hansen Theorem 8.7 in the fixed-weight MD case: the exact fixed-weight linearization
discharges the remainder side condition. -/
theorem mdBeta_fixedWeight_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ)
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (S : Matrix k k ℝ)
    (hS : S.PosSemidef)
    (hbhat_meas : ∀ n, AEStronglyMeasurable (bhat n) μ)
    (hrestrict : Rᵀ *ᵥ β = c)
    (hT : TendstoInDistribution (fun n ω => root n • (bhat n ω - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ) (multivariateGaussian 0 S)) :
    TendstoInDistribution (mdScaledError root bhat (fun _ _ => W) R c β) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (mdAsymptoticVariance W R S)) := by
  exact mdBeta_tendstoInDistribution_multivariateGaussian
    root bhat (fun _ _ => W) W R c β S (fun n ω => root n • (bhat n ω - β)) hS
    hbhat_meas (fun _ => aestronglyMeasurable_const) hT
    (mdFixedWeight_remainder_tendstoInMeasure_zero root bhat W R c β hrestrict)

/-- Hansen Theorem 8.7 random-weight MD case. Assumption 8.2 supplies `What →ₚ W`;
continuity of the MD linear map and the random matrix Slutsky wrapper discharge the
linearization step. -/
theorem mdBeta_randomWeight_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ) (What : ℕ → Ω → Matrix k k ℝ)
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (S : Matrix k k ℝ)
    (hS : S.PosSemidef)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) μ)
    (hWhat : TendstoInMeasure μ What atTop (fun _ => W))
    (hW : IsUnit W.det) (hG : IsUnit (Rᵀ * W⁻¹ * R).det)
    (hrestrict : Rᵀ *ᵥ β = c)
    (hT : TendstoInDistribution (fun n ω => root n • (bhat n ω - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ) (multivariateGaussian 0 S)) :
    TendstoInDistribution (mdScaledError root bhat What R c β) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (mdAsymptoticVariance W R S)) := by
  rw [mdScaledError_eq_randomLinearMap root bhat What R c β hrestrict]
  exact randomMatrix_mulVec_tendstoInDistribution_multivariateGaussian
    (fun n ω => mdLinearMap (What n ω) R) (mdLinearMap W R) S
    (fun n ω => root n • (bhat n ω - β)) hS
    (fun n => mdLinearMap_aestronglyMeasurable (What n) R (hWhat_meas n))
    (mdLinearMap_tendstoInMeasure_of_nonsingular What W R hWhat_meas hWhat hW hG)
    hT

/-- Hansen Theorem 8.7 random-weight MD case with textbook-shaped positive-definite
weight and full-column-rank restriction assumptions. -/
theorem mdBeta_randomWeight_tendstoInDistribution_multivariateGaussian_of_posDef
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ) (What : ℕ → Ω → Matrix k k ℝ)
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (S : Matrix k k ℝ)
    (hS : S.PosSemidef)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) μ)
    (hWhat : TendstoInMeasure μ What atTop (fun _ => W))
    (hW : W.PosDef) (hR : Function.Injective R.mulVec)
    (hrestrict : Rᵀ *ᵥ β = c)
    (hT : TendstoInDistribution (fun n ω => root n • (bhat n ω - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ) (multivariateGaussian 0 S)) :
    TendstoInDistribution (mdScaledError root bhat What R c β) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (mdAsymptoticVariance W R S)) :=
  mdBeta_randomWeight_tendstoInDistribution_multivariateGaussian
    root bhat What W R c β S hS hWhat_meas hWhat
    (posDef_det_isUnit W hW)
    (restrictionGram_det_isUnit_of_weight_posDef W R hW hR)
    hrestrict hT

/-- Hansen Theorem 8.8 CLS asymptotic-normality wrapper as the MD specialization. -/
theorem clsBeta_tendstoInDistribution_gaussian
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ) (Qhat : ℕ → Ω → Matrix k k ℝ)
    (Q : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (T : ℕ → Ω → k → ℝ) (Z : Ω' → k → ℝ)
    (hlin : TendstoInDistribution (fun n ω => mdLinearMap Q R *ᵥ T n ω)
      atTop Z (fun _ => μ) ν)
    (hrem : TendstoInMeasure μ
      (clsMDScaledError root bhat Qhat R c β - fun n ω => mdLinearMap Q R *ᵥ T n ω)
      atTop (fun _ => 0))
    (hmeas : ∀ n, AEMeasurable (clsMDScaledError root bhat Qhat R c β n) μ) :
    TendstoInDistribution (clsMDScaledError root bhat Qhat R c β) atTop Z (fun _ => μ) ν :=
  mdBeta_tendstoInDistribution_gaussian root bhat Qhat Q R c β T Z hlin hrem hmeas

/-- Hansen Theorem 8.8 with scaled CLS error measurability discharged from estimator and
sample-Gram measurability. -/
theorem clsBeta_tendstoInDistribution_gaussian_of_measurable
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ) (Qhat : ℕ → Ω → Matrix k k ℝ)
    (Q : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (T : ℕ → Ω → k → ℝ) (Z : Ω' → k → ℝ)
    (hbhat_meas : ∀ n, AEStronglyMeasurable (bhat n) μ)
    (hQhat_meas : ∀ n, AEStronglyMeasurable (Qhat n) μ)
    (hlin : TendstoInDistribution (fun n ω => mdLinearMap Q R *ᵥ T n ω)
      atTop Z (fun _ => μ) ν)
    (hrem : TendstoInMeasure μ
      (clsMDScaledError root bhat Qhat R c β - fun n ω => mdLinearMap Q R *ᵥ T n ω)
      atTop (fun _ => 0)) :
    TendstoInDistribution (clsMDScaledError root bhat Qhat R c β) atTop Z (fun _ => μ) ν :=
  clsBeta_tendstoInDistribution_gaussian root bhat Qhat Q R c β T Z hlin hrem
    (clsMDScaledError_aemeasurable root bhat Qhat R c β hbhat_meas hQhat_meas)

/-- Hansen Theorem 8.8 with the fixed-linear Gaussian limit and scaled-error measurability
discharged. The remaining statistical input is the CLS-as-MD linearization remainder. -/
theorem clsBeta_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ) (Qhat : ℕ → Ω → Matrix k k ℝ)
    (Q : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (S : Matrix k k ℝ) (T : ℕ → Ω → k → ℝ)
    (hS : S.PosSemidef)
    (hbhat_meas : ∀ n, AEStronglyMeasurable (bhat n) μ)
    (hQhat_meas : ∀ n, AEStronglyMeasurable (Qhat n) μ)
    (hT : TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 S))
    (hrem : TendstoInMeasure μ
      (clsMDScaledError root bhat Qhat R c β - fun n ω => mdLinearMap Q R *ᵥ T n ω)
      atTop (fun _ => 0)) :
    TendstoInDistribution (clsMDScaledError root bhat Qhat R c β) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (clsAsymptoticVariance Q R S)) := by
  have hlin :=
    fixedMatrix_mulVec_tendstoInDistribution_multivariateGaussian
      (M := mdLinearMap Q R) (S := S) hS T hT
  exact clsBeta_tendstoInDistribution_gaussian_of_measurable
    root bhat Qhat Q R c β T (fun z : EuclideanSpace ℝ k => z.ofLp)
    hbhat_meas hQhat_meas (by simpa [clsAsymptoticVariance, mdAsymptoticVariance] using hlin)
    hrem

/-- Hansen Theorem 8.8 random-weight CLS-as-MD case. Convergence of the sample Gram weight
discharges the CLS-as-MD linearization through the random-weight MD theorem. -/
theorem clsBeta_randomWeight_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ) (Qhat : ℕ → Ω → Matrix k k ℝ)
    (Q : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (S : Matrix k k ℝ)
    (hS : S.PosSemidef)
    (hQhat_meas : ∀ n, AEStronglyMeasurable (Qhat n) μ)
    (hQhat : TendstoInMeasure μ Qhat atTop (fun _ => Q))
    (hQ : IsUnit Q.det) (hG : IsUnit (Rᵀ * Q⁻¹ * R).det)
    (hrestrict : Rᵀ *ᵥ β = c)
    (hT : TendstoInDistribution (fun n ω => root n • (bhat n ω - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ) (multivariateGaussian 0 S)) :
    TendstoInDistribution (clsMDScaledError root bhat Qhat R c β) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (clsAsymptoticVariance Q R S)) := by
  simpa [clsMDScaledError, clsAsymptoticVariance] using
    mdBeta_randomWeight_tendstoInDistribution_multivariateGaussian
      root bhat Qhat Q R c β S hS hQhat_meas hQhat hQ hG hrestrict hT

/-- Hansen Theorem 8.8 random-weight CLS-as-MD case with positive-definite population
Gram and full-column-rank restriction assumptions. -/
theorem clsBeta_randomWeight_tendstoInDistribution_multivariateGaussian_of_posDef
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ) (Qhat : ℕ → Ω → Matrix k k ℝ)
    (Q : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ)
    (S : Matrix k k ℝ)
    (hS : S.PosSemidef)
    (hQhat_meas : ∀ n, AEStronglyMeasurable (Qhat n) μ)
    (hQhat : TendstoInMeasure μ Qhat atTop (fun _ => Q))
    (hQ : Q.PosDef) (hR : Function.Injective R.mulVec)
    (hrestrict : Rᵀ *ᵥ β = c)
    (hT : TendstoInDistribution (fun n ω => root n • (bhat n ω - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ) (multivariateGaussian 0 S)) :
    TendstoInDistribution (clsMDScaledError root bhat Qhat R c β) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (clsAsymptoticVariance Q R S)) :=
  clsBeta_randomWeight_tendstoInDistribution_multivariateGaussian
    root bhat Qhat Q R c β S hS hQhat_meas hQhat
    (posDef_det_isUnit Q hQ)
    (restrictionGram_det_isUnit_of_weight_posDef Q R hQ hR)
    hrestrict hT

/-- The Chapter 7 heteroskedastic OLS sandwich covariance is positive semidefinite under
the score CLT condition package. -/
theorem heteroAsymCov_posSemidef
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) :
    (heteroAsymCov μ X e).PosSemidef := by
  let A : Matrix k k ℝ := (popGram μ X)⁻¹
  have hΩ := scoreCovMat_posSemidef (μ := μ) (X := X) (e := e)
    h.toSampleCLTAssumption72
  have hA : Aᵀ = A := by
    simpa [A] using (popGram_inv_isSymm (μ := μ) (X := X)
      h.toSampleMomentAssumption71.int_outer).eq
  have hpsd : (A * scoreCovMat μ X e * Aᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose] using Matrix.PosSemidef.mul_mul_conjTranspose_same hΩ A
  simpa [heteroAsymCov, A, hA] using hpsd

/-- Chapter 7's OLS CLT relabeled with Hansen's heteroskedastic coefficient covariance
`Q⁻¹ Ω Q⁻¹`. -/
theorem olsBetaStar_vector_tendstoInDistribution_heteroAsymCov
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInDistribution
      (fun (n : ℕ) ω => Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (heteroAsymCov μ X e)) := by
  let T : ℕ → Ω → k → ℝ :=
    fun (n : ℕ) ω => Real.sqrt (n : ℝ) •
      (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)
  let Te : ℕ → Ω → EuclideanSpace ℝ k := fun n ω => WithLp.toLp 2 (T n ω)
  have hbase := olsBetaStar_vector_tendstoInDistribution_multivariateGaussian
    (μ := μ) (X := X) (e := e) (y := y) h β hmodel
  have hTe : TendstoInDistribution Te atTop
      (fun z : EuclideanSpace ℝ k => WithLp.toLp 2 ((popGram μ X)⁻¹ *ᵥ z.ofLp))
      (fun _ => μ) (multivariateGaussian 0 (scoreCovMat μ X e)) := by
    have hmap := hbase.continuous_comp (PiLp.continuous_toLp 2 (fun _ : k => ℝ))
    simpa [T, Te, Function.comp_def] using hmap
  have hΩ := scoreCovMat_posSemidef (μ := μ) (X := X) (e := e)
    h.toSampleCLTAssumption72
  let A : Matrix k k ℝ := (popGram μ X)⁻¹
  have hLaw : HasLaw
      (fun z : EuclideanSpace ℝ k => WithLp.toLp 2 (A *ᵥ z.ofLp))
      (multivariateGaussian 0 (heteroAsymCov μ X e))
      (multivariateGaussian 0 (scoreCovMat μ X e)) := by
    have hQinv_transpose : Aᵀ = A := by
      simpa [A] using (popGram_inv_isSymm (μ := μ) (X := X)
        h.toSampleMomentAssumption71.int_outer).eq
    have hraw := hasLaw_multivariateGaussian_zero_linearMap (n := k) (q := k) hΩ A
    simpa [heteroAsymCov, A, hQinv_transpose] using hraw
  have htargetE :
      TendstoInDistribution Te atTop (fun z : EuclideanSpace ℝ k => z)
        (fun _ => μ) (multivariateGaussian 0 (heteroAsymCov μ X e)) := by
    simpa [T, Te, A] using
      tendstoInDistribution_id_of_hasLaw_limit (E := EuclideanSpace ℝ k) hTe hLaw
  have htarget := htargetE.continuous_comp (PiLp.continuous_ofLp 2 (fun _ : k => ℝ))
  simpa [T, Te, Function.comp_def] using htarget

/-- Hansen Theorem 8.7 specialized to totalized OLS under Chapter 7 score-CLT conditions
and a random weight satisfying Assumption 8.2. -/
theorem mdBeta_olsBetaStar_randomWeight_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (What : ℕ → Ω → Matrix k k ℝ)
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) μ)
    (hWhat : TendstoInMeasure μ What atTop (fun _ => W))
    (hW : IsUnit W.det) (hG : IsUnit (Rᵀ * W⁻¹ * R).det)
    (hrestrict : Rᵀ *ᵥ β = c) :
    TendstoInDistribution
      (mdScaledError (fun n => Real.sqrt (n : ℝ))
        (fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω))
        What R c β)
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (mdAsymptoticVariance W R (heteroAsymCov μ X e))) := by
  exact mdBeta_randomWeight_tendstoInDistribution_multivariateGaussian
    (fun n => Real.sqrt (n : ℝ))
    (fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω))
    What W R c β (heteroAsymCov μ X e)
    (heteroAsymCov_posSemidef h)
    hWhat_meas hWhat hW hG hrestrict
    (olsBetaStar_vector_tendstoInDistribution_heteroAsymCov h β hmodel)

/-- Hansen Theorem 8.7 specialized to totalized OLS under Chapter 7 score-CLT conditions,
with textbook-shaped positive-definite weight and full-column-rank restriction assumptions. -/
theorem mdBeta_olsBetaStar_randomWeight_tendstoInDistribution_multivariateGaussian_of_posDef
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (What : ℕ → Ω → Matrix k k ℝ)
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    (hWhat_meas : ∀ n, AEStronglyMeasurable (What n) μ)
    (hWhat : TendstoInMeasure μ What atTop (fun _ => W))
    (hW : W.PosDef) (hR : Function.Injective R.mulVec)
    (hrestrict : Rᵀ *ᵥ β = c) :
    TendstoInDistribution
      (mdScaledError (fun n => Real.sqrt (n : ℝ))
        (fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω))
        What R c β)
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (mdAsymptoticVariance W R (heteroAsymCov μ X e))) := by
  exact mdBeta_randomWeight_tendstoInDistribution_multivariateGaussian_of_posDef
    (fun n => Real.sqrt (n : ℝ))
    (fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω))
    What W R c β (heteroAsymCov μ X e)
    (heteroAsymCov_posSemidef h)
    hWhat_meas hWhat hW hR hrestrict
    (olsBetaStar_vector_tendstoInDistribution_heteroAsymCov h β hmodel)

/-- Hansen Theorem 8.8 specialized to totalized OLS and the Chapter 7 sample-Gram
weight process. -/
theorem clsBeta_olsBetaStar_sampleGram_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (R : Matrix k q ℝ) (c : q → ℝ)
    (hG : IsUnit (Rᵀ * (popGram μ X)⁻¹ * R).det)
    (hrestrict : Rᵀ *ᵥ β = c) :
    TendstoInDistribution
      (clsMDScaledError (fun n => Real.sqrt (n : ℝ))
        (fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω))
        (fun n ω => sampleGram (stackRegressors X n ω)) R c β)
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (clsAsymptoticVariance (popGram μ X) R (heteroAsymCov μ X e))) := by
  exact clsBeta_randomWeight_tendstoInDistribution_multivariateGaussian
    (fun n => Real.sqrt (n : ℝ))
    (fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω))
    (fun n ω => sampleGram (stackRegressors X n ω))
    (popGram μ X) R c β (heteroAsymCov μ X e)
    (heteroAsymCov_posSemidef h)
    (fun n => sampleGram_stackRegressors_aestronglyMeasurable
      h.toSampleMomentAssumption71 n)
    (sampleGram_stackRegressors_tendstoInMeasure_popGram h.toSampleMomentAssumption71)
    h.toSampleMomentAssumption71.Q_nonsing hG hrestrict
    (olsBetaStar_vector_tendstoInDistribution_heteroAsymCov h β hmodel)

/-- Hansen Theorem 8.8 specialized to totalized OLS and the Chapter 7 sample-Gram
weight process, with positive-definite population Gram and full-column-rank restrictions. -/
theorem clsBeta_olsBetaStar_sampleGram_tendstoInDistribution_multivariateGaussian_of_posDef
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (R : Matrix k q ℝ) (c : q → ℝ)
    (hQ : (popGram μ X).PosDef) (hR : Function.Injective R.mulVec)
    (hrestrict : Rᵀ *ᵥ β = c) :
    TendstoInDistribution
      (clsMDScaledError (fun n => Real.sqrt (n : ℝ))
        (fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω))
        (fun n ω => sampleGram (stackRegressors X n ω)) R c β)
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (clsAsymptoticVariance (popGram μ X) R (heteroAsymCov μ X e))) := by
  exact clsBeta_olsBetaStar_sampleGram_tendstoInDistribution_multivariateGaussian
    h β hmodel R c
    (restrictionGram_det_isUnit_of_weight_posDef (popGram μ X) R hQ hR)
    hrestrict

/-- Hansen Theorem 8.8 specialized to totalized OLS and the Chapter 7 sample-Gram
weight process, deriving the positive-definite population Gram condition from the
Chapter 7 moment layer and assuming only full-column-rank restrictions. -/
theorem clsBeta_olsBetaStar_sampleGram_tendstoInDistribution_multivariateGaussian_of_fullRank
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (R : Matrix k q ℝ) (c : q → ℝ)
    (hR : Function.Injective R.mulVec)
    (hrestrict : Rᵀ *ᵥ β = c) :
    TendstoInDistribution
      (clsMDScaledError (fun n => Real.sqrt (n : ℝ))
        (fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω))
        (fun n ω => sampleGram (stackRegressors X n ω)) R c β)
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0
        (clsAsymptoticVariance (popGram μ X) R (heteroAsymCov μ X e))) := by
  exact clsBeta_olsBetaStar_sampleGram_tendstoInDistribution_multivariateGaussian_of_posDef
    h β hmodel R c (popGram_posDef h.toSampleMomentAssumption71) hR hrestrict

/-- Hansen Theorem 8.9 efficient-MD distribution wrapper. -/
theorem emdBeta_tendstoInDistribution_gaussian
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    (V : Matrix k k ℝ) (β : k → ℝ) (T : ℕ → Ω → k → ℝ) (Z : Ω' → k → ℝ)
    (hlin : TendstoInDistribution (fun n ω => mdLinearMap V⁻¹ R *ᵥ T n ω)
      atTop Z (fun _ => μ) ν)
    (hrem : TendstoInMeasure μ
      (emdScaledError root bhat R c V β - fun n ω => mdLinearMap V⁻¹ R *ᵥ T n ω)
      atTop (fun _ => 0))
    (hmeas : ∀ n, AEMeasurable (emdScaledError root bhat R c V β n) μ) :
    TendstoInDistribution (emdScaledError root bhat R c V β) atTop Z (fun _ => μ) ν :=
  tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n ω => mdLinearMap V⁻¹ R *ᵥ T n ω)
    (Y := emdScaledError root bhat R c V β) (Z := Z) hlin hrem hmeas

/-- Hansen Theorem 8.9 efficient-MD distribution wrapper with scaled-error measurability
discharged from unrestricted-estimator measurability. -/
theorem emdBeta_tendstoInDistribution_gaussian_of_measurable
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ) (R : Matrix k q ℝ) (c : q → ℝ)
    (V : Matrix k k ℝ) (β : k → ℝ) (T : ℕ → Ω → k → ℝ) (Z : Ω' → k → ℝ)
    (hbhat_meas : ∀ n, AEStronglyMeasurable (bhat n) μ)
    (hlin : TendstoInDistribution (fun n ω => mdLinearMap V⁻¹ R *ᵥ T n ω)
      atTop Z (fun _ => μ) ν)
    (hrem : TendstoInMeasure μ
      (emdScaledError root bhat R c V β - fun n ω => mdLinearMap V⁻¹ R *ᵥ T n ω)
      atTop (fun _ => 0)) :
    TendstoInDistribution (emdScaledError root bhat R c V β) atTop Z (fun _ => μ) ν :=
  emdBeta_tendstoInDistribution_gaussian root bhat R c V β T Z hlin hrem
    (emdScaledError_aemeasurable root bhat R c V β hbhat_meas)

/-- Efficient-MD distribution with the fixed-linear Gaussian limit and scaled-error measurability
discharged, stated first with the generic MD covariance at weight `V⁻¹`. -/
theorem emdBeta_tendstoInDistribution_multivariateGaussian_mdCov
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ)
    (R : Matrix k q ℝ) (c : q → ℝ) (V : Matrix k k ℝ) (β : k → ℝ)
    (S : Matrix k k ℝ) (T : ℕ → Ω → k → ℝ)
    (hS : S.PosSemidef)
    (hbhat_meas : ∀ n, AEStronglyMeasurable (bhat n) μ)
    (hT : TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 S))
    (hrem : TendstoInMeasure μ
      (emdScaledError root bhat R c V β - fun n ω => mdLinearMap V⁻¹ R *ᵥ T n ω)
      atTop (fun _ => 0)) :
    TendstoInDistribution (emdScaledError root bhat R c V β) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (mdAsymptoticVariance V⁻¹ R S)) := by
  have hlin :=
    fixedMatrix_mulVec_tendstoInDistribution_multivariateGaussian
      (M := mdLinearMap V⁻¹ R) (S := S) hS T hT
  exact emdBeta_tendstoInDistribution_gaussian_of_measurable
    root bhat R c V β T (fun z : EuclideanSpace ℝ k => z.ofLp)
    hbhat_meas (by simpa [mdAsymptoticVariance] using hlin) hrem

/-- Efficient-MD distribution with the fixed efficient weight and no separate remainder input,
stated first with the generic MD covariance at weight `V⁻¹`. -/
theorem emdBeta_fixedWeight_tendstoInDistribution_multivariateGaussian_mdCov
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ)
    (R : Matrix k q ℝ) (c : q → ℝ) (V : Matrix k k ℝ) (β : k → ℝ)
    (S : Matrix k k ℝ)
    (hS : S.PosSemidef)
    (hbhat_meas : ∀ n, AEStronglyMeasurable (bhat n) μ)
    (hrestrict : Rᵀ *ᵥ β = c)
    (hT : TendstoInDistribution (fun n ω => root n • (bhat n ω - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ) (multivariateGaussian 0 S)) :
    TendstoInDistribution (emdScaledError root bhat R c V β) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (mdAsymptoticVariance V⁻¹ R S)) := by
  simpa [emdScaledError, emdBetaStar, mdScaledError] using
    mdBeta_fixedWeight_tendstoInDistribution_multivariateGaussian
      root bhat V⁻¹ R c β S hS hbhat_meas hrestrict hT

/-- The MD linear map with efficient weight `V⁻¹` has the closed efficient form. -/
theorem mdLinearMap_efficientWeight_eq
    (R : Matrix k q ℝ) (V : Matrix k k ℝ) (hV : IsUnit V.det) :
    mdLinearMap V⁻¹ R = 1 - V * R * (Rᵀ * V * R)⁻¹ * Rᵀ := by
  unfold mdLinearMap
  rw [Matrix.nonsing_inv_nonsing_inv V hV]

/-- Hansen Theorem 8.9: the MD asymptotic variance at the efficient weight `V⁻¹`
equals the efficient-MD asymptotic variance. -/
theorem mdAsymptoticVariance_efficientWeight_eq_emd
    (R : Matrix k q ℝ) (V : Matrix k k ℝ)
    (hVunit : IsUnit V.det) (hVsym : Vᵀ = V) (hGunit : IsUnit (Rᵀ * V * R).det) :
    mdAsymptoticVariance V⁻¹ R V = emdAsymptoticVariance R V := by
  unfold mdAsymptoticVariance emdAsymptoticVariance
  rw [mdLinearMap_efficientWeight_eq R V hVunit]
  rw [Matrix.transpose_sub, Matrix.transpose_one]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    hVsym, Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  rw [hVsym]
  simp only [Matrix.mul_assoc]
  let C : Matrix q q ℝ := (Rᵀ * (V * R))⁻¹
  have hC : C * (Rᵀ * (V * R)) = 1 := by
    dsimp [C]
    exact Matrix.nonsing_inv_mul _ (by simpa [Matrix.mul_assoc] using hGunit)
  have hcollapse :
      V * (R * (C * Rᵀ)) * (V * (R * (C * (Rᵀ * V)))) =
        V * (R * (C * (Rᵀ * V))) := by
    calc
      V * (R * (C * Rᵀ)) * (V * (R * (C * (Rᵀ * V)))) =
          V * R * (C * (Rᵀ * (V * R))) * (C * (Rᵀ * V)) := by
        simp [Matrix.mul_assoc]
      _ = V * R * (C * (Rᵀ * V)) := by
        rw [hC]
        simp
      _ = V * (R * (C * (Rᵀ * V))) := by
        simp [Matrix.mul_assoc]
  change (1 - V * (R * (C * Rᵀ))) * (V * (1 - R * (C * (Rᵀ * V)))) =
    V - V * (R * (C * (Rᵀ * V)))
  calc
    (1 - V * (R * (C * Rᵀ))) * (V * (1 - R * (C * (Rᵀ * V)))) =
        V - V * (R * (C * (Rᵀ * V))) - V * (R * (C * (Rᵀ * V))) +
          V * (R * (C * Rᵀ)) * (V * (R * (C * (Rᵀ * V)))) := by
      simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      abel
    _ = V - V * (R * (C * (Rᵀ * V))) := by
      rw [hcollapse]
      abel

/-- Hansen Theorem 8.9 efficient-MD distribution with the final covariance written as
`emdAsymptoticVariance`. The remaining statistical input is the EMD linearization remainder. -/
theorem emdBeta_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ)
    (R : Matrix k q ℝ) (c : q → ℝ) (V : Matrix k k ℝ) (β : k → ℝ)
    (T : ℕ → Ω → k → ℝ)
    (hVpsd : V.PosSemidef) (hVunit : IsUnit V.det) (hVsym : Vᵀ = V)
    (hGunit : IsUnit (Rᵀ * V * R).det)
    (hbhat_meas : ∀ n, AEStronglyMeasurable (bhat n) μ)
    (hT : TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 V))
    (hrem : TendstoInMeasure μ
      (emdScaledError root bhat R c V β - fun n ω => mdLinearMap V⁻¹ R *ᵥ T n ω)
      atTop (fun _ => 0)) :
    TendstoInDistribution (emdScaledError root bhat R c V β) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (emdAsymptoticVariance R V)) := by
  have hraw := emdBeta_tendstoInDistribution_multivariateGaussian_mdCov
    root bhat R c V β V T hVpsd hbhat_meas hT hrem
  simpa [mdAsymptoticVariance_efficientWeight_eq_emd R V hVunit hVsym hGunit] using hraw

/-- Hansen Theorem 8.9 efficient-MD distribution with the fixed efficient weight and no separate
remainder input. -/
theorem emdBeta_fixedWeight_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ)
    (R : Matrix k q ℝ) (c : q → ℝ) (V : Matrix k k ℝ) (β : k → ℝ)
    (hVpsd : V.PosSemidef) (hVunit : IsUnit V.det) (hVsym : Vᵀ = V)
    (hGunit : IsUnit (Rᵀ * V * R).det)
    (hbhat_meas : ∀ n, AEStronglyMeasurable (bhat n) μ)
    (hrestrict : Rᵀ *ᵥ β = c)
    (hT : TendstoInDistribution (fun n ω => root n • (bhat n ω - β))
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ) (multivariateGaussian 0 V)) :
    TendstoInDistribution (emdScaledError root bhat R c V β) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (emdAsymptoticVariance R V)) := by
  have hraw := emdBeta_fixedWeight_tendstoInDistribution_multivariateGaussian_mdCov
    root bhat R c V β V hVpsd hbhat_meas hrestrict hT
  simpa [mdAsymptoticVariance_efficientWeight_eq_emd R V hVunit hVsym hGunit] using hraw

/-- The efficient weight is exactly variance-minimizing relative to itself. This is the zero-gap
specialization of the MD-efficiency comparison in Theorem 8.9. -/
theorem emdAsymptoticVariance_le_md_efficientWeight
    (R : Matrix k q ℝ) (V : Matrix k k ℝ)
    (hVunit : IsUnit V.det) (hVsym : Vᵀ = V) (hGunit : IsUnit (Rᵀ * V * R).det) :
    (mdAsymptoticVariance V⁻¹ R V - emdAsymptoticVariance R V).PosSemidef := by
  rw [mdAsymptoticVariance_efficientWeight_eq_emd R V hVunit hVsym hGunit]
  simpa using (Matrix.PosSemidef.zero : (0 : Matrix k k ℝ).PosSemidef)

/-- Hansen Theorem 8.9, equation (8.28): concrete factorization of the arbitrary-weight
minimum-distance variance gap relative to the efficient-MD variance. -/
theorem mdAsymptoticVariance_sub_emd_factor
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (V : Matrix k k ℝ)
    (hWsym : Wᵀ = W) (hVsym : Vᵀ = V) (hGVunit : IsUnit (Rᵀ * V * R).det) :
    mdAsymptoticVariance W R V - emdAsymptoticVariance R V =
      (W⁻¹ * R * (Rᵀ * W⁻¹ * R)⁻¹ - V * R * (Rᵀ * V * R)⁻¹) *
        (Rᵀ * V * R) *
          (W⁻¹ * R * (Rᵀ * W⁻¹ * R)⁻¹ - V * R * (Rᵀ * V * R)⁻¹)ᵀ := by
  let Winv : Matrix k k ℝ := W⁻¹
  let A : Matrix q q ℝ := (Rᵀ * Winv * R)⁻¹
  let B : Matrix q q ℝ := (Rᵀ * V * R)⁻¹
  have hWinvSym : Winvᵀ = Winv := by
    dsimp [Winv]
    rw [Matrix.transpose_nonsing_inv, hWsym]
  have hGramWsym : (Rᵀ * Winv * R)ᵀ = Rᵀ * Winv * R := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hWinvSym, Matrix.transpose_transpose]
    simp [Matrix.mul_assoc]
  have hGramVsym : (Rᵀ * V * R)ᵀ = Rᵀ * V * R := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hVsym, Matrix.transpose_transpose]
    simp [Matrix.mul_assoc]
  have hAsym : Aᵀ = A := by
    dsimp [A]
    rw [Matrix.transpose_nonsing_inv, hGramWsym]
  have hBsym : Bᵀ = B := by
    dsimp [B]
    rw [Matrix.transpose_nonsing_inv, hGramVsym]
  have hGB : (Rᵀ * V * R) * B = 1 := by
    dsimp [B]
    exact Matrix.mul_nonsing_inv _ hGVunit
  have hBG : B * (Rᵀ * V * R) = 1 := by
    dsimp [B]
    exact Matrix.nonsing_inv_mul _ hGVunit
  have hBG' : B * (Rᵀ * (V * R)) = 1 := by
    simpa [Matrix.mul_assoc] using hBG
  have hGB_aux : Rᵀ * (V * (R * (B * (Rᵀ * V)))) = Rᵀ * V := by
    calc
      Rᵀ * (V * (R * (B * (Rᵀ * V)))) = (Rᵀ * V * R * B) * (Rᵀ * V) := by
        simp [Matrix.mul_assoc]
      _ = Rᵀ * V := by
        rw [hGB]
        simp
  unfold mdAsymptoticVariance mdLinearMap emdAsymptoticVariance
  change (1 - Winv * R * A * Rᵀ) * V * (1 - Winv * R * A * Rᵀ)ᵀ -
      (V - V * R * B * Rᵀ * V) =
    (Winv * R * A - V * R * B) * (Rᵀ * V * R) * (Winv * R * A - V * R * B)ᵀ
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_one,
    Matrix.transpose_transpose, hAsym, hBsym, hWinvSym, hVsym]
  simp only [sub_eq_add_neg]
  simp only [Matrix.add_mul, Matrix.neg_mul, Matrix.mul_add, Matrix.mul_neg]
  simp only [Matrix.mul_assoc, hBG', Matrix.one_mul, Matrix.mul_one, neg_add_rev]
  rw [hGB_aux]
  abel_nf

/-- Hansen Theorem 8.9, equation (8.28): efficient MD weakly lowers asymptotic variance
relative to any symmetric minimum-distance weight at this abstraction layer. -/
theorem emdAsymptoticVariance_le_md_concrete
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (V : Matrix k k ℝ)
    (hWsym : Wᵀ = W) (hVsym : Vᵀ = V)
    (hGVunit : IsUnit (Rᵀ * V * R).det) (hGVpsd : (Rᵀ * V * R).PosSemidef) :
    (mdAsymptoticVariance W R V - emdAsymptoticVariance R V).PosSemidef := by
  rw [mdAsymptoticVariance_sub_emd_factor W R V hWsym hVsym hGVunit]
  simpa [Matrix.conjTranspose] using Matrix.PosSemidef.mul_mul_conjTranspose_same hGVpsd
    (W⁻¹ * R * (Rᵀ * W⁻¹ * R)⁻¹ - V * R * (Rᵀ * V * R)⁻¹)

omit [DecidableEq k] in
/-- Deterministic PSD factorization of the efficient-MD variance gap against the unrestricted
variance, under symmetry of `V` and PSD of the inverse restriction covariance. -/
theorem emdAsymptoticVariance_gap_posSemidef
    (R : Matrix k q ℝ) (V : Matrix k k ℝ)
    (hVsym : Vᵀ = V) (hG : ((Rᵀ * V * R)⁻¹).PosSemidef) :
    (V - emdAsymptoticVariance R V).PosSemidef := by
  have hgap : V - emdAsymptoticVariance R V =
      (Rᵀ * V)ᵀ * (Rᵀ * V * R)⁻¹ * (Rᵀ * V) := by
    unfold emdAsymptoticVariance
    calc
      V - (V - V * R * (Rᵀ * V * R)⁻¹ * Rᵀ * V) =
          V * R * (Rᵀ * V * R)⁻¹ * Rᵀ * V := by
        abel
      _ = (Rᵀ * V)ᵀ * (Rᵀ * V * R)⁻¹ * (Rᵀ * V) := by
        rw [Matrix.transpose_mul, hVsym, Matrix.transpose_transpose]
        simp [Matrix.mul_assoc]
  rw [hgap]
  simpa [Matrix.conjTranspose] using
    Matrix.PosSemidef.conjTranspose_mul_mul_same hG (Rᵀ * V)

omit [DecidableEq k] in
/-- Under Assumption 8.3 and a positive-definite unrestricted covariance, the efficient
nonlinear restricted asymptotic variance is weakly below the unrestricted variance. -/
theorem nonlinearEfficientAsymptoticVariance_gap_posSemidef_of_assumption83
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {Rderiv : Matrix k q ℝ}
    (h83 : NonlinearConstraintAssumption83 r β Rderiv)
    (V : Matrix k k ℝ) (hV : V.PosDef) (hVsym : Vᵀ = V) :
    (V - emdAsymptoticVariance Rderiv V).PosSemidef :=
  emdAsymptoticVariance_gap_posSemidef Rderiv V hVsym
    (h83.efficientRestrictionCov_inv_posSemidef V hV)

/-- Under Assumption 8.3, efficient nonlinear minimum distance weakly lowers asymptotic variance
relative to a symmetric arbitrary-weight nonlinear minimum-distance estimator. -/
theorem nonlinearEfficientAsymptoticVariance_le_md_concrete_of_assumption83
    {r : (k → ℝ) → (q → ℝ)} {β : k → ℝ} {Rderiv : Matrix k q ℝ}
    (h83 : NonlinearConstraintAssumption83 r β Rderiv)
    (W V : Matrix k k ℝ)
    (hWsym : Wᵀ = W) (hV : V.PosDef) (hVsym : Vᵀ = V) :
    (mdAsymptoticVariance W Rderiv V - emdAsymptoticVariance Rderiv V).PosSemidef :=
  emdAsymptoticVariance_le_md_concrete W Rderiv V hWsym hVsym
    (h83.efficientRestrictionCov_det_isUnit V hV)
    (h83.efficientRestrictionCov_posDef V hV).posSemidef

omit [DecidableEq k] in
/-- Efficient MD cannot increase asymptotic variance relative to the unrestricted estimator,
from an explicit PSD factorization of the variance gap. -/
theorem emdAsymptoticVariance_le_unrestricted
    (R : Matrix k q ℝ) (V : Matrix k k ℝ) (F M : Matrix k k ℝ)
    (hfactor : V - emdAsymptoticVariance R V = Fᵀ * M * F) (hM : M.PosSemidef) :
    (V - emdAsymptoticVariance R V).PosSemidef := by
  rw [hfactor]
  simpa [Matrix.conjTranspose] using Matrix.PosSemidef.conjTranspose_mul_mul_same hM F

/-- Factorization-based MD-efficiency wrapper for Theorem 8.9. -/
theorem emdAsymptoticVariance_le_md
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (V : Matrix k k ℝ) (F M : Matrix k k ℝ)
    (hfactor : mdAsymptoticVariance W R V - emdAsymptoticVariance R V = Fᵀ * M * F)
    (hM : M.PosSemidef) :
    (mdAsymptoticVariance W R V - emdAsymptoticVariance R V).PosSemidef := by
  rw [hfactor]
  simpa [Matrix.conjTranspose] using Matrix.PosSemidef.conjTranspose_mul_mul_same hM F

/-- Slutsky transfer after a nonlinear-constraint linearization.

`Rderiv` is the derivative matrix supplied by a separate Delta-method argument; this helper only
transfers from the linearized statistic plus an `oₚ(1)` remainder. -/
theorem linearizedConstraint_tendstoInDistribution_of_remainder
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Y : ℕ → Ω → k → ℝ) (Rderiv : Matrix k q ℝ) (W : Matrix k k ℝ)
    (T : ℕ → Ω → k → ℝ) (Z : Ω' → k → ℝ)
    (hlin : TendstoInDistribution (fun n ω => mdLinearMap W Rderiv *ᵥ T n ω)
      atTop Z (fun _ => μ) ν)
    (hrem : TendstoInMeasure μ
      (Y - fun n ω => mdLinearMap W Rderiv *ᵥ T n ω) atTop (fun _ => 0))
    (hmeas : ∀ n, AEMeasurable (Y n) μ) :
    TendstoInDistribution Y atTop Z (fun _ => μ) ν :=
  tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n ω => mdLinearMap W Rderiv *ᵥ T n ω) (Y := Y) (Z := Z)
    hlin hrem hmeas

/-- Hansen Theorem 8.10, interface-level nonlinear constrained-estimator limit.

The estimator-specific work is isolated in `ConstrainedEstimatorLinearization`: consistency of the
constrained optimizer, differentiability of the restriction map, and first-order conditions should
be used to construct that interface. This theorem performs the stable Slutsky step from the
linearized representation to the asymptotic distribution. -/
theorem nonlinearConstrainedEstimator_tendstoInDistribution_gaussian
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (root : ℕ → ℝ) (btilde : ℕ → Ω → k → ℝ) (β : k → ℝ)
    (W : Matrix k k ℝ) (Rderiv : Matrix k q ℝ)
    (T : ℕ → Ω → k → ℝ) (Z : Ω' → k → ℝ)
    (hlin : TendstoInDistribution (fun n ω => mdLinearMap W Rderiv *ᵥ T n ω)
      atTop Z (fun _ => μ) ν)
    (hlinear : ConstrainedEstimatorLinearization μ root btilde β W Rderiv T) :
    TendstoInDistribution (constrainedScaledError root btilde β) atTop Z (fun _ => μ) ν :=
  linearizedConstraint_tendstoInDistribution_of_remainder
    (Y := constrainedScaledError root btilde β) (Rderiv := Rderiv) (W := W)
    (T := T) (Z := Z) hlin hlinear.expansion hlinear.scaled_measurable

/-- Hansen Theorem 8.10, interface-level nonlinear constrained-estimator Gaussian limit.

This theorem derives the fixed-linear Gaussian image from the unrestricted estimator CLT, so the
public nonlinear wrapper consumes the stable linearization interface rather than a pre-composed
distributional-limit conclusion. -/
theorem nonlinearConstrainedEstimator_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (root : ℕ → ℝ) (btilde : ℕ → Ω → k → ℝ) (β : k → ℝ)
    (W : Matrix k k ℝ) (Rderiv : Matrix k q ℝ)
    (T : ℕ → Ω → k → ℝ) (S : Matrix k k ℝ)
    (hS : S.PosSemidef)
    (hT : TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 S))
    (hlinear : ConstrainedEstimatorLinearization μ root btilde β W Rderiv T) :
    TendstoInDistribution (constrainedScaledError root btilde β) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (mdAsymptoticVariance W Rderiv S)) := by
  have hlin := fixedMatrix_mulVec_tendstoInDistribution_multivariateGaussian
    (M := mdLinearMap W Rderiv) (S := S) hS T hT
  exact nonlinearConstrainedEstimator_tendstoInDistribution_gaussian
    root btilde β W Rderiv T (fun z : EuclideanSpace ℝ k => z.ofLp)
    (by simpa [mdAsymptoticVariance] using hlin) hlinear

/-- Hansen Theorem 8.10 for nonlinear minimum distance at the stable-interface layer. -/
theorem nonlinearMdBeta_tendstoInDistribution_gaussian
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (root : ℕ → ℝ) (btilde : ℕ → Ω → k → ℝ) (β : k → ℝ)
    (W : Matrix k k ℝ) (Rderiv : Matrix k q ℝ)
    (T : ℕ → Ω → k → ℝ) (Z : Ω' → k → ℝ)
    (hlin : TendstoInDistribution (fun n ω => mdLinearMap W Rderiv *ᵥ T n ω)
      atTop Z (fun _ => μ) ν)
    (hlinear : ConstrainedEstimatorLinearization μ root btilde β W Rderiv T) :
    TendstoInDistribution (constrainedScaledError root btilde β) atTop Z (fun _ => μ) ν :=
  nonlinearConstrainedEstimator_tendstoInDistribution_gaussian
    root btilde β W Rderiv T Z hlin hlinear

/-- Hansen Theorem 8.10 for nonlinear minimum distance with the Gaussian image limit
derived from the unrestricted estimator CLT. -/
theorem nonlinearMdBeta_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (root : ℕ → ℝ) (btilde : ℕ → Ω → k → ℝ) (β : k → ℝ)
    (W : Matrix k k ℝ) (Rderiv : Matrix k q ℝ)
    (T : ℕ → Ω → k → ℝ) (S : Matrix k k ℝ)
    (hS : S.PosSemidef)
    (hT : TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 S))
    (hlinear : ConstrainedEstimatorLinearization μ root btilde β W Rderiv T) :
    TendstoInDistribution (constrainedScaledError root btilde β) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (mdAsymptoticVariance W Rderiv S)) :=
  nonlinearConstrainedEstimator_tendstoInDistribution_multivariateGaussian
    root btilde β W Rderiv T S hS hT hlinear

/-- Hansen Theorem 8.10 for nonlinear constrained least squares at the stable-interface layer.

The CLS specialization uses the population Gram weight in the linearized MD map, matching the linear
restriction specialization in Theorem 8.8. -/
theorem nonlinearClsBeta_tendstoInDistribution_gaussian
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (root : ℕ → ℝ) (btilde : ℕ → Ω → k → ℝ) (β : k → ℝ)
    (Q : Matrix k k ℝ) (Rderiv : Matrix k q ℝ)
    (T : ℕ → Ω → k → ℝ) (Z : Ω' → k → ℝ)
    (hlin : TendstoInDistribution (fun n ω => mdLinearMap Q Rderiv *ᵥ T n ω)
      atTop Z (fun _ => μ) ν)
    (hlinear : ConstrainedEstimatorLinearization μ root btilde β Q Rderiv T) :
    TendstoInDistribution (constrainedScaledError root btilde β) atTop Z (fun _ => μ) ν :=
  nonlinearConstrainedEstimator_tendstoInDistribution_gaussian
    root btilde β Q Rderiv T Z hlin hlinear

/-- Hansen Theorem 8.10 for nonlinear constrained least squares with the Gaussian image limit
derived from the unrestricted estimator CLT. -/
theorem nonlinearClsBeta_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (root : ℕ → ℝ) (btilde : ℕ → Ω → k → ℝ) (β : k → ℝ)
    (Q : Matrix k k ℝ) (Rderiv : Matrix k q ℝ)
    (T : ℕ → Ω → k → ℝ) (S : Matrix k k ℝ)
    (hS : S.PosSemidef)
    (hT : TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 S))
    (hlinear : ConstrainedEstimatorLinearization μ root btilde β Q Rderiv T) :
    TendstoInDistribution (constrainedScaledError root btilde β) atTop
      (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (clsAsymptoticVariance Q Rderiv S)) := by
  simpa [clsAsymptoticVariance] using
    nonlinearConstrainedEstimator_tendstoInDistribution_multivariateGaussian
      root btilde β Q Rderiv T S hS hT hlinear

/-- Hansen Theorem 8.10 for nonlinear minimum distance specialized to the Chapter 7
totalized-OLS CLT. The nonlinear optimizer analysis is isolated in
`ConstrainedEstimatorLinearization`, matching Assumption 8.3's role. -/
theorem nonlinearMdBeta_olsBetaStar_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (btilde : ℕ → Ω → k → ℝ) (W : Matrix k k ℝ) (Rderiv : Matrix k q ℝ)
    (hlinear : ConstrainedEstimatorLinearization μ (fun n => Real.sqrt (n : ℝ))
      btilde β W Rderiv
      (fun n ω => Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) :
    TendstoInDistribution
      (constrainedScaledError (fun n => Real.sqrt (n : ℝ)) btilde β)
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (mdAsymptoticVariance W Rderiv (heteroAsymCov μ X e))) := by
  exact nonlinearMdBeta_tendstoInDistribution_multivariateGaussian
    (fun n => Real.sqrt (n : ℝ)) btilde β W Rderiv
    (fun n ω => Real.sqrt (n : ℝ) •
      (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
    (heteroAsymCov μ X e) (heteroAsymCov_posSemidef h)
    (olsBetaStar_vector_tendstoInDistribution_heteroAsymCov h β hmodel)
    hlinear

/-- Hansen Theorem 8.10 for nonlinear constrained least squares specialized to the
Chapter 7 totalized-OLS CLT. -/
theorem nonlinearClsBeta_olsBetaStar_tendstoInDistribution_multivariateGaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    (h : ScoreCLTConditions μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (btilde : ℕ → Ω → k → ℝ) (Q : Matrix k k ℝ) (Rderiv : Matrix k q ℝ)
    (hlinear : ConstrainedEstimatorLinearization μ (fun n => Real.sqrt (n : ℝ))
      btilde β Q Rderiv
      (fun n ω => Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) :
    TendstoInDistribution
      (constrainedScaledError (fun n => Real.sqrt (n : ℝ)) btilde β)
      atTop (fun z : EuclideanSpace ℝ k => z.ofLp) (fun _ => μ)
      (multivariateGaussian 0 (clsAsymptoticVariance Q Rderiv (heteroAsymCov μ X e))) := by
  exact nonlinearClsBeta_tendstoInDistribution_multivariateGaussian
    (fun n => Real.sqrt (n : ℝ)) btilde β Q Rderiv
    (fun n ω => Real.sqrt (n : ℝ) •
      (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
    (heteroAsymCov μ X e) (heteroAsymCov_posSemidef h)
    (olsBetaStar_vector_tendstoInDistribution_heteroAsymCov h β hmodel)
    hlinear

end HansenEconometrics
