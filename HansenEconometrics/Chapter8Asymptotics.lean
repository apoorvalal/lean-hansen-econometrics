import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.Chapter7Asymptotics.Basic

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

/-- Star minimum-distance estimator using total nonsingular inverses. -/
noncomputable def mdBetaStar
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (c : q → ℝ) (bhat : k → ℝ) : k → ℝ :=
  bhat - (W⁻¹ * R * (Rᵀ * W⁻¹ * R)⁻¹) *ᵥ (Rᵀ *ᵥ bhat - c)

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

/-- Expanded form of the MD asymptotic variance definition. -/
theorem mdAsymptoticVariance_eq_expanded
    (W : Matrix k k ℝ) (R : Matrix k q ℝ) (V : Matrix k k ℝ) :
    mdAsymptoticVariance W R V = mdLinearMap W R * V * (mdLinearMap W R)ᵀ :=
  rfl

/-- CLS asymptotic variance is the MD variance with the population Gram weight. -/
noncomputable def clsAsymptoticVariance
    (Q : Matrix k k ℝ) (R : Matrix k q ℝ) (V : Matrix k k ℝ) : Matrix k k ℝ :=
  mdAsymptoticVariance Q R V

/-- Expanded CLS asymptotic variance. -/
theorem clsAsymptoticVariance_eq_expanded
    (Q : Matrix k k ℝ) (R : Matrix k q ℝ) (V : Matrix k k ℝ) :
    clsAsymptoticVariance Q R V = mdLinearMap Q R * V * (mdLinearMap Q R)ᵀ :=
  rfl

/-- Efficient MD asymptotic variance. -/
noncomputable def emdAsymptoticVariance
    (R : Matrix k q ℝ) (V : Matrix k k ℝ) : Matrix k k ℝ :=
  V - V * R * (Rᵀ * V * R)⁻¹ * Rᵀ * V

/-- Efficient MD estimator with the efficient weight. -/
noncomputable def emdBetaStar
    (R : Matrix k q ℝ) (c : q → ℝ) (V : Matrix k k ℝ) (bhat : k → ℝ) : k → ℝ :=
  mdBetaStar V⁻¹ R c bhat

/-- Scaled error for a generic constrained estimator. -/
noncomputable def constrainedScaledError
    {Ω : Type*} (root : ℕ → ℝ) (btilde : ℕ → Ω → k → ℝ) (β : k → ℝ) :
    ℕ → Ω → k → ℝ :=
  fun n ω => root n • (btilde n ω - β)

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

/-- MD scaled-error statistic. -/
noncomputable def mdScaledError
    {Ω : Type*} (root : ℕ → ℝ) (bhat : ℕ → Ω → k → ℝ) (What : ℕ → Ω → Matrix k k ℝ)
    (R : Matrix k q ℝ) (c : q → ℝ) (β : k → ℝ) : ℕ → Ω → k → ℝ :=
  fun n ω => root n • (mdBetaStar (What n ω) R c (bhat n ω) - β)

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

end HansenEconometrics
