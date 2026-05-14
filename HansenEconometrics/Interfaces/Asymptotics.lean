import HansenEconometrics.LinearAlgebraUtils
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Stable Asymptotic Interfaces

This module defines theorem-facing interfaces for asymptotic econometrics.
They record reusable capabilities such as Gram convergence, score CLTs,
asymptotic linearity, and covariance-estimator consistency. Concrete iid,
moment, and HC assumptions should construct these interfaces; public theorem
wrappers should consume them.
-/

open scoped Matrix Real Topology MeasureTheory ProbabilityTheory Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Matrix

namespace HansenEconometrics

variable {Ω Ω' k q : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace Ω']
variable [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
variable {μ : Measure Ω}

omit [DecidableEq k] [DecidableEq q] in
@[reducible]
private noncomputable def matrixBorelMeasurableSpaceInst
    (m n : Type*) [Fintype m] [Fintype n] :
    MeasurableSpace (Matrix m n ℝ) :=
  matrixBorelMeasurableSpace m n

attribute [local instance] matrixBorelMeasurableSpaceInst

omit [DecidableEq k] [DecidableEq q] in
private lemma matrixBorelSpaceInst
    (m n : Type*) [Fintype m] [Fintype n] :
    @BorelSpace (Matrix m n ℝ) inferInstance (matrixBorelMeasurableSpaceInst m n) :=
  matrixBorelSpace m n

attribute [local instance] matrixBorelSpaceInst

/-- Stable interface for convergence of a sample Gram matrix to a nonsingular target. -/
structure GramConsistency
    (μ : Measure Ω) (Qhat : ℕ → Ω → Matrix k k ℝ) (Q : Matrix k k ℝ) where
  gram_measurable : ∀ n, AEStronglyMeasurable (Qhat n) μ
  gram_tendsto : TendstoInMeasure μ Qhat atTop (fun _ => Q)
  gram_nonsing : IsUnit Q.det

/-- Stable interface for a normalized score CLT. -/
structure ScoreCLT
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (score : ℕ → Ω → k → ℝ)
    (Z : Ω' → k → ℝ) (ν : Measure Ω') [IsProbabilityMeasure ν] where
  score_tendsto : TendstoInDistribution score atTop Z (fun _ => μ) ν

/-- Stable interface for an estimator admitting a linear score expansion. -/
structure AsymptoticallyLinearEstimator
    (μ : Measure Ω)
    (bhat : ℕ → Ω → k → ℝ) (β : k → ℝ) (root : ℕ → ℝ)
    (score : ℕ → Ω → k → ℝ) (A : Matrix k k ℝ) where
  estimator_measurable : ∀ n, AEStronglyMeasurable (bhat n) μ
  expansion :
    TendstoInMeasure μ
      (fun n ω => root n • (bhat n ω - β) - A *ᵥ score n ω)
      atTop (fun _ => 0)

/-- Stable interface for convergence of a covariance estimator. -/
structure CovarianceEstimatorConsistent
    (μ : Measure Ω) (Vhat : ℕ → Ω → Matrix q q ℝ) (V : Matrix q q ℝ) where
  covariance_measurable : ∀ n, AEStronglyMeasurable (Vhat n) μ
  covariance_tendsto : TendstoInMeasure μ Vhat atTop (fun _ => V)

/-- Positivity/invertibility data for a covariance limit. -/
structure PositiveCovarianceLimit (V : Matrix q q ℝ) where
  posDef : Matrix.PosDef V

namespace PositiveCovarianceLimit

/-- A positive-definite covariance limit is nonsingular. -/
theorem nonsing {V : Matrix q q ℝ} (h : PositiveCovarianceLimit V) :
    IsUnit V.det :=
  V.isUnit_iff_isUnit_det.mp h.posDef.isUnit

end PositiveCovarianceLimit

/-- Stable interface for a feasible scalar standard error. -/
structure FeasibleStandardErrorConsistent
    (μ : Measure Ω) (se : ℕ → Ω → ℝ) (c : ℝ) where
  se_measurable : ∀ n, AEMeasurable (se n) μ
  se_tendsto : TendstoInMeasure μ se atTop (fun _ => c)
  limit_pos : 0 < c

end HansenEconometrics
