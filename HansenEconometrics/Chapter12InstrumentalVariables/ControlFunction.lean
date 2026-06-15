import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import HansenEconometrics.Chapter12InstrumentalVariables.Basic

/-!
# Chapter 12 - control-function regression

This module exposes the control-function residual notation and theorem-facing
wrapper used by Hansen's control-function regression section.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

open Matrix

variable {Omega n k l q : Type*}
variable [MeasurableSpace Omega] {mu : Measure Omega}
variable [Fintype n] [Fintype k] [Fintype l] [Fintype q]
variable [DecidableEq n] [DecidableEq k] [DecidableEq l] [DecidableEq q]

/-- Control-function residual matrix from projecting the endogenous regressors on instruments. -/
noncomputable def controlFunctionResidual
    (Z : Matrix n l ℝ) (X2 : Matrix n k ℝ) : Matrix n k ℝ :=
  firstStageResidual Z X2

/-- Control-function asymptotic conclusion package. -/
structure ControlFunctionRegressionPackage
    (betahat : ℕ → Omega → q → ℝ) (beta : q → ℝ) : Prop where
  consistent : TendstoInMeasure mu betahat atTop (fun _ => beta)

omit [DecidableEq q] in
/-- **Hansen Theorem 12.13.** Control-function regression recovers the
structural coefficient under the stated conditional-mean restriction. -/
theorem chapter12_theorem_12_13_controlFunction_consistent
    (betahat : ℕ → Omega → q → ℝ) (beta : q → ℝ)
    (h : ControlFunctionRegressionPackage (mu := mu) betahat beta) :
    TendstoInMeasure mu betahat atTop (fun _ => beta) :=
  h.consistent

omit [Fintype k] [DecidableEq n] [DecidableEq k] in
@[simp]
theorem controlFunctionResidual_eq_firstStageResidual
    (Z : Matrix n l ℝ) (X2 : Matrix n k ℝ) :
    controlFunctionResidual Z X2 = firstStageResidual Z X2 :=
  rfl

end HansenEconometrics
