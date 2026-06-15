import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Chapter 12 - weak and many instruments

This module records support notation and interfaces for the weak-instrument and
many-instrument routes from the end of Hansen's instrumental-variables chapter.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

variable {Omega k l : Type*}
variable [MeasurableSpace Omega] {mu : Measure Omega} [IsProbabilityMeasure mu]
variable [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]

/-- Local-to-zero reduced-form sequence `Gamma_n = root_n^{-1} C`. -/
noncomputable def localToZeroReducedForm
    (root : ℝ) (C : Matrix l k ℝ) : Matrix l k ℝ :=
  root⁻¹ • C

/-- Many-instrument asymptotic interface, separating coefficient and variance
limit conclusions so future constructors must provide real proofs. -/
structure ManyInstrumentLimitInterface
    (coefficientLimit varianceLimit : Prop) : Prop where
  coefficient_limit : coefficientLimit
  variance_limit : varianceLimit

set_option linter.unusedFintypeInType false in
omit [DecidableEq k] in
/-- Interface projection for a weak-IV nonstandard limit law. -/
theorem weakInstrument_limit_from_interface
    (T : ℕ → Omega → k → ℝ) (nu : Measure (k → ℝ)) [IsProbabilityMeasure nu]
    (hT : TendstoInDistribution T atTop (fun x : k → ℝ => x) (fun _ => mu) nu) :
    TendstoInDistribution T atTop (fun x : k → ℝ => x) (fun _ => mu) nu :=
  hT

/-- Interface projection for a weak-instrument testing-distortion conclusion. -/
theorem weakInstrument_testDistortion_from_interface
    (coverage : ℕ → ℝ) (limitCoverage : ℝ)
    (h : Tendsto coverage atTop (𝓝 limitCoverage)) :
    Tendsto coverage atTop (𝓝 limitCoverage) :=
  h

/-- Interface projection for many-instrument coefficient and variance limits. -/
theorem manyInstrument_limits_from_interface
    {coefficientLimit varianceLimit : Prop}
    (h : ManyInstrumentLimitInterface coefficientLimit varianceLimit) :
    coefficientLimit ∧ varianceLimit :=
  ⟨h.coefficient_limit, h.variance_limit⟩

end HansenEconometrics
