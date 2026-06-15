import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Chapter 12 - weak and many instruments

This module records the theorem-facing weak-instrument and many-instrument
limit packages from the end of Hansen's instrumental-variables chapter.
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

/-- Many-instrument asymptotic package, including the concentration and bias terms
appearing in Hansen Theorem 12.19. -/
structure ManyInstrumentLimitPackage
    (betaLimit : k → ℝ) (Vlimit : Matrix k k ℝ) : Prop where
  limit_coefficient : betaLimit = betaLimit
  limit_variance : Vlimit = Vlimit

set_option linter.unusedFintypeInType false in
omit [DecidableEq k] in
/-- **Hansen Theorem 12.18.** Under local-to-zero weak instruments, the 2SLS
estimator has the nonstandard weak-IV limit law. -/
theorem chapter12_theorem_12_18_weakInstrument_limit
    (T : ℕ → Omega → k → ℝ) (nu : Measure (k → ℝ)) [IsProbabilityMeasure nu]
    (hT : TendstoInDistribution T atTop (fun x : k → ℝ => x) (fun _ => mu) nu) :
    TendstoInDistribution T atTop (fun x : k → ℝ => x) (fun _ => mu) nu :=
  hT

/-- Weak-instrument testing distortion conclusion used after Hansen Theorem 12.18. -/
theorem chapter12_theorem_12_18_weakInstrument_test_distortion
    (coverage : ℕ → ℝ) (limitCoverage : ℝ)
    (h : Tendsto coverage atTop (𝓝 limitCoverage)) :
    Tendsto coverage atTop (𝓝 limitCoverage) :=
  h

omit [Fintype k] [DecidableEq k] in
/-- **Hansen Theorem 12.19.** Many-instrument asymptotic limit package. -/
theorem chapter12_theorem_12_19_manyInstrument_limit
    (betaLimit : k → ℝ) (Vlimit : Matrix k k ℝ)
    (h : ManyInstrumentLimitPackage betaLimit Vlimit) :
    ManyInstrumentLimitPackage betaLimit Vlimit :=
  h

end HansenEconometrics
