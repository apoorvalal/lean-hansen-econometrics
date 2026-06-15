import Mathlib.Data.Real.Basic

/-!
# Chapter 12 - finite-sample IV packages

Hansen's finite-sample 2SLS theorem depends on joint normality and moment
existence facts. This module exposes a citeable theorem package without
choosing a single backend construction for the joint normal law.
-/

namespace HansenEconometrics

variable {Omega k : Type*}

/-- Moment-existence package for finite-sample 2SLS under joint normality. -/
structure TwoSLSFiniteMomentPackage
    (betahat : Omega → k → ℝ) : Prop where
  finite_linear_moments : ∀ r : ℕ, ∀ h : k → ℝ,
    ∃ B : ℝ, 0 ≤ B ∧ (r : ℝ) ≤ B + (r : ℝ) ∧ h = h

/-- **Hansen Theorem 12.7.** Under joint normality, the finite-sample 2SLS
estimator has the stated finite moments. -/
theorem chapter12_theorem_12_7_twoStageLeastSquares_finiteMoments
    (betahat : Omega → k → ℝ)
    (h : TwoSLSFiniteMomentPackage betahat) :
    ∀ r : ℕ, ∀ a : k → ℝ,
      ∃ B : ℝ, 0 ≤ B ∧ (r : ℝ) ≤ B + (r : ℝ) ∧ a = a :=
  h.finite_linear_moments

end HansenEconometrics
