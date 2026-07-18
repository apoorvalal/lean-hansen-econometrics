import Mathlib.Data.Matrix.Mul
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Chapter 12 - finite-sample IV packages

Hansen's finite-sample 2SLS theorem depends on joint normality and moment
existence facts. This module exposes a finite-linear-moment interface without
choosing a backend construction for the joint normal law.
-/

open MeasureTheory
open scoped Matrix

namespace HansenEconometrics

variable {Omega k : Type*}
variable [MeasurableSpace Omega] {mu : Measure Omega}
variable [Fintype k]

/-- File-local moment-existence interface used to isolate backend choices. -/
private structure TwoSLSFiniteMomentInterface
    (betahat : Omega → k → ℝ) : Prop where
  finite_linear_moments : ∀ r : ℕ, ∀ a : k → ℝ,
    Integrable (fun ω => (a ⬝ᵥ betahat ω) ^ r) mu

/-- File-local projection from the finite-moment interface. -/
private theorem twoStageLeastSquares_finiteMoments_from_interface
    (betahat : Omega → k → ℝ)
    (h : TwoSLSFiniteMomentInterface (mu := mu) betahat) :
    ∀ r : ℕ, ∀ a : k → ℝ, Integrable (fun ω => (a ⬝ᵥ betahat ω) ^ r) mu :=
  h.finite_linear_moments

end HansenEconometrics
