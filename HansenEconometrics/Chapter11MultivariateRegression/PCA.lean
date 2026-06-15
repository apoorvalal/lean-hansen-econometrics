import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Chapter 11 — principal components

Principal components are exposed through the covariance quadratic form. The
current file supplies reusable PCA notation plus algebraic bridge lemmas; the
spectral existence theorem behind Hansen Theorem 11.8 remains a separate gap in
the chapter inventory.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {Ω k : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable [Fintype k] [DecidableEq k]

/-- Linear principal-component score `h'X`. -/
noncomputable def principalComponent
    (h : k → ℝ) (X : Ω → k → ℝ) : Ω → ℝ :=
  fun ω => h ⬝ᵥ X ω

/-- Covariance quadratic form maximized by a principal component. -/
noncomputable def principalComponentVariance
    (Sigma : Matrix k k ℝ) (h : k → ℝ) : ℝ :=
  h ⬝ᵥ (Sigma *ᵥ h)

/-- A vector satisfying the principal-component first-order and optimality conditions. -/
structure PrincipalComponentSolution
    (Sigma : Matrix k k ℝ) (h : k → ℝ) (lambda : ℝ) : Prop where
  unit_norm : h ⬝ᵥ h = 1
  eigenvector : Sigma *ᵥ h = lambda • h
  maximizes_variance :
    ∀ g : k → ℝ, g ⬝ᵥ g = 1 →
      principalComponentVariance Sigma g ≤ principalComponentVariance Sigma h

omit [DecidableEq k] in
/-- Eigenvector component of a supplied `PrincipalComponentSolution`. -/
theorem principalComponent_eigenvector_of_solution
    (Sigma : Matrix k k ℝ) (h : k → ℝ) (lambda : ℝ)
    (hh : PrincipalComponentSolution Sigma h lambda) :
    Sigma *ᵥ h = lambda • h :=
  hh.eigenvector

omit [DecidableEq k] in
/-- A principal component's variance is the eigenvalue attached to a unit eigenvector. -/
theorem principalComponentVariance_eq_eigenvalue
    (Sigma : Matrix k k ℝ) (h : k → ℝ) (lambda : ℝ)
    (hunit : h ⬝ᵥ h = 1) (heig : Sigma *ᵥ h = lambda • h) :
    principalComponentVariance Sigma h = lambda := by
  rw [principalComponentVariance, heig]
  simp [dotProduct_smul, hunit]

end HansenEconometrics
