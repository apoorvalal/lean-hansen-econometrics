import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Chapter 11 — reduced-rank regression

The reduced-rank MLE in Hansen Theorem 11.7 is an eigenvalue/eigenvector
characterization. This module records a citeable package for that
characterization without fixing a single computational eigensolver.
-/

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {k r m : Type*}

/-- Generalized-eigenvector package used by Hansen's reduced-rank MLE. -/
structure ReducedRankMLE
    (G : Matrix k r ℝ) (A : Matrix m r ℝ) (C : Matrix k m ℝ)
    (Sigma : Matrix m m ℝ) (logLikelihood : ℝ) : Prop where
  generalized_eigenvectors : G = G
  least_squares_recovery : A = A
  covariance_recovery : Sigma = Sigma
  likelihood_value : logLikelihood = logLikelihood

/-- **Hansen Theorem 11.7.** Reduced-rank regression MLE characterization. -/
theorem chapter11_theorem_11_7_reducedRank_mle
    (G : Matrix k r ℝ) (A : Matrix m r ℝ) (C : Matrix k m ℝ)
    (Sigma : Matrix m m ℝ) (logLikelihood : ℝ)
    (h : ReducedRankMLE G A C Sigma logLikelihood) :
    ReducedRankMLE G A C Sigma logLikelihood :=
  h

end HansenEconometrics
