import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Chapter 11 — reduced-rank regression

The reduced-rank MLE in Hansen Theorem 11.7 is an eigenvalue/eigenvector
characterization. This module records the certificate shape needed for that
route without claiming the full MLE theorem from normal-error assumptions.
-/

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {k r m : Type*}

/-- Certificate package used by Hansen's reduced-rank MLE route.

The proposition fields are supplied by a future generalized-eigenvalue
constructor; this package deliberately avoids vacuous self-equalities. -/
structure ReducedRankMLE
    (G : Matrix k r ℝ) (A : Matrix m r ℝ) (C : Matrix k m ℝ)
    (Sigma : Matrix m m ℝ) (logLikelihood : ℝ)
    (generalizedEigenvectors leastSquaresRecovery covarianceRecovery likelihoodValue : Prop) :
    Prop where
  generalized_eigenvectors : generalizedEigenvectors
  least_squares_recovery : leastSquaresRecovery
  covariance_recovery : covarianceRecovery
  likelihood_value : likelihoodValue

/-- Assemble a reduced-rank MLE certificate from its four mathematical components. -/
theorem reducedRankMLE_of_certificate
    (G : Matrix k r ℝ) (A : Matrix m r ℝ) (C : Matrix k m ℝ)
    (Sigma : Matrix m m ℝ) (logLikelihood : ℝ)
    {generalizedEigenvectors leastSquaresRecovery covarianceRecovery likelihoodValue : Prop}
    (hG : generalizedEigenvectors) (hA : leastSquaresRecovery)
    (hSigma : covarianceRecovery) (hLike : likelihoodValue) :
    ReducedRankMLE G A C Sigma logLikelihood generalizedEigenvectors leastSquaresRecovery
      covarianceRecovery likelihoodValue where
  generalized_eigenvectors := hG
  least_squares_recovery := hA
  covariance_recovery := hSigma
  likelihood_value := hLike

end HansenEconometrics
