import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Mul
import HansenEconometrics.Chapter3FWL

/-!
# Chapter 11 — reduced-rank regression

The reduced-rank MLE in Hansen Theorem 11.7 is an eigenvalue/eigenvector
characterization. This module records a concrete generalized-eigenvector
predicate and the certificate shape needed for that route without claiming the
full likelihood optimizer from normal-error assumptions.
-/

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {k r m ell : Type*}

section GeneralizedEigenvectors

variable [Fintype k]

/-- Generalized eigenvector equation `A v = λ B v` for a matrix pencil `(A, B)`.

This is the concrete spectral predicate needed by Hansen Theorem 11.7 before the
full reduced-rank likelihood optimizer is assembled. -/
def generalizedEigenvector
    (A B : Matrix k k ℝ) (lambda : ℝ) (v : k → ℝ) : Prop :=
  v ≠ 0 ∧ A *ᵥ v = lambda • (B *ᵥ v)

/-- Columns of `G` solve the generalized eigenvector equations for a matrix
pencil `(A, B)`, with eigenvalues indexed by the reduced-rank coordinate. -/
def generalizedEigenvectorColumns
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ) : Prop :=
  ∀ j : r, generalizedEigenvector A B (lambda j) (fun i => G i j)

/-- Projection from the generalized-eigenvector column package. -/
theorem generalizedEigenvectorColumns_apply
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G) (j : r) :
    generalizedEigenvector A B (lambda j) (fun i => G i j) :=
  h j

end GeneralizedEigenvectors

section HansenPencil

variable {n : Type*}
variable [Fintype n] [DecidableEq n]
variable [Fintype k] [Fintype m] [Fintype ell]
variable [DecidableEq m] [DecidableEq ell]

/-- Residualized outcome matrix `Ỹ` from regressing `Y` on controls `Z`. -/
noncomputable def reducedRankTildeY
    (Z : Matrix n ell ℝ) (Y : Matrix n m ℝ)
    [Invertible (Zᵀ * Z)] : Matrix n m ℝ :=
  residualizedRegressors Z Y

/-- Residualized regressor matrix `X̃` from regressing `X` on controls `Z`. -/
noncomputable def reducedRankTildeX
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ)
    [Invertible (Zᵀ * Z)] : Matrix n k ℝ :=
  residualizedRegressors Z X

/-- Hansen Theorem 11.7 generalized-eigenvalue pencil numerator
`X̃'Ỹ(Ỹ'Ỹ)⁻¹Ỹ'X̃`. -/
noncomputable def reducedRankGPencilA
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) : Matrix k k ℝ :=
  Xtildeᵀ * Ytilde * (Ytildeᵀ * Ytilde)⁻¹ * Ytildeᵀ * Xtilde

/-- Hansen Theorem 11.7 generalized-eigenvalue pencil denominator `X̃'X̃`. -/
noncomputable def reducedRankGPencilB
    (Xtilde : Matrix n k ℝ) : Matrix k k ℝ :=
  Xtildeᵀ * Xtilde

/-- Hansen's residualized generalized-eigenvector package for the `G` block in
Theorem 11.7. This is still a support predicate: it does not assert that the
selected eigenvalues are the largest `r` values. -/
def reducedRankHansenGEigenvectors
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ) : Prop :=
  generalizedEigenvectorColumns
    (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda G

end HansenPencil

/-- Certificate package used by Hansen's reduced-rank MLE route.

The proposition fields are supplied by a future generalized-eigenvalue
constructor; this package deliberately avoids vacuous self-equalities. -/
structure ReducedRankMLE
    (G : Matrix k r ℝ) (A : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (Sigma : Matrix m m ℝ) (logLikelihood : ℝ)
    (generalizedEigenvectors leastSquaresRecovery covarianceRecovery likelihoodValue : Prop) :
    Prop where
  generalized_eigenvectors : generalizedEigenvectors
  least_squares_recovery : leastSquaresRecovery
  covariance_recovery : covarianceRecovery
  likelihood_value : likelihoodValue

/-- Assemble a reduced-rank MLE certificate from its four mathematical components. -/
theorem reducedRankMLE_of_certificate
    (G : Matrix k r ℝ) (A : Matrix m r ℝ) (C : Matrix ell m ℝ)
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

section GeneralizedEigenCertificate

variable [Fintype k]

/-- Reduced-rank MLE certificate whose generalized-eigenvector component is the
concrete matrix-pencil predicate used in Hansen Theorem 11.7. -/
theorem reducedRankMLE_of_generalizedEigenvectors
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (Sigma : Matrix m m ℝ) (logLikelihood : ℝ)
    (pencilA pencilB : Matrix k k ℝ) (lambda : r → ℝ)
    {leastSquaresRecovery covarianceRecovery likelihoodValue : Prop}
    (hG : generalizedEigenvectorColumns pencilA pencilB lambda G)
    (hA : leastSquaresRecovery)
    (hSigma : covarianceRecovery) (hLike : likelihoodValue) :
    ReducedRankMLE G Acoef C Sigma logLikelihood
      (generalizedEigenvectorColumns pencilA pencilB lambda G)
      leastSquaresRecovery covarianceRecovery likelihoodValue where
  generalized_eigenvectors := hG
  least_squares_recovery := hA
  covariance_recovery := hSigma
  likelihood_value := hLike

end GeneralizedEigenCertificate

section HansenGeneralizedEigenCertificate

variable {n : Type*}
variable [Fintype n] [DecidableEq n]
variable [Fintype k] [Fintype m] [Fintype ell]
variable [DecidableEq m] [DecidableEq ell]

omit [DecidableEq n] [Fintype ell] [DecidableEq ell] in
/-- Reduced-rank MLE certificate whose generalized-eigenvector component is
Hansen's residualized matrix pencil from Theorem 11.7. -/
theorem reducedRankMLE_of_hansen_generalizedEigenvectors
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ)
    (Sigma : Matrix m m ℝ) (logLikelihood : ℝ)
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (lambda : r → ℝ)
    {leastSquaresRecovery covarianceRecovery likelihoodValue : Prop}
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hA : leastSquaresRecovery)
    (hSigma : covarianceRecovery) (hLike : likelihoodValue) :
    ReducedRankMLE G Acoef C Sigma logLikelihood
      (reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
      leastSquaresRecovery covarianceRecovery likelihoodValue :=
  reducedRankMLE_of_generalizedEigenvectors G Acoef C Sigma logLikelihood
    (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda
    hG hA hSigma hLike

end HansenGeneralizedEigenCertificate

end HansenEconometrics
