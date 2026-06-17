import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Mul
import HansenEconometrics.Chapter3FWL

/-!
# Chapter 11 — reduced-rank regression

The reduced-rank MLE in Hansen Theorem 11.7 is an eigenvalue/eigenvector
characterization. This module records the residualized matrix pencil, the
concentrated determinant objective, concrete least-squares recovery formulas,
and the algebraic bridge from normalized generalized eigenvectors to the
eigenvalue product in Hansen's concentrated objective. It does not claim the
remaining existence theorem selecting the leading generalized eigenspace from
the normal likelihood.
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

variable [Fintype r] [DecidableEq r]

/-- Generalized-eigenvector columns diagonalize the pencil numerator against
the denominator on the selected column space. This is the matrix form of
`A v_j = λ_j B v_j`, one column at a time. -/
theorem generalizedEigenvectorColumns_mul_eq_mul_diagonal
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G) :
    A * G = B * G * Matrix.diagonal lambda := by
  ext i j
  have hj := (h j).2
  calc
    (A * G) i j = (A *ᵥ fun a => G a j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    _ = (lambda j • (B *ᵥ fun a => G a j)) i := by
      rw [hj]
    _ = (B * G * Matrix.diagonal lambda) i j := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.diagonal, mul_comm]

/-- Generalized-eigenvector columns convert Hansen's determinant numerator
`G'A G` into the denominator Gram matrix times the diagonal eigenvalue matrix. -/
theorem generalizedEigenvectorColumns_crossGram_eq_mul_diagonal
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G) :
    Gᵀ * A * G = (Gᵀ * B * G) * Matrix.diagonal lambda := by
  calc
    Gᵀ * A * G = Gᵀ * (A * G) := by
      rw [Matrix.mul_assoc]
    _ = Gᵀ * (B * G * Matrix.diagonal lambda) := by
      rw [generalizedEigenvectorColumns_mul_eq_mul_diagonal A B lambda G h]
    _ = (Gᵀ * B * G) * Matrix.diagonal lambda := by
      simp [Matrix.mul_assoc]

/-- Hansen's normalization for generalized-eigenvector columns:
`G' B G = I`. -/
def generalizedEigenvectorBNormalized
    (B : Matrix k k ℝ) (G : Matrix k r ℝ) : Prop :=
  Gᵀ * B * G = 1

/-- Determinant ratio in Hansen's concentrated reduced-rank objective. -/
noncomputable def generalizedEigenDetObjective
    (A B : Matrix k k ℝ) (G : Matrix k r ℝ) : ℝ :=
  (Gᵀ * A * G).det / (Gᵀ * B * G).det

/-- Normalized generalized-eigenvector columns make Hansen's determinant ratio
equal to the product of the selected generalized eigenvalues. This is the
deterministic bridge from the generalized-eigenvalue statement to the
concentrated likelihood/objective expression. -/
theorem generalizedEigenDetObjective_eq_prod_eigenvalues_of_normalized
    (A B : Matrix k k ℝ) (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : generalizedEigenvectorColumns A B lambda G)
    (hNorm : generalizedEigenvectorBNormalized B G) :
    generalizedEigenDetObjective A B G = ∏ j, lambda j := by
  change Gᵀ * B * G = 1 at hNorm
  rw [generalizedEigenDetObjective,
    generalizedEigenvectorColumns_crossGram_eq_mul_diagonal A B lambda G h, hNorm]
  simp [Matrix.det_diagonal]

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

section Objective

variable [Fintype r] [DecidableEq r]

/-- Hansen normalization for Theorem 11.7's `G` block:
`G' X̃'X̃ G = I_r`. -/
def reducedRankGNormalized
    (Xtilde : Matrix n k ℝ) (G : Matrix k r ℝ) : Prop :=
  generalizedEigenvectorBNormalized (reducedRankGPencilB Xtilde) G

/-- Hansen's concentrated determinant objective in equation (11.20), written
for the `argmax` form using the residualized pencil numerator. -/
noncomputable def reducedRankConcentratedEigenObjective
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ) : ℝ :=
  generalizedEigenDetObjective (reducedRankGPencilA Xtilde Ytilde)
    (reducedRankGPencilB Xtilde) G

/-- Global maximizer predicate for Hansen's concentrated determinant objective
over normalized `G` matrices. -/
def reducedRankConcentratedObjectiveMaximizer
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ) : Prop :=
  reducedRankGNormalized Xtilde G ∧
    ∀ H : Matrix k r ℝ, reducedRankGNormalized Xtilde H →
      reducedRankConcentratedEigenObjective Xtilde Ytilde H ≤
        reducedRankConcentratedEigenObjective Xtilde Ytilde G

/-- The weaker comparison obtained after restricting competitors to normalized
generalized-eigenvector candidates. This is useful proof infrastructure for
the leading-eigenvalue route without claiming the full determinant optimizer. -/
def reducedRankGEigenObjectiveMaximizerOnEigenvectors
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) : Prop :=
  ∀ (H : Matrix k r ℝ) (mu : r → ℝ),
    reducedRankHansenGEigenvectors Xtilde Ytilde mu H →
      reducedRankGNormalized Xtilde H →
        reducedRankConcentratedEigenObjective Xtilde Ytilde H ≤
          reducedRankConcentratedEigenObjective Xtilde Ytilde G

omit [DecidableEq n] in
/-- In Hansen's residualized pencil, normalized generalized eigenvectors make
the concentrated determinant objective equal to the product of the selected
generalized eigenvalues. -/
theorem reducedRankConcentratedObjective_eq_prod_eigenvalues_of_normalized
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hNorm : reducedRankGNormalized Xtilde G) :
    reducedRankConcentratedEigenObjective Xtilde Ytilde G = ∏ j, lambda j :=
  generalizedEigenDetObjective_eq_prod_eigenvalues_of_normalized
    (reducedRankGPencilA Xtilde Ytilde) (reducedRankGPencilB Xtilde) lambda G h hNorm

omit [DecidableEq n] in
/-- If the selected generalized eigenvalues dominate the eigenvalue products
of all normalized generalized-eigenvector competitors, then the corresponding
columns maximize Hansen's determinant objective on that generalized-eigenvector
candidate class. -/
theorem reducedRankGEigenObjectiveMaximizerOnEigenvectors_of_eigenvalueProduct_maximal
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (lambda : r → ℝ) (G : Matrix k r ℝ)
    (h : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hNorm : reducedRankGNormalized Xtilde G)
    (hlead : ∀ (H : Matrix k r ℝ) (mu : r → ℝ),
      reducedRankHansenGEigenvectors Xtilde Ytilde mu H →
        reducedRankGNormalized Xtilde H → ∏ j, mu j ≤ ∏ j, lambda j) :
    reducedRankGEigenObjectiveMaximizerOnEigenvectors Xtilde Ytilde G := by
  intro H mu hH hHNorm
  rw [reducedRankConcentratedObjective_eq_prod_eigenvalues_of_normalized
        Xtilde Ytilde mu H hH hHNorm,
      reducedRankConcentratedObjective_eq_prod_eigenvalues_of_normalized
        Xtilde Ytilde lambda G h hNorm]
  exact hlead H mu hH hHNorm

end Objective

section Recovery

variable [Fintype r] [DecidableEq r]

/-- Hansen's concentrated least-squares recovery
`Â(G) = Ỹ'X̃G (G'X̃'X̃G)⁻¹`. -/
noncomputable def reducedRankAhat
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ) :
    Matrix m r ℝ :=
  Ytildeᵀ * Xtilde * G * (Gᵀ * Xtildeᵀ * Xtilde * G)⁻¹

/-- Least-squares recovery of the unrestricted `Z` coefficients after fixing
`G` and `A`: regress the remaining outcome `Y - X G A'` on `Z`. -/
noncomputable def reducedRankChat
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) : Matrix ell m ℝ :=
  (Zᵀ * Z)⁻¹ * Zᵀ * (Y - X * G * Acoefᵀ)

/-- Hansen's concentrated covariance recovery
`Σ̂(G) = n⁻¹(Ỹ'Ỹ - Ỹ'X̃G(G'X̃'X̃G)⁻¹G'X̃'Ỹ)`. -/
noncomputable def reducedRankSigmaHat
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ) (G : Matrix k r ℝ) :
    Matrix m m ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    (Ytildeᵀ * Ytilde -
      Ytildeᵀ * Xtilde * G * (Gᵀ * Xtildeᵀ * Xtilde * G)⁻¹ * Gᵀ * Xtildeᵀ * Ytilde)

/-- Hansen Theorem 11.7 maximized log-likelihood value, expressed through the
residualized outcome cross-product and selected generalized eigenvalues. -/
noncomputable def reducedRankMaximizedLogLikelihood
    (Ytilde : Matrix n m ℝ) (lambda : r → ℝ) : ℝ :=
  ((Fintype.card m : ℝ) / 2) *
      ((Fintype.card n : ℝ) * Real.log (2 * Real.pi) - 1)
    - ((Fintype.card n : ℝ) / 2) * Real.log (Ytildeᵀ * Ytilde).det
    - ((Fintype.card n : ℝ) / 2) * ∑ j, Real.log (1 - lambda j)

/-- Concrete least-squares recovery predicate for Hansen Theorem 11.7. -/
def reducedRankLeastSquaresRecovery
    (Z : Matrix n ell ℝ) (X : Matrix n k ℝ) (Y : Matrix n m ℝ)
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Acoef : Matrix m r ℝ) (C : Matrix ell m ℝ) : Prop :=
  Acoef = reducedRankAhat Xtilde Ytilde G ∧
    C = reducedRankChat Z X Y G Acoef

/-- Concrete covariance recovery predicate for Hansen Theorem 11.7. -/
def reducedRankCovarianceRecovery
    (Xtilde : Matrix n k ℝ) (Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (Sigma : Matrix m m ℝ) : Prop :=
  Sigma = reducedRankSigmaHat Xtilde Ytilde G

/-- Concrete maximized likelihood-value predicate for Hansen Theorem 11.7. -/
def reducedRankLikelihoodValue
    (Ytilde : Matrix n m ℝ) (lambda : r → ℝ) (logLikelihood : ℝ) : Prop :=
  logLikelihood = reducedRankMaximizedLogLikelihood Ytilde lambda

end Recovery

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

section HansenObjectiveCertificate

variable {n : Type*}
variable [Fintype n] [DecidableEq n]
variable [Fintype k] [Fintype m] [Fintype ell] [Fintype r]
variable [DecidableEq m] [DecidableEq ell] [DecidableEq r]

omit [DecidableEq n] in
/-- Hansen Theorem 11.7 certificate assembled from the concrete concentrated
objective optimizer, residualized generalized-eigenvector equations, and
least-squares recovery formulas. The remaining theorem needed for full closure
is the spectral/likelihood result proving that the leading generalized
eigenvectors satisfy `reducedRankConcentratedObjectiveMaximizer`. -/
theorem reducedRankMLE_of_hansen_objective_optimizer
    (Z : Matrix n ell ℝ) (X Xtilde : Matrix n k ℝ) (Y Ytilde : Matrix n m ℝ)
    (G : Matrix k r ℝ) (lambda : r → ℝ)
    (hG : reducedRankHansenGEigenvectors Xtilde Ytilde lambda G)
    (hOpt : reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G) :
    ReducedRankMLE G
      (reducedRankAhat Xtilde Ytilde G)
      (reducedRankChat Z X Y G (reducedRankAhat Xtilde Ytilde G))
      (reducedRankSigmaHat Xtilde Ytilde G)
      (reducedRankMaximizedLogLikelihood Ytilde lambda)
      (reducedRankHansenGEigenvectors Xtilde Ytilde lambda G ∧
        reducedRankConcentratedObjectiveMaximizer Xtilde Ytilde G)
      (reducedRankLeastSquaresRecovery Z X Y Xtilde Ytilde G
        (reducedRankAhat Xtilde Ytilde G)
        (reducedRankChat Z X Y G (reducedRankAhat Xtilde Ytilde G)))
      (reducedRankCovarianceRecovery Xtilde Ytilde G
        (reducedRankSigmaHat Xtilde Ytilde G))
      (reducedRankLikelihoodValue Ytilde lambda
        (reducedRankMaximizedLogLikelihood Ytilde lambda)) where
  generalized_eigenvectors := ⟨hG, hOpt⟩
  least_squares_recovery := ⟨rfl, rfl⟩
  covariance_recovery := rfl
  likelihood_value := rfl

end HansenObjectiveCertificate

end HansenEconometrics
