import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import HansenEconometrics.Chapter3FWL
import HansenEconometrics.Chapter11MultivariateRegression.MatrixNormal
import HansenEconometrics.Chapter12InstrumentalVariables.Basic
import HansenEconometrics.StudentT

/-!
# Chapter 12 — Kinal moment-threshold support

This module contains the deterministic bridge layer and theorem-facing
product-tail closure for Hansen Theorem 12.7.  The theorem itself is an exact
random-design tail result for the endogenous 2SLS block under joint normality:

`E ‖β̂₂sls,2‖^r < ∞ ↔ r < ℓ₂ - k₂ + 1`.

The public stochastic condition package deliberately does not hide that iff as
an assumption.  Instead, the final theorem face consumes the residualized
fitted-Gram Wishart law, coordinate inverse-Wishart map identities, score laws
and independence, coefficient product representation, and scalar product-tail
calculation needed for the genuine vector/product inverse-Gram tail argument.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal NNReal MeasureTheory ProbabilityTheory

namespace HansenEconometrics

open Matrix

@[reducible]
private noncomputable def kinalMatrixBorelMeasurableSpaceInst
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurableSpace (Matrix ι κ ℝ) :=
  matrixBorelMeasurableSpace ι κ

attribute [local instance] kinalMatrixBorelMeasurableSpaceInst

private lemma kinalMatrixBorelSpaceInst
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    @BorelSpace (Matrix ι κ ℝ) _
      (kinalMatrixBorelMeasurableSpaceInst (ι := ι) (κ := κ)) :=
  matrixBorelSpace ι κ

attribute [local instance] kinalMatrixBorelSpaceInst

private instance kinalMatrixPseudoMetrizableSpaceInst
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix ι κ ℝ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (ι → κ → ℝ))

private instance kinalMatrixSecondCountableTopologyInst
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    SecondCountableTopology (Matrix ι κ ℝ) :=
  inferInstanceAs (SecondCountableTopology (ι → κ → ℝ))

private theorem kinalMatrixBorelMeasurableSpaceInst_le_pi
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    kinalMatrixBorelMeasurableSpaceInst (ι := ι) (κ := κ) ≤
      (inferInstance : MeasurableSpace (ι → κ → ℝ)) := by
  have hPiBorel :
      @BorelSpace (ι → κ → ℝ) _
        (inferInstance : MeasurableSpace (ι → κ → ℝ)) :=
    inferInstance
  have hEq : (inferInstance : MeasurableSpace (ι → κ → ℝ)) =
      borel (ι → κ → ℝ) :=
    @BorelSpace.measurable_eq (ι → κ → ℝ) _
      (inferInstance : MeasurableSpace (ι → κ → ℝ)) hPiBorel
  simpa [kinalMatrixBorelMeasurableSpaceInst, matrixBorelMeasurableSpace] using
    le_of_eq hEq.symm

private theorem pi_le_kinalMatrixBorelMeasurableSpaceInst
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    (inferInstance : MeasurableSpace (ι → κ → ℝ)) ≤
      kinalMatrixBorelMeasurableSpaceInst (ι := ι) (κ := κ) := by
  have hPiBorel :
      @BorelSpace (ι → κ → ℝ) _
        (inferInstance : MeasurableSpace (ι → κ → ℝ)) :=
    inferInstance
  have hEq : (inferInstance : MeasurableSpace (ι → κ → ℝ)) =
      borel (ι → κ → ℝ) :=
    @BorelSpace.measurable_eq (ι → κ → ℝ) _
      (inferInstance : MeasurableSpace (ι → κ → ℝ)) hPiBorel
  simpa [kinalMatrixBorelMeasurableSpaceInst, matrixBorelMeasurableSpace] using
    le_of_eq hEq

namespace KinalSupport

variable {n k₁ k₂ l₂ : Type*}
variable [Fintype n] [DecidableEq n]
variable [Fintype k₁] [DecidableEq k₁]
variable [Fintype k₂] [DecidableEq k₂]
variable [Fintype l₂] [DecidableEq l₂]

/-- The first, included-regressor block of the first-stage fitted regressors in
Hansen's Kinal setup.  The full instrument matrix is `(X₁, Z₂)` and the full
regressor matrix is `(X₁, Y₂)`. -/
noncomputable def twoSLSFittedIncludedRegressors
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ) (Z₂ : Matrix n l₂ ℝ)
    [Invertible ((Matrix.fromCols X₁ Z₂)ᵀ * Matrix.fromCols X₁ Z₂)] :
    Matrix n k₁ ℝ :=
  fun i j =>
    fittedRegressors (Matrix.fromCols X₁ Z₂) (Matrix.fromCols X₁ Y₂) i (Sum.inl j)

/-- The second, endogenous-regressor block of the first-stage fitted regressors
in Hansen's Kinal setup. -/
noncomputable def twoSLSFittedEndogenousRegressors
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ) (Z₂ : Matrix n l₂ ℝ)
    [Invertible ((Matrix.fromCols X₁ Z₂)ᵀ * Matrix.fromCols X₁ Z₂)] :
    Matrix n k₂ ℝ :=
  fun i j =>
    fittedRegressors (Matrix.fromCols X₁ Z₂) (Matrix.fromCols X₁ Y₂) i (Sum.inr j)

/-- Star version of the included fitted block, used in a.e. rank assumptions
where no global inverse typeclass is available. -/
noncomputable def twoSLSFittedIncludedRegressorsStar
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ) (Z₂ : Matrix n l₂ ℝ) :
    Matrix n k₁ ℝ :=
  fun i j =>
    fittedRegressorsStar (Matrix.fromCols X₁ Z₂) (Matrix.fromCols X₁ Y₂) i (Sum.inl j)

/-- Star version of the endogenous fitted block, used in a.e. rank assumptions
where no global inverse typeclass is available. -/
noncomputable def twoSLSFittedEndogenousRegressorsStar
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ) (Z₂ : Matrix n l₂ ℝ) :
    Matrix n k₂ ℝ :=
  fun i j =>
    fittedRegressorsStar (Matrix.fromCols X₁ Z₂) (Matrix.fromCols X₁ Y₂) i (Sum.inr j)

/-- Star residualization of the second block against the first block.  This is
only a rank-assumption surface for Kinal's random-design theorem; finite-sample
FWL identities below use Chapter 3's typeclass-inverse `residualizedRegressors`
on the nonsingular branch. -/
noncomputable def residualizedRegressorsStar
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ) : Matrix n k₂ ℝ :=
  ((1 : Matrix n n ℝ) - X₁ * (X₁ᵀ * X₁)⁻¹ * X₁ᵀ) * X₂

/-- Star residualization of an outcome against a regressor block.  This is the
outcome analogue of `residualizedRegressorsStar`, used to state the exact
FWL form of the Kinal coefficient without finite-sample inverse typeclasses. -/
noncomputable def residualizedOutcomeStar
    (X₁ : Matrix n k₁ ℝ) (y : n → ℝ) : n → ℝ :=
  ((1 : Matrix n n ℝ) - X₁ * (X₁ᵀ * X₁)⁻¹ * X₁ᵀ) *ᵥ y

/-- Residualized fitted endogenous regressors in Hansen's Kinal setup. -/
noncomputable def twoSLSKinalResidualizedFittedEndogenousStar
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ) (Z₂ : Matrix n l₂ ℝ) :
    Matrix n k₂ ℝ :=
  residualizedRegressorsStar
    (twoSLSFittedIncludedRegressorsStar X₁ Y₂ Z₂)
    (twoSLSFittedEndogenousRegressorsStar X₁ Y₂ Z₂)

/-- Outcome residualized against the fitted included regressors in Hansen's
Kinal setup. -/
noncomputable def twoSLSKinalResidualizedOutcomeStar
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ)
    (Z₂ : Matrix n l₂ ℝ) (Y₁ : n → ℝ) : n → ℝ :=
  residualizedOutcomeStar
    (twoSLSFittedIncludedRegressorsStar X₁ Y₂ Z₂) Y₁

/-- Totalized FWL coefficient for the endogenous 2SLS block in Hansen's Kinal
setup.  This is the proof-facing random-design object whose inverse-Gram tail
must be analyzed to prove Theorem 12.7. -/
noncomputable def twoSLSKinalFWLBetaStar
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ)
    (Z₂ : Matrix n l₂ ℝ) (Y₁ : n → ℝ) : k₂ → ℝ :=
  let R := twoSLSKinalResidualizedFittedEndogenousStar X₁ Y₂ Z₂
  (Rᵀ * R)⁻¹ *ᵥ
    (Rᵀ *ᵥ twoSLSKinalResidualizedOutcomeStar X₁ Y₂ Z₂ Y₁)

/-- Residualized fitted-endogenous Gram matrix for Hansen's Kinal FWL
reduction.  This is the random inverse-Gram object whose lower tail drives
Theorem 12.7. -/
noncomputable def twoSLSKinalFWLGramStar
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ)
    (Z₂ : Matrix n l₂ ℝ) : Matrix k₂ k₂ ℝ :=
  let R := twoSLSKinalResidualizedFittedEndogenousStar X₁ Y₂ Z₂
  Rᵀ * R

/-- Residualized fitted-endogenous score vector for Hansen's Kinal FWL
reduction.  Together with `twoSLSKinalFWLGramStar`, this is the algebraic
object to which the remaining scalar Kinal tail proof should apply. -/
noncomputable def twoSLSKinalFWLScoreStar
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ)
    (Z₂ : Matrix n l₂ ℝ) (Y₁ : n → ℝ) : k₂ → ℝ :=
  let R := twoSLSKinalResidualizedFittedEndogenousStar X₁ Y₂ Z₂
  Rᵀ *ᵥ twoSLSKinalResidualizedOutcomeStar X₁ Y₂ Z₂ Y₁

/-- The totalized FWL coefficient is the inverse residualized fitted-endogenous
Gram matrix times the residualized score. -/
theorem twoSLSKinalFWLBetaStar_eq_inverseGram_mul_score
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ)
    (Z₂ : Matrix n l₂ ℝ) (Y₁ : n → ℝ) :
    twoSLSKinalFWLBetaStar X₁ Y₂ Z₂ Y₁ =
      (twoSLSKinalFWLGramStar X₁ Y₂ Z₂)⁻¹ *ᵥ
        twoSLSKinalFWLScoreStar X₁ Y₂ Z₂ Y₁ := by
  simp [twoSLSKinalFWLBetaStar, twoSLSKinalFWLGramStar,
    twoSLSKinalFWLScoreStar]

/-- Coordinate form of `twoSLSKinalFWLBetaStar_eq_inverseGram_mul_score`. -/
theorem twoSLSKinalFWLBetaStar_apply_eq_inverseGram_mul_score
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ)
    (Z₂ : Matrix n l₂ ℝ) (Y₁ : n → ℝ) (j : k₂) :
    twoSLSKinalFWLBetaStar X₁ Y₂ Z₂ Y₁ j =
      ((twoSLSKinalFWLGramStar X₁ Y₂ Z₂)⁻¹ *ᵥ
        twoSLSKinalFWLScoreStar X₁ Y₂ Z₂ Y₁) j := by
  rw [twoSLSKinalFWLBetaStar_eq_inverseGram_mul_score]

/-- Coordinate-sum form of the Kinal FWL coefficient.  This is the scalar
algebraic endpoint needed before applying the inverse-Gram tail theorem. -/
theorem twoSLSKinalFWLBetaStar_apply_eq_sum_inverseGram_score
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ)
    (Z₂ : Matrix n l₂ ℝ) (Y₁ : n → ℝ) (j : k₂) :
    twoSLSKinalFWLBetaStar X₁ Y₂ Z₂ Y₁ j =
      ∑ a : k₂,
        (twoSLSKinalFWLGramStar X₁ Y₂ Z₂)⁻¹ j a *
          twoSLSKinalFWLScoreStar X₁ Y₂ Z₂ Y₁ a := by
  rw [twoSLSKinalFWLBetaStar_apply_eq_inverseGram_mul_score]
  simp [Matrix.mulVec, dotProduct]

omit [Fintype k₂] [DecidableEq k₂] [Fintype l₂] [DecidableEq l₂] in
/-- The Star residualized-regressor surface agrees with Chapter 3 FWL
residualization on the nonsingular branch. -/
theorem residualizedRegressorsStar_eq_residualizedRegressors
    (X₁ : Matrix n k₁ ℝ) (X₂ : Matrix n k₂ ℝ)
    [Invertible (X₁ᵀ * X₁)] :
    residualizedRegressorsStar X₁ X₂ = residualizedRegressors X₁ X₂ := by
  unfold residualizedRegressorsStar residualizedRegressors annihilatorMatrix hatMatrix
  rw [← invOf_eq_nonsing_inv]

omit [Fintype k₂] [DecidableEq k₂] [Fintype l₂] [DecidableEq l₂] in
/-- The Star residualized-outcome surface agrees with Chapter 3's annihilator
on the nonsingular branch. -/
theorem residualizedOutcomeStar_eq_annihilatorMatrix_mulVec
    (X₁ : Matrix n k₁ ℝ) (y : n → ℝ)
    [Invertible (X₁ᵀ * X₁)] :
    residualizedOutcomeStar X₁ y = annihilatorMatrix X₁ *ᵥ y := by
  unfold residualizedOutcomeStar annihilatorMatrix hatMatrix
  rw [← invOf_eq_nonsing_inv]

/-- The totalized Kinal FWL coefficient agrees with Chapter 3's FWL
coefficient on the nonsingular fitted-design branch. -/
theorem twoSLSKinalFWLBetaStar_eq_fwlBeta
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ)
    (Z₂ : Matrix n l₂ ℝ) (Y₁ : n → ℝ)
    [Invertible
      (((twoSLSFittedIncludedRegressorsStar X₁ Y₂ Z₂)ᵀ *
        twoSLSFittedIncludedRegressorsStar X₁ Y₂ Z₂))]
    [Invertible
      (((residualizedRegressors
        (twoSLSFittedIncludedRegressorsStar X₁ Y₂ Z₂)
        (twoSLSFittedEndogenousRegressorsStar X₁ Y₂ Z₂))ᵀ *
        residualizedRegressors
          (twoSLSFittedIncludedRegressorsStar X₁ Y₂ Z₂)
          (twoSLSFittedEndogenousRegressorsStar X₁ Y₂ Z₂)))] :
    twoSLSKinalFWLBetaStar X₁ Y₂ Z₂ Y₁ =
      fwlBeta
        (twoSLSFittedIncludedRegressorsStar X₁ Y₂ Z₂)
        (twoSLSFittedEndogenousRegressorsStar X₁ Y₂ Z₂)
        Y₁ := by
  simp [twoSLSKinalFWLBetaStar, twoSLSKinalResidualizedFittedEndogenousStar,
    twoSLSKinalResidualizedOutcomeStar, fwlBeta, olsBeta,
    residualizedRegressorsStar_eq_residualizedRegressors,
    residualizedOutcomeStar_eq_annihilatorMatrix_mulVec,
    Matrix.invOf_eq_nonsing_inv]

omit [DecidableEq n] [Fintype k₂] [DecidableEq k₂] in
@[simp]
theorem fromCols_twoSLSFittedRegressors
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ) (Z₂ : Matrix n l₂ ℝ)
    [Invertible ((Matrix.fromCols X₁ Z₂)ᵀ * Matrix.fromCols X₁ Z₂)] :
    Matrix.fromCols (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
        (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂) =
      fittedRegressors (Matrix.fromCols X₁ Z₂) (Matrix.fromCols X₁ Y₂) := by
  ext i j
  cases j <;> rfl

omit [DecidableEq n] [Fintype k₂] [DecidableEq k₂] in
@[simp]
theorem fromCols_twoSLSFittedRegressorsStar
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ) (Z₂ : Matrix n l₂ ℝ) :
    Matrix.fromCols (twoSLSFittedIncludedRegressorsStar X₁ Y₂ Z₂)
        (twoSLSFittedEndogenousRegressorsStar X₁ Y₂ Z₂) =
      fittedRegressorsStar (Matrix.fromCols X₁ Z₂) (Matrix.fromCols X₁ Y₂) := by
  ext i j
  cases j <;> rfl

omit [DecidableEq n] [Fintype k₂] [DecidableEq k₂] in
/-- On the nonsingular first-stage branch, the Star included fitted block is
the ordinary fitted included block. -/
theorem twoSLSFittedIncludedRegressorsStar_eq_fitted
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ) (Z₂ : Matrix n l₂ ℝ)
    [Invertible ((Matrix.fromCols X₁ Z₂)ᵀ * Matrix.fromCols X₁ Z₂)] :
    twoSLSFittedIncludedRegressorsStar X₁ Y₂ Z₂ =
      twoSLSFittedIncludedRegressors X₁ Y₂ Z₂ := by
  have hfit :
      fittedRegressorsStar (Matrix.fromCols X₁ Z₂) (Matrix.fromCols X₁ Y₂) =
        fittedRegressors (Matrix.fromCols X₁ Z₂) (Matrix.fromCols X₁ Y₂) := by
    unfold fittedRegressorsStar fittedRegressors
    rw [instrumentProjectionStar_eq_projection]
  ext i j
  exact congrFun (congrFun hfit i) (Sum.inl j)

omit [DecidableEq n] [Fintype k₂] [DecidableEq k₂] in
/-- On the nonsingular first-stage branch, the Star endogenous fitted block is
the ordinary fitted endogenous block. -/
theorem twoSLSFittedEndogenousRegressorsStar_eq_fitted
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ) (Z₂ : Matrix n l₂ ℝ)
    [Invertible ((Matrix.fromCols X₁ Z₂)ᵀ * Matrix.fromCols X₁ Z₂)] :
    twoSLSFittedEndogenousRegressorsStar X₁ Y₂ Z₂ =
      twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂ := by
  have hfit :
      fittedRegressorsStar (Matrix.fromCols X₁ Z₂) (Matrix.fromCols X₁ Y₂) =
        fittedRegressors (Matrix.fromCols X₁ Z₂) (Matrix.fromCols X₁ Y₂) := by
    unfold fittedRegressorsStar fittedRegressors
    rw [instrumentProjectionStar_eq_projection]
  ext i j
  exact congrFun (congrFun hfit i) (Sum.inr j)

omit [DecidableEq n] [Fintype k₂] [DecidableEq k₂] in
/-- The included regressors are fixed by the projection onto `(X₁, Z₂)`. -/
theorem twoSLSFittedIncludedRegressors_eq_left
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ) (Z₂ : Matrix n l₂ ℝ)
    [Invertible ((Matrix.fromCols X₁ Z₂)ᵀ * Matrix.fromCols X₁ Z₂)] :
    twoSLSFittedIncludedRegressors X₁ Y₂ Z₂ = X₁ := by
  have hproj :
      instrumentProjection (Matrix.fromCols X₁ Z₂) * Matrix.fromCols X₁ Z₂ =
        Matrix.fromCols X₁ Z₂ :=
    instrumentProjection_mul_Z (Matrix.fromCols X₁ Z₂)
  ext i j
  have h := congrArg (fun M : Matrix n (k₁ ⊕ l₂) ℝ => M i (Sum.inl j)) hproj
  simpa [twoSLSFittedIncludedRegressors, fittedRegressors, Matrix.mul_fromCols] using h

omit [DecidableEq n] in
/-- On the nonsingular branch, Hansen's textbook-facing endogenous 2SLS block
is the right block of OLS on the first-stage fitted regressors.  This is the
deterministic bridge from Chapter 12 2SLS notation to Chapter 3 partitioned
regression notation. -/
theorem twoSLSEndogenousBetaOrZero_eq_fromColsRightBeta_fitted
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ)
    (Z₂ : Matrix n l₂ ℝ) (Y₁ : n → ℝ)
    [Invertible ((Matrix.fromCols X₁ Z₂)ᵀ * Matrix.fromCols X₁ Z₂)]
    [Invertible
      ((Matrix.fromCols (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
        (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂))ᵀ *
        Matrix.fromCols (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
          (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂))] :
    twoSLSEndogenousBetaOrZero X₁ Y₂ Z₂ Y₁ =
      fromColsRightBeta
        (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
        (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂)
        Y₁ := by
  ext j
  unfold twoSLSEndogenousBetaOrZero fromColsRightBeta
  rw [twoSLSBetaOrZero_eq_twoSLSBetaStar]
  rw [twoSLSBetaStar_eq_olsBetaStar_fitted]
  rw [show
      fittedRegressors (Matrix.fromCols X₁ Z₂) (Matrix.fromCols X₁ Y₂) =
        Matrix.fromCols
          (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
          (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂) by
    exact (fromCols_twoSLSFittedRegressors X₁ Y₂ Z₂).symm]
  rw [olsBetaStar_eq_olsBeta]

/-- FWL form of the endogenous 2SLS block on the nonsingular branch: partial
out the fitted included regressors from the fitted endogenous regressors. -/
theorem twoSLSEndogenousBetaOrZero_eq_fwlBeta_fitted
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ)
    (Z₂ : Matrix n l₂ ℝ) (Y₁ : n → ℝ)
    [Invertible ((Matrix.fromCols X₁ Z₂)ᵀ * Matrix.fromCols X₁ Z₂)]
    [Invertible
      ((Matrix.fromCols (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
        (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂))ᵀ *
        Matrix.fromCols (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
          (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂))]
    [Invertible
      ((twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)ᵀ *
        twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)]
    [Invertible
      ((residualizedRegressors
        (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
        (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂))ᵀ *
        residualizedRegressors
          (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
          (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂))] :
    twoSLSEndogenousBetaOrZero X₁ Y₂ Z₂ Y₁ =
      fwlBeta
        (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
        (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂)
        Y₁ := by
  rw [twoSLSEndogenousBetaOrZero_eq_fromColsRightBeta_fitted]
  rw [fromColsRightBeta_eq_fwlBeta]

/-- Rank-field bridge for Hansen/Kinal: on the nonsingular first-stage and
fitted-design event, the textbook endogenous 2SLS block is exactly the
totalized FWL coefficient used by the random inverse-Gram tail theorem. -/
theorem twoSLSEndogenousBetaOrZero_eq_twoSLSKinalFWLBetaStar_of_ranks
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ)
    (Z₂ : Matrix n l₂ ℝ) (Y₁ : n → ℝ)
    (hinstr :
      IsUnit (((Matrix.fromCols X₁ Z₂)ᵀ * Matrix.fromCols X₁ Z₂)).det)
    (hfitted :
      IsUnit
        ((((Matrix.fromCols
          (twoSLSFittedIncludedRegressorsStar X₁ Y₂ Z₂)
          (twoSLSFittedEndogenousRegressorsStar X₁ Y₂ Z₂))ᵀ *
          Matrix.fromCols
            (twoSLSFittedIncludedRegressorsStar X₁ Y₂ Z₂)
            (twoSLSFittedEndogenousRegressorsStar X₁ Y₂ Z₂)))).det)
    (hincluded :
      IsUnit
        ((((twoSLSFittedIncludedRegressorsStar X₁ Y₂ Z₂)ᵀ *
          twoSLSFittedIncludedRegressorsStar X₁ Y₂ Z₂))).det)
    (hresid :
      IsUnit
        ((((residualizedRegressorsStar
          (twoSLSFittedIncludedRegressorsStar X₁ Y₂ Z₂)
          (twoSLSFittedEndogenousRegressorsStar X₁ Y₂ Z₂))ᵀ *
          residualizedRegressorsStar
            (twoSLSFittedIncludedRegressorsStar X₁ Y₂ Z₂)
            (twoSLSFittedEndogenousRegressorsStar X₁ Y₂ Z₂)))).det) :
    twoSLSEndogenousBetaOrZero X₁ Y₂ Z₂ Y₁ =
      twoSLSKinalFWLBetaStar X₁ Y₂ Z₂ Y₁ := by
  classical
  letI : Invertible ((Matrix.fromCols X₁ Z₂)ᵀ * Matrix.fromCols X₁ Z₂) :=
    Matrix.invertibleOfIsUnitDet
      (A := (Matrix.fromCols X₁ Z₂)ᵀ * Matrix.fromCols X₁ Z₂) hinstr
  have hincStar :
      twoSLSFittedIncludedRegressorsStar X₁ Y₂ Z₂ =
        twoSLSFittedIncludedRegressors X₁ Y₂ Z₂ :=
    twoSLSFittedIncludedRegressorsStar_eq_fitted X₁ Y₂ Z₂
  have hendoStar :
      twoSLSFittedEndogenousRegressorsStar X₁ Y₂ Z₂ =
        twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂ :=
    twoSLSFittedEndogenousRegressorsStar_eq_fitted X₁ Y₂ Z₂
  letI : Invertible
      ((Matrix.fromCols
        (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
        (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂))ᵀ *
        Matrix.fromCols
          (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
          (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂)) :=
    Matrix.invertibleOfIsUnitDet
      (A := (Matrix.fromCols
        (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
        (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂))ᵀ *
        Matrix.fromCols
          (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
          (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂))
      (by simpa [hincStar, hendoStar] using hfitted)
  letI : Invertible
      ((twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)ᵀ *
        twoSLSFittedIncludedRegressors X₁ Y₂ Z₂) :=
    Matrix.invertibleOfIsUnitDet
      (A := (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)ᵀ *
        twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
      (by simpa [hincStar] using hincluded)
  letI : Invertible
      ((residualizedRegressors
        (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
        (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂))ᵀ *
        residualizedRegressors
          (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
          (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂)) :=
    Matrix.invertibleOfIsUnitDet
      (A := (residualizedRegressors
        (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
        (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂))ᵀ *
        residualizedRegressors
          (twoSLSFittedIncludedRegressors X₁ Y₂ Z₂)
          (twoSLSFittedEndogenousRegressors X₁ Y₂ Z₂))
      (by
        simpa [hincStar, hendoStar, residualizedRegressorsStar_eq_residualizedRegressors]
          using hresid)
  rw [twoSLSEndogenousBetaOrZero_eq_fwlBeta_fitted]
  simp [fwlBeta, olsBeta, twoSLSKinalFWLBetaStar,
    twoSLSKinalResidualizedFittedEndogenousStar,
    twoSLSKinalResidualizedOutcomeStar,
    residualizedRegressorsStar_eq_residualizedRegressors,
    residualizedOutcomeStar_eq_annihilatorMatrix_mulVec,
    Matrix.invOf_eq_nonsing_inv, hincStar, hendoStar]

/-- One finite Euclidean vector containing Hansen's Kinal data
`(X₁, Y₂, Z₂, Y₁)`.  Encoding the data this way gives `HasGaussianLaw` a
canonical measurable/topological codomain instead of relying on product
instances for raw matrix types. -/
noncomputable def twoSLSKinalJointData
    {Ω : Type*} (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ) :
    Ω → EuclideanSpace ℝ (n × (((k₁ ⊕ k₂) ⊕ l₂) ⊕ Unit)) :=
  fun ω =>
    WithLp.toLp 2 fun idx =>
      match idx with
      | (i, Sum.inl (Sum.inl (Sum.inl j))) => X₁ ω i j
      | (i, Sum.inl (Sum.inl (Sum.inr j))) => Y₂ ω i j
      | (i, Sum.inl (Sum.inr j)) => Z₂ ω i j
      | (i, Sum.inr _) => Y₁ ω i

/-- Faithful stochastic assumptions for Hansen Theorem 12.7.

The package deliberately does not include the Kinal moment iff as a field.  It
records joint normality and the finite-sample rank/order assumptions needed to
state the theorem.  The missing proof ingredient is an external exact-tail
theorem deriving the iff from these hypotheses. -/
structure TwoSLSKinalJointNormalConditions
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ) : Prop where
  /-- Hansen's finite-sample data vector is jointly Gaussian. -/
  joint_gaussian : HasGaussianLaw (twoSLSKinalJointData X₁ Y₂ Z₂ Y₁) μ
  /-- The endogenous instrument count satisfies the overidentification side
  condition used by the Kinal threshold. -/
  instrument_count : Fintype.card k₂ ≤ Fintype.card l₂
  /-- The full instrument matrix `(X₁, Z₂)` has full column rank a.s. -/
  instrument_rank_ae :
    ∀ᵐ ω ∂μ,
      IsUnit
        ((((Matrix.fromCols (X₁ ω) (Z₂ ω))ᵀ *
          Matrix.fromCols (X₁ ω) (Z₂ ω))).det)
  /-- The fitted full regressor matrix has full column rank a.s. -/
  fitted_rank_ae :
    ∀ᵐ ω ∂μ,
      IsUnit
        ((((Matrix.fromCols
          (twoSLSFittedIncludedRegressorsStar (X₁ ω) (Y₂ ω) (Z₂ ω))
          (twoSLSFittedEndogenousRegressorsStar (X₁ ω) (Y₂ ω) (Z₂ ω)))ᵀ *
          Matrix.fromCols
            (twoSLSFittedIncludedRegressorsStar (X₁ ω) (Y₂ ω) (Z₂ ω))
            (twoSLSFittedEndogenousRegressorsStar (X₁ ω) (Y₂ ω) (Z₂ ω)))).det)
  /-- The included fitted block has full rank a.s., so the FWL residualization
  is well behaved on the nonsingular branch. -/
  included_fitted_rank_ae :
    ∀ᵐ ω ∂μ,
      IsUnit
        ((((twoSLSFittedIncludedRegressorsStar (X₁ ω) (Y₂ ω) (Z₂ ω))ᵀ *
          twoSLSFittedIncludedRegressorsStar (X₁ ω) (Y₂ ω) (Z₂ ω))).det)
  /-- The residualized fitted endogenous block has full rank a.s.; this is the
  random-design Gram matrix whose inverse tail drives Kinal's threshold. -/
  residualized_fitted_endogenous_rank_ae :
    ∀ᵐ ω ∂μ,
      IsUnit
        ((((residualizedRegressorsStar
          (twoSLSFittedIncludedRegressorsStar (X₁ ω) (Y₂ ω) (Z₂ ω))
          (twoSLSFittedEndogenousRegressorsStar (X₁ ω) (Y₂ ω) (Z₂ ω)))ᵀ *
          residualizedRegressorsStar
            (twoSLSFittedIncludedRegressorsStar (X₁ ω) (Y₂ ω) (Z₂ ω))
            (twoSLSFittedEndogenousRegressorsStar (X₁ ω) (Y₂ ω) (Z₂ ω)))).det)

/-- The encoded jointly Gaussian Kinal data vector makes the included
regressor block a.e. measurable. -/
theorem TwoSLSKinalJointNormalConditions.aemeasurable_X₁
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁) :
    AEMeasurable X₁ μ := by
  let π :
      EuclideanSpace ℝ (n × (((k₁ ⊕ k₂) ⊕ l₂) ⊕ Unit)) →
        Matrix n k₁ ℝ :=
    fun z i j => z.ofLp (i, Sum.inl (Sum.inl (Sum.inl j)))
  have hπ : Measurable π := by
    have hπ_fun :
        @Measurable
          (EuclideanSpace ℝ (n × (((k₁ ⊕ k₂) ⊕ l₂) ⊕ Unit)))
          (n → k₁ → ℝ) _ inferInstance
          (fun z => fun i j => z.ofLp (i, Sum.inl (Sum.inl (Sum.inl j)))) := by
      fun_prop
    change
      @Measurable
        (EuclideanSpace ℝ (n × (((k₁ ⊕ k₂) ⊕ l₂) ⊕ Unit)))
        (Matrix n k₁ ℝ) _ (kinalMatrixBorelMeasurableSpaceInst) π
    exact hπ_fun.mono le_rfl
      (kinalMatrixBorelMeasurableSpaceInst_le_pi (ι := n) (κ := k₁))
  simpa [twoSLSKinalJointData, π] using
    hπ.aemeasurable.comp_aemeasurable h.joint_gaussian.aemeasurable

/-- The encoded jointly Gaussian Kinal data vector makes the endogenous
regressor block a.e. measurable. -/
theorem TwoSLSKinalJointNormalConditions.aemeasurable_Y₂
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁) :
    AEMeasurable Y₂ μ := by
  let π :
      EuclideanSpace ℝ (n × (((k₁ ⊕ k₂) ⊕ l₂) ⊕ Unit)) →
        Matrix n k₂ ℝ :=
    fun z i j => z.ofLp (i, Sum.inl (Sum.inl (Sum.inr j)))
  have hπ : Measurable π := by
    have hπ_fun :
        @Measurable
          (EuclideanSpace ℝ (n × (((k₁ ⊕ k₂) ⊕ l₂) ⊕ Unit)))
          (n → k₂ → ℝ) _ inferInstance
          (fun z => fun i j => z.ofLp (i, Sum.inl (Sum.inl (Sum.inr j)))) := by
      fun_prop
    change
      @Measurable
        (EuclideanSpace ℝ (n × (((k₁ ⊕ k₂) ⊕ l₂) ⊕ Unit)))
        (Matrix n k₂ ℝ) _ (kinalMatrixBorelMeasurableSpaceInst) π
    exact hπ_fun.mono le_rfl
      (kinalMatrixBorelMeasurableSpaceInst_le_pi (ι := n) (κ := k₂))
  simpa [twoSLSKinalJointData, π] using
    hπ.aemeasurable.comp_aemeasurable h.joint_gaussian.aemeasurable

/-- The encoded jointly Gaussian Kinal data vector makes the excluded
instrument block a.e. measurable. -/
theorem TwoSLSKinalJointNormalConditions.aemeasurable_Z₂
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁) :
    AEMeasurable Z₂ μ := by
  let π :
      EuclideanSpace ℝ (n × (((k₁ ⊕ k₂) ⊕ l₂) ⊕ Unit)) →
        Matrix n l₂ ℝ :=
    fun z i j => z.ofLp (i, Sum.inl (Sum.inr j))
  have hπ : Measurable π := by
    have hπ_fun :
        @Measurable
          (EuclideanSpace ℝ (n × (((k₁ ⊕ k₂) ⊕ l₂) ⊕ Unit)))
          (n → l₂ → ℝ) _ inferInstance
          (fun z => fun i j => z.ofLp (i, Sum.inl (Sum.inr j))) := by
      fun_prop
    change
      @Measurable
        (EuclideanSpace ℝ (n × (((k₁ ⊕ k₂) ⊕ l₂) ⊕ Unit)))
        (Matrix n l₂ ℝ) _ (kinalMatrixBorelMeasurableSpaceInst) π
    exact hπ_fun.mono le_rfl
      (kinalMatrixBorelMeasurableSpaceInst_le_pi (ι := n) (κ := l₂))
  simpa [twoSLSKinalJointData, π] using
    hπ.aemeasurable.comp_aemeasurable h.joint_gaussian.aemeasurable

/-- The encoded jointly Gaussian Kinal data vector makes the scalar outcome
block a.e. measurable. -/
theorem TwoSLSKinalJointNormalConditions.aemeasurable_Y₁
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁) :
    AEMeasurable Y₁ μ := by
  let π :
      EuclideanSpace ℝ (n × (((k₁ ⊕ k₂) ⊕ l₂) ⊕ Unit)) →
        (n → ℝ) :=
    fun z i => z.ofLp (i, Sum.inr ())
  have hπ : Measurable π := by
    dsimp [π]
    fun_prop
  simpa [twoSLSKinalJointData, π] using
    hπ.aemeasurable.comp_aemeasurable h.joint_gaussian.aemeasurable

private theorem kinal_fromCols_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {κ η : Type*} [Fintype κ] [Fintype η]
    {A : Ω → Matrix n κ ℝ} {B : Ω → Matrix n η ℝ}
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ) :
    AEStronglyMeasurable (fun ω => Matrix.fromCols (A ω) (B ω)) μ := by
  have hraw :
      @AEMeasurable Ω (n → κ ⊕ η → ℝ) inferInstance _
      (fun ω => fun i (j : κ ⊕ η) =>
        Sum.elim (fun a : κ => A ω i a) (fun b : η => B ω i b) j) μ
      := by
    rw [aemeasurable_pi_iff]
    intro i
    rw [aemeasurable_pi_iff]
    intro j
    cases j with
    | inl a =>
        have hsource_ge :
            (inferInstance : MeasurableSpace (n → κ → ℝ)) ≤
              kinalMatrixBorelMeasurableSpaceInst (ι := n) (κ := κ) :=
          pi_le_kinalMatrixBorelMeasurableSpaceInst (ι := n) (κ := κ)
        have hcoord_pi :
            @Measurable (n → κ → ℝ) ℝ
              (inferInstance : MeasurableSpace (n → κ → ℝ)) inferInstance
              (fun M : n → κ → ℝ => M i a) :=
          ((continuous_apply a :
            Continuous (fun x : κ → ℝ => x a)).comp
            (continuous_apply i :
              Continuous (fun M : n → κ → ℝ => M i))).measurable
        have hcoord :
            @Measurable (Matrix n κ ℝ) ℝ
              (kinalMatrixBorelMeasurableSpaceInst (ι := n) (κ := κ))
              inferInstance (fun M : Matrix n κ ℝ => M i a) := by
          change @Measurable (n → κ → ℝ) ℝ
            (kinalMatrixBorelMeasurableSpaceInst (ι := n) (κ := κ))
            inferInstance (fun M : n → κ → ℝ => M i a)
          exact hcoord_pi.mono hsource_ge le_rfl
        exact hcoord.aemeasurable.comp_aemeasurable hA.aemeasurable
    | inr b =>
        have hsource_ge :
            (inferInstance : MeasurableSpace (n → η → ℝ)) ≤
              kinalMatrixBorelMeasurableSpaceInst (ι := n) (κ := η) :=
          pi_le_kinalMatrixBorelMeasurableSpaceInst (ι := n) (κ := η)
        have hcoord_pi :
            @Measurable (n → η → ℝ) ℝ
              (inferInstance : MeasurableSpace (n → η → ℝ)) inferInstance
              (fun M : n → η → ℝ => M i b) :=
          ((continuous_apply b :
            Continuous (fun x : η → ℝ => x b)).comp
            (continuous_apply i :
              Continuous (fun M : n → η → ℝ => M i))).measurable
        have hcoord :
            @Measurable (Matrix n η ℝ) ℝ
              (kinalMatrixBorelMeasurableSpaceInst (ι := n) (κ := η))
              inferInstance (fun M : Matrix n η ℝ => M i b) := by
          change @Measurable (n → η → ℝ) ℝ
            (kinalMatrixBorelMeasurableSpaceInst (ι := n) (κ := η))
            inferInstance (fun M : n → η → ℝ => M i b)
          exact hcoord_pi.mono hsource_ge le_rfl
        exact hcoord.aemeasurable.comp_aemeasurable hB.aemeasurable
  have htarget_le :
      kinalMatrixBorelMeasurableSpaceInst (ι := n) (κ := κ ⊕ η) ≤
        (inferInstance : MeasurableSpace (n → κ ⊕ η → ℝ)) :=
    kinalMatrixBorelMeasurableSpaceInst_le_pi (ι := n) (κ := κ ⊕ η)
  have hAE : AEMeasurable (fun ω => Matrix.fromCols (A ω) (B ω)) μ := by
    change @AEMeasurable Ω (n → κ ⊕ η → ℝ)
      (kinalMatrixBorelMeasurableSpaceInst (ι := n) (κ := κ ⊕ η)) _
      (fun ω => fun i (j : κ ⊕ η) =>
        Sum.elim (fun a : κ => A ω i a) (fun b : η => B ω i b) j) μ
    rcases hraw with ⟨g, hg, hfg⟩
    exact ⟨g, hg.mono le_rfl htarget_le, hfg⟩
  exact hAE.aestronglyMeasurable

private theorem kinal_instrumentProjectionStar_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {Z : Ω → Matrix n κ ℝ}
    (hZ : AEStronglyMeasurable Z μ) :
    AEStronglyMeasurable (fun ω => instrumentProjectionStar (Z ω)) μ := by
  have hZt : AEStronglyMeasurable (fun ω => (Z ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hZ
  have hZZ : AEStronglyMeasurable (fun ω => (Z ω)ᵀ * Z ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hZt.prodMk hZ)
  have hZZinv : AEStronglyMeasurable (fun ω => ((Z ω)ᵀ * Z ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hZZ
  have hleft : AEStronglyMeasurable
      (fun ω => Z ω * ((Z ω)ᵀ * Z ω)⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hZ.prodMk hZZinv)
  have hproj : AEStronglyMeasurable
      (fun ω => Z ω * ((Z ω)ᵀ * Z ω)⁻¹ * (Z ω)ᵀ) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hleft.prodMk hZt)
  simpa [instrumentProjectionStar, Matrix.mul_assoc] using hproj

private theorem kinal_fittedRegressorsStar_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {κ η : Type*} [Fintype κ] [DecidableEq κ] [Fintype η]
    {Z : Ω → Matrix n κ ℝ} {X : Ω → Matrix n η ℝ}
    (hZ : AEStronglyMeasurable Z μ) (hX : AEStronglyMeasurable X μ) :
    AEStronglyMeasurable (fun ω => fittedRegressorsStar (Z ω) (X ω)) μ := by
  have hP : AEStronglyMeasurable (fun ω => instrumentProjectionStar (Z ω)) μ :=
    kinal_instrumentProjectionStar_aestronglyMeasurable hZ
  have hPX : AEStronglyMeasurable
      (fun ω => instrumentProjectionStar (Z ω) * X ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hP.prodMk hX)
  simpa [fittedRegressorsStar] using hPX

private theorem kinal_twoSLSFittedIncludedRegressorsStar_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ}
    (hX₁ : AEStronglyMeasurable X₁ μ)
    (hY₂ : AEStronglyMeasurable Y₂ μ)
    (hZ₂ : AEStronglyMeasurable Z₂ μ) :
    AEStronglyMeasurable
      (fun ω => twoSLSFittedIncludedRegressorsStar (X₁ ω) (Y₂ ω) (Z₂ ω)) μ := by
  have hInstr : AEStronglyMeasurable
      (fun ω => Matrix.fromCols (X₁ ω) (Z₂ ω)) μ :=
    kinal_fromCols_aestronglyMeasurable hX₁ hZ₂
  have hReg : AEStronglyMeasurable
      (fun ω => Matrix.fromCols (X₁ ω) (Y₂ ω)) μ :=
    kinal_fromCols_aestronglyMeasurable hX₁ hY₂
  have hFitted : AEStronglyMeasurable
      (fun ω =>
        fittedRegressorsStar (Matrix.fromCols (X₁ ω) (Z₂ ω))
          (Matrix.fromCols (X₁ ω) (Y₂ ω))) μ :=
    kinal_fittedRegressorsStar_aestronglyMeasurable hInstr hReg
  have hcont :
      Continuous
        (fun M : Matrix n (k₁ ⊕ k₂) ℝ => fun i j => M i (Sum.inl j)) := by
    fun_prop
  simpa [twoSLSFittedIncludedRegressorsStar] using
    hcont.comp_aestronglyMeasurable hFitted

private theorem kinal_twoSLSFittedEndogenousRegressorsStar_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ}
    (hX₁ : AEStronglyMeasurable X₁ μ)
    (hY₂ : AEStronglyMeasurable Y₂ μ)
    (hZ₂ : AEStronglyMeasurable Z₂ μ) :
    AEStronglyMeasurable
      (fun ω => twoSLSFittedEndogenousRegressorsStar (X₁ ω) (Y₂ ω) (Z₂ ω)) μ := by
  have hInstr : AEStronglyMeasurable
      (fun ω => Matrix.fromCols (X₁ ω) (Z₂ ω)) μ :=
    kinal_fromCols_aestronglyMeasurable hX₁ hZ₂
  have hReg : AEStronglyMeasurable
      (fun ω => Matrix.fromCols (X₁ ω) (Y₂ ω)) μ :=
    kinal_fromCols_aestronglyMeasurable hX₁ hY₂
  have hFitted : AEStronglyMeasurable
      (fun ω =>
        fittedRegressorsStar (Matrix.fromCols (X₁ ω) (Z₂ ω))
          (Matrix.fromCols (X₁ ω) (Y₂ ω))) μ :=
    kinal_fittedRegressorsStar_aestronglyMeasurable hInstr hReg
  have hcont :
      Continuous
        (fun M : Matrix n (k₁ ⊕ k₂) ℝ => fun i j => M i (Sum.inr j)) := by
    fun_prop
  simpa [twoSLSFittedEndogenousRegressorsStar] using
    hcont.comp_aestronglyMeasurable hFitted

set_option maxHeartbeats 800000 in
-- Total matrix inverse measurability over finite matrix products unfolds a large Pi type here.
private theorem kinal_residualizedRegressorsStar_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {κ η : Type*} [Fintype κ] [DecidableEq κ] [Fintype η]
    {A : Ω → Matrix n κ ℝ} {B : Ω → Matrix n η ℝ}
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ) :
    AEStronglyMeasurable (fun ω => residualizedRegressorsStar (A ω) (B ω)) μ := by
  have hAt : AEStronglyMeasurable (fun ω => (A ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hA
  have hGram : AEStronglyMeasurable (fun ω => (A ω)ᵀ * A ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hAt.prodMk hA)
  have hInv : AEStronglyMeasurable (fun ω => ((A ω)ᵀ * A ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hGram
  have hLeft : AEStronglyMeasurable
      (fun ω => A ω * ((A ω)ᵀ * A ω)⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hA.prodMk hInv)
  have hHat : AEStronglyMeasurable
      (fun ω => A ω * ((A ω)ᵀ * A ω)⁻¹ * (A ω)ᵀ) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hLeft.prodMk hAt)
  have hAnnihilator : AEStronglyMeasurable
      (fun ω => (1 : Matrix n n ℝ) - A ω * ((A ω)ᵀ * A ω)⁻¹ * (A ω)ᵀ) μ :=
    aestronglyMeasurable_const.sub hHat
  have hResidualized : AEStronglyMeasurable
      (fun ω => ((1 : Matrix n n ℝ) -
          A ω * ((A ω)ᵀ * A ω)⁻¹ * (A ω)ᵀ) * B ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hAnnihilator.prodMk hB)
  simpa only [residualizedRegressorsStar] using hResidualized

set_option maxHeartbeats 800000 in
-- Same finite-matrix inverse measurability pattern as the regressor residualization helper.
private theorem kinal_residualizedOutcomeStar_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Ω → Matrix n κ ℝ} {y : Ω → n → ℝ}
    (hA : AEStronglyMeasurable A μ) (hy : AEStronglyMeasurable y μ) :
    AEStronglyMeasurable (fun ω => residualizedOutcomeStar (A ω) (y ω)) μ := by
  have hAt : AEStronglyMeasurable (fun ω => (A ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hA
  have hGram : AEStronglyMeasurable (fun ω => (A ω)ᵀ * A ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hAt.prodMk hA)
  have hInv : AEStronglyMeasurable (fun ω => ((A ω)ᵀ * A ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hGram
  have hLeft : AEStronglyMeasurable
      (fun ω => A ω * ((A ω)ᵀ * A ω)⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hA.prodMk hInv)
  have hHat : AEStronglyMeasurable
      (fun ω => A ω * ((A ω)ᵀ * A ω)⁻¹ * (A ω)ᵀ) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hLeft.prodMk hAt)
  have hAnnihilator : AEStronglyMeasurable
      (fun ω => (1 : Matrix n n ℝ) - A ω * ((A ω)ᵀ * A ω)⁻¹ * (A ω)ᵀ) μ :=
    aestronglyMeasurable_const.sub hHat
  have hResidualized : AEStronglyMeasurable
      (fun ω => ((1 : Matrix n n ℝ) -
          A ω * ((A ω)ᵀ * A ω)⁻¹ * (A ω)ᵀ) *ᵥ y ω) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hAnnihilator.prodMk hy)
  simpa only [residualizedOutcomeStar] using hResidualized

private theorem kinal_fwlScoreStar_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hX₁ : AEStronglyMeasurable X₁ μ)
    (hY₂ : AEStronglyMeasurable Y₂ μ)
    (hZ₂ : AEStronglyMeasurable Z₂ μ)
    (hY₁ : AEStronglyMeasurable Y₁ μ) :
    AEStronglyMeasurable
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) μ := by
  have hInc : AEStronglyMeasurable
      (fun ω => twoSLSFittedIncludedRegressorsStar (X₁ ω) (Y₂ ω) (Z₂ ω)) μ :=
    kinal_twoSLSFittedIncludedRegressorsStar_aestronglyMeasurable hX₁ hY₂ hZ₂
  have hEndo : AEStronglyMeasurable
      (fun ω => twoSLSFittedEndogenousRegressorsStar (X₁ ω) (Y₂ ω) (Z₂ ω)) μ :=
    kinal_twoSLSFittedEndogenousRegressorsStar_aestronglyMeasurable hX₁ hY₂ hZ₂
  have hR : AEStronglyMeasurable
      (fun ω => twoSLSKinalResidualizedFittedEndogenousStar
        (X₁ ω) (Y₂ ω) (Z₂ ω)) μ := by
    simpa [twoSLSKinalResidualizedFittedEndogenousStar] using
      kinal_residualizedRegressorsStar_aestronglyMeasurable hInc hEndo
  have hYresid : AEStronglyMeasurable
      (fun ω => twoSLSKinalResidualizedOutcomeStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) μ := by
    simpa [twoSLSKinalResidualizedOutcomeStar] using
      kinal_residualizedOutcomeStar_aestronglyMeasurable hInc hY₁
  have hRt : AEStronglyMeasurable
      (fun ω => (twoSLSKinalResidualizedFittedEndogenousStar
        (X₁ ω) (Y₂ ω) (Z₂ ω))ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hR
  have hScore : AEStronglyMeasurable
      (fun ω =>
        (twoSLSKinalResidualizedFittedEndogenousStar
          (X₁ ω) (Y₂ ω) (Z₂ ω))ᵀ *ᵥ
          twoSLSKinalResidualizedOutcomeStar
            (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hRt.prodMk hYresid)
  simpa [twoSLSKinalFWLScoreStar] using hScore

/-- Measurability of the residualized fitted-endogenous Gram from measurable
Kinal design blocks. -/
private theorem kinal_fwlGramStar_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ}
    (hX₁ : AEStronglyMeasurable X₁ μ)
    (hY₂ : AEStronglyMeasurable Y₂ μ)
    (hZ₂ : AEStronglyMeasurable Z₂ μ) :
    AEStronglyMeasurable
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω)) μ := by
  have hInc : AEStronglyMeasurable
      (fun ω => twoSLSFittedIncludedRegressorsStar (X₁ ω) (Y₂ ω) (Z₂ ω)) μ :=
    kinal_twoSLSFittedIncludedRegressorsStar_aestronglyMeasurable hX₁ hY₂ hZ₂
  have hEndo : AEStronglyMeasurable
      (fun ω => twoSLSFittedEndogenousRegressorsStar (X₁ ω) (Y₂ ω) (Z₂ ω)) μ :=
    kinal_twoSLSFittedEndogenousRegressorsStar_aestronglyMeasurable hX₁ hY₂ hZ₂
  have hR : AEStronglyMeasurable
      (fun ω => twoSLSKinalResidualizedFittedEndogenousStar
        (X₁ ω) (Y₂ ω) (Z₂ ω)) μ := by
    simpa [twoSLSKinalResidualizedFittedEndogenousStar] using
      kinal_residualizedRegressorsStar_aestronglyMeasurable hInc hEndo
  have hRt : AEStronglyMeasurable
      (fun ω => (twoSLSKinalResidualizedFittedEndogenousStar
        (X₁ ω) (Y₂ ω) (Z₂ ω))ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hR
  have hGram : AEStronglyMeasurable
      (fun ω =>
        (twoSLSKinalResidualizedFittedEndogenousStar
          (X₁ ω) (Y₂ ω) (Z₂ ω))ᵀ *
          twoSLSKinalResidualizedFittedEndogenousStar
            (X₁ ω) (Y₂ ω) (Z₂ ω)) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hRt.prodMk hR)
  simpa [twoSLSKinalFWLGramStar] using hGram

/-- Joint normality supplies a.e. measurability of the actual residualized FWL
score vector used in the canonical score law for Kinal's theorem. -/
theorem TwoSLSKinalJointNormalConditions.aemeasurable_fwlScoreStar
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁) :
    AEMeasurable
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) μ :=
  (kinal_fwlScoreStar_aestronglyMeasurable
    h.aemeasurable_X₁.aestronglyMeasurable
    h.aemeasurable_Y₂.aestronglyMeasurable
    h.aemeasurable_Z₂.aestronglyMeasurable
    h.aemeasurable_Y₁.aestronglyMeasurable).aemeasurable

/-- Joint normality supplies a.e. measurability of the actual residualized FWL
Gram matrix used in Kinal's inverse-Gram tail argument. -/
theorem TwoSLSKinalJointNormalConditions.aemeasurable_fwlGramStar
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁) :
    AEMeasurable
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω)) μ :=
  (kinal_fwlGramStar_aestronglyMeasurable
    h.aemeasurable_X₁.aestronglyMeasurable
    h.aemeasurable_Y₂.aestronglyMeasurable
    h.aemeasurable_Z₂.aestronglyMeasurable).aemeasurable

/-- Canonical push-forward law of the residualized Kinal FWL score vector.

This removes an artificial raw-boundary choice from Theorem 12.7 reductions:
callers can use the actual push-forward law rather than naming a separate
score-vector law. -/
noncomputable def twoSLSKinalFWLScoreVectorLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ) :
    Measure (k₂ → ℝ) :=
  μ.map fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)

omit [Fintype k₂] [DecidableEq k₂] in
/-- The residualized FWL score has its canonical push-forward law. -/
theorem twoSLSKinalFWLScoreVector_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hScore :
      AEMeasurable
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) μ) :
    HasLaw
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) μ :=
  ⟨hScore, rfl⟩

/-- The exact theorem still missing from Mathlib/this repo.

Supplying a proof of this proposition from `TwoSLSKinalJointNormalConditions`
would complete Hansen Theorem 12.7.  It is separated from the condition package
so the package cannot hide the theorem's conclusion as an assumption. -/
def TwoSLSKinalExactMomentIff
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ) : Prop :=
  ∀ r : ℝ≥0,
    MemLp (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂

/-- Exact Kinal moment iff for the totalized FWL reduction of the endogenous
2SLS block.  This is the random inverse-Gram tail theorem that remains after
the deterministic 2SLS/FWL reductions have been applied. -/
def TwoSLSKinalFWLMomentIff
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ) : Prop :=
  ∀ r : ℝ≥0,
    MemLp (fun ω => twoSLSKinalFWLBetaStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂

/-- Coordinatewise form of the exact Kinal moment iff for the FWL coefficient.
This is equivalent to `TwoSLSKinalFWLMomentIff` by finite-product `MemLp`, but
it exposes the scalar obligations that an inverse-Wishart/Kinal tail proof has
to discharge. -/
def TwoSLSKinalFWLCoordinateMomentIff
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ) : Prop :=
  ∀ r : ℝ≥0,
    (∀ j : k₂,
      MemLp
        (fun ω => twoSLSKinalFWLBetaStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (r : ℝ≥0∞) μ) ↔
      (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂

/-- Score-coordinate form of the exact Kinal FWL moment iff.

This is deliberately lower-level than `TwoSLSKinalFWLCoordinateMomentIff`:
the scalar functions are written directly as
`(RᵀR)⁻¹ Rᵀ M y` coordinates.  A future inverse-Gram tail proof can target
this proposition without passing through any 2SLS or FWL notation. -/
def TwoSLSKinalFWLScoreCoordinateMomentIff
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ) : Prop :=
  ∀ r : ℝ≥0,
    (∀ j : k₂,
      MemLp
        (fun ω =>
          ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
            twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        (r : ℝ≥0∞) μ) ↔
      (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂

/-- The FWL vector-tail theorem is exactly its coordinatewise finite-product
form.  This turns the remaining Kinal proof obligation into scalar `MemLp`
thresholds for each endogenous coefficient coordinate. -/
theorem twoSLSKinalFWLMomentIff_iff_coordinateMomentIff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ} :
    TwoSLSKinalFWLMomentIff μ X₁ Y₂ Z₂ Y₁ ↔
      TwoSLSKinalFWLCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁ := by
  unfold TwoSLSKinalFWLMomentIff TwoSLSKinalFWLCoordinateMomentIff
  constructor
  · intro h r
    constructor
    · intro hcoord
      exact (h r).mp (MeasureTheory.MemLp.of_eval hcoord)
    · intro hlt j
      exact MeasureTheory.MemLp.eval ((h r).mpr hlt) j
  · intro h r
    constructor
    · intro hmem
      exact (h r).mp fun j => MeasureTheory.MemLp.eval hmem j
    · intro hlt
      exact MeasureTheory.MemLp.of_eval ((h r).mpr hlt)

/-- Convenience direction from coordinate scalar thresholds to the FWL vector
tail theorem. -/
theorem twoSLSKinalFWLMomentIff_of_coordinateMomentIff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hcoord : TwoSLSKinalFWLCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁) :
    TwoSLSKinalFWLMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  twoSLSKinalFWLMomentIff_iff_coordinateMomentIff.mpr hcoord

/-- Coefficient-coordinate and score-coordinate Kinal FWL moment thresholds
are the same deterministic proposition. -/
theorem twoSLSKinalFWLCoordinateMomentIff_iff_scoreCoordinateMomentIff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ} :
    TwoSLSKinalFWLCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁ ↔
      TwoSLSKinalFWLScoreCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁ := by
  unfold TwoSLSKinalFWLCoordinateMomentIff
    TwoSLSKinalFWLScoreCoordinateMomentIff
  simp [twoSLSKinalFWLBetaStar, twoSLSKinalFWLGramStar,
    twoSLSKinalFWLScoreStar]

/-- Convenience direction from lower-level score-coordinate scalar thresholds
to the FWL coefficient-coordinate thresholds. -/
theorem twoSLSKinalFWLCoordinateMomentIff_of_scoreCoordinateMomentIff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hscore : TwoSLSKinalFWLScoreCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁) :
    TwoSLSKinalFWLCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  twoSLSKinalFWLCoordinateMomentIff_iff_scoreCoordinateMomentIff.mpr hscore

/-- Lower-level score-coordinate scalar thresholds are enough to obtain the
FWL vector-tail theorem. -/
theorem twoSLSKinalFWLMomentIff_of_scoreCoordinateMomentIff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hscore : TwoSLSKinalFWLScoreCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁) :
    TwoSLSKinalFWLMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  twoSLSKinalFWLMomentIff_of_coordinateMomentIff
    (twoSLSKinalFWLCoordinateMomentIff_of_scoreCoordinateMomentIff hscore)

/-- Named Wishart-law input for the residualized fitted endogenous Gram matrix
that appears in Kinal's random-design inverse-Gram tail argument. -/
def TwoSLSKinalResidualGramWishartLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (R : Ω → Matrix n k₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ) : Prop :=
  HasLaw (fun ω => (R ω)ᵀ * R ω) (wishartLaw (n := l₂) Sigma) μ

/-- Kinal-specialized Wishart-law input for the residualized fitted endogenous
Gram matrix. -/
def TwoSLSKinalFittedResidualGramWishartLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ) : Prop :=
  TwoSLSKinalResidualGramWishartLaw (n := n) (l₂ := l₂) μ
    (fun ω => twoSLSKinalResidualizedFittedEndogenousStar (X₁ ω) (Y₂ ω) (Z₂ ω))
    Sigma

/-- Kinal fitted residual-Gram Wishart law from an explicit standardized
matrix-Gaussian representation of the same Gram matrix.

This is the Chapter 11 bridge needed before applying inverse-Wishart support:
if a standardized `ℓ₂ × k₂` Gaussian matrix has cross-product a.e. equal to the
Kinal residualized fitted-endogenous Gram matrix, Chapter 11's Wishart
cross-product theorem supplies the named Kinal Wishart field. -/
theorem twoSLSKinalFittedResidualGramWishartLaw_of_iidMatrixGaussian_gram_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ)
    (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω)) :
    TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma := by
  have hW :
      HasLaw (fun ω => matrixCrossProduct (Rstd ω))
        (wishartLaw (n := l₂) Sigma) μ :=
    matrixCrossProduct_hasLaw_wishartLaw (Y := Rstd) (Sigma := Sigma) hRstd
  simpa [TwoSLSKinalFittedResidualGramWishartLaw,
    TwoSLSKinalResidualGramWishartLaw, twoSLSKinalFWLGramStar] using
    hW.congr hGram

omit [DecidableEq k₂] in
/-- Independence of the score vector from a standardized Gaussian
cross-product transfers to independence from the Kinal fitted residual Gram
when the two Gram matrices agree a.e. -/
theorem twoSLSKinalFWLScoreStar_indep_gram_of_iidMatrixGaussian_gram_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (hInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω)) :
    (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω) :=
  IndepFun.congr hInd Filter.EventuallyEq.rfl hGram.symm

omit [DecidableEq k₂] [DecidableEq l₂] in
private theorem measurable_matrixCrossProduct_kinal :
    Measurable (fun R : Matrix l₂ k₂ ℝ => matrixCrossProduct R) := by
  have hcross :
      Continuous (fun R : Matrix l₂ k₂ ℝ => matrixCrossProduct R) := by
    change Continuous (fun R : Matrix l₂ k₂ ℝ => Rᵀ * R)
    fun_prop
  exact hcross.measurable

private def kinalMatrixOfPairCoords {ι κ : Type*}
    (v : ι × κ → ℝ) : Matrix ι κ ℝ :=
  fun i j => v (i, j)

private theorem measurable_kinalMatrixOfPairCoords
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    Measurable
      (kinalMatrixOfPairCoords (ι := ι) (κ := κ)) := by
  have hfun :
      @Measurable
        ((ι × κ) → ℝ) (ι → κ → ℝ)
        inferInstance inferInstance
        (fun v => fun (i : ι) (j : κ) => v (i, j)) := by
    fun_prop
  change
    @Measurable
      ((ι × κ) → ℝ) (Matrix ι κ ℝ)
      inferInstance (kinalMatrixBorelMeasurableSpaceInst)
      (kinalMatrixOfPairCoords (ι := ι) (κ := κ))
  exact hfun.mono le_rfl
    (kinalMatrixBorelMeasurableSpaceInst_le_pi (ι := ι) (κ := κ))

omit [DecidableEq k₂] in
/-- Joint Gaussianity of the score vector and standardized residualized matrix,
plus zero score/matrix coordinate covariances, gives the matrix-level
independence input used by Kinal's Gaussian decomposition route.

This is the raw covariance bridge behind Hansen's normal-theory argument: the
assumption is coordinatewise zero covariance for the finite Gaussian vector
`(S, Rstd)`, and Mathlib's Gaussian independence theorem supplies
`S ⟂ Rstd`. -/
theorem twoSLSKinalFWLScoreStar_indep_Rstd_of_jointGaussian_coordinate_covariance_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (hGaussian :
      HasGaussianLaw
        (fun ω =>
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω),
            fun p : l₂ × k₂ => Rstd ω p.1 p.2)) μ)
    (hCovZero : ∀ (j : k₂) (p : l₂ × k₂),
      cov[
        fun ω => twoSLSKinalFWLScoreStar
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
        fun ω => Rstd ω p.1 p.2;
        μ] = 0) :
    (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      ⟂ᵢ[μ]
      Rstd := by
  let Rcoords : Ω → l₂ × k₂ → ℝ :=
    fun ω p => Rstd ω p.1 p.2
  have hIndCoords :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rcoords :=
    hGaussian.indepFun_of_covariance_eval hCovZero
  have hIndMatrix :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => kinalMatrixOfPairCoords (Rcoords ω) := by
    simpa [kinalMatrixOfPairCoords, Function.comp_def] using
      IndepFun.comp (φ := id)
        (ψ := kinalMatrixOfPairCoords (ι := l₂) (κ := k₂))
        hIndCoords measurable_id
        (measurable_kinalMatrixOfPairCoords (ι := l₂) (κ := k₂))
  simpa [Rcoords, kinalMatrixOfPairCoords] using hIndMatrix

omit [DecidableEq k₂] in
/-- Independence of the score vector from a standardized Gaussian matrix
implies independence from the Kinal fitted residual Gram once the standardized
matrix cross-product is identified with that Gram a.e. -/
theorem twoSLSKinalFWLScoreStar_indep_gram_of_iidMatrixGaussian_matrix_indep_gram_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (hInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω)) :
    (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω) := by
  have hIndCross :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => matrixCrossProduct (Rstd ω) := by
    simpa [Function.comp_def] using
      IndepFun.comp (φ := id)
        (ψ := fun R : Matrix l₂ k₂ ℝ => matrixCrossProduct R)
        hInd measurable_id measurable_matrixCrossProduct_kinal
  exact
    twoSLSKinalFWLScoreStar_indep_gram_of_iidMatrixGaussian_gram_ae_eq
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Rstd := Rstd) hIndCross hGram

/-- Chapter 11-facing scalar inverse-Wishart laws for the residualized fitted
endogenous Gram matrix.  These laws are necessary input for Kinal's random
inverse-Gram tail theorem, but by themselves they are not Hansen Theorem 12.7:
the theorem still has to lift scalar inverse-Wishart tail behavior to the full
random coefficient vector. -/
def TwoSLSKinalResidualGramInverseWishartScalarLaws
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (R : Ω → Matrix n k₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ) : Prop :=
  ∀ α : k₂ → ℝ, α ≠ 0 →
    HasLaw
      (fun ω => inverseWishartScaledLinearForm Sigma α ((R ω)ᵀ * R ω))
      (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)) μ

omit [DecidableEq n] [DecidableEq l₂] in
/-- Kinal residual-Gram scalar laws obtained by reusing the Chapter 11
inverse-Wishart bridge.

The remaining substantive input is exactly the Chapter 11 fixed-parameter
map identity for the named `wishartLaw`; this wrapper only specializes the
degrees of freedom to Hansen's Kinal threshold `ℓ₂ - k₂ + 1`. -/
theorem twoSLSKinalResidualGramInverseWishartScalarLaws_of_chapter11_map_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (R : Ω → Matrix n k₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ)
    (hW : HasLaw (fun ω => (R ω)ᵀ * R ω)
      (wishartLaw (n := l₂) Sigma) μ)
    (hmap : ∀ α : k₂ → ℝ, α ≠ 0 →
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma α) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)) :
    TwoSLSKinalResidualGramInverseWishartScalarLaws (l₂ := l₂) μ R Sigma := by
  intro α hα
  exact inverseWishartScaledLinearForm_hasLaw_theorem11_11
    (n := l₂) (m := k₂) (W := fun ω => (R ω)ᵀ * R ω)
    (Sigma := Sigma) (α := α) hW (hmap α hα)

omit [DecidableEq n] [DecidableEq l₂] in
/-- Kinal residual-Gram scalar inverse-Wishart laws from a named residual-Gram
Wishart-law premise. -/
theorem twoSLSKinalResidualGramInverseWishartScalarLaws_of_residualGramWishartLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (R : Ω → Matrix n k₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ)
    (hW : TwoSLSKinalResidualGramWishartLaw (l₂ := l₂) μ R Sigma)
    (hmap : ∀ α : k₂ → ℝ, α ≠ 0 →
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma α) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)) :
    TwoSLSKinalResidualGramInverseWishartScalarLaws (l₂ := l₂) μ R Sigma :=
  twoSLSKinalResidualGramInverseWishartScalarLaws_of_chapter11_map_eq
    (R := R) (Sigma := Sigma) hW hmap

/-- Kinal-specialized residual-Gram scalar inverse-Wishart laws for the fitted
endogenous block.  This is the Chapter 12 endpoint that can consume the
Chapter 11 inverse-Wishart support once the residualized fitted Gram matrix is
identified as Wishart. -/
theorem twoSLSKinalFittedResidualGramInverseWishartScalarLaws_of_chapter11_map_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ)
    (hW : HasLaw
      (fun ω =>
        (twoSLSKinalResidualizedFittedEndogenousStar (X₁ ω) (Y₂ ω) (Z₂ ω))ᵀ *
          twoSLSKinalResidualizedFittedEndogenousStar (X₁ ω) (Y₂ ω) (Z₂ ω))
      (wishartLaw (n := l₂) Sigma) μ)
    (hmap : ∀ α : k₂ → ℝ, α ≠ 0 →
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma α) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)) :
    TwoSLSKinalResidualGramInverseWishartScalarLaws (n := n) (l₂ := l₂) μ
      (fun ω => twoSLSKinalResidualizedFittedEndogenousStar (X₁ ω) (Y₂ ω) (Z₂ ω))
      Sigma :=
  twoSLSKinalResidualGramInverseWishartScalarLaws_of_chapter11_map_eq
    (R := fun ω =>
      twoSLSKinalResidualizedFittedEndogenousStar (X₁ ω) (Y₂ ω) (Z₂ ω))
    (Sigma := Sigma) hW hmap

/-- Kinal-specialized scalar inverse-Wishart laws from the named fitted
residual-Gram Wishart-law premise. -/
theorem twoSLSKinalFittedResidualGramInverseWishartScalarLaws_of_residualGramWishartLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hmap : ∀ α : k₂ → ℝ, α ≠ 0 →
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma α) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)) :
    TwoSLSKinalResidualGramInverseWishartScalarLaws (n := n) (l₂ := l₂) μ
      (fun ω => twoSLSKinalResidualizedFittedEndogenousStar (X₁ ω) (Y₂ ω) (Z₂ ω))
      Sigma :=
  twoSLSKinalResidualGramInverseWishartScalarLaws_of_residualGramWishartLaw
    (R := fun ω =>
      twoSLSKinalResidualizedFittedEndogenousStar (X₁ ω) (Y₂ ω) (Z₂ ω))
    (Sigma := Sigma) hW hmap

omit [DecidableEq n] [DecidableEq l₂] in
/-- Coordinate inverse-scale laws for the residualized fitted-endogenous Gram
matrix.

This is the `α = e_j` specialization of the Chapter 11 inverse-Wishart scalar
law.  It is lower-level than the Kinal moment iff: it only identifies the
chi-square law of the inverse scale that controls the lower tail of each
coordinate variance proxy. -/
def TwoSLSKinalResidualGramCoordinateInverseScaleLaws
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (R : Ω → Matrix n k₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ) : Prop :=
  ∀ j : k₂,
    HasLaw
      (fun ω =>
        inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))
          ((R ω)ᵀ * R ω))
      (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)) μ

omit [Fintype k₂] [DecidableEq n] [DecidableEq l₂] in
private theorem kinalCoordinateVector_ne_zero (j : k₂) :
    (Pi.single j (1 : ℝ) : k₂ → ℝ) ≠ 0 := by
  intro hzero
  have hcoord := congrFun hzero j
  simp at hcoord

omit [DecidableEq n] [DecidableEq l₂] in
/-- Coordinate inverse-scale laws obtained from the all-fixed-parameter
inverse-Wishart scalar laws. -/
theorem twoSLSKinalResidualGramCoordinateInverseScaleLaws_of_scalarLaws
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (R : Ω → Matrix n k₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ)
    (hscalar :
      TwoSLSKinalResidualGramInverseWishartScalarLaws (n := n) (l₂ := l₂)
        μ R Sigma) :
    TwoSLSKinalResidualGramCoordinateInverseScaleLaws (l₂ := l₂)
      μ R Sigma := by
  intro j
  exact hscalar (Pi.single j (1 : ℝ)) (kinalCoordinateVector_ne_zero j)

/-- Kinal-specialized coordinate inverse-scale laws from the residual-Gram
Wishart law and Chapter 11's fixed-parameter inverse-Wishart map identities. -/
theorem twoSLSKinalFittedResidualGramCoordinateInverseScaleLaws_of_residualGramWishartLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hmap : ∀ α : k₂ → ℝ, α ≠ 0 →
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma α) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)) :
    TwoSLSKinalResidualGramCoordinateInverseScaleLaws (n := n) (l₂ := l₂)
      μ
      (fun ω => twoSLSKinalResidualizedFittedEndogenousStar (X₁ ω) (Y₂ ω) (Z₂ ω))
      Sigma :=
  twoSLSKinalResidualGramCoordinateInverseScaleLaws_of_scalarLaws
    (R := fun ω =>
      twoSLSKinalResidualizedFittedEndogenousStar (X₁ ω) (Y₂ ω) (Z₂ ω))
    (Sigma := Sigma)
    (twoSLSKinalFittedResidualGramInverseWishartScalarLaws_of_residualGramWishartLaw
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Sigma := Sigma) hW hmap)

/-- Score-aligned inverse-Wishart chi-square law for Kinal's residualized
Gram matrix.

For a random score direction `S`, this names the law of
`(S'Σ⁻¹S) * (S'(R'R)⁻¹S)⁻¹`.  It is a law-level ingredient for the eventual
score-coordinate tail theorem, not a `MemLp` threshold assumption. -/
def TwoSLSKinalScoreAlignedInverseWishartLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (R : Ω → Matrix n k₂ ℝ) (S : Ω → k₂ → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ) : Prop :=
  HasLaw
    (fun ω =>
      inverseWishartScaledLinearForm Sigma (S ω) ((R ω)ᵀ * R ω))
    (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)) μ

/-- Kinal-specialized score-aligned inverse-Wishart chi-square law for the FWL
score `RᵀMy`. -/
def TwoSLSKinalFWLScoreAlignedInverseWishartLaw
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ) : Prop :=
  TwoSLSKinalScoreAlignedInverseWishartLaw (n := n) (l₂ := l₂) μ
    (fun ω => twoSLSKinalResidualizedFittedEndogenousStar (X₁ ω) (Y₂ ω) (Z₂ ω))
    (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
    Sigma

omit [DecidableEq n] [DecidableEq l₂] in
/-- Random-score inverse-Wishart law from residual-Gram Wishart, independence,
and Chapter 11 fixed-parameter map identities.

This is the Kinal analogue of the random-parameter bridge used for Hotelling's
Theorem 11.12.  The assumptions are strictly below the final Kinal moment iff:
they give a Wishart law for `RᵀR`, a law and a.s. nondegeneracy for the score
direction, independence between score and Gram, and the fixed-parameter
Chapter 11 push-forward identities. -/
theorem twoSLSKinalScoreAlignedInverseWishartLaw_of_residualGramWishartLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (R : Ω → Matrix n k₂ ℝ) (S : Ω → k₂ → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ) (Slaw : Measure (k₂ → ℝ))
    [SFinite (wishartLaw (n := l₂) Sigma)] [IsProbabilityMeasure Slaw]
    (hS : HasLaw S Slaw μ)
    (hW : TwoSLSKinalResidualGramWishartLaw (l₂ := l₂) μ R Sigma)
    (hInd : S ⟂ᵢ[μ] fun ω => (R ω)ᵀ * R ω)
    (hS_ne : ∀ᵐ α ∂Slaw, α ≠ 0)
    (hmap : ∀ α : k₂ → ℝ, α ≠ 0 →
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma α) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)) :
    TwoSLSKinalScoreAlignedInverseWishartLaw (l₂ := l₂)
      μ R S Sigma := by
  have hfixed :
      ∀ᵐ α ∂Slaw,
        (wishartLaw (n := l₂) Sigma).map
            (inverseWishartScaledLinearForm Sigma α) =
          chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1) :=
    hS_ne.mono fun α hα => hmap α hα
  exact
    inverseWishartScaledLinearForm_hasLaw_of_indep_random_parameter_ae
      (A := S) (W := fun ω => (R ω)ᵀ * R ω)
      (Alaw := Slaw) (Wlaw := wishartLaw (n := l₂) Sigma)
      (Sigma := Sigma)
      (df := Fintype.card l₂ - Fintype.card k₂ + 1)
      hS (by simpa [TwoSLSKinalResidualGramWishartLaw] using hW) hInd hfixed

/-- Kinal FWL score-aligned inverse-Wishart law from the fitted residual-Gram
Wishart law, score/Gram independence, and Chapter 11 fixed-parameter map
identities. -/
theorem twoSLSKinalFWLScoreAlignedInverseWishartLaw_of_residualGramWishartLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ) (ScoreLaw : Measure (k₂ → ℝ))
    [SFinite (wishartLaw (n := l₂) Sigma)] [IsProbabilityMeasure ScoreLaw]
    (hScore :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreLaw μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
    (hScore_ne : ∀ᵐ α ∂ScoreLaw, α ≠ 0)
    (hmap : ∀ α : k₂ → ℝ, α ≠ 0 →
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma α) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)) :
    TwoSLSKinalFWLScoreAlignedInverseWishartLaw (n := n) (l₂ := l₂)
      μ X₁ Y₂ Z₂ Y₁ Sigma := by
  refine
    twoSLSKinalScoreAlignedInverseWishartLaw_of_residualGramWishartLaw
      (R := fun ω =>
        twoSLSKinalResidualizedFittedEndogenousStar (X₁ ω) (Y₂ ω) (Z₂ ω))
      (S := fun ω =>
        twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      (Sigma := Sigma) (Slaw := ScoreLaw)
      hScore ?_ ?_ hScore_ne hmap
  · simpa [TwoSLSKinalFittedResidualGramWishartLaw] using hW
  · simpa [twoSLSKinalFWLGramStar] using hInd

/-- Coordinate inverse-scale statistic for the residualized fitted-endogenous
Gram matrix.  For coordinate `j` this is Hansen's scaled inverse-Wishart
linear form with `α = e_j`. -/
noncomputable def twoSLSKinalFWLCoordinateInverseScaleStar
    (X₁ : Matrix n k₁ ℝ) (Y₂ : Matrix n k₂ ℝ)
    (Z₂ : Matrix n l₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ) (j : k₂) : ℝ :=
  inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))
    (twoSLSKinalFWLGramStar X₁ Y₂ Z₂)

/-- Kinal-specialized coordinate inverse-scale laws for the residualized
fitted-endogenous Gram matrix. -/
def TwoSLSKinalFWLCoordinateInverseScaleLaws
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ) : Prop :=
  TwoSLSKinalResidualGramCoordinateInverseScaleLaws (n := n) (l₂ := l₂) μ
    (fun ω => twoSLSKinalResidualizedFittedEndogenousStar (X₁ ω) (Y₂ ω) (Z₂ ω))
    Sigma

/-- The named coordinate inverse-scale law has the chi-square law supplied by
the residual-Gram coordinate inverse-scale package. -/
theorem twoSLSKinalFWLCoordinateInverseScaleStar_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ)
    (h :
      TwoSLSKinalFWLCoordinateInverseScaleLaws (n := n) (l₂ := l₂)
        μ X₁ Y₂ Z₂ Sigma)
    (j : k₂) :
    HasLaw
      (fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
      (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)) μ := by
  simpa [TwoSLSKinalFWLCoordinateInverseScaleLaws,
    twoSLSKinalFWLCoordinateInverseScaleStar, twoSLSKinalFWLGramStar] using h j

/-- Kinal FWL coordinate inverse-scale laws from the residualized fitted-Gram
Wishart law and coordinate Schur-complement map identities.

Compared with the all-`α` inverse-Wishart scalar-law interface above, this
wrapper asks only for the coordinate identities actually used by the current
Kinal product-tail reduction. -/
theorem twoSLSKinalFWLCoordinateInverseScaleLaws_of_coordinate_map_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hmap : ∀ j : k₂,
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)) :
    TwoSLSKinalFWLCoordinateInverseScaleLaws (n := n) (l₂ := l₂)
      μ X₁ Y₂ Z₂ Sigma := by
  intro j
  exact
    inverseWishartScaledLinearForm_hasLaw_theorem11_11
      (n := l₂)
      (W := fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
      (Sigma := Sigma) (α := Pi.single j (1 : ℝ))
      (by
        simpa [TwoSLSKinalFittedResidualGramWishartLaw,
          TwoSLSKinalResidualGramWishartLaw, twoSLSKinalFWLGramStar] using hW)
      (hmap j)

/-- Standard-coordinate whitening/alignment bridge for Kinal's coordinate
inverse-Wishart map identities.

For each endogenous coordinate `j`, the bridge gives a type-changing
whitening map to the Chapter 11 standard-coordinate split, aligns `e_j` with
the first standardized coordinate up to a nonzero scale, and supplies the
nonsingularity inputs needed by the Chapter 11 Theorem 11.11 endpoint.  This is
strictly narrower than assuming the raw push-forward identity
`wishartLaw.map ... = chiSquared ...` for each coordinate. -/
structure TwoSLSKinalCoordinateInverseWishartWhiteningBridge
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ)
    (S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ)
    (c : k₂ → ℝ) : Prop where
  /-- The residual-Gram scale matrix is positive definite. -/
  sigma_posDef : Sigma.PosDef
  /-- Standard-coordinate residual blocks have fewer columns than Wishart
  degrees of freedom. -/
  card_lt : ∀ j : k₂, Fintype.card (rIdx j) < Fintype.card l₂
  /-- Chapter 11 standard-coordinate nonsingularity input. -/
  standard_coordinate_nonsingular : ∀ j : k₂,
    ∀ᵐ Y ∂iidMatrixGaussianLaw (n := l₂) (m := Sum Unit (rIdx j))
        (0 : Sum Unit (rIdx j) → ℝ)
        (1 : Matrix (Sum Unit (rIdx j)) (Sum Unit (rIdx j)) ℝ),
      Nonempty (Invertible (matrixCrossProduct Y)) ∧
        Nonempty (Invertible
          ((standardCoordinateRestColumns (n := l₂) Y)ᵀ *
            standardCoordinateRestColumns (n := l₂) Y))
  /-- The standardized residual dimension gives Hansen's Kinal degrees of
  freedom `ℓ₂ - k₂ + 1`. -/
  df_eq : ∀ j : k₂,
    Fintype.card l₂ - Fintype.card (Sum Unit (rIdx j)) + 1 =
      Fintype.card l₂ - Fintype.card k₂ + 1
  /-- Left inverse for the coordinate transform. -/
  left_inverse : ∀ j : k₂, S j * T j = 1
  /-- Right inverse for the coordinate transform. -/
  right_inverse : ∀ j : k₂, T j * S j = 1
  /-- Original Wishart draws are nonsingular a.s. -/
  wishart_nonsingular :
    ∀ᵐ W ∂wishartLaw (n := l₂) Sigma, IsUnit W.det
  /-- The coordinate transform whitens `Σ`. -/
  sigma_whiten : ∀ j : k₂,
    (T j)ᵀ * Sigma * T j =
      (1 : Matrix (Sum Unit (rIdx j)) (Sum Unit (rIdx j)) ℝ)
  /-- The coordinate transform aligns `e_j` with the first standardized
  coordinate up to the nonzero scale `c j`. -/
  alpha_align : ∀ j : k₂,
    (T j)ᵀ *ᵥ (Pi.single j (1 : ℝ) : k₂ → ℝ) =
      c j • (Pi.single (Sum.inl ()) (1 : ℝ) :
        Sum Unit (rIdx j) → ℝ)
  /-- The coordinate-alignment scale is nonzero. -/
  scale_ne : ∀ j : k₂, c j ≠ 0

/-- Nuisance-only standard-coordinate whitening/alignment bridge for Kinal's
coordinate inverse-Wishart map identities.

This is a thinner version of
`TwoSLSKinalCoordinateInverseWishartWhiteningBridge`: Chapter 11 now derives
the full standardized Gram nonsingularity and original Wishart nonsingularity
from nuisance-column Gram nonsingularity, so the Kinal-facing bridge only keeps
that remaining raw Gaussian rank certificate. -/
structure TwoSLSKinalCoordinateInverseWishartNuisanceWhiteningBridge
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ)
    (S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ)
    (c : k₂ → ℝ) : Prop where
  /-- The residual-Gram scale matrix is positive definite. -/
  sigma_posDef : Sigma.PosDef
  /-- Standard-coordinate residual blocks have fewer columns than Wishart
  degrees of freedom. -/
  card_lt : ∀ j : k₂, Fintype.card (rIdx j) < Fintype.card l₂
  /-- Chapter 11 standard-coordinate nuisance-Gram nonsingularity input. -/
  standard_coordinate_nuisance_nonsingular : ∀ j : k₂,
    ∀ᵐ Y ∂iidMatrixGaussianLaw (n := l₂) (m := Sum Unit (rIdx j))
        (0 : Sum Unit (rIdx j) → ℝ)
        (1 : Matrix (Sum Unit (rIdx j)) (Sum Unit (rIdx j)) ℝ),
      Nonempty (Invertible
        ((standardCoordinateRestColumns (n := l₂) Y)ᵀ *
          standardCoordinateRestColumns (n := l₂) Y))
  /-- The standardized residual dimension gives Hansen's Kinal degrees of
  freedom `ℓ₂ - k₂ + 1`. -/
  df_eq : ∀ j : k₂,
    Fintype.card l₂ - Fintype.card (Sum Unit (rIdx j)) + 1 =
      Fintype.card l₂ - Fintype.card k₂ + 1
  /-- Left inverse for the coordinate transform. -/
  left_inverse : ∀ j : k₂, S j * T j = 1
  /-- Right inverse for the coordinate transform. -/
  right_inverse : ∀ j : k₂, T j * S j = 1
  /-- The coordinate transform whitens `Σ`. -/
  sigma_whiten : ∀ j : k₂,
    (T j)ᵀ * Sigma * T j =
      (1 : Matrix (Sum Unit (rIdx j)) (Sum Unit (rIdx j)) ℝ)
  /-- The coordinate transform aligns `e_j` with the first standardized
  coordinate up to the nonzero scale `c j`. -/
  alpha_align : ∀ j : k₂,
    (T j)ᵀ *ᵥ (Pi.single j (1 : ℝ) : k₂ → ℝ) =
      c j • (Pi.single (Sum.inl ()) (1 : ℝ) :
        Sum Unit (rIdx j) → ℝ)
  /-- The coordinate-alignment scale is nonzero. -/
  scale_ne : ∀ j : k₂, c j ≠ 0

/-- Standard-Gram version of the Kinal coordinate inverse-Wishart whitening
bridge.

This is the closest Kinal-facing interface to the completed Chapter 11
standard-coordinate boundary.  Instead of asking directly for nuisance
rest-column nonsingularity under the `1 + r` standard-coordinate law, it asks
for the canonical rectangular iid standard-Gaussian Gram certificate on
`ℓ₂ × r`, plus existential whitening/alignment data for each coordinate. -/
structure TwoSLSKinalCoordinateInverseWishartStandardGramBridge
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)] : Prop where
  /-- The residual-Gram scale matrix is positive definite. -/
  sigma_posDef : Sigma.PosDef
  /-- The standard-coordinate nuisance block has fewer rows than Wishart
  degrees of freedom. -/
  card_lt : ∀ j : k₂, Fintype.card (rIdx j) < Fintype.card l₂
  /-- The standard-coordinate split has the same total dimension as `k₂`. -/
  card_dim : ∀ j : k₂,
    Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂
  /-- Canonical rectangular iid standard-Gaussian Gram nonsingularity. -/
  standard_gram_nonsingular : ∀ j : k₂,
    ∀ᵐ Z ∂iidMatrixGaussianLaw (n := l₂) (m := rIdx j)
        (0 : rIdx j → ℝ) (1 : Matrix (rIdx j) (rIdx j) ℝ),
      Nonempty (Invertible (matrixCrossProduct Z))
  /-- Existential whitening/alignment data for the coordinate direction. -/
  whitening_exists : ∀ j : k₂,
    ∃ (T : Matrix k₂ (Sum Unit (rIdx j)) ℝ)
      (S : Matrix (Sum Unit (rIdx j)) k₂ ℝ) (c : ℝ),
      S * T = 1 ∧ T * S = 1 ∧
        Tᵀ * Sigma * T =
          (1 : Matrix (Sum Unit (rIdx j)) (Sum Unit (rIdx j)) ℝ) ∧
        Tᵀ *ᵥ (Pi.single j (1 : ℝ) : k₂ → ℝ) =
          c • (Pi.single (Sum.inl ()) (1 : ℝ) :
            Sum Unit (rIdx j) → ℝ) ∧
        c ≠ 0

omit [Fintype n] [DecidableEq n] [Fintype k₁] [DecidableEq k₁]
    [Fintype l₂] [DecidableEq l₂] in
/-- Canonical nuisance-coordinate family for the standard-coordinate split:
all endogenous coordinates except the distinguished coordinate `j`. -/
abbrev kinalCoordinateRestIdx (j : k₂) : Type _ :=
  {i : k₂ // i ≠ j}

omit [Fintype n] [DecidableEq n] [Fintype k₁] [DecidableEq k₁]
    [Fintype l₂] [DecidableEq l₂] in
/-- The canonical split `Unit ⊕ {i // i ≠ j}` has exactly the endogenous
dimension. -/
theorem kinalCoordinateRestIdx_card_dim (j : k₂) :
    Fintype.card (Sum Unit (kinalCoordinateRestIdx j)) = Fintype.card k₂ := by
  classical
  rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_subtype]
  have hfilter :
      Finset.univ.filter (fun i : k₂ => i ≠ j) = Finset.univ.erase j := by
    ext i
    simp
  rw [hfilter, Finset.card_erase_of_mem]
  · rw [Finset.card_univ]
    have hpos : 0 < Fintype.card k₂ := Fintype.card_pos_iff.mpr ⟨j⟩
    omega
  · simp

omit [DecidableEq k₂] [DecidableEq l₂] in
private theorem kinal_rest_card_lt_of_sum_card_eq
    {r : Type*} [Fintype r]
    (hcard_dim : Fintype.card (Sum Unit r) = Fintype.card k₂)
    (hinstr : Fintype.card k₂ ≤ Fintype.card l₂) :
    Fintype.card r < Fintype.card l₂ := by
  have hrest_lt : Fintype.card r < Fintype.card k₂ := by
    rw [← hcard_dim]
    simp [Fintype.card_sum]
  exact lt_of_lt_of_le hrest_lt hinstr

omit [DecidableEq l₂] in
/-- Standard-Gram inverse-Wishart bridge from the concrete deterministic data
that Hansen's Kinal proof needs.

This wrapper reuses Chapter 11 twice: canonical rectangular standard-Gaussian
Gram nonsingularity supplies the stochastic rank field, and
`standardCoordinate_whitening_alignment_exists_of_posDef` supplies the
coordinate whitening/alignment data from `Σ.PosDef`.  Thus Kinal callers only
need the residual-Gram scale to be positive definite and the coordinate split
to have the same dimension as the endogenous block. -/
theorem TwoSLSKinalCoordinateInverseWishartStandardGramBridge.of_posDef_cardDim
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (hSigma : Sigma.PosDef)
    (hinstr : Fintype.card k₂ ≤ Fintype.card l₂)
    (hcard_dim : ∀ j : k₂,
      Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂) :
    TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
      Sigma (rIdx := rIdx) where
  sigma_posDef := hSigma
  card_lt := fun j =>
    kinal_rest_card_lt_of_sum_card_eq
      (k₂ := k₂) (l₂ := l₂) (hcard_dim j) hinstr
  card_dim := hcard_dim
  standard_gram_nonsingular := fun j =>
    iidMatrixGaussianLaw_standard_crossProduct_nonsingular_ae
      (n := l₂) (r := rIdx j)
      (Nat.le_of_lt
        (kinal_rest_card_lt_of_sum_card_eq
          (k₂ := k₂) (l₂ := l₂) (hcard_dim j) hinstr))
  whitening_exists := fun j => by
    have hsingle_ne :
        (Pi.single j (1 : ℝ) : k₂ → ℝ) ≠ 0 := by
      intro hzero
      have hcoord := congr_fun hzero j
      simp at hcoord
    exact
      standardCoordinate_whitening_alignment_exists_of_posDef
        (m := k₂) (r := rIdx j)
        Sigma (Pi.single j (1 : ℝ)) hSigma hsingle_ne
        (hcard_dim j)

omit [DecidableEq l₂] in
/-- Standard-Gram inverse-Wishart bridge using the canonical rest-coordinate
split, so callers do not have to provide the bookkeeping cardinality premise
`card (Unit ⊕ rest_j) = card k₂`. -/
theorem
    TwoSLSKinalCoordinateInverseWishartStandardGramBridge.of_posDef_canonicalRest
    (Sigma : Matrix k₂ k₂ ℝ)
    (hSigma : Sigma.PosDef)
    (hinstr : Fintype.card k₂ ≤ Fintype.card l₂) :
    TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
      Sigma (rIdx := fun j : k₂ => kinalCoordinateRestIdx j) :=
  TwoSLSKinalCoordinateInverseWishartStandardGramBridge.of_posDef_cardDim
    (l₂ := l₂) Sigma hSigma hinstr
    (fun j => kinalCoordinateRestIdx_card_dim (k₂ := k₂) j)

set_option linter.style.longLine false

omit [DecidableEq l₂] in
/-- Coordinate inverse-Wishart map identity from Chapter 11 standard-coordinate
whitening data. -/
theorem twoSLSKinalCoordinateInverseScale_map_eq_of_standardCoordinate_whitening
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ)
    (S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ)
    (c : k₂ → ℝ)
    (h :
      TwoSLSKinalCoordinateInverseWishartWhiteningBridge (l₂ := l₂)
        Sigma T S c)
    (j : k₂) :
    (wishartLaw (n := l₂) Sigma).map
        (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
      chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1) := by
  classical
  exact
    inverseWishartScaledLinearForm_wishartLaw_map_eq_chiSquared_of_standardCoordinate_whitening_transport
      (dfidx := l₂) (r := rIdx j) (m := k₂)
      (Sigma := Sigma) (α := Pi.single j (1 : ℝ))
      (df := Fintype.card l₂ - Fintype.card k₂ + 1)
      (T := T j) (S := S j) (c := c j)
      h.sigma_posDef (h.card_lt j)
      (h.standard_coordinate_nonsingular j) (h.df_eq j)
      (h.left_inverse j) (h.right_inverse j)
      h.wishart_nonsingular (h.sigma_whiten j)
      (h.alpha_align j) (h.scale_ne j)

omit [DecidableEq l₂] in
/-- Coordinate inverse-Wishart map identity from Chapter 11 nuisance-only
standard-coordinate whitening data. -/
theorem twoSLSKinalCoordinateInverseScale_map_eq_of_standardCoordinate_nuisance_whitening
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ)
    (S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ)
    (c : k₂ → ℝ)
    (h :
      TwoSLSKinalCoordinateInverseWishartNuisanceWhiteningBridge (l₂ := l₂)
        Sigma T S c)
    (j : k₂) :
    (wishartLaw (n := l₂) Sigma).map
        (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
      chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1) := by
  classical
  exact
    inverseWishartScaledLinearForm_wishartLaw_map_eq_chiSquared_of_standardCoordinate_whitening_transport_of_standard_nuisance_nonsingular
      (dfidx := l₂) (r := rIdx j) (m := k₂)
      (Sigma := Sigma) (α := Pi.single j (1 : ℝ))
      (df := Fintype.card l₂ - Fintype.card k₂ + 1)
      (T := T j) (S := S j) (c := c j)
      h.sigma_posDef (h.card_lt j)
      (h.standard_coordinate_nuisance_nonsingular j) (h.df_eq j)
      (h.left_inverse j) (h.right_inverse j)
      (h.sigma_whiten j) (h.alpha_align j) (h.scale_ne j)

omit [DecidableEq l₂] in
/-- Coordinate inverse-Wishart map identity from Chapter 11's
standard-Gram/existential-whitening endpoint.

This wrapper reuses
`inverseWishartScaledLinearForm_wishartLaw_map_eq_chiSquared_of_standardCoordinate_whitening_exists_card_eq_of_standard_gram_nonsingular`
so Kinal callers can provide the canonical rectangular standard-Gaussian Gram
certificate rather than the rest-column nuisance certificate. -/
theorem twoSLSKinalCoordinateInverseScale_map_eq_of_standardGramBridge
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (h :
      TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
        Sigma (rIdx := rIdx))
    (j : k₂) :
    (wishartLaw (n := l₂) Sigma).map
        (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
      chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1) := by
  classical
  exact
    inverseWishartScaledLinearForm_wishartLaw_map_eq_chiSquared_of_standardCoordinate_whitening_exists_card_eq_of_standard_gram_nonsingular
      (dfidx := l₂) (r := rIdx j) (m := k₂)
      (Sigma := Sigma) (α := Pi.single j (1 : ℝ))
      h.sigma_posDef (h.card_lt j) (h.card_dim j)
      (h.standard_gram_nonsingular j) (h.whitening_exists j)

omit [DecidableEq l₂] in
/-- Coordinate inverse-Wishart map identity from positive definiteness and the
canonical standard-Gram bridge. -/
theorem twoSLSKinalCoordinateInverseScale_map_eq_of_posDef_cardDim
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    (hSigma : Sigma.PosDef)
    (hinstr : Fintype.card k₂ ≤ Fintype.card l₂)
    (hcard_dim : ∀ j : k₂,
      Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂)
    (j : k₂) :
    (wishartLaw (n := l₂) Sigma).map
        (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
      chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1) := by
  classical
  exact
    twoSLSKinalCoordinateInverseScale_map_eq_of_standardGramBridge
      (l₂ := l₂) Sigma
      (TwoSLSKinalCoordinateInverseWishartStandardGramBridge.of_posDef_cardDim
        (l₂ := l₂) Sigma hSigma hinstr hcard_dim)
      j

set_option linter.style.longLine true

/-- Kinal FWL coordinate inverse-scale laws from the residualized fitted-Gram
Wishart law and Chapter 11 standard-coordinate whitening data. -/
theorem twoSLSKinalFWLCoordinateInverseScaleLaws_of_standardCoordinate_whitening
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ)
    (S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ)
    (c : k₂ → ℝ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartWhiteningBridge (l₂ := l₂)
        Sigma T S c) :
    TwoSLSKinalFWLCoordinateInverseScaleLaws (n := n) (l₂ := l₂)
      μ X₁ Y₂ Z₂ Sigma :=
  twoSLSKinalFWLCoordinateInverseScaleLaws_of_coordinate_map_eq
    X₁ Y₂ Z₂ Sigma hW
    (fun j =>
      twoSLSKinalCoordinateInverseScale_map_eq_of_standardCoordinate_whitening
        (l₂ := l₂) Sigma T S c hBridge j)

/-- Kinal FWL coordinate inverse-scale laws from residualized fitted-Gram
Wishart and Chapter 11 nuisance-only standard-coordinate whitening data. -/
theorem twoSLSKinalFWLCoordinateInverseScaleLaws_of_standardCoordinate_nuisance_whitening
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ)
    (S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ)
    (c : k₂ → ℝ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartNuisanceWhiteningBridge (l₂ := l₂)
        Sigma T S c) :
    TwoSLSKinalFWLCoordinateInverseScaleLaws (n := n) (l₂ := l₂)
      μ X₁ Y₂ Z₂ Sigma :=
  twoSLSKinalFWLCoordinateInverseScaleLaws_of_coordinate_map_eq
    X₁ Y₂ Z₂ Sigma hW
    (fun j =>
      twoSLSKinalCoordinateInverseScale_map_eq_of_standardCoordinate_nuisance_whitening
        (l₂ := l₂) Sigma T S c hBridge j)

/-- Kinal FWL coordinate inverse-scale laws from residualized fitted-Gram
Wishart and Chapter 11 standard-Gram/existential-whitening data. -/
theorem twoSLSKinalFWLCoordinateInverseScaleLaws_of_standardGramBridge
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
        Sigma (rIdx := rIdx)) :
    TwoSLSKinalFWLCoordinateInverseScaleLaws (n := n) (l₂ := l₂)
      μ X₁ Y₂ Z₂ Sigma :=
  twoSLSKinalFWLCoordinateInverseScaleLaws_of_coordinate_map_eq
    X₁ Y₂ Z₂ Sigma hW
    (fun j =>
      twoSLSKinalCoordinateInverseScale_map_eq_of_standardGramBridge
        (l₂ := l₂) Sigma hBridge j)

/-- Kinal FWL coordinate inverse-scale laws from positive definiteness, Hansen's
instrument-count order condition, and the coordinate dimension split. -/
theorem twoSLSKinalFWLCoordinateInverseScaleLaws_of_posDef_cardDim
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hSigma : Sigma.PosDef)
    (hinstr : Fintype.card k₂ ≤ Fintype.card l₂)
    (hcard_dim : ∀ j : k₂,
      Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂) :
    TwoSLSKinalFWLCoordinateInverseScaleLaws (n := n) (l₂ := l₂)
      μ X₁ Y₂ Z₂ Sigma := by
  classical
  exact
    twoSLSKinalFWLCoordinateInverseScaleLaws_of_coordinate_map_eq
      X₁ Y₂ Z₂ Sigma hW
      (fun j =>
        twoSLSKinalCoordinateInverseScale_map_eq_of_posDef_cardDim
          (l₂ := l₂) Sigma hSigma hinstr hcard_dim j)

private theorem real_memLp_iff_memLp_id_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ν : Measure ℝ}
    {X : Ω → ℝ} {p : ℝ≥0∞} (hX : HasLaw X ν μ) :
    MemLp X p μ ↔ MemLp (fun x : ℝ => x) p ν := by
  rw [← hX.map_eq]
  simpa [Function.comp_def] using
    (memLp_map_measure_iff
      (g := fun x : ℝ => x) (f := X)
      aestronglyMeasurable_id hX.aemeasurable).symm

private theorem real_memLp_iff_memLp_map_of_hasLaw
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} {ν : Measure α} {X : Ω → ℝ}
    {F : α → ℝ} {p : ℝ≥0∞}
    (hX : HasLaw X (ν.map F) μ) (hF : AEMeasurable F ν) :
    MemLp X p μ ↔ MemLp F p ν := by
  exact (real_memLp_iff_memLp_id_of_hasLaw hX).trans
    (by
      simpa [Function.comp_def] using
        memLp_map_measure_iff
          (g := fun x : ℝ => x) (f := F)
          aestronglyMeasurable_id hF)

private theorem hasLaw_map_of_indepFun_pair
    {Ω α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω}
    [IsFiniteMeasure μ] {A : Ω → α} {B : Ω → β}
    {Alaw : Measure α} {Blaw : Measure β} {F : α × β → γ}
    (hA : HasLaw A Alaw μ) (hB : HasLaw B Blaw μ)
    (hInd : A ⟂ᵢ[μ] B) (hF : AEMeasurable F (Alaw.prod Blaw)) :
    HasLaw (fun ω => F (A ω, B ω)) ((Alaw.prod Blaw).map F) μ := by
  have hPair :
      HasLaw (fun ω => (A ω, B ω)) (Alaw.prod Blaw) μ := by
    refine ⟨hA.aemeasurable.prodMk hB.aemeasurable, ?_⟩
    rw [(indepFun_iff_map_prod_eq_prod_map_map
      hA.aemeasurable hB.aemeasurable).1 hInd, hA.map_eq, hB.map_eq]
  let hMap : HasLaw F ((Alaw.prod Blaw).map F) (Alaw.prod Blaw) :=
    ⟨hF, rfl⟩
  simpa [Function.comp_def] using hMap.comp hPair

omit [Fintype k₂] [DecidableEq k₂] in
/-- A vector law for the Kinal FWL score supplies all coordinate score laws
used by the scalar product-tail reduction. -/
theorem twoSLSKinalFWLScoreCoordinateLaws_of_scoreVectorLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (ScoreVectorLaw : Measure (k₂ → ℝ))
    (hScoreVector :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreVectorLaw μ) :
    ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreVectorLaw.map fun s : k₂ → ℝ => s j) μ := by
  intro j
  let evalJ : (k₂ → ℝ) → ℝ := fun s => s j
  have hEval : HasLaw evalJ (ScoreVectorLaw.map evalJ) ScoreVectorLaw :=
    ⟨(measurable_pi_apply j).aemeasurable, rfl⟩
  simpa [evalJ, Function.comp_def] using hEval.comp hScoreVector

/-- Full score-vector/Gram independence implies the coordinate
score/inverse-scale independence required by Kinal's scalar product-tail
route, once Chapter 11 has identified the fixed coordinate inverse-Wishart
push-forward law. -/
theorem twoSLSKinalFWLScoreCoordinate_indep_coordinateInverseScale_of_scoreVector_indep_gram
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ) (ScoreVectorLaw : Measure (k₂ → ℝ))
    [SFinite (wishartLaw (n := l₂) Sigma)]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hScoreVector :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreVectorLaw μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hScoreGramInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
    (hScaleMap : ∀ j : k₂,
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)) :
    ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j := by
  intro j
  let evalJ : (k₂ → ℝ) → ℝ := fun s => s j
  let scaleJ : Matrix k₂ k₂ ℝ → ℝ :=
    inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))
  have hScoreCoord :
      HasLaw
        (fun ω =>
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreVectorLaw.map evalJ) μ := by
    simpa [evalJ] using
      twoSLSKinalFWLScoreCoordinateLaws_of_scoreVectorLaw
        (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
        (ScoreVectorLaw := ScoreVectorLaw) hScoreVector j
  haveI : IsProbabilityMeasure (ScoreVectorLaw.map evalJ) :=
    (hScoreCoord.isProbabilityMeasure_iff).1 inferInstance
  have hGramLaw :
      HasLaw
        (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        (wishartLaw (n := l₂) Sigma) μ := by
    simpa [TwoSLSKinalFittedResidualGramWishartLaw,
      TwoSLSKinalResidualGramWishartLaw, twoSLSKinalFWLGramStar] using hW
  have hScaleAE :
      AEMeasurable scaleJ (wishartLaw (n := l₂) Sigma) := by
    have hId :
        HasLaw (fun W : Matrix k₂ k₂ ℝ => W)
          (wishartLaw (n := l₂) Sigma)
          (wishartLaw (n := l₂) Sigma) :=
      HasLaw.id
    exact
      (inverseWishartScaledLinearForm_hasLaw_map
        (W := fun W : Matrix k₂ k₂ ℝ => W)
        (Wlaw := wishartLaw (n := l₂) Sigma)
        (Sigma := Sigma) (α := Pi.single j (1 : ℝ)) hId).aemeasurable
  have hF :
      AEMeasurable
        (fun z : ℝ × Matrix k₂ k₂ ℝ => scaleJ z.2)
        ((ScoreVectorLaw.map evalJ).prod (wishartLaw (n := l₂) Sigma)) :=
    by
      have hSnd :
          (((ScoreVectorLaw.map evalJ).prod
              (wishartLaw (n := l₂) Sigma)).map Prod.snd) =
            wishartLaw (n := l₂) Sigma := by
        rw [Measure.map_snd_prod]
        simp
      have hScaleAE' :
          AEMeasurable scaleJ
            (((ScoreVectorLaw.map evalJ).prod
              (wishartLaw (n := l₂) Sigma)).map Prod.snd) := by
        simpa [hSnd] using hScaleAE
      exact hScaleAE'.comp_aemeasurable measurable_snd.aemeasurable
  have hFixed :
      ∀ᵐ _a ∂ScoreVectorLaw.map evalJ,
        (wishartLaw (n := l₂) Sigma).map
            (fun W : Matrix k₂ k₂ ℝ => scaleJ W) =
          chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1) :=
    ae_of_all _ fun _ => by
      simpa [scaleJ] using hScaleMap j
  have hScoreCoordGramInd :
      (fun ω =>
        twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω) := by
    simpa [evalJ, Function.comp_def] using
      IndepFun.comp (φ := evalJ) (ψ := id) hScoreGramInd
        (measurable_pi_apply j) measurable_id
  simpa [twoSLSKinalFWLCoordinateInverseScaleStar, scaleJ] using
    indepFun_of_indepFun_ae_fixed_map_eq_ae
      (F := fun z : ℝ × Matrix k₂ k₂ ℝ => scaleJ z.2)
      hScoreCoord hGramLaw hScoreCoordGramInd hF
      (fun _ => hScaleAE) hFixed

/-- Score-coordinate laws are probability laws once the Kinal joint-normal
condition supplies a probability source measure. -/
theorem twoSLSKinal_scoreLaw_isProbabilityMeasure_of_jointNormalConditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {ScoreLaw : k₂ → Measure ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ) :
    ∀ j : k₂, IsProbabilityMeasure (ScoreLaw j) := by
  intro j
  haveI : IsProbabilityMeasure μ := h.joint_gaussian.isProbabilityMeasure
  exact (hScoreLaw j).isProbabilityMeasure_iff.1 inferInstance

/-- Lower-level scalar product-tail theorem for Kinal's coefficient
coordinates.

For each coordinate `j`, `coordMap j` is the scalar model obtained after
reducing the coefficient coordinate to a function of an independent score
coordinate and its chi-square inverse-scale statistic.  Proving this
proposition is an analytic inverse-chi-square/Gaussian product calculation;
it is strictly below `TwoSLSKinalFWLScoreCoordinateMomentIff`, which still
refers to the original random matrices. -/
def TwoSLSKinalScalarProductTailIff
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ) : Prop :=
  ∀ r : ℝ≥0,
    (∀ j : k₂,
      MemLp (coordMap j) (r : ℝ≥0∞)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))) ↔
      (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂

/-- Vector-score version of the remaining scalar Kinal product-tail theorem.

This is closer to the output of a raw Gaussian decomposition than
`TwoSLSKinalScalarProductTailIff`: the score law is kept as one joint
finite-dimensional law, and each coordinate product model is obtained by
projecting that score vector and pairing the projection with the independent
chi-square inverse-scale variable. -/
def TwoSLSKinalScoreVectorProductTailIff
    (ScoreVectorLaw : Measure (k₂ → ℝ))
    (coordMap : k₂ → ℝ × ℝ → ℝ) : Prop :=
  ∀ r : ℝ≥0,
    (∀ j : k₂,
      MemLp
        (fun z : (k₂ → ℝ) × ℝ => coordMap j (z.1 j, z.2))
        (r : ℝ≥0∞)
        (ScoreVectorLaw.prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))) ↔
      (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂

omit [DecidableEq k₂] [DecidableEq l₂] in
/-- The concrete scalar map in Kinal's Gaussian/inverse-chi-square tail
calculation: a Gaussian score divided by the square root of the independent
chi-square inverse-scale statistic. -/
noncomputable def twoSLSKinalGaussianInverseChiSqCoordMap :
    k₂ → ℝ × ℝ → ℝ :=
  fun _ z => z.1 / Real.sqrt z.2

omit [DecidableEq k₂] [DecidableEq l₂] in
/-- Law-level Gaussian/inverse-chi-square tail primitive for Kinal's theorem.

This is the exact analytic statement still needed to close Theorem 12.7 from
normal theory: for every coordinate, the product law
`N(m_j, σ_j²) × χ²(ℓ₂-k₂+1)` has finite `r`-moment after the Kinal map
`(x, q) ↦ x / sqrt q` exactly when `r < ℓ₂-k₂+1`.  The right side deliberately
uses `twoSLSKinalMomentThreshold`, so the statement cannot accidentally weaken
Hansen's real-valued threshold. -/
def TwoSLSKinalGaussianInverseChiSqProductTailIff
    (scoreMean : k₂ → ℝ) (scoreVar : k₂ → ℝ≥0) : Prop :=
  ∀ r : ℝ≥0,
    (∀ j : k₂,
      MemLp (twoSLSKinalGaussianInverseChiSqCoordMap (k₂ := k₂) j)
        (r : ℝ≥0∞)
        ((gaussianReal (scoreMean j) (scoreVar j)).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))) ↔
      (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂

omit [DecidableEq k₂] [DecidableEq l₂] in
/-- Coordinate scalar Gaussian/inverse-chi-square threshold facts assemble the
law-level Kinal product-tail package.

This is the noncentral analogue of the standard Student-`t` bridge below.  It
keeps the remaining analytic work at the reusable scalar level
`GaussianInverseChiSqMomentThresholdIff`, while preserving Hansen's exact
threshold `ℓ₂ - k₂ + 1` at the Kinal theorem boundary. -/
theorem twoSLSKinalGaussianInverseChiSqProductTailIff_of_coordinate_momentThresholds
    [Nonempty k₂]
    (hcard : Fintype.card k₂ ≤ Fintype.card l₂)
    (scoreMean : k₂ → ℝ) (scoreVar : k₂ → ℝ≥0)
    (hTail : ∀ j : k₂,
      GaussianInverseChiSqMomentThresholdIff
        (Fintype.card l₂ - Fintype.card k₂ + 1)
        (scoreMean j) (scoreVar j)) :
    TwoSLSKinalGaussianInverseChiSqProductTailIff (l₂ := l₂)
      scoreMean scoreVar := by
  have hν_eq :
      ((Fintype.card l₂ - Fintype.card k₂ + 1 : ℕ) : ℝ) =
        twoSLSKinalMomentThreshold k₂ l₂ := by
    simp [twoSLSKinalMomentThreshold, Nat.cast_sub hcard]
  intro r
  constructor
  · intro hmem
    have hmem_one :
        MemLp
          (twoSLSKinalGaussianInverseChiSqCoordMap (k₂ := k₂)
            (Classical.choice inferInstance))
          (r : ℝ≥0∞)
          ((gaussianReal (scoreMean (Classical.choice inferInstance))
              (scoreVar (Classical.choice inferInstance))).prod
            (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))) :=
      hmem (Classical.choice inferInstance)
    exact
      (by
        simpa [twoSLSKinalGaussianInverseChiSqCoordMap, hν_eq] using
          (hTail (Classical.choice inferInstance) r).mp hmem_one)
  · intro hlt j
    have hmem :
        MemLp (fun z : ℝ × ℝ => z.1 / Real.sqrt z.2)
          (r : ℝ≥0∞)
          ((gaussianReal (scoreMean j) (scoreVar j)).prod
            (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))) := by
      exact
        (hTail j r).mpr
          (by
            simpa [hν_eq] using hlt)
    simpa [twoSLSKinalGaussianInverseChiSqCoordMap] using hmem

omit [DecidableEq k₂] [DecidableEq l₂] in
/-- The standard zero-mean Gaussian/inverse-chi-square Kinal tail calculation
reduces to the reusable Student-`t` moment-threshold primitive.

The map is exactly `(x, q) ↦ x / sqrt q`; the only remaining analytic input is
the Student-`t` moment iff for `ν = ℓ₂-k₂+1` degrees of freedom. -/
theorem twoSLSKinalGaussianInverseChiSqProductTailIff_standard_of_studentTMomentIff
    [Nonempty k₂]
    (hcard : Fintype.card k₂ ≤ Fintype.card l₂)
    (hTail :
      StudentTMomentThresholdIff
        (Fintype.card l₂ - Fintype.card k₂ + 1)) :
    TwoSLSKinalGaussianInverseChiSqProductTailIff (l₂ := l₂)
      (fun _ : k₂ => 0) (fun _ : k₂ => 1) := by
  exact
    twoSLSKinalGaussianInverseChiSqProductTailIff_of_coordinate_momentThresholds
      (l₂ := l₂) hcard (fun _ : k₂ => 0) (fun _ : k₂ => 1)
      fun _ =>
        gaussianInverseChiSqMomentThresholdIff_standard_of_studentTMomentThresholdIff
          (by omega) hTail

omit [DecidableEq k₂] [DecidableEq l₂] in
/-- A Gaussian/inverse-chi-square tail theorem supplies the generic scalar
product-tail package used by the Kinal reductions.

This bridge removes the arbitrary `ScoreLaw`/`coordMap` tail premise from
callers once they have identified each score-coordinate law as Gaussian and
have proved the exact analytic Gaussian-over-square-root-chi-square moment
criterion. -/
theorem twoSLSKinalScalarProductTailIff_of_gaussianInverseChiSqProductTailIff
    (ScoreLaw : k₂ → Measure ℝ)
    (scoreMean : k₂ → ℝ) (scoreVar : k₂ → ℝ≥0)
    (hScoreLaw : ∀ j : k₂,
      ScoreLaw j = gaussianReal (scoreMean j) (scoreVar j))
    (hTail :
      TwoSLSKinalGaussianInverseChiSqProductTailIff (l₂ := l₂)
        scoreMean scoreVar) :
    TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw
      (twoSLSKinalGaussianInverseChiSqCoordMap (k₂ := k₂)) := by
  intro r
  constructor
  · intro hmem
    exact (hTail r).mp fun j => by
      simpa [hScoreLaw j] using hmem j
  · intro hlt j
    have hmem := (hTail r).mpr hlt j
    simpa [hScoreLaw j] using hmem

omit [DecidableEq k₂] [DecidableEq l₂] in
/-- Score-vector specialization of
`twoSLSKinalScalarProductTailIff_of_gaussianInverseChiSqProductTailIff`.

It is tailored to the canonical-score-law Kinal endpoints: once each coordinate
push-forward of the score-vector law is Gaussian, the remaining scalar-tail
input is exactly the law-level Gaussian/inverse-chi-square moment iff. -/
theorem twoSLSKinalScalarProductTailIff_of_scoreVectorGaussianInverseChiSqProductTailIff
    (ScoreVectorLaw : Measure (k₂ → ℝ))
    (scoreMean : k₂ → ℝ) (scoreVar : k₂ → ℝ≥0)
    (hScoreLaw : ∀ j : k₂,
      ScoreVectorLaw.map (fun s : k₂ → ℝ => s j) =
        gaussianReal (scoreMean j) (scoreVar j))
    (hTail :
      TwoSLSKinalGaussianInverseChiSqProductTailIff (l₂ := l₂)
        scoreMean scoreVar) :
    TwoSLSKinalScalarProductTailIff (l₂ := l₂)
      (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j)
      (twoSLSKinalGaussianInverseChiSqCoordMap (k₂ := k₂)) :=
  twoSLSKinalScalarProductTailIff_of_gaussianInverseChiSqProductTailIff
    (l₂ := l₂)
    (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j)
    scoreMean scoreVar hScoreLaw hTail

omit [DecidableEq k₂] [DecidableEq l₂] in
/-- The full score-vector product-tail theorem implies the existing
coordinate-marginal scalar product-tail theorem.

This bridge uses only measure transport: the product of the marginal score
law and chi-square law is the push-forward of the full score-vector/chi-square
product law under `(s, v) ↦ (s j, v)`.  The exact analytic inverse-chi-square
moment threshold is still the content of the vector product-tail premise. -/
theorem twoSLSKinalScalarProductTailIff_of_scoreVectorProductTailIff
    (ScoreVectorLaw : Measure (k₂ → ℝ))
    [SFinite ScoreVectorLaw]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        (((ScoreVectorLaw.map fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        ScoreVectorLaw coordMap) :
    TwoSLSKinalScalarProductTailIff (l₂ := l₂)
      (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j)
      coordMap := by
  intro r
  constructor
  · intro hcoord
    exact (hTail r).mp fun j => by
      let evalJ : (k₂ → ℝ) → ℝ := fun s => s j
      let evalPair : (k₂ → ℝ) × ℝ → ℝ × ℝ :=
        fun z => (evalJ z.1, z.2)
      have hmap :
          ((ScoreVectorLaw.map evalJ).prod
            (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))) =
            (ScoreVectorLaw.prod
              (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))).map
              evalPair := by
        simpa [evalJ, evalPair] using
          (Measure.map_prod_map ScoreVectorLaw
            (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))
            (measurable_pi_apply j) measurable_id)
      have hmeas :
          AEStronglyMeasurable (coordMap j)
            ((ScoreVectorLaw.prod
              (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))).map
              evalPair) := by
        rw [← hmap]
        exact (hCoordMap j).aestronglyMeasurable
      have hiff :
          MemLp (coordMap j) (r : ℝ≥0∞)
              ((ScoreVectorLaw.map evalJ).prod
                (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))) ↔
            MemLp
              (fun z : (k₂ → ℝ) × ℝ => coordMap j (z.1 j, z.2))
              (r : ℝ≥0∞)
              (ScoreVectorLaw.prod
                (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))) := by
        rw [hmap]
        simpa [evalJ, evalPair, Function.comp_def] using
          (memLp_map_measure_iff hmeas
            (by
              have hEvalPair : Measurable evalPair := by
                fun_prop
              exact hEvalPair.aemeasurable))
      exact hiff.mp (hcoord j)
  · intro hlt j
    let evalJ : (k₂ → ℝ) → ℝ := fun s => s j
    let evalPair : (k₂ → ℝ) × ℝ → ℝ × ℝ :=
      fun z => (evalJ z.1, z.2)
    have hmap :
        ((ScoreVectorLaw.map evalJ).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))) =
          (ScoreVectorLaw.prod
            (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))).map
            evalPair := by
      simpa [evalJ, evalPair] using
        (Measure.map_prod_map ScoreVectorLaw
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))
          (measurable_pi_apply j) measurable_id)
    have hmeas :
        AEStronglyMeasurable (coordMap j)
          ((ScoreVectorLaw.prod
            (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))).map
            evalPair) := by
      rw [← hmap]
      exact (hCoordMap j).aestronglyMeasurable
    have hiff :
        MemLp (coordMap j) (r : ℝ≥0∞)
            ((ScoreVectorLaw.map evalJ).prod
              (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))) ↔
          MemLp
            (fun z : (k₂ → ℝ) × ℝ => coordMap j (z.1 j, z.2))
            (r : ℝ≥0∞)
            (ScoreVectorLaw.prod
              (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))) := by
      rw [hmap]
      simpa [evalJ, evalPair, Function.comp_def] using
        (memLp_map_measure_iff hmeas
          (by
            have hEvalPair : Measurable evalPair := by
              fun_prop
            exact hEvalPair.aemeasurable))
    exact hiff.mpr ((hTail r).mpr hlt j)

/-- Product-law bridge for one Kinal score-coordinate coefficient.

If a coefficient coordinate is a.e. a scalar function of its score coordinate
and the coordinate inverse-scale statistic, and these two scalar inputs are
independent with the stated laws, then the coefficient coordinate has the
corresponding product push-forward law. -/
theorem twoSLSKinalFWLScoreCoordinate_hasLaw_of_independent_product
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ)
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ)
    (hScoreProb : ∀ j : k₂, IsProbabilityMeasure (ScoreLaw j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))))
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ)
    (hScaleLaw :
      TwoSLSKinalFWLCoordinateInverseScaleLaws (n := n) (l₂ := l₂)
        μ X₁ Y₂ Z₂ Sigma)
    (hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (j : k₂) :
    HasLaw
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
      (((ScoreLaw j).prod
        (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))).map
          (coordMap j)) μ := by
  haveI : IsProbabilityMeasure (ScoreLaw j) := hScoreProb j
  haveI : IsFiniteMeasure μ := (hScoreLaw j).isFiniteMeasure
  have hScale := twoSLSKinalFWLCoordinateInverseScaleStar_hasLaw
    (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Sigma := Sigma) hScaleLaw j
  have hModel : HasLaw
      (fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
      (((ScoreLaw j).prod
        (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))).map
          (coordMap j)) μ :=
    hasLaw_map_of_indepFun_pair
      (A := fun ω =>
        twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
      (B := fun ω =>
        twoSLSKinalFWLCoordinateInverseScaleStar
          (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
      (Alaw := ScoreLaw j)
      (Blaw := chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))
      (F := coordMap j)
      (hScoreLaw j) hScale (hInd j) (hCoordMap j)
  exact hModel.congr (hCoeff j)

/-- Score/inverse-scale product tails imply the lower-level Kinal
score-coordinate moment iff.

This is the point at which the stochastic Kinal proof is reduced to an
ordinary scalar product-tail theorem.  The assumptions expose, rather than
hide, the remaining work: score-coordinate laws, independence from the
coordinate inverse-scale chi-square statistic, an a.e. scalar representation
of each coefficient coordinate, and the scalar product-tail calculation. -/
theorem twoSLSKinalFWLScoreCoordinateMomentIff_of_independent_product_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ)
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ)
    (hScoreProb : ∀ j : k₂, IsProbabilityMeasure (ScoreLaw j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))))
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ)
    (hScaleLaw :
      TwoSLSKinalFWLCoordinateInverseScaleLaws (n := n) (l₂ := l₂)
        μ X₁ Y₂ Z₂ Sigma)
    (hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail : TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap) :
    TwoSLSKinalFWLScoreCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁ := by
  intro r
  constructor
  · intro hCoord
    exact (hTail r).mp fun j => by
      have hLaw :=
        twoSLSKinalFWLScoreCoordinate_hasLaw_of_independent_product
          (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
          (Sigma := Sigma) (ScoreLaw := ScoreLaw) (coordMap := coordMap)
          hScoreProb hCoordMap hScoreLaw hScaleLaw hInd hCoeff j
      exact
        (real_memLp_iff_memLp_map_of_hasLaw hLaw (hCoordMap j)).mp
          (hCoord j)
  · intro hlt j
    have hLaw :=
      twoSLSKinalFWLScoreCoordinate_hasLaw_of_independent_product
        (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
        (Sigma := Sigma) (ScoreLaw := ScoreLaw) (coordMap := coordMap)
        hScoreProb hCoordMap hScoreLaw hScaleLaw hInd hCoeff j
    exact
      (real_memLp_iff_memLp_map_of_hasLaw hLaw (hCoordMap j)).mpr
        ((hTail r).mpr hlt j)

/-- Residual-Gram Wishart laws, coordinate Schur-complement map identities,
and score/inverse-scale product tails imply the lower-level Kinal
score-coordinate moment iff.

This is the strongest current non-tautological local reduction: it reuses the
Chapter 11 inverse-Wishart law transfer for each coordinate and leaves only
the genuinely Kinal-specific product representation and scalar product-tail
calculation as explicit assumptions. -/
theorem twoSLSKinalFWLScoreCoordinateMomentIff_of_residualGram_product_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ)
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ)
    (hScoreProb : ∀ j : k₂, IsProbabilityMeasure (ScoreLaw j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))))
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hScaleMap : ∀ j : k₂,
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))
    (hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail : TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap) :
    TwoSLSKinalFWLScoreCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  twoSLSKinalFWLScoreCoordinateMomentIff_of_independent_product_tail
    (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
    (Sigma := Sigma) (ScoreLaw := ScoreLaw) (coordMap := coordMap)
    hScoreProb hCoordMap hScoreLaw
    (twoSLSKinalFWLCoordinateInverseScaleLaws_of_coordinate_map_eq
      X₁ Y₂ Z₂ Sigma hW hScaleMap)
    hInd hCoeff hTail

/-- Vector-score residual-Gram product-tail inputs imply the lower-level Kinal
score-coordinate moment iff.

This is the score-vector analogue of
`twoSLSKinalFWLScoreCoordinateMomentIff_of_residualGram_product_tail`: it
derives all coordinate score laws, score/inverse-scale independence, and the
coordinate-marginal scalar product-tail theorem from one full score-vector
law, one score/Gram independence statement, and one vector product-tail
calculation.  The coefficient product representation and analytic vector-tail
iff remain explicit, so this bridge does not assume Hansen's final conclusion. -/
theorem twoSLSKinalFWLScoreCoordinateMomentIff_of_scoreVector_residualGram_product_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ)
    (ScoreVectorLaw : Measure (k₂ → ℝ)) (coordMap : k₂ → ℝ × ℝ → ℝ)
    [SFinite (wishartLaw (n := l₂) Sigma)]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hScoreVector :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreVectorLaw μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hScaleMap : ∀ j : k₂,
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))
    (hScoreGramInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        (((ScoreVectorLaw.map fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        ScoreVectorLaw coordMap) :
    TwoSLSKinalFWLScoreCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁ := by
  haveI : IsProbabilityMeasure ScoreVectorLaw :=
    (hScoreVector.isProbabilityMeasure_iff).1 inferInstance
  have hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ((ScoreVectorLaw.map fun s : k₂ → ℝ => s j)) μ :=
    twoSLSKinalFWLScoreCoordinateLaws_of_scoreVectorLaw
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (ScoreVectorLaw := ScoreVectorLaw) hScoreVector
  have hScoreProb : ∀ j : k₂,
      IsProbabilityMeasure (ScoreVectorLaw.map fun s : k₂ → ℝ => s j) := by
    intro j
    exact (hScoreLaw j).isProbabilityMeasure_iff.1 inferInstance
  have hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j :=
    twoSLSKinalFWLScoreCoordinate_indep_coordinateInverseScale_of_scoreVector_indep_gram
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Sigma := Sigma) (ScoreVectorLaw := ScoreVectorLaw)
      hScoreVector hW hScoreGramInd hScaleMap
  exact
    twoSLSKinalFWLScoreCoordinateMomentIff_of_residualGram_product_tail
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Sigma := Sigma)
      (ScoreLaw := fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j)
      (coordMap := coordMap)
      hScoreProb hCoordMap hScoreLaw hW hScaleMap hInd hCoeff
      (twoSLSKinalScalarProductTailIff_of_scoreVectorProductTailIff
        (l₂ := l₂) ScoreVectorLaw hCoordMap hTail)

/-- Residual-Gram Wishart laws, Chapter 11 standard-coordinate
inverse-Wishart whitening data, and score/inverse-scale product tails imply
the lower-level Kinal score-coordinate moment iff.

Compared with
`twoSLSKinalFWLScoreCoordinateMomentIff_of_residualGram_product_tail`, this
replaces the raw coordinate push-forward identity premise with the narrower
Chapter 11 whitening/alignment bridge and derives the score-law probability
premise from `TwoSLSKinalJointNormalConditions`. -/
theorem twoSLSKinalFWLScoreCoordinateMomentIff_of_standardCoordinate_product_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ)
    (S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ)
    (c : k₂ → ℝ)
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ)
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))))
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartWhiteningBridge (l₂ := l₂)
        Sigma T S c)
    (hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail : TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap) :
    TwoSLSKinalFWLScoreCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  twoSLSKinalFWLScoreCoordinateMomentIff_of_independent_product_tail
    (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
    (Sigma := Sigma) (ScoreLaw := ScoreLaw) (coordMap := coordMap)
    (twoSLSKinal_scoreLaw_isProbabilityMeasure_of_jointNormalConditions
      hJoint hScoreLaw)
    hCoordMap hScoreLaw
    (twoSLSKinalFWLCoordinateInverseScaleLaws_of_standardCoordinate_whitening
      X₁ Y₂ Z₂ Sigma T S c hW hBridge)
    hInd hCoeff hTail

/-- Residual-Gram Wishart laws, Chapter 11 nuisance-only standard-coordinate
inverse-Wishart whitening data, and score/inverse-scale product tails imply
the lower-level Kinal score-coordinate moment iff.

Compared with
`twoSLSKinalFWLScoreCoordinateMomentIff_of_standardCoordinate_product_tail`,
this wrapper uses the Chapter 11 endpoint that derives full standardized Gram
and Wishart nonsingularity from nuisance-Gram nonsingularity alone. -/
theorem twoSLSKinalFWLScoreCoordinateMomentIff_of_standardCoordinate_nuisance_product_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ)
    (S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ)
    (c : k₂ → ℝ)
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ)
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))))
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartNuisanceWhiteningBridge (l₂ := l₂)
        Sigma T S c)
    (hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail : TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap) :
    TwoSLSKinalFWLScoreCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  twoSLSKinalFWLScoreCoordinateMomentIff_of_independent_product_tail
    (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
    (Sigma := Sigma) (ScoreLaw := ScoreLaw) (coordMap := coordMap)
    (twoSLSKinal_scoreLaw_isProbabilityMeasure_of_jointNormalConditions
      hJoint hScoreLaw)
    hCoordMap hScoreLaw
    (twoSLSKinalFWLCoordinateInverseScaleLaws_of_standardCoordinate_nuisance_whitening
      X₁ Y₂ Z₂ Sigma T S c hW hBridge)
    hInd hCoeff hTail

/-- Residual-Gram Wishart laws, Chapter 11 standard-Gram/existential
whitening data, and score/inverse-scale product tails imply the lower-level
Kinal score-coordinate moment iff.

Compared with the nuisance-whitening wrapper, this version uses Chapter 11's
endpoint that derives the rest-column nuisance rank certificate from the
canonical rectangular iid standard-Gaussian Gram certificate. -/
theorem twoSLSKinalFWLScoreCoordinateMomentIff_of_standardGram_product_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ)
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))))
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
        Sigma (rIdx := rIdx))
    (hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail : TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap) :
    TwoSLSKinalFWLScoreCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  twoSLSKinalFWLScoreCoordinateMomentIff_of_independent_product_tail
    (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
    (Sigma := Sigma) (ScoreLaw := ScoreLaw) (coordMap := coordMap)
    (twoSLSKinal_scoreLaw_isProbabilityMeasure_of_jointNormalConditions
      hJoint hScoreLaw)
    hCoordMap hScoreLaw
    (twoSLSKinalFWLCoordinateInverseScaleLaws_of_standardGramBridge
      X₁ Y₂ Z₂ Sigma hW hBridge)
    hInd hCoeff hTail

/-- If the textbook endogenous 2SLS block is a.e. equal to the totalized FWL
reduction, the FWL random inverse-Gram tail theorem is exactly Hansen's Kinal
moment iff. -/
theorem twoSLSKinalExactMomentIff_of_fwl_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hFWL :
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        =ᵐ[μ]
      fun ω => twoSLSKinalFWLBetaStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
    (hTail : TwoSLSKinalFWLMomentIff μ X₁ Y₂ Z₂ Y₁) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ := by
  intro r
  constructor
  · intro hmem
    exact (hTail r).mp (MemLp.ae_eq hFWL hmem)
  · intro hlt
    exact MemLp.ae_eq hFWL.symm ((hTail r).mpr hlt)

/-- Coordinatewise scalar FWL moment thresholds are enough to complete the
exact textbook Kinal moment iff once the a.e. deterministic FWL bridge is
available. -/
theorem twoSLSKinalExactMomentIff_of_fwl_coordinateMomentIff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hFWL :
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        =ᵐ[μ]
      fun ω => twoSLSKinalFWLBetaStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
    (hCoord : TwoSLSKinalFWLCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  twoSLSKinalExactMomentIff_of_fwl_ae_eq hFWL
    (twoSLSKinalFWLMomentIff_of_coordinateMomentIff hCoord)

/-- Score-coordinate scalar FWL moment thresholds are enough to complete the
exact textbook Kinal moment iff once the a.e. deterministic FWL bridge is
available. -/
theorem twoSLSKinalExactMomentIff_of_fwl_scoreCoordinateMomentIff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hFWL :
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        =ᵐ[μ]
      fun ω => twoSLSKinalFWLBetaStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
    (hScore : TwoSLSKinalFWLScoreCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  twoSLSKinalExactMomentIff_of_fwl_coordinateMomentIff hFWL
    (twoSLSKinalFWLCoordinateMomentIff_of_scoreCoordinateMomentIff hScore)

/-- Independent product-tail inputs are enough to close the exact Kinal moment
iff once the deterministic 2SLS/FWL equality is available.

This is only a composition theorem: it does not derive the score laws,
independence, coefficient product representation, or scalar product-tail
calculation.  Those are the remaining substantive Kinal ingredients. -/
theorem twoSLSKinalExactMomentIff_of_fwl_independent_product_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hFWL :
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        =ᵐ[μ]
      fun ω => twoSLSKinalFWLBetaStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
    (Sigma : Matrix k₂ k₂ ℝ)
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ)
    (hScoreProb : ∀ j : k₂, IsProbabilityMeasure (ScoreLaw j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))))
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ)
    (hScaleLaw :
      TwoSLSKinalFWLCoordinateInverseScaleLaws (n := n) (l₂ := l₂)
        μ X₁ Y₂ Z₂ Sigma)
    (hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail : TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  twoSLSKinalExactMomentIff_of_fwl_scoreCoordinateMomentIff hFWL
    (twoSLSKinalFWLScoreCoordinateMomentIff_of_independent_product_tail
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Sigma := Sigma) (ScoreLaw := ScoreLaw) (coordMap := coordMap)
      hScoreProb hCoordMap hScoreLaw hScaleLaw hInd hCoeff hTail)

/-- Residual-Gram Wishart laws, coordinate Schur-complement map identities,
and score/inverse-scale product tails are enough to close the exact Kinal
moment iff once the deterministic 2SLS/FWL equality is available. -/
theorem twoSLSKinalExactMomentIff_of_fwl_residualGram_product_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hFWL :
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        =ᵐ[μ]
      fun ω => twoSLSKinalFWLBetaStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
    (Sigma : Matrix k₂ k₂ ℝ)
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ)
    (hScoreProb : ∀ j : k₂, IsProbabilityMeasure (ScoreLaw j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))))
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hScaleMap : ∀ j : k₂,
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))
    (hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail : TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  twoSLSKinalExactMomentIff_of_fwl_scoreCoordinateMomentIff hFWL
    (twoSLSKinalFWLScoreCoordinateMomentIff_of_residualGram_product_tail
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Sigma := Sigma) (ScoreLaw := ScoreLaw) (coordMap := coordMap)
      hScoreProb hCoordMap hScoreLaw hW hScaleMap hInd hCoeff hTail)

/-- Vector-score residual-Gram product-tail inputs close the exact Kinal
moment iff once the deterministic 2SLS/FWL equality is available. -/
theorem twoSLSKinalExactMomentIff_of_fwl_scoreVector_residualGram_product_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hFWL :
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        =ᵐ[μ]
      fun ω => twoSLSKinalFWLBetaStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
    (Sigma : Matrix k₂ k₂ ℝ)
    (ScoreVectorLaw : Measure (k₂ → ℝ)) (coordMap : k₂ → ℝ × ℝ → ℝ)
    [SFinite (wishartLaw (n := l₂) Sigma)]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hScoreVector :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreVectorLaw μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hScaleMap : ∀ j : k₂,
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))
    (hScoreGramInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        (((ScoreVectorLaw.map fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        ScoreVectorLaw coordMap) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  twoSLSKinalExactMomentIff_of_fwl_scoreCoordinateMomentIff hFWL
    (twoSLSKinalFWLScoreCoordinateMomentIff_of_scoreVector_residualGram_product_tail
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Sigma := Sigma) (ScoreVectorLaw := ScoreVectorLaw)
      (coordMap := coordMap)
      hScoreVector hW hScaleMap hScoreGramInd hCoeff hCoordMap hTail)

/-- The rank fields in `TwoSLSKinalJointNormalConditions` imply the a.e.
deterministic FWL bridge needed by the Kinal vector-tail theorem. -/
theorem twoSLSKinal_fwl_ae_eq_of_jointNormalConditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁) :
    (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      =ᵐ[μ]
    fun ω => twoSLSKinalFWLBetaStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) := by
  filter_upwards
    [h.instrument_rank_ae, h.fitted_rank_ae, h.included_fitted_rank_ae,
      h.residualized_fitted_endogenous_rank_ae] with
    ω hinstr hfitted hincluded hresid
  exact
    twoSLSEndogenousBetaOrZero_eq_twoSLSKinalFWLBetaStar_of_ranks
      (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) hinstr hfitted hincluded hresid

/-- Joint-normal rank/FWL conditions, residual-Gram Wishart laws, Chapter 11
nuisance-only standard-coordinate inverse-Wishart whitening data, and
score/inverse-scale product tails imply the exact Kinal moment iff.

This is the current strongest theorem-facing reduction in this file.  It
derives the deterministic a.e. 2SLS/FWL bridge from
`TwoSLSKinalJointNormalConditions`, reuses the Chapter 11 inverse-Wishart
coordinate law through
`twoSLSKinalFWLScoreCoordinateMomentIff_of_standardCoordinate_nuisance_product_tail`,
and leaves only the genuinely Kinal-specific stochastic/product-tail inputs as
premises. -/
theorem twoSLSKinalExactMomentIff_of_jointNormal_standardCoordinate_nuisance_product_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ)
    (S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ)
    (c : k₂ → ℝ)
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ)
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))))
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartNuisanceWhiteningBridge (l₂ := l₂)
        Sigma T S c)
    (hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail : TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  twoSLSKinalExactMomentIff_of_fwl_scoreCoordinateMomentIff
    (twoSLSKinal_fwl_ae_eq_of_jointNormalConditions hJoint)
    (twoSLSKinalFWLScoreCoordinateMomentIff_of_standardCoordinate_nuisance_product_tail
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Sigma := Sigma) (T := T) (S := S) (c := c)
      (ScoreLaw := ScoreLaw) (coordMap := coordMap)
      hJoint hCoordMap hScoreLaw hW hBridge hInd hCoeff hTail)

/-- Hansen Theorem 12.7 reduced to the exact FWL tail theorem.

This theorem keeps Hansen's joint-normal condition package in the statement,
but the proof obligation is now localized: prove the a.e. 2SLS/FWL equality on
the nonsingular branch and prove the Kinal random inverse-Gram tail iff for
`twoSLSKinalFWLBetaStar`. -/
theorem twoSLSKinal_theorem12_7_of_fwl_tail_theorem
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (_h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hFWL :
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        =ᵐ[μ]
      fun ω => twoSLSKinalFWLBetaStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
    (hTail : TwoSLSKinalFWLMomentIff μ X₁ Y₂ Z₂ Y₁) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
          (r : ℝ≥0∞) μ ↔
        (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂ :=
  twoSLSKinalExactMomentIff_of_fwl_ae_eq hFWL hTail

/-- Hansen Theorem 12.7 reduced to the exact FWL vector-tail theorem, with the
a.e. 2SLS/FWL equality derived from the rank fields in the joint-normal
condition package. -/
theorem twoSLSKinal_theorem12_7_of_fwl_tail_theorem_from_conditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hTail : TwoSLSKinalFWLMomentIff μ X₁ Y₂ Z₂ Y₁) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
          (r : ℝ≥0∞) μ ↔
        (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂ :=
  twoSLSKinal_theorem12_7_of_fwl_tail_theorem h
    (twoSLSKinal_fwl_ae_eq_of_jointNormalConditions h) hTail

/-- Hansen Theorem 12.7 reduced to coordinatewise scalar FWL moment
thresholds and the deterministic a.e. FWL bridge. -/
theorem twoSLSKinal_theorem12_7_of_fwl_coordinate_tail_theorem
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (_h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hFWL :
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        =ᵐ[μ]
      fun ω => twoSLSKinalFWLBetaStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
    (hCoord : TwoSLSKinalFWLCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
          (r : ℝ≥0∞) μ ↔
        (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂ :=
  twoSLSKinalExactMomentIff_of_fwl_coordinateMomentIff hFWL hCoord

/-- Hansen Theorem 12.7 reduced to coordinatewise scalar FWL moment
thresholds, with the a.e. deterministic FWL bridge supplied by the
joint-normal condition package. -/
theorem twoSLSKinal_theorem12_7_of_fwl_coordinate_tail_theorem_from_conditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hCoord : TwoSLSKinalFWLCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
          (r : ℝ≥0∞) μ ↔
        (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂ :=
  twoSLSKinal_theorem12_7_of_fwl_coordinate_tail_theorem h
    (twoSLSKinal_fwl_ae_eq_of_jointNormalConditions h) hCoord

/-- Hansen Theorem 12.7 reduced to score-coordinate scalar FWL moment
thresholds and the deterministic a.e. FWL bridge.  This is the lowest-level
Theorem 12.7 wrapper in this file: the remaining tail theorem is about
coordinates of `(RᵀR)⁻¹ Rᵀ M y`. -/
theorem twoSLSKinal_theorem12_7_of_fwl_score_coordinate_tail_theorem
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (_h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hFWL :
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        =ᵐ[μ]
      fun ω => twoSLSKinalFWLBetaStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
    (hScore : TwoSLSKinalFWLScoreCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
          (r : ℝ≥0∞) μ ↔
        (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂ :=
  twoSLSKinalExactMomentIff_of_fwl_scoreCoordinateMomentIff hFWL hScore

/-- Hansen Theorem 12.7 reduced to score-coordinate scalar FWL moment
thresholds, with the deterministic a.e. FWL bridge supplied by the
joint-normal condition package. -/
theorem twoSLSKinal_theorem12_7_of_fwl_score_coordinate_tail_theorem_from_conditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hScore : TwoSLSKinalFWLScoreCoordinateMomentIff μ X₁ Y₂ Z₂ Y₁) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
          (r : ℝ≥0∞) μ ↔
        (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂ :=
  twoSLSKinal_theorem12_7_of_fwl_score_coordinate_tail_theorem h
    (twoSLSKinal_fwl_ae_eq_of_jointNormalConditions h) hScore

/-- Hansen Theorem 12.7 from the current lowest-level product-tail inputs.

The joint-normal package supplies the deterministic a.e. FWL bridge through
its rank fields.  The other hypotheses are the exact remaining Kinal work:
coordinate score laws, coordinate inverse-scale laws, their independence, the
a.e. coefficient product representation, and the scalar product-tail iff. -/
theorem twoSLSKinal_theorem12_7_of_independent_product_tail_from_conditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Sigma : Matrix k₂ k₂ ℝ)
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ)
    (hScoreProb : ∀ j : k₂, IsProbabilityMeasure (ScoreLaw j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))))
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ)
    (hScaleLaw :
      TwoSLSKinalFWLCoordinateInverseScaleLaws (n := n) (l₂ := l₂)
        μ X₁ Y₂ Z₂ Sigma)
    (hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail : TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
          (r : ℝ≥0∞) μ ↔
        (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂ :=
  twoSLSKinal_theorem12_7_of_fwl_score_coordinate_tail_theorem_from_conditions h
    (twoSLSKinalFWLScoreCoordinateMomentIff_of_independent_product_tail
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Sigma := Sigma) (ScoreLaw := ScoreLaw) (coordMap := coordMap)
      hScoreProb hCoordMap hScoreLaw hScaleLaw hInd hCoeff hTail)

/-- Hansen Theorem 12.7 from residual-Gram Wishart laws, coordinate
Schur-complement map identities, and the current scalar product-tail inputs.

This is the strongest theorem-facing wrapper in this file that does not assume
the Kinal moment iff itself: the joint-normal package supplies the deterministic
2SLS/FWL bridge, Chapter 11 supplies the law-transfer interface for the
coordinate inverse scales, and the remaining hypotheses are precisely the
Kinal-specific product representation and scalar tail calculation. -/
theorem twoSLSKinal_theorem12_7_of_residualGram_product_tail_from_conditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Sigma : Matrix k₂ k₂ ℝ)
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ)
    (hScoreProb : ∀ j : k₂, IsProbabilityMeasure (ScoreLaw j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))))
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hScaleMap : ∀ j : k₂,
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))
    (hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail : TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
          (r : ℝ≥0∞) μ ↔
        (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂ :=
  twoSLSKinal_theorem12_7_of_fwl_score_coordinate_tail_theorem_from_conditions h
    (twoSLSKinalFWLScoreCoordinateMomentIff_of_residualGram_product_tail
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Sigma := Sigma) (ScoreLaw := ScoreLaw) (coordMap := coordMap)
      hScoreProb hCoordMap hScoreLaw hW hScaleMap hInd hCoeff hTail)

/-- Hansen Theorem 12.7 from full score-vector residual-Gram product-tail
inputs.

Compared with
`twoSLSKinal_theorem12_7_of_residualGram_product_tail_from_conditions`, this
wrapper derives coordinate score laws, score-law probabilities,
score/inverse-scale independence, and the coordinate scalar tail theorem from
one score-vector law, one score/Gram independence statement, and one vector
product-tail iff. -/
theorem twoSLSKinal_theorem12_7_of_scoreVector_residualGram_product_tail_from_conditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Sigma : Matrix k₂ k₂ ℝ)
    (ScoreVectorLaw : Measure (k₂ → ℝ)) (coordMap : k₂ → ℝ × ℝ → ℝ)
    [SFinite (wishartLaw (n := l₂) Sigma)]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hScoreVector :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreVectorLaw μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hScaleMap : ∀ j : k₂,
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))
    (hScoreGramInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        (((ScoreVectorLaw.map fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        ScoreVectorLaw coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
          (r : ℝ≥0∞) μ ↔
        (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂ := by
  haveI : IsProbabilityMeasure μ := h.joint_gaussian.isProbabilityMeasure
  exact
    twoSLSKinal_theorem12_7_of_fwl_score_coordinate_tail_theorem_from_conditions h
      (twoSLSKinalFWLScoreCoordinateMomentIff_of_scoreVector_residualGram_product_tail
        (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
        (Sigma := Sigma) (ScoreVectorLaw := ScoreVectorLaw)
        (coordMap := coordMap)
        hScoreVector hW hScaleMap hScoreGramInd hCoeff hCoordMap hTail)

/-- Hansen Theorem 12.7 from residual-Gram Wishart laws, Chapter 11
standard-coordinate inverse-Wishart whitening data, and the current scalar
product-tail inputs.

This wrapper reduces the public theorem surface relative to
`twoSLSKinal_theorem12_7_of_residualGram_product_tail_from_conditions`: it no
longer asks for score-law probability premises or raw coordinate
`wishartLaw.map` identities.  The remaining inverse-Wishart premise is the
named whitening/alignment bridge used by Chapter 11's Theorem 11.11 endpoint. -/
theorem twoSLSKinal_theorem12_7_of_standardCoordinate_product_tail_from_conditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ)
    (S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ)
    (c : k₂ → ℝ)
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ)
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))))
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartWhiteningBridge (l₂ := l₂)
        Sigma T S c)
    (hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail : TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
          (r : ℝ≥0∞) μ ↔
        (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂ :=
  twoSLSKinal_theorem12_7_of_fwl_score_coordinate_tail_theorem_from_conditions h
    (twoSLSKinalFWLScoreCoordinateMomentIff_of_standardCoordinate_product_tail
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (hJoint := h) (Sigma := Sigma) (T := T) (S := S) (c := c)
      (ScoreLaw := ScoreLaw) (coordMap := coordMap)
      hCoordMap hScoreLaw hW hBridge hInd hCoeff hTail)

/-- Hansen Theorem 12.7 from residual-Gram Wishart laws, Chapter 11
nuisance-only standard-coordinate inverse-Wishart whitening data, and the
current scalar product-tail inputs.

This wrapper is the nuisance-Gram version of
`twoSLSKinal_theorem12_7_of_standardCoordinate_product_tail_from_conditions`.
It no longer asks for standardized full-Gram nonsingularity, Wishart
nonsingularity, raw coordinate map identities, score-law probabilities, or
raw score-law probabilities. -/
theorem twoSLSKinal_theorem12_7_of_standardCoordinate_nuisance_product_tail_from_conditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ)
    (S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ)
    (c : k₂ → ℝ)
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ)
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))))
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartNuisanceWhiteningBridge (l₂ := l₂)
        Sigma T S c)
    (hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail : TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
          (r : ℝ≥0∞) μ ↔
        (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂ :=
  twoSLSKinal_theorem12_7_of_fwl_score_coordinate_tail_theorem_from_conditions h
    (twoSLSKinalFWLScoreCoordinateMomentIff_of_standardCoordinate_nuisance_product_tail
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (hJoint := h) (Sigma := Sigma) (T := T) (S := S) (c := c)
      (ScoreLaw := ScoreLaw) (coordMap := coordMap)
      hCoordMap hScoreLaw hW hBridge hInd hCoeff hTail)

/-- Hansen Theorem 12.7 from residual-Gram Wishart laws, Chapter 11
standard-Gram/existential-whitening data, and the current scalar product-tail
inputs.

This is the standard-Gram version of the nuisance product-tail wrapper.  It
uses Chapter 11 to derive the nuisance rest-column rank certificate from a
canonical rectangular iid standard-Gaussian Gram certificate, and keeps the
Hansen moment threshold unchanged. -/
theorem twoSLSKinal_theorem12_7_of_standardGram_product_tail_from_conditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
        Sigma (rIdx := rIdx))
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ)
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))))
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail : TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
          (r : ℝ≥0∞) μ ↔
        (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂ :=
  twoSLSKinal_theorem12_7_of_fwl_score_coordinate_tail_theorem_from_conditions h
    (twoSLSKinalFWLScoreCoordinateMomentIff_of_standardGram_product_tail
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (hJoint := h) (Sigma := Sigma) (rIdx := rIdx)
      (ScoreLaw := ScoreLaw) (coordMap := coordMap)
      hCoordMap hScoreLaw hW hBridge hInd hCoeff hTail)

omit [DecidableEq n] in
/-- Unfolded Hansen/Kinal threshold form of the exact moment iff.

This is the statement shape closest to Theorem 12.7:
`E ‖β̂₂sls,2‖^r < ∞` iff `r < ℓ₂ - k₂ + 1`, with the right-hand side
displayed rather than hidden behind `twoSLSKinalMomentThreshold`. -/
theorem twoSLSKinalExactMomentIff_card_threshold
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hiff : TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 := by
  intro r
  simpa [twoSLSKinalMomentThreshold] using hiff r

/-- Theorem-facing residual-Gram/product-tail package for Hansen Theorem 12.7.

The package bundles the strongest current non-tautological route to Kinal's
finite-moment iff.  It keeps the joint-normal assumptions separate from the
remaining analytic tail inputs: residualized fitted-Gram Wishart law,
coordinate inverse-Wishart map identities, score laws and independence,
coefficient product representation, and the scalar product-tail calculation. -/
structure TwoSLSKinalResidualGramProductTailConditions
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ)
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ) : Prop where
  /-- Hansen's joint-normal and finite-sample rank/order assumptions. -/
  joint_normal : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁
  /-- Each score-coordinate law is a probability measure. -/
  score_prob : ∀ j : k₂, IsProbabilityMeasure (ScoreLaw j)
  /-- The scalar product model is measurable under its product law. -/
  coordMap_aemeasurable : ∀ j : k₂,
    AEMeasurable (coordMap j)
      ((ScoreLaw j).prod
        (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))
  /-- Law of each residualized FWL score coordinate. -/
  score_law : ∀ j : k₂,
    HasLaw
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
      (ScoreLaw j) μ
  /-- Wishart law for the residualized fitted-endogenous Gram matrix. -/
  residual_gram_wishart :
    TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma
  /-- Coordinate inverse-Wishart map identity, with Hansen's degrees of
  freedom `ℓ₂ - k₂ + 1`. -/
  coordinate_inverse_scale_map : ∀ j : k₂,
    (wishartLaw (n := l₂) Sigma).map
        (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
      chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)
  /-- Independence between each score coordinate and its inverse-scale
  statistic. -/
  score_inverse_scale_independent : ∀ j : k₂,
    (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
      ⟂ᵢ[μ]
    fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
      (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j
  /-- A.e. scalar product representation of each coefficient coordinate. -/
  coefficient_product_ae : ∀ j : k₂,
    (fun ω =>
      ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
        twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
      =ᵐ[μ]
    fun ω =>
      coordMap j
        (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
          twoSLSKinalFWLCoordinateInverseScaleStar
            (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
  /-- Scalar product-tail calculation giving exactly the Kinal threshold. -/
  scalar_product_tail :
    TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap

/-- Residual-Gram/product-tail package constructor from full score-vector
inputs.

This derives the coordinate score laws and the coordinate score/inverse-scale
independence fields from a single full score-vector law and full
score/residual-Gram independence.  The analytic product-tail input remains the
genuine vector-score Kinal tail calculation, not the final moment iff. -/
theorem TwoSLSKinalResidualGramProductTailConditions.of_scoreVectorProductTail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {ScoreVectorLaw : Measure (k₂ → ℝ)}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (wishartLaw (n := l₂) Sigma)]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hScoreVector :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreVectorLaw μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hScaleMap : ∀ j : k₂,
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))
    (hScoreGramInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        (((ScoreVectorLaw.map fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        ScoreVectorLaw coordMap) :
    TwoSLSKinalResidualGramProductTailConditions
      μ X₁ Y₂ Z₂ Y₁ Sigma
      (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j)
      coordMap := by
  haveI : IsProbabilityMeasure μ := hJoint.joint_gaussian.isProbabilityMeasure
  haveI : IsProbabilityMeasure ScoreVectorLaw :=
    (hScoreVector.isProbabilityMeasure_iff).1 inferInstance
  have hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ((ScoreVectorLaw.map fun s : k₂ → ℝ => s j)) μ :=
    twoSLSKinalFWLScoreCoordinateLaws_of_scoreVectorLaw
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (ScoreVectorLaw := ScoreVectorLaw) hScoreVector
  have hScoreProb : ∀ j : k₂,
      IsProbabilityMeasure (ScoreVectorLaw.map fun s : k₂ → ℝ => s j) := by
    intro j
    exact (hScoreLaw j).isProbabilityMeasure_iff.1 inferInstance
  have hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j :=
    twoSLSKinalFWLScoreCoordinate_indep_coordinateInverseScale_of_scoreVector_indep_gram
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Sigma := Sigma) (ScoreVectorLaw := ScoreVectorLaw)
      hScoreVector hW hScoreGramInd hScaleMap
  exact
    { joint_normal := hJoint
      score_prob := hScoreProb
      coordMap_aemeasurable := hCoordMap
      score_law := hScoreLaw
      residual_gram_wishart := hW
      coordinate_inverse_scale_map := hScaleMap
      score_inverse_scale_independent := hInd
      coefficient_product_ae := hCoeff
      scalar_product_tail :=
        twoSLSKinalScalarProductTailIff_of_scoreVectorProductTailIff
          (l₂ := l₂) ScoreVectorLaw hCoordMap hTail }

/-- Residual-Gram/product-tail package constructor using the canonical
push-forward law of the actual residualized FWL score vector. -/
theorem
    TwoSLSKinalResidualGramProductTailConditions.of_canonicalScoreVectorProductTail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (wishartLaw (n := l₂) Sigma)]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hScaleMap : ∀ j : k₂,
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))
    (hScoreGramInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((((twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) coordMap) :
    TwoSLSKinalResidualGramProductTailConditions
      μ X₁ Y₂ Z₂ Y₁ Sigma
      (fun j : k₂ =>
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          fun s : k₂ → ℝ => s j)
      coordMap :=
  TwoSLSKinalResidualGramProductTailConditions.of_scoreVectorProductTail
    hJoint (twoSLSKinalFWLScoreVector_hasLaw hJoint.aemeasurable_fwlScoreStar)
    hW hScaleMap hScoreGramInd hCoeff hCoordMap hTail

/-- The residual-Gram/product-tail package implies the exact Kinal moment iff. -/
theorem TwoSLSKinalResidualGramProductTailConditions.toExactMomentIff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (h :
      TwoSLSKinalResidualGramProductTailConditions
        μ X₁ Y₂ Z₂ Y₁ Sigma ScoreLaw coordMap) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ := by
  exact
    twoSLSKinalExactMomentIff_of_fwl_residualGram_product_tail
      (twoSLSKinal_fwl_ae_eq_of_jointNormalConditions h.joint_normal)
      Sigma ScoreLaw coordMap
      h.score_prob h.coordMap_aemeasurable h.score_law
      h.residual_gram_wishart h.coordinate_inverse_scale_map
      h.score_inverse_scale_independent h.coefficient_product_ae
      h.scalar_product_tail

/-- Hansen Theorem 12.7 from the exact residual-Gram/product-tail package.

This is the canonical theorem-facing closure in Kinal form: it proves the
finite-dimensional vector moment iff for the endogenous 2SLS block with the
threshold kept as `twoSLSKinalMomentThreshold`, i.e. `ℓ₂ - k₂ + 1`.  The
package assumptions are the genuine inverse-Gram/product-tail ingredients; the
conclusion itself is not assumed. -/
theorem twoSLSKinal_theorem12_7
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (h :
      TwoSLSKinalResidualGramProductTailConditions
        μ X₁ Y₂ Z₂ Y₁ Sigma ScoreLaw coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂ :=
  h.toExactMomentIff

/-- Hansen Theorem 12.7 from the theorem-facing residual-Gram/product-tail
condition package, with the finite-moment threshold displayed as
`ℓ₂ - k₂ + 1`. -/
theorem twoSLSKinal_theorem12_7_of_residualGramProductTailConditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (h :
      TwoSLSKinalResidualGramProductTailConditions
        μ X₁ Y₂ Z₂ Y₁ Sigma ScoreLaw coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
  twoSLSKinalExactMomentIff_card_threshold h.toExactMomentIff

/-- Theorem-facing standard-coordinate product-tail package for Hansen Theorem
12.7.

This package is the current strongest non-tautological public surface in this
file.  Compared with `TwoSLSKinalResidualGramProductTailConditions`, it removes
the redundant score-probability field and replaces the raw coordinate
inverse-Wishart map identities by the Chapter 11 standard-coordinate
whitening/alignment bridge. -/
structure TwoSLSKinalStandardCoordinateProductTailConditions
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ)
    (S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ)
    (c : k₂ → ℝ)
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ) : Prop where
  /-- Hansen's joint-normal and finite-sample rank/order assumptions. -/
  joint_normal : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁
  /-- The scalar product model is measurable under its product law. -/
  coordMap_aemeasurable : ∀ j : k₂,
    AEMeasurable (coordMap j)
      ((ScoreLaw j).prod
        (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))
  /-- Law of each residualized FWL score coordinate. -/
  score_law : ∀ j : k₂,
    HasLaw
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
      (ScoreLaw j) μ
  /-- Wishart law for the residualized fitted-endogenous Gram matrix. -/
  residual_gram_wishart :
    TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma
  /-- Chapter 11 standard-coordinate whitening/alignment bridge for the
  coordinate inverse-Wishart map identities. -/
  coordinate_inverse_wishart_whitening :
    TwoSLSKinalCoordinateInverseWishartWhiteningBridge (l₂ := l₂)
      Sigma T S c
  /-- Independence between each score coordinate and its inverse-scale
  statistic. -/
  score_inverse_scale_independent : ∀ j : k₂,
    (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
      ⟂ᵢ[μ]
    fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
      (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j
  /-- A.e. scalar product representation of each coefficient coordinate. -/
  coefficient_product_ae : ∀ j : k₂,
    (fun ω =>
      ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
        twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
      =ᵐ[μ]
    fun ω =>
      coordMap j
        (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
          twoSLSKinalFWLCoordinateInverseScaleStar
            (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
  /-- Scalar product-tail calculation giving exactly the Kinal threshold. -/
  scalar_product_tail :
    TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap

/-- The standard-coordinate product-tail package refines to the earlier
residual-Gram/product-tail package by deriving score probabilities and
coordinate inverse-Wishart map identities. -/
theorem TwoSLSKinalStandardCoordinateProductTailConditions.toResidualGramProductTailConditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (h :
      TwoSLSKinalStandardCoordinateProductTailConditions
        μ X₁ Y₂ Z₂ Y₁ Sigma T S c ScoreLaw coordMap) :
    TwoSLSKinalResidualGramProductTailConditions
      μ X₁ Y₂ Z₂ Y₁ Sigma ScoreLaw coordMap where
  joint_normal := h.joint_normal
  score_prob :=
    twoSLSKinal_scoreLaw_isProbabilityMeasure_of_jointNormalConditions
      h.joint_normal h.score_law
  coordMap_aemeasurable := h.coordMap_aemeasurable
  score_law := h.score_law
  residual_gram_wishart := h.residual_gram_wishart
  coordinate_inverse_scale_map := fun j =>
    twoSLSKinalCoordinateInverseScale_map_eq_of_standardCoordinate_whitening
      (l₂ := l₂) Sigma T S c h.coordinate_inverse_wishart_whitening j
  score_inverse_scale_independent := h.score_inverse_scale_independent
  coefficient_product_ae := h.coefficient_product_ae
  scalar_product_tail := h.scalar_product_tail

/-- The standard-coordinate product-tail package implies the exact Kinal
moment iff. -/
theorem TwoSLSKinalStandardCoordinateProductTailConditions.toExactMomentIff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (h :
      TwoSLSKinalStandardCoordinateProductTailConditions
        μ X₁ Y₂ Z₂ Y₁ Sigma T S c ScoreLaw coordMap) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  h.toResidualGramProductTailConditions.toExactMomentIff

/-- Hansen Theorem 12.7 from the standard-coordinate product-tail package,
with the finite-moment threshold displayed as `ℓ₂ - k₂ + 1`. -/
theorem twoSLSKinal_theorem12_7_of_standardCoordinateProductTailConditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (h :
      TwoSLSKinalStandardCoordinateProductTailConditions
        μ X₁ Y₂ Z₂ Y₁ Sigma T S c ScoreLaw coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
  twoSLSKinalExactMomentIff_card_threshold h.toExactMomentIff

omit [DecidableEq k₂] [DecidableEq l₂] in
/-- Under Hansen's order condition `k₂ ≤ ℓ₂`, the Kinal threshold
`ℓ₂ - k₂ + 1` is strictly positive. -/
theorem twoSLSKinalMomentThreshold_pos_of_instrument_count
    (h : Fintype.card k₂ ≤ Fintype.card l₂) :
    0 < twoSLSKinalMomentThreshold k₂ l₂ := by
  have hle : (Fintype.card k₂ : ℝ) ≤ (Fintype.card l₂ : ℝ) := by
    exact_mod_cast h
  unfold twoSLSKinalMomentThreshold
  linarith

/-- The scalar product-tail iff already contains the measurability needed by
the standard-coordinate product-tail package.  Under Hansen's order condition,
the threshold is positive, so applying the iff at moment order zero gives
`MemLp` for every scalar product model, hence a.e. measurability. -/
theorem twoSLSKinalScalarProductTailIff_coordMap_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hTail : TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap) :
    ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))) := by
  intro j
  have hpos : (0 : ℝ) < twoSLSKinalMomentThreshold k₂ l₂ :=
    twoSLSKinalMomentThreshold_pos_of_instrument_count hJoint.instrument_count
  have hzero :
      (((0 : ℝ≥0) : ℝ) < twoSLSKinalMomentThreshold k₂ l₂) := by
    simpa using hpos
  exact ((hTail 0).mpr hzero j).aestronglyMeasurable.aemeasurable

/-- Constructor for the standard-coordinate product-tail package from
Hansen's joint-normal assumptions and the remaining non-tautological Kinal
product-tail inputs.

Compared with constructing `TwoSLSKinalStandardCoordinateProductTailConditions`
directly, this discharges the scalar-product measurability field from the
scalar tail iff itself.  Score-law probabilities and coordinate
inverse-Wishart map identities are still derived later by the existing package
projection. -/
theorem TwoSLSKinalStandardCoordinateProductTailConditions.of_jointNormalConditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartWhiteningBridge (l₂ := l₂)
        Sigma T S c)
    (hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail : TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap) :
    TwoSLSKinalStandardCoordinateProductTailConditions
      μ X₁ Y₂ Z₂ Y₁ Sigma T S c ScoreLaw coordMap where
  joint_normal := hJoint
  coordMap_aemeasurable :=
    twoSLSKinalScalarProductTailIff_coordMap_aemeasurable hJoint hTail
  score_law := hScoreLaw
  residual_gram_wishart := hW
  coordinate_inverse_wishart_whitening := hBridge
  score_inverse_scale_independent := hInd
  coefficient_product_ae := hCoeff
  scalar_product_tail := hTail

/-- The exact Kinal inputs still to be derived from joint normality in order
to build the standard-coordinate product-tail package.

The fields here are deliberately the non-tautological pieces only.  Given a
`TwoSLSKinalJointNormalConditions` value, the existing local bridges derive
score-law probability, coordinate-product measurability, and the coordinate
inverse-Wishart map identities from these fields. -/
structure TwoSLSKinalJointNormalStandardCoordinateInputs
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ)
    (S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ)
    (c : k₂ → ℝ)
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ) : Prop where
  /-- Law of each residualized FWL score coordinate. -/
  score_law : ∀ j : k₂,
    HasLaw
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
      (ScoreLaw j) μ
  /-- Wishart law for the residualized fitted-endogenous Gram matrix. -/
  residual_gram_wishart :
    TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma
  /-- Chapter 11 standard-coordinate whitening/alignment data. -/
  coordinate_inverse_wishart_whitening :
    TwoSLSKinalCoordinateInverseWishartWhiteningBridge (l₂ := l₂)
      Sigma T S c
  /-- Independence between each score coordinate and its inverse-scale
  statistic. -/
  score_inverse_scale_independent : ∀ j : k₂,
    (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
      ⟂ᵢ[μ]
    fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
      (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j
  /-- A.e. scalar product representation of each coefficient coordinate. -/
  coefficient_product_ae : ∀ j : k₂,
    (fun ω =>
      ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
        twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
      =ᵐ[μ]
    fun ω =>
      coordMap j
        (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
          twoSLSKinalFWLCoordinateInverseScaleStar
            (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
  /-- Scalar product-tail calculation giving exactly the Kinal threshold. -/
  scalar_product_tail :
    TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap

/-- The remaining standard-coordinate inputs derive the coordinate
inverse-Wishart map identities through the Chapter 11 whitening bridge. -/
theorem TwoSLSKinalJointNormalStandardCoordinateInputs.coordinate_inverse_scale_map
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (h :
      TwoSLSKinalJointNormalStandardCoordinateInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma T S c ScoreLaw coordMap) :
    ∀ j : k₂,
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1) :=
  fun j =>
    twoSLSKinalCoordinateInverseScale_map_eq_of_standardCoordinate_whitening
      (l₂ := l₂) Sigma T S c h.coordinate_inverse_wishart_whitening j

/-- The remaining standard-coordinate inputs derive scalar product
measurability from the scalar product-tail iff and Hansen's order condition. -/
theorem TwoSLSKinalJointNormalStandardCoordinateInputs.coordMap_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (h :
      TwoSLSKinalJointNormalStandardCoordinateInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma T S c ScoreLaw coordMap) :
    ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))) :=
  twoSLSKinalScalarProductTailIff_coordMap_aemeasurable
    hJoint h.scalar_product_tail

/-- The remaining standard-coordinate inputs plus joint normality assemble the
standard-coordinate product-tail package. -/
theorem TwoSLSKinalJointNormalStandardCoordinateInputs.toStandardCoordinateProductTailConditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (h :
      TwoSLSKinalJointNormalStandardCoordinateInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma T S c ScoreLaw coordMap) :
    TwoSLSKinalStandardCoordinateProductTailConditions
      μ X₁ Y₂ Z₂ Y₁ Sigma T S c ScoreLaw coordMap :=
  TwoSLSKinalStandardCoordinateProductTailConditions.of_jointNormalConditions
    hJoint h.score_law h.residual_gram_wishart
    h.coordinate_inverse_wishart_whitening
    h.score_inverse_scale_independent h.coefficient_product_ae
    h.scalar_product_tail

/-- Joint normality plus the remaining exact Kinal inputs assemble the
standard-coordinate product-tail package. -/
theorem TwoSLSKinalJointNormalConditions.toStandardCoordinateProductTailConditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hInputs :
      TwoSLSKinalJointNormalStandardCoordinateInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma T S c ScoreLaw coordMap) :
    TwoSLSKinalStandardCoordinateProductTailConditions
      μ X₁ Y₂ Z₂ Y₁ Sigma T S c ScoreLaw coordMap :=
  hInputs.toStandardCoordinateProductTailConditions hJoint

/-- Hansen Theorem 12.7 directly from joint-normal assumptions plus the
remaining standard-coordinate product-tail inputs, with scalar-product
measurability derived from the scalar tail iff. -/
theorem twoSLSKinal_theorem12_7_of_jointNormal_standardCoordinateProductTail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreLaw j) μ)
    (hW : TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma)
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartWhiteningBridge (l₂ := l₂)
        Sigma T S c)
    (hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail : TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
  twoSLSKinal_theorem12_7_of_standardCoordinateProductTailConditions
    (TwoSLSKinalStandardCoordinateProductTailConditions.of_jointNormalConditions
      hJoint hScoreLaw hW hBridge hInd hCoeff hTail)

/-- Hansen Theorem 12.7 from joint normality plus the remaining exact
standard-coordinate derivation inputs, with the displayed Kinal threshold. -/
theorem twoSLSKinal_theorem12_7_of_jointNormal_standardCoordinateInputs
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hInputs :
      TwoSLSKinalJointNormalStandardCoordinateInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma T S c ScoreLaw coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
  twoSLSKinal_theorem12_7_of_standardCoordinateProductTailConditions
    (hJoint.toStandardCoordinateProductTailConditions hInputs)

/-- The exact nuisance-only standard-coordinate inputs still to be derived
from joint normality for Hansen Theorem 12.7.

This is the strongest current non-tautological bridge surface for the
Chapter 11 nuisance route.  Given `TwoSLSKinalJointNormalConditions`, the
lemmas below derive score-law probabilities, scalar-product measurability,
the deterministic FWL bridge, and the coordinate inverse-Wishart map
identities.  The remaining fields are the genuine stochastic Kinal inputs:
score-coordinate laws, residualized fitted-Gram Wishart law, nuisance
whitening/alignment data, score/scale independence, coefficient product
representation, and the scalar product-tail calculation. -/
structure TwoSLSKinalJointNormalStandardCoordinateNuisanceInputs
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ)
    (S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ)
    (c : k₂ → ℝ)
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ) : Prop where
  /-- Law of each residualized FWL score coordinate. -/
  score_law : ∀ j : k₂,
    HasLaw
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
      (ScoreLaw j) μ
  /-- Wishart law for the residualized fitted-endogenous Gram matrix. -/
  residual_gram_wishart :
    TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma
  /-- Chapter 11 nuisance-only standard-coordinate whitening/alignment data. -/
  coordinate_inverse_wishart_nuisance_whitening :
    TwoSLSKinalCoordinateInverseWishartNuisanceWhiteningBridge (l₂ := l₂)
      Sigma T S c
  /-- Independence between each score coordinate and its inverse-scale
  statistic. -/
  score_inverse_scale_independent : ∀ j : k₂,
    (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
      ⟂ᵢ[μ]
    fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
      (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j
  /-- A.e. scalar product representation of each coefficient coordinate. -/
  coefficient_product_ae : ∀ j : k₂,
    (fun ω =>
      ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
        twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
      =ᵐ[μ]
    fun ω =>
      coordMap j
        (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
          twoSLSKinalFWLCoordinateInverseScaleStar
            (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
  /-- Scalar product-tail calculation giving exactly the Kinal threshold. -/
  scalar_product_tail :
    TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap

/-- Constructor for the nuisance standard-coordinate input package from
Chapter 11-facing primitive stochastic pieces.

This derives the fitted residual-Gram Wishart field from an explicit
standardized `ℓ₂ × k₂` Gaussian matrix whose cross-product agrees a.e. with
the Kinal Gram, derives all score-coordinate laws from one score-vector law,
and derives score/inverse-scale independence from independence of the score
vector and the standardized Gram.  The remaining inputs are exactly the pieces
not supplied by the current repo API: nuisance whitening/alignment data, the
a.e. scalar coefficient product representation, and the scalar product-tail
calculation. -/
theorem TwoSLSKinalJointNormalStandardCoordinateNuisanceInputs.of_iidMatrixGaussian_gram_scoreVector
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartNuisanceWhiteningBridge (l₂ := l₂)
        Sigma T S c)
    (ScoreVectorLaw : Measure (k₂ → ℝ))
    [SFinite (wishartLaw (n := l₂) Sigma)]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hScoreVector :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreVectorLaw μ)
    (hScoreStdGramInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail :
      TwoSLSKinalScalarProductTailIff (l₂ := l₂)
        (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j) coordMap) :
    TwoSLSKinalJointNormalStandardCoordinateNuisanceInputs
      μ X₁ Y₂ Z₂ Y₁ Sigma T S c
      (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j) coordMap := by
  haveI : IsProbabilityMeasure μ := hJoint.joint_gaussian.isProbabilityMeasure
  have hW :
      TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma :=
    twoSLSKinalFittedResidualGramWishartLaw_of_iidMatrixGaussian_gram_ae_eq
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Sigma := Sigma)
      (Rstd := Rstd) hRstd hGram
  have hScoreGramInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω) :=
    twoSLSKinalFWLScoreStar_indep_gram_of_iidMatrixGaussian_gram_ae_eq
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Rstd := Rstd) hScoreStdGramInd hGram
  refine
    { score_law := ?_
      residual_gram_wishart := hW
      coordinate_inverse_wishart_nuisance_whitening := hBridge
      score_inverse_scale_independent := ?_
      coefficient_product_ae := hCoeff
      scalar_product_tail := hTail }
  · exact
      twoSLSKinalFWLScoreCoordinateLaws_of_scoreVectorLaw
        (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
        (ScoreVectorLaw := ScoreVectorLaw) hScoreVector
  · exact
      twoSLSKinalFWLScoreCoordinate_indep_coordinateInverseScale_of_scoreVector_indep_gram
        (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
        (Sigma := Sigma) (ScoreVectorLaw := ScoreVectorLaw)
        hScoreVector hW hScoreGramInd
        (fun j =>
          twoSLSKinalCoordinateInverseScale_map_eq_of_standardCoordinate_nuisance_whitening
            (l₂ := l₂) Sigma T S c hBridge j)

/-- Nuisance standard-coordinate inputs derive the coordinate inverse-Wishart
map identities through the Chapter 11 nuisance bridge. -/
theorem TwoSLSKinalJointNormalStandardCoordinateNuisanceInputs.coordinate_inverse_scale_map
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (h :
      TwoSLSKinalJointNormalStandardCoordinateNuisanceInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma T S c ScoreLaw coordMap) :
    ∀ j : k₂,
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1) :=
  fun j =>
    twoSLSKinalCoordinateInverseScale_map_eq_of_standardCoordinate_nuisance_whitening
      (l₂ := l₂) Sigma T S c
      h.coordinate_inverse_wishart_nuisance_whitening j

/-- Nuisance standard-coordinate inputs derive scalar-product measurability
from the scalar product-tail iff and Hansen's order condition. -/
theorem TwoSLSKinalJointNormalStandardCoordinateNuisanceInputs.coordMap_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (h :
      TwoSLSKinalJointNormalStandardCoordinateNuisanceInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma T S c ScoreLaw coordMap) :
    ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))) :=
  twoSLSKinalScalarProductTailIff_coordMap_aemeasurable
    hJoint h.scalar_product_tail

/-- Nuisance standard-coordinate inputs plus joint normality refine to the
residual-Gram/product-tail package. -/
theorem TwoSLSKinalJointNormalStandardCoordinateNuisanceInputs.toResidualGramProductTailConditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (h :
      TwoSLSKinalJointNormalStandardCoordinateNuisanceInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma T S c ScoreLaw coordMap) :
    TwoSLSKinalResidualGramProductTailConditions
      μ X₁ Y₂ Z₂ Y₁ Sigma ScoreLaw coordMap where
  joint_normal := hJoint
  score_prob :=
    twoSLSKinal_scoreLaw_isProbabilityMeasure_of_jointNormalConditions
      hJoint h.score_law
  coordMap_aemeasurable := h.coordMap_aemeasurable hJoint
  score_law := h.score_law
  residual_gram_wishart := h.residual_gram_wishart
  coordinate_inverse_scale_map := h.coordinate_inverse_scale_map
  score_inverse_scale_independent := h.score_inverse_scale_independent
  coefficient_product_ae := h.coefficient_product_ae
  scalar_product_tail := h.scalar_product_tail

/-- Nuisance standard-coordinate inputs plus joint normality imply the exact
Kinal moment iff. -/
theorem TwoSLSKinalJointNormalStandardCoordinateNuisanceInputs.toExactMomentIff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (h :
      TwoSLSKinalJointNormalStandardCoordinateNuisanceInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma T S c ScoreLaw coordMap) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  (h.toResidualGramProductTailConditions hJoint).toExactMomentIff

/-- Hansen Theorem 12.7 from joint normality plus the remaining exact
nuisance standard-coordinate inputs, with the displayed Kinal threshold. -/
theorem twoSLSKinal_theorem12_7_of_jointNormal_standardCoordinateNuisanceInputs
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (h :
      TwoSLSKinalJointNormalStandardCoordinateNuisanceInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma T S c ScoreLaw coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
  twoSLSKinalExactMomentIff_card_threshold (h.toExactMomentIff hJoint)

/-- Hansen Theorem 12.7 from a standardized Gaussian Gram representation and a
full score-vector law.

This composes the nuisance-input constructor
`TwoSLSKinalJointNormalStandardCoordinateNuisanceInputs.of_iidMatrixGaussian_gram_scoreVector`
with the theorem-facing nuisance-input endpoint.  The remaining premises are
the exact stochastic pieces not exposed by the current raw joint-normal package:
the standardized Gram representation, score-vector law and independence,
nuisance whitening/alignment data, coefficient product representation, and the
scalar product-tail calculation. -/
theorem twoSLSKinal_theorem12_7_of_iidGaussianGram_scoreVector
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {T : ∀ j : k₂, Matrix k₂ (Sum Unit (rIdx j)) ℝ}
    {S : ∀ j : k₂, Matrix (Sum Unit (rIdx j)) k₂ ℝ}
    {c : k₂ → ℝ}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartNuisanceWhiteningBridge (l₂ := l₂)
        Sigma T S c)
    (ScoreVectorLaw : Measure (k₂ → ℝ))
    [SFinite (wishartLaw (n := l₂) Sigma)]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hScoreVector :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreVectorLaw μ)
    (hScoreStdGramInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail :
      TwoSLSKinalScalarProductTailIff (l₂ := l₂)
        (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j) coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
  twoSLSKinal_theorem12_7_of_jointNormal_standardCoordinateNuisanceInputs
    hJoint
    (TwoSLSKinalJointNormalStandardCoordinateNuisanceInputs.of_iidMatrixGaussian_gram_scoreVector
      hJoint Rstd hRstd hGram hBridge ScoreVectorLaw
      hScoreVector hScoreStdGramInd hCoeff hTail)

/-- Hansen Theorem 12.7 from a standardized Gaussian Gram representation, a
full score-vector law, and Chapter 11 standard-Gram whitening data.

This is the standard-Gram analogue of
`twoSLSKinal_theorem12_7_of_iidGaussianGram_scoreVector`: the Kinal endpoint no
longer requires the nuisance rest-column rank certificate directly.  Chapter
11 derives that certificate from the canonical rectangular iid
standard-Gaussian Gram nonsingularity field inside
`TwoSLSKinalCoordinateInverseWishartStandardGramBridge`. -/
theorem twoSLSKinal_theorem12_7_of_iidGaussianGram_scoreVector_standardGramBridge
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
        Sigma (rIdx := rIdx))
    (ScoreVectorLaw : Measure (k₂ → ℝ))
    [SFinite (wishartLaw (n := l₂) Sigma)]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hScoreVector :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreVectorLaw μ)
    (hScoreStdGramInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail :
      TwoSLSKinalScalarProductTailIff (l₂ := l₂)
        (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j) coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 := by
  haveI : IsProbabilityMeasure μ := hJoint.joint_gaussian.isProbabilityMeasure
  have hW :
      TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma :=
    twoSLSKinalFittedResidualGramWishartLaw_of_iidMatrixGaussian_gram_ae_eq
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Sigma := Sigma)
      (Rstd := Rstd) hRstd hGram
  have hScoreGramInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω) :=
    twoSLSKinalFWLScoreStar_indep_gram_of_iidMatrixGaussian_gram_ae_eq
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Rstd := Rstd) hScoreStdGramInd hGram
  have hScoreLaw : ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ((ScoreVectorLaw.map fun s : k₂ → ℝ => s j)) μ :=
    twoSLSKinalFWLScoreCoordinateLaws_of_scoreVectorLaw
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (ScoreVectorLaw := ScoreVectorLaw) hScoreVector
  have hScaleMap : ∀ j : k₂,
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1) :=
    fun j =>
      twoSLSKinalCoordinateInverseScale_map_eq_of_standardGramBridge
        (l₂ := l₂) Sigma hBridge j
  have hInd : ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j :=
    twoSLSKinalFWLScoreCoordinate_indep_coordinateInverseScale_of_scoreVector_indep_gram
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Sigma := Sigma) (ScoreVectorLaw := ScoreVectorLaw)
      hScoreVector hW hScoreGramInd hScaleMap
  exact
    twoSLSKinal_theorem12_7_of_standardGram_product_tail_from_conditions
      (h := hJoint) (Sigma := Sigma) (rIdx := rIdx) hBridge
      (ScoreLaw := fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j)
      (coordMap := coordMap)
      (twoSLSKinalScalarProductTailIff_coordMap_aemeasurable
        hJoint hTail)
      hScoreLaw hW hInd hCoeff hTail

/-- The exact standard-Gram inputs still to be derived from joint normality for
Hansen Theorem 12.7.

This is the Chapter 11 standard-Gram version of
`TwoSLSKinalJointNormalStandardCoordinateNuisanceInputs`.  It replaces the
nuisance rest-column rank certificate by
`TwoSLSKinalCoordinateInverseWishartStandardGramBridge`, whose Chapter 11
endpoint derives that nuisance event from the canonical rectangular
standard-Gaussian Gram nonsingularity theorem. -/
structure TwoSLSKinalJointNormalStandardGramInputs
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (ScoreLaw : k₂ → Measure ℝ) (coordMap : k₂ → ℝ × ℝ → ℝ) : Prop where
  /-- Law of each residualized FWL score coordinate. -/
  score_law : ∀ j : k₂,
    HasLaw
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
      (ScoreLaw j) μ
  /-- Wishart law for the residualized fitted-endogenous Gram matrix. -/
  residual_gram_wishart :
    TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma
  /-- Chapter 11 standard-Gram/existential-whitening data. -/
  coordinate_inverse_wishart_standardGram :
    TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
      Sigma (rIdx := rIdx)
  /-- Independence between each score coordinate and its inverse-scale
  statistic. -/
  score_inverse_scale_independent : ∀ j : k₂,
    (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
      ⟂ᵢ[μ]
    fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
      (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j
  /-- A.e. scalar product representation of each coefficient coordinate. -/
  coefficient_product_ae : ∀ j : k₂,
    (fun ω =>
      ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
        twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
      =ᵐ[μ]
    fun ω =>
      coordMap j
        (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
          twoSLSKinalFWLCoordinateInverseScaleStar
            (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
  /-- Scalar product-tail calculation giving exactly the Kinal threshold. -/
  scalar_product_tail :
    TwoSLSKinalScalarProductTailIff (l₂ := l₂) ScoreLaw coordMap

/-- Constructor for the standard-Gram input package from Chapter 11-facing
primitive stochastic pieces.

This is the package version of
`twoSLSKinal_theorem12_7_of_iidGaussianGram_scoreVector_standardGramBridge`.
It derives the residualized fitted-Gram Wishart law, coordinate score laws,
and score/inverse-scale independence from a standardized Gaussian Gram
representation, one full score-vector law, and full score/standardized-Gram
independence. -/
theorem TwoSLSKinalJointNormalStandardGramInputs.of_iidMatrixGaussian_gram_scoreVector
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
        Sigma (rIdx := rIdx))
    (ScoreVectorLaw : Measure (k₂ → ℝ))
    [SFinite (wishartLaw (n := l₂) Sigma)]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hScoreVector :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreVectorLaw μ)
    (hScoreStdGramInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail :
      TwoSLSKinalScalarProductTailIff (l₂ := l₂)
        (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j) coordMap) :
    TwoSLSKinalJointNormalStandardGramInputs
      μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx)
      (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j) coordMap := by
  haveI : IsProbabilityMeasure μ := hJoint.joint_gaussian.isProbabilityMeasure
  have hW :
      TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma :=
    twoSLSKinalFittedResidualGramWishartLaw_of_iidMatrixGaussian_gram_ae_eq
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Sigma := Sigma)
      (Rstd := Rstd) hRstd hGram
  have hScoreGramInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω) :=
    twoSLSKinalFWLScoreStar_indep_gram_of_iidMatrixGaussian_gram_ae_eq
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Rstd := Rstd) hScoreStdGramInd hGram
  have hScaleMap : ∀ j : k₂,
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1) :=
    fun j =>
      twoSLSKinalCoordinateInverseScale_map_eq_of_standardGramBridge
        (l₂ := l₂) Sigma hBridge j
  refine
    { score_law := ?_
      residual_gram_wishart := hW
      coordinate_inverse_wishart_standardGram := hBridge
      score_inverse_scale_independent := ?_
      coefficient_product_ae := hCoeff
      scalar_product_tail := hTail }
  · exact
      twoSLSKinalFWLScoreCoordinateLaws_of_scoreVectorLaw
        (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
        (ScoreVectorLaw := ScoreVectorLaw) hScoreVector
  · exact
      twoSLSKinalFWLScoreCoordinate_indep_coordinateInverseScale_of_scoreVector_indep_gram
        (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
        (Sigma := Sigma) (ScoreVectorLaw := ScoreVectorLaw)
        hScoreVector hW hScoreGramInd hScaleMap

/-- Constructor for the standard-Gram input package from a vector-score
product-tail theorem.

This is the same stochastic reduction as
`TwoSLSKinalJointNormalStandardGramInputs.of_iidMatrixGaussian_gram_scoreVector`,
but it no longer asks for `TwoSLSKinalScalarProductTailIff` over the already
marginalized score-coordinate laws.  Instead, it accepts one product-tail
statement under the full score-vector law paired with the independent
chi-square inverse-scale variable, plus the scalar-product measurability
needed to transport that statement to each coordinate marginal. -/
theorem
    TwoSLSKinalJointNormalStandardGramInputs.of_iidMatrixGaussian_gram_scoreVector_vectorProductTail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
        Sigma (rIdx := rIdx))
    (ScoreVectorLaw : Measure (k₂ → ℝ))
    [SFinite (wishartLaw (n := l₂) Sigma)]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hScoreVector :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreVectorLaw μ)
    (hScoreStdGramInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        (((ScoreVectorLaw.map fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        ScoreVectorLaw coordMap) :
    TwoSLSKinalJointNormalStandardGramInputs
      μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx)
      (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j) coordMap := by
  haveI : IsProbabilityMeasure μ := hJoint.joint_gaussian.isProbabilityMeasure
  haveI : IsProbabilityMeasure ScoreVectorLaw :=
    (hScoreVector.isProbabilityMeasure_iff).1 inferInstance
  exact
    TwoSLSKinalJointNormalStandardGramInputs.of_iidMatrixGaussian_gram_scoreVector
      hJoint Rstd hRstd hGram hBridge ScoreVectorLaw hScoreVector
      hScoreStdGramInd hCoeff
      (twoSLSKinalScalarProductTailIff_of_scoreVectorProductTailIff
        (l₂ := l₂) ScoreVectorLaw hCoordMap hTail)

/-- Constructor for the standard-Gram input package from matrix-level
score/standardized-Gaussian independence.

Compared with
`TwoSLSKinalJointNormalStandardGramInputs.of_iidMatrixGaussian_gram_scoreVector`,
this version lets a raw Gaussian decomposition prove independence of the score
from the standardized matrix `Rstd`; the score/Gram independence is then
obtained by measurable composition with `matrixCrossProduct`. -/
theorem TwoSLSKinalJointNormalStandardGramInputs.of_iidMatrixGaussian_matrixIndep_scoreVector
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
        Sigma (rIdx := rIdx))
    (ScoreVectorLaw : Measure (k₂ → ℝ))
    [SFinite (wishartLaw (n := l₂) Sigma)]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hScoreVector :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreVectorLaw μ)
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail :
      TwoSLSKinalScalarProductTailIff (l₂ := l₂)
        (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j) coordMap) :
    TwoSLSKinalJointNormalStandardGramInputs
      μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx)
      (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j) coordMap :=
  TwoSLSKinalJointNormalStandardGramInputs.of_iidMatrixGaussian_gram_scoreVector
    hJoint Rstd hRstd hGram
    hBridge ScoreVectorLaw hScoreVector
    (by
      simpa [Function.comp_def] using
        IndepFun.comp (φ := id)
          (ψ := fun R : Matrix l₂ k₂ ℝ => matrixCrossProduct R)
          hScoreRstdInd measurable_id measurable_matrixCrossProduct_kinal)
    hCoeff hTail

/-- Constructor for the standard-Gram input package from matrix-level
score/standardized-Gaussian independence and a vector-score product-tail
theorem.

This combines
`TwoSLSKinalJointNormalStandardGramInputs.of_iidMatrixGaussian_matrixIndep_scoreVector`
and
`TwoSLSKinalJointNormalStandardGramInputs.of_iidMatrixGaussian_gram_scoreVector_vectorProductTail`:
raw Gaussian decomposition work can prove independence from the standardized
matrix `Rstd`, while the analytic tail calculation can stay at the full
score-vector level. -/
theorem
    TwoSLSKinalJointNormalStandardGramInputs.of_iidMatrixGaussian_matrixIndep_vectorTail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
        Sigma (rIdx := rIdx))
    (ScoreVectorLaw : Measure (k₂ → ℝ))
    [SFinite (wishartLaw (n := l₂) Sigma)]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hScoreVector :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreVectorLaw μ)
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        (((ScoreVectorLaw.map fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        ScoreVectorLaw coordMap) :
    TwoSLSKinalJointNormalStandardGramInputs
      μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx)
      (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j) coordMap := by
  have hScoreStdGramInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      fun ω => matrixCrossProduct (Rstd ω) := by
    simpa [Function.comp_def] using
      IndepFun.comp (φ := id)
        (ψ := fun R : Matrix l₂ k₂ ℝ => matrixCrossProduct R)
        hScoreRstdInd measurable_id measurable_matrixCrossProduct_kinal
  exact
    TwoSLSKinalJointNormalStandardGramInputs.of_iidMatrixGaussian_gram_scoreVector_vectorProductTail
      hJoint Rstd hRstd hGram hBridge ScoreVectorLaw hScoreVector
      hScoreStdGramInd hCoeff hCoordMap hTail

namespace TwoSLSKinalJointNormalStandardGramInputs

/-- Canonical-score-law version of
`of_iidMatrixGaussian_matrixIndep_scoreVector`.

This keeps the scalar product-tail route, but removes the artificial need to
choose a separate full score-vector law: the law is the push-forward of the
residualized FWL score vector itself. -/
theorem of_iidMatrixGaussian_matrixIndep_canonicalScoreLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
        Sigma (rIdx := rIdx))
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hScoreAEMeasurable :
      AEMeasurable
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) μ)
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail :
      TwoSLSKinalScalarProductTailIff (l₂ := l₂)
        (fun j : k₂ =>
          (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
            fun s : k₂ → ℝ => s j)
        coordMap) :
    TwoSLSKinalJointNormalStandardGramInputs
      μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx)
      (fun j : k₂ =>
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          fun s : k₂ → ℝ => s j)
      coordMap :=
  of_iidMatrixGaussian_matrixIndep_scoreVector
    hJoint Rstd hRstd hGram hBridge
    (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁)
    (twoSLSKinalFWLScoreVector_hasLaw hScoreAEMeasurable)
    hScoreRstdInd hCoeff hTail

/-- Canonical-score-law standard-Gram constructor with score-vector
measurability derived from the joint-normal Kinal data package. -/
theorem of_iidMatrixGaussian_matrixIndep_canonicalScoreLaw_autoMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
        Sigma (rIdx := rIdx))
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail :
      TwoSLSKinalScalarProductTailIff (l₂ := l₂)
        (fun j : k₂ =>
          (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
            fun s : k₂ → ℝ => s j)
        coordMap) :
    TwoSLSKinalJointNormalStandardGramInputs
      μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx)
      (fun j : k₂ =>
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          fun s : k₂ → ℝ => s j)
      coordMap :=
  of_iidMatrixGaussian_matrixIndep_canonicalScoreLaw
    hJoint Rstd hRstd hGram hBridge hJoint.aemeasurable_fwlScoreStar
    hScoreRstdInd hCoeff hTail

/-- Canonical-score-law version of `of_iidMatrixGaussian_matrixIndep_vectorTail`.

This removes the raw `ScoreVectorLaw` choice from the theorem boundary: the
score-vector law is the push-forward of the residualized FWL score itself. -/
theorem of_iidMatrixGaussian_matrixIndep_vectorTail_canonicalScoreLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
        Sigma (rIdx := rIdx))
    [SFinite (wishartLaw (n := l₂) Sigma)]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hScoreAEMeasurable :
      AEMeasurable
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) μ)
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((((twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) coordMap) :
    TwoSLSKinalJointNormalStandardGramInputs
      μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx)
      (fun j : k₂ =>
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          fun s : k₂ → ℝ => s j)
      coordMap :=
    of_iidMatrixGaussian_matrixIndep_vectorTail
      hJoint Rstd hRstd hGram hBridge
      (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁)
      (twoSLSKinalFWLScoreVector_hasLaw hScoreAEMeasurable)
      hScoreRstdInd hCoeff hCoordMap hTail

/-- Canonical-score-law standard-Gram input constructor with score-vector
measurability derived from the joint-normal Kinal data package. -/
theorem of_iidMatrixGaussian_matrixIndep_vectorTail_canonicalScoreLaw_autoMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hBridge :
      TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
        Sigma (rIdx := rIdx))
    [SFinite (wishartLaw (n := l₂) Sigma)]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((((twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) coordMap) :
    TwoSLSKinalJointNormalStandardGramInputs
      μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx)
      (fun j : k₂ =>
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          fun s : k₂ → ℝ => s j)
      coordMap :=
  of_iidMatrixGaussian_matrixIndep_vectorTail_canonicalScoreLaw
    hJoint Rstd hRstd hGram hBridge hJoint.aemeasurable_fwlScoreStar
    hScoreRstdInd hCoeff hCoordMap hTail

end TwoSLSKinalJointNormalStandardGramInputs

/-- Standard-Gram inputs derive the coordinate inverse-Wishart map identities
through the Chapter 11 standard-Gram bridge. -/
theorem TwoSLSKinalJointNormalStandardGramInputs.coordinate_inverse_scale_map
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (h :
      TwoSLSKinalJointNormalStandardGramInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) ScoreLaw coordMap) :
    ∀ j : k₂,
      (wishartLaw (n := l₂) Sigma).map
          (inverseWishartScaledLinearForm Sigma (Pi.single j (1 : ℝ))) =
        chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1) :=
  fun j =>
    twoSLSKinalCoordinateInverseScale_map_eq_of_standardGramBridge
      (l₂ := l₂) Sigma h.coordinate_inverse_wishart_standardGram j

/-- Standard-Gram inputs derive scalar-product measurability from the scalar
product-tail iff and Hansen's order condition. -/
theorem TwoSLSKinalJointNormalStandardGramInputs.coordMap_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (h :
      TwoSLSKinalJointNormalStandardGramInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) ScoreLaw coordMap) :
    ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((ScoreLaw j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))) :=
  twoSLSKinalScalarProductTailIff_coordMap_aemeasurable
    hJoint h.scalar_product_tail

/-- Standard-Gram inputs plus joint normality refine to the residual-Gram
product-tail package. -/
theorem TwoSLSKinalJointNormalStandardGramInputs.toResidualGramProductTailConditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (h :
      TwoSLSKinalJointNormalStandardGramInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) ScoreLaw coordMap) :
    TwoSLSKinalResidualGramProductTailConditions
      μ X₁ Y₂ Z₂ Y₁ Sigma ScoreLaw coordMap where
  joint_normal := hJoint
  score_prob :=
    twoSLSKinal_scoreLaw_isProbabilityMeasure_of_jointNormalConditions
      hJoint h.score_law
  coordMap_aemeasurable := h.coordMap_aemeasurable hJoint
  score_law := h.score_law
  residual_gram_wishart := h.residual_gram_wishart
  coordinate_inverse_scale_map := h.coordinate_inverse_scale_map
  score_inverse_scale_independent := h.score_inverse_scale_independent
  coefficient_product_ae := h.coefficient_product_ae
  scalar_product_tail := h.scalar_product_tail

/-- Standard-Gram inputs plus joint normality imply the exact Kinal moment
iff. -/
theorem TwoSLSKinalJointNormalStandardGramInputs.toExactMomentIff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (h :
      TwoSLSKinalJointNormalStandardGramInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) ScoreLaw coordMap) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  (h.toResidualGramProductTailConditions hJoint).toExactMomentIff

/-- Hansen Theorem 12.7 from joint normality plus the remaining exact
standard-Gram inputs, with the displayed Kinal threshold. -/
theorem twoSLSKinal_theorem12_7_of_jointNormal_standardGramInputs
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {ScoreLaw : k₂ → Measure ℝ} {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (h :
      TwoSLSKinalJointNormalStandardGramInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) ScoreLaw coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
  twoSLSKinalExactMomentIff_card_threshold (h.toExactMomentIff hJoint)

/-- Strong Hansen-facing decomposition package for Kinal's Theorem 12.7.

This is stronger than the raw `HasGaussianLaw` field in
`TwoSLSKinalJointNormalConditions`, but it avoids weakening Hansen's theorem:
each remaining stochastic claim is an explicit decomposition fact that should
be proved from the concrete mean/covariance block structure of the jointly
normal reduced-form model.  The inverse-Wishart nuisance bridge is not a field;
it is derived below from `Σ.PosDef`, Hansen's order condition, and the
coordinate dimension split by reusing Chapter 11. -/
structure TwoSLSKinalJointNormalGaussianDecompositionConditions
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ)
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (ScoreVectorLaw : Measure (k₂ → ℝ))
    (coordMap : k₂ → ℝ × ℝ → ℝ) : Prop where
  /-- Hansen's raw joint-normal and rank/order assumptions. -/
  joint_normal : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁
  /-- Positive-definite residual-Gram scale matrix. -/
  sigma_posDef : Sigma.PosDef
  /-- The standard-coordinate split has the same dimension as the endogenous
  block for every coefficient coordinate. -/
  card_dim : ∀ j : k₂,
    Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂
  /-- Standardized Gaussian residualized fitted-endogenous matrix. -/
  standardized_gaussian_matrix :
    HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ
  /-- Its cross-product is the Kinal residualized fitted-endogenous Gram
  matrix a.e. -/
  gram_ae_eq :
    (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
      =ᵐ[μ]
    fun ω => matrixCrossProduct (Rstd ω)
  /-- Full residualized FWL score-vector law. -/
  score_vector_law :
    HasLaw
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      ScoreVectorLaw μ
  /-- Full score-vector independence from the standardized Gram. -/
  score_standardized_gram_independent :
    (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      ⟂ᵢ[μ]
    fun ω => matrixCrossProduct (Rstd ω)
  /-- A.e. scalar product representation of each coefficient coordinate. -/
  coefficient_product_ae : ∀ j : k₂,
    (fun ω =>
      ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
        twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
      =ᵐ[μ]
    fun ω =>
      coordMap j
        (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
          twoSLSKinalFWLCoordinateInverseScaleStar
            (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)
  /-- Scalar product-tail calculation giving exactly the Kinal threshold. -/
  scalar_product_tail :
    TwoSLSKinalScalarProductTailIff (l₂ := l₂)
      (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j)
      coordMap

/-- Constructor for the strong Gaussian decomposition package from the
matrix-level independence and vector-tail form closest to a raw joint-normal
decomposition.

The constructor derives two fields that are otherwise easy to assemble
manually and inconsistently: score/standardized-Gram independence follows from
score/standardized-matrix independence by measurable composition, and the
coordinate scalar product-tail iff follows from the full score-vector
product-tail theorem by measure transport. -/
theorem
    TwoSLSKinalJointNormalGaussianDecompositionConditions.of_iidGaussian_matrixIndep_vectorTail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {ScoreVectorLaw : Measure (k₂ → ℝ)}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hcard_dim : ∀ j : k₂,
      Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreVector :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreVectorLaw μ)
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        (((ScoreVectorLaw.map fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        ScoreVectorLaw coordMap) :
    TwoSLSKinalJointNormalGaussianDecompositionConditions
      μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx)
      Rstd ScoreVectorLaw coordMap := by
  haveI : IsProbabilityMeasure μ := hJoint.joint_gaussian.isProbabilityMeasure
  haveI : IsProbabilityMeasure ScoreVectorLaw :=
    (hScoreVector.isProbabilityMeasure_iff).1 inferInstance
  refine
    { joint_normal := hJoint
      sigma_posDef := hSigma
      card_dim := hcard_dim
      standardized_gaussian_matrix := hRstd
      gram_ae_eq := hGram
      score_vector_law := hScoreVector
      score_standardized_gram_independent := ?_
      coefficient_product_ae := hCoeff
      scalar_product_tail := ?_ }
  · simpa [Function.comp_def] using
      IndepFun.comp (φ := id)
        (ψ := fun R : Matrix l₂ k₂ ℝ => matrixCrossProduct R)
        hScoreRstdInd measurable_id measurable_matrixCrossProduct_kinal
  · exact
      twoSLSKinalScalarProductTailIff_of_scoreVectorProductTailIff
        (l₂ := l₂) ScoreVectorLaw hCoordMap hTail

namespace TwoSLSKinalJointNormalGaussianDecompositionConditions

/-- Canonical-score-law version of `of_iidGaussian_matrixIndep_vectorTail`.

This narrows the Gaussian decomposition boundary by using the actual
push-forward law of the residualized FWL score vector. -/
theorem of_iidGaussian_matrixIndep_vectorTail_canonicalScoreLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hcard_dim : ∀ j : k₂,
      Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreAEMeasurable :
      AEMeasurable
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) μ)
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((((twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) coordMap) :
    TwoSLSKinalJointNormalGaussianDecompositionConditions
      μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) Rstd
      (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) coordMap :=
    of_iidGaussian_matrixIndep_vectorTail
      hJoint hSigma hcard_dim hRstd hGram
      (twoSLSKinalFWLScoreVector_hasLaw hScoreAEMeasurable)
      hScoreRstdInd hCoeff hCoordMap hTail

/-- Canonical-score-law Gaussian decomposition constructor with score-vector
measurability derived from the joint-normal Kinal data package. -/
theorem of_iidGaussian_matrixIndep_vectorTail_canonicalScoreLaw_autoMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hcard_dim : ∀ j : k₂,
      Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((((twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) coordMap) :
    TwoSLSKinalJointNormalGaussianDecompositionConditions
      μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) Rstd
      (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) coordMap :=
  of_iidGaussian_matrixIndep_vectorTail_canonicalScoreLaw
    hJoint hSigma hcard_dim hRstd hGram hJoint.aemeasurable_fwlScoreStar
    hScoreRstdInd hCoeff hCoordMap hTail

/-- Vector-tail Gaussian decomposition constructor from raw joint-Gaussian
score/matrix coordinates and zero cross-covariances.

This is the theorem-facing normal-theory independence step in Hansen's Kinal
argument: once the finite vector `(score, vec Rstd)` is jointly Gaussian and
all score/matrix coordinate covariances vanish, Mathlib supplies independence
of the score vector from the standardized Gaussian matrix.  The existing
matrix-independence constructor then derives independence from the Gram and
the coordinate scalar tails. -/
theorem of_iidGaussian_coordinateCovarianceZero_vectorTail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {ScoreVectorLaw : Measure (k₂ → ℝ)}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hcard_dim : ∀ j : k₂,
      Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreVector :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreVectorLaw μ)
    (hScoreRstdGaussian :
      HasGaussianLaw
        (fun ω =>
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω),
            fun p : l₂ × k₂ => Rstd ω p.1 p.2)) μ)
    (hScoreRstdCovZero : ∀ (j : k₂) (p : l₂ × k₂),
      cov[
        fun ω => twoSLSKinalFWLScoreStar
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
        fun ω => Rstd ω p.1 p.2;
        μ] = 0)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        (((ScoreVectorLaw.map fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        ScoreVectorLaw coordMap) :
    TwoSLSKinalJointNormalGaussianDecompositionConditions
      μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) Rstd
      ScoreVectorLaw coordMap :=
  of_iidGaussian_matrixIndep_vectorTail
    hJoint hSigma hcard_dim hRstd hGram hScoreVector
    (twoSLSKinalFWLScoreStar_indep_Rstd_of_jointGaussian_coordinate_covariance_zero
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Rstd := Rstd) hScoreRstdGaussian hScoreRstdCovZero)
    hCoeff hCoordMap hTail

/-- Canonical-score-law version of
`of_iidGaussian_coordinateCovarianceZero_vectorTail`.

The residualized FWL score-vector law is the push-forward law generated by the
score itself; only the raw joint-Gaussian score/matrix covariance calculation
and the analytic vector-product tail remain as stochastic inputs. -/
theorem of_iidGaussian_coordinateCovarianceZero_vectorTail_canonicalScoreLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hcard_dim : ∀ j : k₂,
      Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreAEMeasurable :
      AEMeasurable
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) μ)
    (hScoreRstdGaussian :
      HasGaussianLaw
        (fun ω =>
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω),
            fun p : l₂ × k₂ => Rstd ω p.1 p.2)) μ)
    (hScoreRstdCovZero : ∀ (j : k₂) (p : l₂ × k₂),
      cov[
        fun ω => twoSLSKinalFWLScoreStar
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
        fun ω => Rstd ω p.1 p.2;
        μ] = 0)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((((twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) coordMap) :
    TwoSLSKinalJointNormalGaussianDecompositionConditions
      μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) Rstd
      (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) coordMap :=
  of_iidGaussian_coordinateCovarianceZero_vectorTail
    hJoint hSigma hcard_dim hRstd hGram
    (twoSLSKinalFWLScoreVector_hasLaw hScoreAEMeasurable)
    hScoreRstdGaussian hScoreRstdCovZero hCoeff hCoordMap hTail

/-- Canonical-score-law coordinate-covariance constructor with score-vector
measurability derived from the joint-normal Kinal data package. -/
theorem of_iidGaussian_coordinateCovarianceZero_vectorTail_canonicalScoreLaw_autoMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hcard_dim : ∀ j : k₂,
      Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRstdGaussian :
      HasGaussianLaw
        (fun ω =>
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω),
            fun p : l₂ × k₂ => Rstd ω p.1 p.2)) μ)
    (hScoreRstdCovZero : ∀ (j : k₂) (p : l₂ × k₂),
      cov[
        fun ω => twoSLSKinalFWLScoreStar
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
        fun ω => Rstd ω p.1 p.2;
        μ] = 0)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((((twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) coordMap) :
    TwoSLSKinalJointNormalGaussianDecompositionConditions
      μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) Rstd
      (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) coordMap :=
  of_iidGaussian_coordinateCovarianceZero_vectorTail_canonicalScoreLaw
    hJoint hSigma hcard_dim hRstd hGram hJoint.aemeasurable_fwlScoreStar
    hScoreRstdGaussian hScoreRstdCovZero hCoeff hCoordMap hTail

/-- Scalar-tail Gaussian decomposition constructor from raw joint-Gaussian
score/matrix coordinates and zero cross-covariances, using the canonical score
law.

Compared with
`of_iidGaussian_coordinateCovarianceZero_vectorTail_canonicalScoreLaw_autoMeasurable`,
this constructor accepts the already-coordinatewise scalar product-tail
calculation.  It derives the canonical score-vector law from the joint-normal
data package and derives score/standardized-Gram independence from the raw
joint Gaussian zero cross-covariances. -/
theorem of_iidGaussian_coordinateCovarianceZero_scalarTail_canonicalScoreLaw_autoMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hcard_dim : ∀ j : k₂,
      Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRstdGaussian :
      HasGaussianLaw
        (fun ω =>
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω),
            fun p : l₂ × k₂ => Rstd ω p.1 p.2)) μ)
    (hScoreRstdCovZero : ∀ (j : k₂) (p : l₂ × k₂),
      cov[
        fun ω => twoSLSKinalFWLScoreStar
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
        fun ω => Rstd ω p.1 p.2;
        μ] = 0)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail :
      TwoSLSKinalScalarProductTailIff (l₂ := l₂)
        (fun j : k₂ =>
          (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
            fun s : k₂ → ℝ => s j)
        coordMap) :
    TwoSLSKinalJointNormalGaussianDecompositionConditions
      μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) Rstd
      (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) coordMap := by
  have hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd :=
    twoSLSKinalFWLScoreStar_indep_Rstd_of_jointGaussian_coordinate_covariance_zero
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Rstd := Rstd) hScoreRstdGaussian hScoreRstdCovZero
  refine
    { joint_normal := hJoint
      sigma_posDef := hSigma
      card_dim := hcard_dim
      standardized_gaussian_matrix := hRstd
      gram_ae_eq := hGram
      score_vector_law :=
        twoSLSKinalFWLScoreVector_hasLaw hJoint.aemeasurable_fwlScoreStar
      score_standardized_gram_independent := ?_
      coefficient_product_ae := hCoeff
      scalar_product_tail := hTail }
  simpa [Function.comp_def] using
    IndepFun.comp (φ := id)
      (ψ := fun R : Matrix l₂ k₂ ℝ => matrixCrossProduct R)
      hScoreRstdInd measurable_id measurable_matrixCrossProduct_kinal

end TwoSLSKinalJointNormalGaussianDecompositionConditions

/-- The strong Gaussian decomposition package derives the Chapter 11
standard-Gram inverse-Wishart bridge. -/
theorem TwoSLSKinalJointNormalGaussianDecompositionConditions.standardGramBridge
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {ScoreVectorLaw : Measure (k₂ → ℝ)}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (h :
      TwoSLSKinalJointNormalGaussianDecompositionConditions
        μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) Rstd ScoreVectorLaw coordMap) :
    TwoSLSKinalCoordinateInverseWishartStandardGramBridge (l₂ := l₂)
      Sigma (rIdx := rIdx) :=
  TwoSLSKinalCoordinateInverseWishartStandardGramBridge.of_posDef_cardDim
    (l₂ := l₂) Sigma h.sigma_posDef
    h.joint_normal.instrument_count h.card_dim

/-- The strong Gaussian decomposition package supplies the fitted
residual-Gram Wishart law used by the residual-Gram product-tail route. -/
theorem TwoSLSKinalJointNormalGaussianDecompositionConditions.residualGramWishartLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {ScoreVectorLaw : Measure (k₂ → ℝ)}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (h :
      TwoSLSKinalJointNormalGaussianDecompositionConditions
        μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) Rstd ScoreVectorLaw coordMap) :
    TwoSLSKinalFittedResidualGramWishartLaw μ X₁ Y₂ Z₂ Sigma :=
  twoSLSKinalFittedResidualGramWishartLaw_of_iidMatrixGaussian_gram_ae_eq
    (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Sigma := Sigma)
    (Rstd := Rstd) h.standardized_gaussian_matrix h.gram_ae_eq

/-- The strong Gaussian decomposition package transports score independence
from the standardized Gram to the actual Kinal FWL Gram. -/
theorem TwoSLSKinalJointNormalGaussianDecompositionConditions.score_independent_gram
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {ScoreVectorLaw : Measure (k₂ → ℝ)}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (h :
      TwoSLSKinalJointNormalGaussianDecompositionConditions
        μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) Rstd ScoreVectorLaw coordMap) :
    (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω) :=
  twoSLSKinalFWLScoreStar_indep_gram_of_iidMatrixGaussian_gram_ae_eq
    (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
    (Rstd := Rstd) h.score_standardized_gram_independent h.gram_ae_eq

/-- The full score-vector law in the strong Gaussian decomposition package
supplies all coordinate score laws. -/
theorem TwoSLSKinalJointNormalGaussianDecompositionConditions.coordinate_score_laws
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {ScoreVectorLaw : Measure (k₂ → ℝ)}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    (h :
      TwoSLSKinalJointNormalGaussianDecompositionConditions
        μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) Rstd ScoreVectorLaw coordMap) :
    ∀ j : k₂,
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        (ScoreVectorLaw.map fun s : k₂ → ℝ => s j) μ :=
  twoSLSKinalFWLScoreCoordinateLaws_of_scoreVectorLaw
    (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
    (ScoreVectorLaw := ScoreVectorLaw) h.score_vector_law

/-- The strong Gaussian decomposition package supplies coordinate
score/inverse-scale independence after Chapter 11 identifies the coordinate
inverse-Wishart scale laws. -/
theorem
    TwoSLSKinalJointNormalGaussianDecompositionConditions.coordinate_score_inverseScale_independent
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {ScoreVectorLaw : Measure (k₂ → ℝ)}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (h :
      TwoSLSKinalJointNormalGaussianDecompositionConditions
        μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) Rstd ScoreVectorLaw coordMap) :
    ∀ j : k₂,
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j)
        ⟂ᵢ[μ]
      fun ω => twoSLSKinalFWLCoordinateInverseScaleStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j := by
  haveI : IsProbabilityMeasure μ := h.joint_normal.joint_gaussian.isProbabilityMeasure
  exact
    twoSLSKinalFWLScoreCoordinate_indep_coordinateInverseScale_of_scoreVector_indep_gram
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Sigma := Sigma) (ScoreVectorLaw := ScoreVectorLaw)
      h.score_vector_law h.residualGramWishartLaw h.score_independent_gram
      (fun j =>
        twoSLSKinalCoordinateInverseScale_map_eq_of_standardGramBridge
          (l₂ := l₂) Sigma h.standardGramBridge j)

/-- The strong Gaussian decomposition package refines to the existing
standard-Gram input package. -/
theorem TwoSLSKinalJointNormalGaussianDecompositionConditions.toStandardGramInputs
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {ScoreVectorLaw : Measure (k₂ → ℝ)}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (h :
      TwoSLSKinalJointNormalGaussianDecompositionConditions
        μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) Rstd ScoreVectorLaw coordMap) :
    TwoSLSKinalJointNormalStandardGramInputs
      μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx)
      (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j)
      coordMap :=
  TwoSLSKinalJointNormalStandardGramInputs.of_iidMatrixGaussian_gram_scoreVector
    h.joint_normal Rstd h.standardized_gaussian_matrix h.gram_ae_eq
    h.standardGramBridge ScoreVectorLaw h.score_vector_law
    h.score_standardized_gram_independent h.coefficient_product_ae
    h.scalar_product_tail

/-- The strong Gaussian decomposition package refines directly to the
residual-Gram/product-tail package. -/
theorem TwoSLSKinalJointNormalGaussianDecompositionConditions.toResidualGramProductTailConditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {ScoreVectorLaw : Measure (k₂ → ℝ)}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (h :
      TwoSLSKinalJointNormalGaussianDecompositionConditions
        μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) Rstd ScoreVectorLaw coordMap) :
    TwoSLSKinalResidualGramProductTailConditions
      μ X₁ Y₂ Z₂ Y₁ Sigma
      (fun j : k₂ => ScoreVectorLaw.map fun s : k₂ → ℝ => s j)
      coordMap :=
  h.toStandardGramInputs.toResidualGramProductTailConditions h.joint_normal

/-- The strong Gaussian decomposition package implies the exact Kinal moment
iff. -/
theorem TwoSLSKinalJointNormalGaussianDecompositionConditions.toExactMomentIff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {ScoreVectorLaw : Measure (k₂ → ℝ)}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (h :
      TwoSLSKinalJointNormalGaussianDecompositionConditions
        μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) Rstd ScoreVectorLaw coordMap) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  (h.toStandardGramInputs).toExactMomentIff h.joint_normal

/-- Hansen Theorem 12.7 from the strong joint-normal Gaussian decomposition
package, with the displayed Kinal threshold. -/
theorem twoSLSKinal_theorem12_7_of_jointNormal_gaussianDecompositionConditions
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    [∀ j : k₂, DecidableEq (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {ScoreVectorLaw : Measure (k₂ → ℝ)}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (h :
      TwoSLSKinalJointNormalGaussianDecompositionConditions
        μ X₁ Y₂ Z₂ Y₁ Sigma (rIdx := rIdx) Rstd ScoreVectorLaw coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
  twoSLSKinalExactMomentIff_card_threshold h.toExactMomentIff

/-- Hansen Theorem 12.7 from the matrix-level Gaussian decomposition and
full score-vector product-tail form.

This is the strongest theorem-facing bridge in this file below the raw
joint-normal covariance calculation: it derives the Chapter 11 standard-Gram
inverse-Wishart bridge from `Σ.PosDef`, Hansen's order condition, and the
coordinate dimension split; transports score independence from the standardized
matrix to its Gram; and converts the vector-score product-tail iff to the
coordinate scalar iff without weakening the threshold. -/
theorem
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_vectorTail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {ScoreVectorLaw : Measure (k₂ → ℝ)}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hcard_dim : ∀ j : k₂,
      Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreVector :
      HasLaw
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ScoreVectorLaw μ)
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        (((ScoreVectorLaw.map fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        ScoreVectorLaw coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
by
  classical
  exact
    twoSLSKinal_theorem12_7_of_jointNormal_gaussianDecompositionConditions
      (TwoSLSKinalJointNormalGaussianDecompositionConditions.of_iidGaussian_matrixIndep_vectorTail
        hJoint hSigma hcard_dim hRstd hGram hScoreVector hScoreRstdInd
        hCoeff hCoordMap hTail)

/-- Canonical-score-law scalar-tail version of the Gaussian-matrix
decomposition endpoint.

This keeps Hansen's exact threshold and removes two bookkeeping assumptions
from the scalar-tail route: a caller no longer has to choose a separate
full-score law, and scalar-product measurability is derived from the scalar
tail iff by the standard-Gram input package. -/
theorem
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_scalarTail_canonicalScoreLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hcard_dim : ∀ j : k₂,
      Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreAEMeasurable :
      AEMeasurable
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) μ)
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail :
      TwoSLSKinalScalarProductTailIff (l₂ := l₂)
        (fun j : k₂ =>
          (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
            fun s : k₂ → ℝ => s j)
        coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
by
  classical
  exact
    twoSLSKinal_theorem12_7_of_jointNormal_standardGramInputs
      hJoint
      (TwoSLSKinalJointNormalStandardGramInputs.of_iidMatrixGaussian_matrixIndep_canonicalScoreLaw
        (rIdx := rIdx) hJoint Rstd hRstd hGram
        (TwoSLSKinalCoordinateInverseWishartStandardGramBridge.of_posDef_cardDim
          (l₂ := l₂) Sigma hSigma hJoint.instrument_count hcard_dim)
        hScoreAEMeasurable hScoreRstdInd hCoeff hTail)

/-- Hansen Theorem 12.7 from a standardized Gaussian-matrix decomposition and
the canonical scalar-tail route, with score-vector measurability derived from
the joint-normal Kinal data package. -/
theorem
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_scalarTail_canonicalScoreLaw_auto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hcard_dim : ∀ j : k₂,
      Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail :
      TwoSLSKinalScalarProductTailIff (l₂ := l₂)
        (fun j : k₂ =>
          (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
            fun s : k₂ → ℝ => s j)
        coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
by
  classical
  exact
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_scalarTail_canonicalScoreLaw
      hJoint hSigma hcard_dim hRstd hGram hJoint.aemeasurable_fwlScoreStar
      hScoreRstdInd hCoeff hTail

/-- Canonical-score-law version of
`twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_vectorTail`.

This keeps Hansen's exact threshold and removes the artificial need to choose a
separate full score-vector law: the law is the push-forward of the residualized
FWL score vector itself. -/
theorem
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_vectorTail_canonicalScoreLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hcard_dim : ∀ j : k₂,
      Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreAEMeasurable :
      AEMeasurable
        (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) μ)
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((((twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
by
  classical
    exact
      twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_vectorTail
        hJoint hSigma hcard_dim hRstd hGram
        (twoSLSKinalFWLScoreVector_hasLaw hScoreAEMeasurable)
        hScoreRstdInd hCoeff hCoordMap hTail

set_option linter.style.longLine false in
/-- Hansen Theorem 12.7 from a standardized Gaussian-matrix decomposition and
the canonical residualized FWL score law, with score-vector measurability
derived from the joint-normal Kinal data package. -/
theorem
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_vectorTail_canonicalScoreLaw_autoMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {rIdx : k₂ → Type*} [∀ j : k₂, Fintype (rIdx j)]
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hcard_dim : ∀ j : k₂,
      Fintype.card (Sum Unit (rIdx j)) = Fintype.card k₂)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((((twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
by
  classical
  exact
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_vectorTail_canonicalScoreLaw
      hJoint hSigma hcard_dim hRstd hGram hJoint.aemeasurable_fwlScoreStar
      hScoreRstdInd hCoeff hCoordMap hTail

set_option linter.style.longLine false in
/-- Canonical-rest version of
`twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_vectorTail_canonicalScoreLaw_autoMeasurable`.

The standard-coordinate nuisance index is fixed to the canonical family
`{i // i ≠ j}`, so the theorem boundary no longer includes the raw
bookkeeping premise
`∀ j, card (Unit ⊕ rIdx j) = card k₂`.  The exact Hansen threshold and iff are
unchanged. -/
theorem
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_vectorTail_canonicalRest
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((((twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
by
  classical
  exact
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_vectorTail_canonicalScoreLaw_autoMeasurable
      (rIdx := fun j : k₂ => kinalCoordinateRestIdx j)
      hJoint hSigma (fun j => kinalCoordinateRestIdx_card_dim (k₂ := k₂) j)
      hRstd hGram hScoreRstdInd hCoeff hCoordMap hTail

set_option linter.style.longLine false in
/-- Canonical-rest scalar-tail version of
`twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_scalarTail_canonicalScoreLaw_auto`.

This is the scalar-tail analogue of
`twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_vectorTail_canonicalRest`:
the standard-coordinate nuisance index is fixed to `{i // i ≠ j}`, so callers
do not have to provide the cardinality bookkeeping premise. -/
theorem
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_scalarTail_canonicalRest
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail :
      TwoSLSKinalScalarProductTailIff (l₂ := l₂)
        (fun j : k₂ =>
          (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
            fun s : k₂ → ℝ => s j)
        coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
by
  classical
  exact
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_scalarTail_canonicalScoreLaw_auto
      (rIdx := fun j : k₂ => kinalCoordinateRestIdx j)
      hJoint hSigma (fun j => kinalCoordinateRestIdx_card_dim (k₂ := k₂) j)
      hRstd hGram hScoreRstdInd hCoeff hTail

set_option linter.style.longLine false in
/-- Canonical-rest vector-tail Kinal endpoint from raw joint-Gaussian
score/matrix coordinate covariances.

Compared with
`twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_vectorTail_canonicalRest`,
this theorem no longer assumes score/Rstd independence directly.  It derives
that independence from joint Gaussianity of `(score, vec Rstd)` plus
coordinatewise zero covariance, then reuses the existing Gaussian-matrix
decomposition route. -/
theorem
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_vectorTail_coordinateCovarianceZero_canonicalRest
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRstdGaussian :
      HasGaussianLaw
        (fun ω =>
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω),
            fun p : l₂ × k₂ => Rstd ω p.1 p.2)) μ)
    (hScoreRstdCovZero : ∀ (j : k₂) (p : l₂ × k₂),
      cov[
        fun ω => twoSLSKinalFWLScoreStar
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
        fun ω => Rstd ω p.1 p.2;
        μ] = 0)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hCoordMap : ∀ j : k₂,
      AEMeasurable (coordMap j)
        ((((twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          fun s : k₂ → ℝ => s j).prod
          (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1)))))
    (hTail :
      TwoSLSKinalScoreVectorProductTailIff (l₂ := l₂)
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁) coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
by
  classical
  have hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd :=
    twoSLSKinalFWLScoreStar_indep_Rstd_of_jointGaussian_coordinate_covariance_zero
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Rstd := Rstd) hScoreRstdGaussian hScoreRstdCovZero
  exact
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_vectorTail_canonicalRest
      hJoint hSigma hRstd hGram hScoreRstdInd hCoeff hCoordMap hTail

set_option linter.style.longLine false in
/-- Canonical-rest scalar-tail Kinal endpoint from raw joint-Gaussian
score/matrix coordinate covariances.

This is the closest current endpoint to Hansen's displayed normal-theory
claim.  It derives score/Rstd independence from joint Gaussian zero
cross-covariances, uses the canonical score-vector law and canonical rest
coordinate split, and derives coordinate-map measurability from the scalar
Gaussian/inverse-chi-square product-tail equivalence. -/
theorem
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_scalarTail_coordinateCovarianceZero_canonicalRest
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {coordMap : k₂ → ℝ × ℝ → ℝ}
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRstdGaussian :
      HasGaussianLaw
        (fun ω =>
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω),
            fun p : l₂ × k₂ => Rstd ω p.1 p.2)) μ)
    (hScoreRstdCovZero : ∀ (j : k₂) (p : l₂ × k₂),
      cov[
        fun ω => twoSLSKinalFWLScoreStar
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
        fun ω => Rstd ω p.1 p.2;
        μ] = 0)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        coordMap j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail :
      TwoSLSKinalScalarProductTailIff (l₂ := l₂)
        (fun j : k₂ =>
          (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
            fun s : k₂ → ℝ => s j)
        coordMap) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
by
  classical
  have hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd :=
    twoSLSKinalFWLScoreStar_indep_Rstd_of_jointGaussian_coordinate_covariance_zero
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Rstd := Rstd) hScoreRstdGaussian hScoreRstdCovZero
  exact
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_scalarTail_canonicalScoreLaw_auto
      (rIdx := fun j : k₂ => kinalCoordinateRestIdx j)
      hJoint hSigma (fun j => kinalCoordinateRestIdx_card_dim (k₂ := k₂) j)
      hRstd hGram hScoreRstdInd hCoeff hTail

set_option linter.style.longLine false in
/-- Canonical-rest Kinal endpoint with the remaining scalar tail premise
specialized to the concrete Gaussian/inverse-chi-square product calculation.

Compared with
`twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_scalarTail_canonicalRest`,
this wrapper fixes the coordinate product map to `(x, q) ↦ x / sqrt q` and
asks only for Gaussian coordinate laws for the canonical score vector together
with the law-level Gaussian/inverse-chi-square moment iff.  The conclusion keeps
Hansen's exact displayed threshold `r < ℓ₂ - k₂ + 1`. -/
theorem
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_gaussianInverseChiSqTail_canonicalRest
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    (scoreMean : k₂ → ℝ) (scoreVar : k₂ → ℝ≥0)
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hScoreLaw : ∀ j : k₂,
      (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          (fun s : k₂ → ℝ => s j) =
        gaussianReal (scoreMean j) (scoreVar j))
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        twoSLSKinalGaussianInverseChiSqCoordMap (k₂ := k₂) j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail :
      TwoSLSKinalGaussianInverseChiSqProductTailIff (l₂ := l₂)
        scoreMean scoreVar) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
by
  classical
  exact
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_scalarTail_canonicalRest
      hJoint hSigma hRstd hGram hScoreRstdInd hCoeff
      (twoSLSKinalScalarProductTailIff_of_scoreVectorGaussianInverseChiSqProductTailIff
        (l₂ := l₂)
        (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁)
        scoreMean scoreVar hScoreLaw hTail)

set_option linter.style.longLine false in
/-- Canonical-rest Kinal endpoint from per-coordinate scalar
Gaussian/inverse-chi-square threshold facts.

Compared with
`twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_gaussianInverseChiSqTail_canonicalRest`,
callers no longer assemble the all-coordinate Kinal product-tail package
manually.  They supply the reusable scalar analytic statement
`GaussianInverseChiSqMomentThresholdIff` for each score coordinate; this wrapper
keeps Hansen's threshold exactly as `ℓ₂ - k₂ + 1`. -/
theorem
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_coordinateGaussianInverseChiSqTail_canonicalRest
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    (scoreMean : k₂ → ℝ) (scoreVar : k₂ → ℝ≥0)
    [Nonempty k₂]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hScoreLaw : ∀ j : k₂,
      (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          (fun s : k₂ → ℝ => s j) =
        gaussianReal (scoreMean j) (scoreVar j))
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        twoSLSKinalGaussianInverseChiSqCoordMap (k₂ := k₂) j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail : ∀ j : k₂,
      GaussianInverseChiSqMomentThresholdIff
        (Fintype.card l₂ - Fintype.card k₂ + 1)
        (scoreMean j) (scoreVar j)) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
by
  classical
  exact
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_gaussianInverseChiSqTail_canonicalRest
      scoreMean scoreVar hJoint hSigma hRstd hGram hScoreRstdInd hScoreLaw hCoeff
      (twoSLSKinalGaussianInverseChiSqProductTailIff_of_coordinate_momentThresholds
        (l₂ := l₂) hJoint.instrument_count scoreMean scoreVar hTail)

/-- Standard-score specialization of
`twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_gaussianInverseChiSqTail_canonicalRest`.

When the canonical FWL score coordinates have standard-normal laws, the
Gaussian/inverse-chi-square product-tail input is supplied by the reusable
Student-`t` moment-threshold predicate. The conclusion still displays
Hansen's exact threshold `r < ℓ₂ - k₂ + 1`; the only remaining analytic
primitive is the reusable Student-`t` moment theorem. -/
theorem
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_standardStudentTail_canonicalRest
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd)
    (hScoreLaw : ∀ j : k₂,
      (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          (fun s : k₂ → ℝ => s j) =
        gaussianReal 0 1)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        twoSLSKinalGaussianInverseChiSqCoordMap (k₂ := k₂) j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j))
    (hTail :
      StudentTMomentThresholdIff
        (Fintype.card l₂ - Fintype.card k₂ + 1)) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
by
  classical
  exact
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_gaussianInverseChiSqTail_canonicalRest
      (scoreMean := fun _ : k₂ => 0) (scoreVar := fun _ : k₂ => 1)
      hJoint hSigma hRstd hGram hScoreRstdInd hScoreLaw hCoeff
      (twoSLSKinalGaussianInverseChiSqProductTailIff_standard_of_studentTMomentIff
        (l₂ := l₂) hJoint.instrument_count hTail)

set_option linter.style.longLine false in
/-- Closed standard-score Kinal endpoint from raw joint-Gaussian
score/matrix coordinate covariances.

Compared with
`twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_standardStudentTail_canonicalRest`,
this theorem does not assume score/Rstd independence directly and does not
leave the Student-`t` threshold as a premise.  Joint Gaussianity plus
coordinatewise zero score/matrix covariance gives the independence input, and
`studentTMomentThresholdIff_of_pos` supplies the exact
`r < ℓ₂ - k₂ + 1` scalar tail calculation. -/
theorem
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_standardStudentTail_coordinateCovarianceZero_canonicalRest
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRstdGaussian :
      HasGaussianLaw
        (fun ω =>
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω),
            fun p : l₂ × k₂ => Rstd ω p.1 p.2)) μ)
    (hScoreRstdCovZero : ∀ (j : k₂) (p : l₂ × k₂),
      cov[
        fun ω => twoSLSKinalFWLScoreStar
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
        fun ω => Rstd ω p.1 p.2;
        μ] = 0)
    (hScoreLaw : ∀ j : k₂,
      (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          (fun s : k₂ → ℝ => s j) =
        gaussianReal 0 1)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        twoSLSKinalGaussianInverseChiSqCoordMap (k₂ := k₂) j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
by
  classical
  have hScoreRstdInd :
      (fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        ⟂ᵢ[μ]
      Rstd :=
    twoSLSKinalFWLScoreStar_indep_Rstd_of_jointGaussian_coordinate_covariance_zero
      (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
      (Rstd := Rstd) hScoreRstdGaussian hScoreRstdCovZero
  exact
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_standardStudentTail_canonicalRest
      hJoint hSigma hRstd hGram hScoreRstdInd hScoreLaw hCoeff
      (studentTMomentThresholdIff_of_pos (by omega))

set_option linter.style.longLine false in
/-- Closed standard-score Kinal endpoint from primitive score/Rstd Gaussian
data and score normalization.

Compared with
`twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_standardStudentTail_coordinateCovarianceZero_canonicalRest`,
this bridge no longer asks callers to prove the score-coordinate laws as
measure equalities.  The raw joint-Gaussian law gives Gaussian score
coordinates, and the supplied mean-zero / variance-one normalization identifies
those coordinates as standard normal before reusing the existing Student-`t`
tail closure. -/
theorem
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_standardizedScore_coordinateCovarianceZero_canonicalRest
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ}
    {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRstdGaussian :
      HasGaussianLaw
        (fun ω =>
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω),
            fun p : l₂ × k₂ => Rstd ω p.1 p.2)) μ)
    (hScoreRstdCovZero : ∀ (j : k₂) (p : l₂ × k₂),
      cov[
        fun ω => twoSLSKinalFWLScoreStar
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
        fun ω => Rstd ω p.1 p.2;
        μ] = 0)
    (hScoreMeanZero : ∀ j : k₂,
      ∫ ω, twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j ∂μ = 0)
    (hScoreVarOne : ∀ j : k₂,
      (Var[
        fun ω => twoSLSKinalFWLScoreStar
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j;
        μ]).toNNReal = 1)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        twoSLSKinalGaussianInverseChiSqCoordMap (k₂ := k₂) j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
by
  classical
  let scoreVec : Ω → k₂ → ℝ :=
    fun ω => twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)
  have hScoreGaussian : HasGaussianLaw scoreVec μ := by
    simpa [scoreVec] using hScoreRstdGaussian.fst
  have hScoreLaw : ∀ j : k₂,
      (twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map
          (fun s : k₂ → ℝ => s j) =
        gaussianReal 0 1 := by
    intro j
    let scoreCoord : Ω → ℝ := fun ω => scoreVec ω j
    let evalJ : (k₂ → ℝ) → ℝ := fun s => s j
    have hCoordGaussian : HasGaussianLaw scoreCoord μ := by
      let scoreFamily : k₂ → Ω → ℝ := fun j ω => scoreVec ω j
      have hScoreGaussian' :
          HasGaussianLaw (fun ω => (scoreFamily · ω)) μ := by
        simpa [scoreFamily, scoreVec] using hScoreGaussian
      simpa [scoreFamily, scoreCoord, scoreVec] using hScoreGaussian'.eval j
    have hCoordLaw :
        HasLaw scoreCoord
          ((twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁).map evalJ) μ := by
      simpa [scoreVec, scoreCoord, evalJ] using
        twoSLSKinalFWLScoreCoordinateLaws_of_scoreVectorLaw
          (X₁ := X₁) (Y₂ := Y₂) (Z₂ := Z₂) (Y₁ := Y₁)
          (ScoreVectorLaw := twoSLSKinalFWLScoreVectorLaw μ X₁ Y₂ Z₂ Y₁)
          (twoSLSKinalFWLScoreVector_hasLaw hJoint.aemeasurable_fwlScoreStar) j
    have hGaussianMap :
        μ.map scoreCoord =
          gaussianReal ((μ.map scoreCoord)[id])
            (Var[id; μ.map scoreCoord]).toNNReal :=
      IsGaussian.eq_gaussianReal (μ.map scoreCoord) hCoordGaussian.isGaussian_map
    have hMeanMap :
        (μ.map scoreCoord)[id] = ∫ ω, scoreCoord ω ∂μ := by
      rw [integral_map hCoordGaussian.aemeasurable (by fun_prop)]
      rfl
    have hVarMap :
        (Var[id; μ.map scoreCoord]).toNNReal =
          (Var[scoreCoord; μ]).toNNReal := by
      rw [variance_map (by fun_prop) hCoordGaussian.aemeasurable]
      rfl
    rw [← hCoordLaw.map_eq]
    calc
      μ.map scoreCoord =
          gaussianReal ((μ.map scoreCoord)[id])
            (Var[id; μ.map scoreCoord]).toNNReal := hGaussianMap
      _ = gaussianReal 0 1 := by
        rw [hMeanMap, hVarMap]
        simp [scoreCoord, scoreVec, hScoreMeanZero j, hScoreVarOne j]
  exact
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_standardStudentTail_coordinateCovarianceZero_canonicalRest
      hJoint hSigma hRstd hGram hScoreRstdGaussian hScoreRstdCovZero
      hScoreLaw hCoeff

set_option linter.style.longLine false in
/-- Closed standard-score Kinal endpoint from one block Gaussian score/rest law.

This bridge replaces separate score Gaussianity, score mean/variance, and
score/rest covariance-zero premises by the single finite-dimensional block law
for `(score, vec Rstd)`.  The diagonal score block and zero score/rest block of
the covariance matrix give the standard-score and independence inputs used by
`twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_standardizedScore_coordinateCovarianceZero_canonicalRest`. -/
theorem
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_standardizedScoreRestCovariance_canonicalRest
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {C : Matrix (k₂ ⊕ (l₂ × k₂)) (k₂ ⊕ (l₂ × k₂)) ℝ}
    [Nonempty k₂]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hC : C.PosSemidef)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRestLaw :
      HasLaw
        (fun ω : Ω =>
          WithLp.toLp 2 fun idx : k₂ ⊕ (l₂ × k₂) =>
            match idx with
            | Sum.inl j =>
                twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j
            | Sum.inr p => Rstd ω p.1 p.2)
        (multivariateGaussian 0 C) μ)
    (hScoreVar : ∀ j : k₂, C (Sum.inl j) (Sum.inl j) = 1)
    (hScoreRestCovZero : ∀ (j : k₂) (p : l₂ × k₂),
      C (Sum.inl j) (Sum.inr p) = 0)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        twoSLSKinalGaussianInverseChiSqCoordMap (k₂ := k₂) j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 := by
  classical
  let scoreRest :
      Ω → EuclideanSpace ℝ (k₂ ⊕ (l₂ × k₂)) :=
    fun ω =>
      WithLp.toLp 2 fun idx : k₂ ⊕ (l₂ × k₂) =>
        match idx with
        | Sum.inl j =>
            twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j
        | Sum.inr p => Rstd ω p.1 p.2
  let splitSumCLM :
      ((k₂ ⊕ (l₂ × k₂)) → ℝ) →L[ℝ]
        ((k₂ → ℝ) × ((l₂ × k₂) → ℝ)) :=
    { toLinearMap :=
        (LinearEquiv.sumArrowLequivProdArrow
          k₂ (l₂ × k₂) ℝ ℝ).toLinearMap
      cont := by
        change Continuous
          (fun f : (k₂ ⊕ (l₂ × k₂)) → ℝ =>
            (fun j : k₂ => f (Sum.inl j),
              fun p : l₂ × k₂ => f (Sum.inr p)))
        fun_prop }
  let splitLpCLM :
      EuclideanSpace ℝ (k₂ ⊕ (l₂ × k₂)) →L[ℝ]
        ((k₂ → ℝ) × ((l₂ × k₂) → ℝ)) :=
    splitSumCLM.comp
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : k₂ ⊕ (l₂ × k₂) => ℝ)).toContinuousLinearMap
  have hScoreRestGaussian :
      HasGaussianLaw
        (fun ω =>
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω),
            fun p : l₂ × k₂ => Rstd ω p.1 p.2)) μ := by
    have hBlockGaussian : HasGaussianLaw scoreRest μ := by
      simpa [scoreRest] using hScoreRestLaw.hasGaussianLaw
    simpa [scoreRest, splitLpCLM, splitSumCLM,
      LinearEquiv.sumArrowLequivProdArrow] using
      hBlockGaussian.map_fun splitLpCLM
  have hScoreRestCovZero' : ∀ (j : k₂) (p : l₂ × k₂),
      cov[
        fun ω => twoSLSKinalFWLScoreStar
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
        fun ω => Rstd ω p.1 p.2;
        μ] = 0 := by
    intro j p
    let f : EuclideanSpace ℝ (k₂ ⊕ (l₂ × k₂)) → ℝ :=
      fun z => z.ofLp (Sum.inl j)
    let g : EuclideanSpace ℝ (k₂ ⊕ (l₂ × k₂)) → ℝ :=
      fun z => z.ofLp (Sum.inr p)
    have hcov := hScoreRestLaw.covariance_fun_comp
      (f := f) (g := g) (by fun_prop) (by fun_prop)
    calc
      cov[
        fun ω => twoSLSKinalFWLScoreStar
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
        fun ω => Rstd ω p.1 p.2;
        μ] = cov[f, g; multivariateGaussian 0 C] := by
          simpa [scoreRest, f, g] using hcov
      _ = C (Sum.inl j) (Sum.inr p) := by
          simpa [f, g] using
            (multivariateGaussian_covariance_eval
              (μ := (0 : EuclideanSpace ℝ (k₂ ⊕ (l₂ × k₂))))
              (S := C) hC (Sum.inl j) (Sum.inr p))
      _ = 0 := hScoreRestCovZero j p
  have hScoreMeanZero : ∀ j : k₂,
      ∫ ω, twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j ∂μ = 0 := by
    intro j
    let f : EuclideanSpace ℝ (k₂ ⊕ (l₂ × k₂)) → ℝ :=
      fun z => z.ofLp (Sum.inl j)
    have hInt := hScoreRestLaw.integral_comp (f := f) (by fun_prop)
    have hMeanCoord :
        ∫ z, f z ∂multivariateGaussian
            (0 : EuclideanSpace ℝ (k₂ ⊕ (l₂ × k₂))) C = 0 := by
      have hproj := (EuclideanSpace.proj (Sum.inl j)).integral_comp_comm
        (μ := multivariateGaussian
          (0 : EuclideanSpace ℝ (k₂ ⊕ (l₂ × k₂))) C)
        IsGaussian.integrable_id
      calc
        ∫ z, f z ∂multivariateGaussian
            (0 : EuclideanSpace ℝ (k₂ ⊕ (l₂ × k₂))) C =
            ((∫ z, z ∂multivariateGaussian
              (0 : EuclideanSpace ℝ (k₂ ⊕ (l₂ × k₂))) C).ofLp
                (Sum.inl j)) := by
              simpa [f, EuclideanSpace.proj] using hproj
        _ = 0 := by
              simp
    calc
      ∫ ω, twoSLSKinalFWLScoreStar
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j ∂μ =
          ∫ z, f z ∂multivariateGaussian
            (0 : EuclideanSpace ℝ (k₂ ⊕ (l₂ × k₂))) C := by
            simpa [scoreRest, f] using hInt
      _ = 0 := hMeanCoord
  have hScoreVarOne : ∀ j : k₂,
      (Var[
        fun ω => twoSLSKinalFWLScoreStar
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j;
        μ]).toNNReal = 1 := by
    intro j
    let f : EuclideanSpace ℝ (k₂ ⊕ (l₂ × k₂)) → ℝ :=
      fun z => z.ofLp (Sum.inl j)
    let scoreCoord : Ω → ℝ :=
      fun ω => twoSLSKinalFWLScoreStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j
    have hcov := hScoreRestLaw.covariance_fun_comp
      (f := f) (g := f) (by fun_prop) (by fun_prop)
    have hcovScore : cov[scoreCoord, scoreCoord; μ] = 1 := by
      calc
        cov[scoreCoord, scoreCoord; μ] =
            cov[f, f; multivariateGaussian
              (0 : EuclideanSpace ℝ (k₂ ⊕ (l₂ × k₂))) C] := by
              simpa [scoreRest, f, scoreCoord] using hcov
        _ = C (Sum.inl j) (Sum.inl j) := by
              simpa [f] using
                (multivariateGaussian_covariance_eval
                  (μ := (0 : EuclideanSpace ℝ (k₂ ⊕ (l₂ × k₂))))
                  (S := C) hC (Sum.inl j) (Sum.inl j))
        _ = 1 := hScoreVar j
    have hAEMeas : AEMeasurable scoreCoord μ := by
      simpa [scoreCoord] using (hScoreRestGaussian.fst.eval j).aemeasurable
    have hvarReal : Var[scoreCoord; μ] = 1 :=
      (covariance_self (X := scoreCoord) hAEMeas).symm.trans hcovScore
    simpa [scoreCoord] using congrArg Real.toNNReal hvarReal
  exact
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_standardizedScore_coordinateCovarianceZero_canonicalRest
      hJoint hSigma hRstd hGram hScoreRestGaussian hScoreRestCovZero'
      hScoreMeanZero hScoreVarOne hCoeff

set_option linter.style.longLine false in
/-- Named exact-moment version of the block Gaussian score/rest covariance
Kinal endpoint.

This is the compact target for the remaining raw-normal decomposition work:
once the standardized residualized Gram law, block Gaussian score/rest law,
displayed score variances, zero score/rest covariance block, and coefficient
product representation are supplied, the exact Kinal moment-threshold predicate
follows without a separate product-tail assumption. -/
theorem
    twoSLSKinalExactMomentIff_of_gaussianMatrixDecomposition_standardizedScoreRestCovariance_canonicalRest
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {C : Matrix (k₂ ⊕ (l₂ × k₂)) (k₂ ⊕ (l₂ × k₂)) ℝ}
    [Nonempty k₂]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hC : C.PosSemidef)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRestLaw :
      HasLaw
        (fun ω : Ω =>
          WithLp.toLp 2 fun idx : k₂ ⊕ (l₂ × k₂) =>
            match idx with
            | Sum.inl j =>
                twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j
            | Sum.inr p => Rstd ω p.1 p.2)
        (multivariateGaussian 0 C) μ)
    (hScoreVar : ∀ j : k₂, C (Sum.inl j) (Sum.inl j) = 1)
    (hScoreRestCovZero : ∀ (j : k₂) (p : l₂ × k₂),
      C (Sum.inl j) (Sum.inr p) = 0)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        twoSLSKinalGaussianInverseChiSqCoordMap (k₂ := k₂) j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ := by
  intro r
  simpa [TwoSLSKinalExactMomentIff, twoSLSKinalMomentThreshold] using
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_standardizedScoreRestCovariance_canonicalRest
      hJoint hSigma hC hRstd hGram hScoreRestLaw hScoreVar hScoreRestCovZero
      hCoeff r

set_option linter.style.longLine false in
/-- Closed standard-score block-law Kinal endpoint with the chi-square
`SFinite` side condition inferred locally from the positive degrees of freedom.

This is the direct block-law analogue of
`twoSLSKinal_theorem12_7_of_jointNormal_standardizedScoreCanonicalRestInputs_autoSFinite`. -/
theorem
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_standardizedScoreRestCovariance_canonicalRest_autoSFinite
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {C : Matrix (k₂ ⊕ (l₂ × k₂)) (k₂ ⊕ (l₂ × k₂)) ℝ}
    [Nonempty k₂]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hC : C.PosSemidef)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRestLaw :
      HasLaw
        (fun ω : Ω =>
          WithLp.toLp 2 fun idx : k₂ ⊕ (l₂ × k₂) =>
            match idx with
            | Sum.inl j =>
                twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j
            | Sum.inr p => Rstd ω p.1 p.2)
        (multivariateGaussian 0 C) μ)
    (hScoreVar : ∀ j : k₂, C (Sum.inl j) (Sum.inl j) = 1)
    (hScoreRestCovZero : ∀ (j : k₂) (p : l₂ × k₂),
      C (Sum.inl j) (Sum.inr p) = 0)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        twoSLSKinalGaussianInverseChiSqCoordMap (k₂ := k₂) j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 := by
  haveI : Fact (0 < Fintype.card l₂ - Fintype.card k₂ + 1) :=
    ⟨Nat.succ_pos _⟩
  exact
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_standardizedScoreRestCovariance_canonicalRest
      hJoint hSigma hC hRstd hGram hScoreRestLaw hScoreVar hScoreRestCovZero
      hCoeff

set_option linter.style.longLine false in
/-- Named exact-moment version of the block-law Kinal endpoint, with the
chi-square `SFinite` side condition inferred locally. -/
theorem
    twoSLSKinalExactMomentIff_of_gaussianMatrixDecomposition_standardizedScoreRestCovariance_canonicalRest_autoSFinite
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {C : Matrix (k₂ ⊕ (l₂ × k₂)) (k₂ ⊕ (l₂ × k₂)) ℝ}
    [Nonempty k₂]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hSigma : Sigma.PosDef)
    (hC : C.PosSemidef)
    (hRstd : HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ)
    (hGram :
      (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
        =ᵐ[μ]
      fun ω => matrixCrossProduct (Rstd ω))
    (hScoreRestLaw :
      HasLaw
        (fun ω : Ω =>
          WithLp.toLp 2 fun idx : k₂ ⊕ (l₂ × k₂) =>
            match idx with
            | Sum.inl j =>
                twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j
            | Sum.inr p => Rstd ω p.1 p.2)
        (multivariateGaussian 0 C) μ)
    (hScoreVar : ∀ j : k₂, C (Sum.inl j) (Sum.inl j) = 1)
    (hScoreRestCovZero : ∀ (j : k₂) (p : l₂ × k₂),
      C (Sum.inl j) (Sum.inr p) = 0)
    (hCoeff : ∀ j : k₂,
      (fun ω =>
        ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
          twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
        =ᵐ[μ]
      fun ω =>
        twoSLSKinalGaussianInverseChiSqCoordMap (k₂ := k₂) j
          (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
            twoSLSKinalFWLCoordinateInverseScaleStar
              (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ := by
  intro r
  simpa [TwoSLSKinalExactMomentIff, twoSLSKinalMomentThreshold] using
    twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_standardizedScoreRestCovariance_canonicalRest_autoSFinite
      hJoint hSigma hC hRstd hGram hScoreRestLaw hScoreVar hScoreRestCovZero
      hCoeff r

set_option linter.style.longLine false in
/-- Hansen-facing bridge package for the remaining raw joint-normal work in
Theorem 12.7.

This structure does not assume the Kinal moment conclusion.  Instead, it names
the decomposition facts still to be derived from Hansen's concrete
joint-normal reduced-form covariance structure: a standardized Gaussian
residualized-Gram representation, the a.e. equality between that Gram and the
actual FWL Gram, the block Gaussian law for score and standardized rest
coordinates, the displayed score-variance and zero score/rest covariance
blocks, and the inverse-chi-square coordinate representation of the
coefficient.  Once these bridge facts are supplied, the existing block-law
endpoint proves Hansen's exact `ℓ₂ - k₂ + 1` moment threshold. -/
structure TwoSLSKinalHansenRawJointNormalBridgeInputs
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ) (Rstd : Ω → Matrix l₂ k₂ ℝ)
    (C : Matrix (k₂ ⊕ (l₂ × k₂)) (k₂ ⊕ (l₂ × k₂)) ℝ) :
    Prop where
  /-- Hansen's observed finite-sample row is jointly Gaussian and satisfies
  the rank/order assumptions used by the Kinal FWL bridge. -/
  joint_normal : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁
  /-- Positive-definite covariance used by the Chapter 11 inverse-Wishart
  standard-Gram bridge. -/
  sigma_posDef : Sigma.PosDef
  /-- Positive-semidefinite block covariance for the score/rest Gaussian law. -/
  score_rest_cov_posSemidef : C.PosSemidef
  /-- Standardized Gaussian representation of the residualized fitted
  endogenous matrix. -/
  standardized_gram_law :
    HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ
  /-- A.e. equality between Hansen's actual FWL Gram and the standardized
  Gaussian cross-product. -/
  gram_eq :
    (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
      =ᵐ[μ]
    fun ω => matrixCrossProduct (Rstd ω)
  /-- Block Gaussian law for the residualized FWL score and standardized rest
  coordinates. -/
  score_rest_block_law :
    HasLaw
      (fun ω : Ω =>
        WithLp.toLp 2 fun idx : k₂ ⊕ (l₂ × k₂) =>
          match idx with
          | Sum.inl j =>
              twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j
          | Sum.inr p => Rstd ω p.1 p.2)
      (multivariateGaussian 0 C) μ
  /-- Displayed standardized-score variances. -/
  score_var : ∀ j : k₂, C (Sum.inl j) (Sum.inl j) = 1
  /-- Displayed zero score/rest covariance block, which gives independence by
  joint Gaussianity. -/
  score_rest_cov_zero : ∀ (j : k₂) (p : l₂ × k₂),
    C (Sum.inl j) (Sum.inr p) = 0
  /-- A.e. coordinate product representation of the endogenous 2SLS block. -/
  coefficient_coord_ae : ∀ j : k₂,
    (fun ω =>
      ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
        twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
      =ᵐ[μ]
    fun ω =>
      twoSLSKinalGaussianInverseChiSqCoordMap (k₂ := k₂) j
        (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
          twoSLSKinalFWLCoordinateInverseScaleStar
            (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)

set_option linter.style.longLine false in
/-- The Hansen-facing raw joint-normal bridge package proves the exact Kinal
moment-threshold predicate. -/
theorem TwoSLSKinalHansenRawJointNormalBridgeInputs.toExactMomentIff_autoSFinite
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {C : Matrix (k₂ ⊕ (l₂ × k₂)) (k₂ ⊕ (l₂ × k₂)) ℝ}
    [Nonempty k₂]
    (h :
      TwoSLSKinalHansenRawJointNormalBridgeInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd C) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  twoSLSKinalExactMomentIff_of_gaussianMatrixDecomposition_standardizedScoreRestCovariance_canonicalRest_autoSFinite
    h.joint_normal h.sigma_posDef h.score_rest_cov_posSemidef
    h.standardized_gram_law h.gram_eq h.score_rest_block_law h.score_var
    h.score_rest_cov_zero h.coefficient_coord_ae

set_option linter.style.longLine false in
/-- Hansen Theorem 12.7 from the raw joint-normal bridge package, with the
displayed Kinal threshold. -/
theorem twoSLSKinal_theorem12_7_of_hansenRawJointNormalBridgeInputs_autoSFinite
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    {C : Matrix (k₂ ⊕ (l₂ × k₂)) (k₂ ⊕ (l₂ × k₂)) ℝ}
    [Nonempty k₂]
    (h :
      TwoSLSKinalHansenRawJointNormalBridgeInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd C) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
  twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_standardizedScoreRestCovariance_canonicalRest_autoSFinite
    h.joint_normal h.sigma_posDef h.score_rest_cov_posSemidef
    h.standardized_gram_law h.gram_eq h.score_rest_block_law h.score_var
    h.score_rest_cov_zero h.coefficient_coord_ae

/-- Primitive canonical-rest inputs for the closed standardized-score Kinal
endpoint.

This package keeps the genuine stochastic ingredients explicit: the
standardized residualized fitted-gram decomposition, joint Gaussian
score/rest law, coordinate covariance-zero conditions, score normalization, and
the FWL coefficient product representation.  Joint normality itself remains a
separate theorem argument so the package does not hide the Hansen assumption. -/
structure TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X₁ : Ω → Matrix n k₁ ℝ) (Y₂ : Ω → Matrix n k₂ ℝ)
    (Z₂ : Ω → Matrix n l₂ ℝ) (Y₁ : Ω → n → ℝ)
    (Sigma : Matrix k₂ k₂ ℝ) (Rstd : Ω → Matrix l₂ k₂ ℝ) :
    Prop where
  /-- Positive-definite covariance of the standardized residualized
  first-stage rest matrix. -/
  sigma_posDef : Sigma.PosDef
  /-- Standard matrix-normal law for the canonical rest block. -/
  Rstd_law :
    HasLaw Rstd
      (iidMatrixGaussianLaw (n := l₂) (m := k₂) (0 : k₂ → ℝ) Sigma) μ
  /-- A.e. identification of the residualized fitted Gram with the canonical
  rest cross-product. -/
  gram_eq :
    (fun ω => twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))
      =ᵐ[μ]
    fun ω => matrixCrossProduct (Rstd ω)
  /-- Joint Gaussian law of the residualized score and canonical rest entries. -/
  score_rest_gaussian :
    HasGaussianLaw
      (fun ω =>
        (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω),
          fun p : l₂ × k₂ => Rstd ω p.1 p.2)) μ
  /-- Coordinate covariance-zero condition implying independence of score and
  rest by joint Gaussianity. -/
  score_rest_cov_zero : ∀ (j : k₂) (p : l₂ × k₂),
    cov[
      fun ω => twoSLSKinalFWLScoreStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
      fun ω => Rstd ω p.1 p.2;
      μ] = 0
  /-- Standardized score means. -/
  score_mean_zero : ∀ j : k₂,
    ∫ ω, twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j ∂μ = 0
  /-- Standardized score variances. -/
  score_var_one : ∀ j : k₂,
    (Var[
      fun ω => twoSLSKinalFWLScoreStar
        (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j;
      μ]).toNNReal = 1
  /-- A.e. inverse-chi-square coordinate representation of the endogenous
  coefficient block. -/
  coefficient_coord_ae : ∀ j : k₂,
    (fun ω =>
      ((twoSLSKinalFWLGramStar (X₁ ω) (Y₂ ω) (Z₂ ω))⁻¹ *ᵥ
        twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω)) j)
      =ᵐ[μ]
    fun ω =>
      twoSLSKinalGaussianInverseChiSqCoordMap (k₂ := k₂) j
        (twoSLSKinalFWLScoreStar (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω) j,
          twoSLSKinalFWLCoordinateInverseScaleStar
            (X₁ ω) (Y₂ ω) (Z₂ ω) Sigma j)

set_option linter.style.longLine false in
/-- Hansen Theorem 12.7 from joint normality plus the bundled canonical-rest
standardized-score inputs. -/
theorem twoSLSKinal_theorem12_7_of_jointNormal_standardizedScoreCanonicalRestInputs
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hInputs :
      TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 :=
  twoSLSKinal_theorem12_7_of_gaussianMatrixDecomposition_standardizedScore_coordinateCovarianceZero_canonicalRest
    hJoint hInputs.sigma_posDef hInputs.Rstd_law hInputs.gram_eq
    hInputs.score_rest_gaussian hInputs.score_rest_cov_zero
    hInputs.score_mean_zero hInputs.score_var_one
    hInputs.coefficient_coord_ae

set_option linter.style.longLine false in
/-- Hansen Theorem 12.7 from joint normality plus standardized-score canonical
rest inputs, with the chi-square `SFinite` side condition inferred locally from
the positive degrees of freedom. -/
theorem twoSLSKinal_theorem12_7_of_jointNormal_standardizedScoreCanonicalRestInputs_autoSFinite
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hInputs :
      TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero
          (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (r : ℝ≥0∞) μ ↔
      (r : ℝ) < (Fintype.card l₂ : ℝ) - (Fintype.card k₂ : ℝ) + 1 := by
  haveI : Fact (0 < Fintype.card l₂ - Fintype.card k₂ + 1) :=
    ⟨Nat.succ_pos _⟩
  exact
    twoSLSKinal_theorem12_7_of_jointNormal_standardizedScoreCanonicalRestInputs
      hJoint hInputs

set_option linter.style.longLine false in
/-- Named-predicate version of the standardized-score canonical-rest Kinal
endpoint. -/
theorem twoSLSKinalExactMomentIff_of_jointNormal_standardizedScoreCanonicalRestInputs
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hInputs :
      TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ := by
  intro r
  simpa [TwoSLSKinalExactMomentIff, twoSLSKinalMomentThreshold] using
    twoSLSKinal_theorem12_7_of_jointNormal_standardizedScoreCanonicalRestInputs
      hJoint hInputs r

set_option linter.style.longLine false in
/-- Named-predicate version of the standardized-score canonical-rest Kinal
endpoint, with the chi-square `SFinite` side condition inferred locally. -/
theorem twoSLSKinalExactMomentIff_of_jointNormal_standardizedScoreCanonicalRestInputs_autoSFinite
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hInputs :
      TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ := by
  intro r
  simpa [TwoSLSKinalExactMomentIff, twoSLSKinalMomentThreshold] using
    twoSLSKinal_theorem12_7_of_jointNormal_standardizedScoreCanonicalRestInputs_autoSFinite
      hJoint hInputs r

/-- Method-style closure for the standardized-score canonical-rest Kinal
package.

This gives the newest tight Theorem 12.7 input package the same public API
shape as the older product-tail packages: once Hansen's raw joint-normal
condition is supplied separately, the package proves the exact moment-threshold
predicate rather than assuming it. -/
theorem TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs.toExactMomentIff
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hInputs :
      TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd)
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  twoSLSKinalExactMomentIff_of_jointNormal_standardizedScoreCanonicalRestInputs
    hJoint hInputs

/-- Method-style standardized-score Kinal closure with the chi-square
`SFinite` side condition inferred locally. -/
theorem
    TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs.toExactMomentIff_autoSFinite
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    (hInputs :
      TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd)
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁) :
    TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁ :=
  twoSLSKinalExactMomentIff_of_jointNormal_standardizedScoreCanonicalRestInputs_autoSFinite
    hJoint hInputs

omit [DecidableEq k₂] [DecidableEq l₂] in
/-- In the just-identified case `ℓ₂ = k₂`, Kinal's threshold is exactly one. -/
theorem twoSLSKinalMomentThreshold_eq_one_of_justIdentified
    (h : Fintype.card l₂ = Fintype.card k₂) :
    twoSLSKinalMomentThreshold k₂ l₂ = 1 := by
  unfold twoSLSKinalMomentThreshold
  rw [h]
  ring

omit [DecidableEq k₂] [DecidableEq l₂] in
/-- One overidentifying restriction is enough for the threshold to exceed one,
which is the finite-mean side of Hansen's discussion after Theorem 12.7. -/
theorem one_lt_twoSLSKinalMomentThreshold_of_overidentified
    (h : Fintype.card k₂ < Fintype.card l₂) :
    1 < twoSLSKinalMomentThreshold k₂ l₂ := by
  have hlt : (Fintype.card k₂ : ℝ) < (Fintype.card l₂ : ℝ) := by
    exact_mod_cast h
  unfold twoSLSKinalMomentThreshold
  linarith

omit [DecidableEq k₂] [DecidableEq l₂] in
/-- Two overidentifying restrictions are enough for the threshold to exceed two,
which is the finite-variance side of Hansen's discussion after Theorem 12.7. -/
theorem two_lt_twoSLSKinalMomentThreshold_of_two_overidentifying
    (h : Fintype.card k₂ + 1 < Fintype.card l₂) :
    2 < twoSLSKinalMomentThreshold k₂ l₂ := by
  have hlt : (Fintype.card k₂ : ℝ) + 1 < (Fintype.card l₂ : ℝ) := by
    exact_mod_cast h
  unfold twoSLSKinalMomentThreshold
  linarith

/-- Hansen Theorem 12.7, stated as a theorem face from an explicit Kinal tail
engine.  The tail engine is kept as a separate premise so the joint-normal
condition package does not hide the theorem's conclusion. -/
theorem twoSLSKinal_theorem12_7_of_tail_theorem
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (h : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hKinal :
      TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁ →
        TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁) :
    ∀ r : ℝ≥0,
      MemLp (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
          (r : ℝ≥0∞) μ ↔
        (r : ℝ) < twoSLSKinalMomentThreshold k₂ l₂ :=
  hKinal h

omit [DecidableEq n] in
/-- Exact Kinal consequence: in the just-identified case, the endogenous 2SLS
block has no finite first moment. -/
theorem twoSLSKinalExactMomentIff_not_memLp_one_of_justIdentified
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hiff : TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁)
    (hjust : Fintype.card l₂ = Fintype.card k₂) :
    ¬ MemLp
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      (1 : ℝ≥0∞) μ := by
  intro hmem
  have hlt := (hiff (1 : ℝ≥0)).mp hmem
  rw [twoSLSKinalMomentThreshold_eq_one_of_justIdentified hjust] at hlt
  norm_num at hlt

omit [DecidableEq n] in
/-- Exact Kinal consequence: in the just-identified case, every moment order
`r ≥ 1` is infinite.  This is the formal version of Hansen's statement that
the just-identified IV/2SLS estimator has no finite integer moments. -/
theorem twoSLSKinalExactMomentIff_not_memLp_of_justIdentified_of_one_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hiff : TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁)
    (hjust : Fintype.card l₂ = Fintype.card k₂)
    {r : ℝ≥0} (hr : 1 ≤ r) :
    ¬ MemLp
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      (r : ℝ≥0∞) μ := by
  intro hmem
  have hlt := (hiff r).mp hmem
  rw [twoSLSKinalMomentThreshold_eq_one_of_justIdentified hjust] at hlt
  have hr_real : (1 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast hr
  linarith

omit [DecidableEq n] in
/-- Exact Kinal consequence: one overidentifying restriction gives a finite
first moment for the endogenous 2SLS block. -/
theorem twoSLSKinalExactMomentIff_memLp_one_of_overidentified
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hiff : TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁)
    (hover : Fintype.card k₂ < Fintype.card l₂) :
    MemLp
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      (1 : ℝ≥0∞) μ := by
  exact (hiff (1 : ℝ≥0)).mpr
    (one_lt_twoSLSKinalMomentThreshold_of_overidentified hover)

omit [DecidableEq n] in
/-- Exact Kinal consequence: two overidentifying restrictions give a finite
second moment for the endogenous 2SLS block. -/
theorem twoSLSKinalExactMomentIff_memLp_two_of_two_overidentifying
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hiff : TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁)
    (hover2 : Fintype.card k₂ + 1 < Fintype.card l₂) :
    MemLp
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      (2 : ℝ≥0∞) μ := by
  exact (hiff (2 : ℝ≥0)).mpr
    (two_lt_twoSLSKinalMomentThreshold_of_two_overidentifying hover2)

omit [DecidableEq n] in
/-- Exact Kinal consequence: with exactly one overidentifying restriction, the
endogenous 2SLS block has no finite second moment.  Together with
`twoSLSKinalExactMomentIff_memLp_two_of_two_overidentifying`, this gives
Hansen's finite-variance iff: at least two overidentifying restrictions are
needed. -/
theorem twoSLSKinalExactMomentIff_not_memLp_two_of_one_overidentifying
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hiff : TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁)
    (hover1 : Fintype.card l₂ = Fintype.card k₂ + 1) :
    ¬ MemLp
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      (2 : ℝ≥0∞) μ := by
  intro hmem
  have hlt := (hiff (2 : ℝ≥0)).mp hmem
  have hthr : twoSLSKinalMomentThreshold k₂ l₂ = 2 := by
    have hover1_real :
        (Fintype.card l₂ : ℝ) = (Fintype.card k₂ : ℝ) + 1 := by
      exact_mod_cast hover1
    unfold twoSLSKinalMomentThreshold
    linarith
  rw [hthr] at hlt
  norm_num at hlt

omit [DecidableEq n] in
/-- Exact Kinal one-overidentifying corollary: the endogenous 2SLS block has a
finite first moment but no finite second moment.  This is the sharp boundary
case in Hansen's discussion after Theorem 12.7. -/
theorem twoSLSKinalExactMomentIff_memLp_one_and_not_memLp_two_of_one_overidentifying
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    (hiff : TwoSLSKinalExactMomentIff μ X₁ Y₂ Z₂ Y₁)
    (hover1 : Fintype.card l₂ = Fintype.card k₂ + 1) :
    MemLp
        (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (1 : ℝ≥0∞) μ ∧
      ¬ MemLp
        (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (2 : ℝ≥0∞) μ := by
  have hover : Fintype.card k₂ < Fintype.card l₂ := by
    omega
  exact
    ⟨twoSLSKinalExactMomentIff_memLp_one_of_overidentified hiff hover,
      twoSLSKinalExactMomentIff_not_memLp_two_of_one_overidentifying hiff hover1⟩

set_option linter.style.longLine false in
/-- Standardized-score canonical-rest Kinal consequence: in the just-identified
case, every moment order `r ≥ 1` is infinite. -/
theorem twoSLSKinal_not_memLp_of_justIdentified_of_jointNormal_standardizedScoreCanonicalRestInputs
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hInputs :
      TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd)
    (hjust : Fintype.card l₂ = Fintype.card k₂)
    {r : ℝ≥0} (hr : 1 ≤ r) :
    ¬ MemLp
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      (r : ℝ≥0∞) μ :=
  twoSLSKinalExactMomentIff_not_memLp_of_justIdentified_of_one_le
    (twoSLSKinalExactMomentIff_of_jointNormal_standardizedScoreCanonicalRestInputs
      hJoint hInputs)
    hjust hr

set_option linter.style.longLine false in
/-- Auto-`SFinite` version of
`twoSLSKinal_not_memLp_of_justIdentified_of_jointNormal_standardizedScoreCanonicalRestInputs`. -/
theorem twoSLSKinal_not_memLp_of_justIdentified_of_jointNormal_standardizedScoreCanonicalRestInputs_autoSFinite
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hInputs :
      TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd)
    (hjust : Fintype.card l₂ = Fintype.card k₂)
    {r : ℝ≥0} (hr : 1 ≤ r) :
    ¬ MemLp
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      (r : ℝ≥0∞) μ :=
  twoSLSKinalExactMomentIff_not_memLp_of_justIdentified_of_one_le
    (twoSLSKinalExactMomentIff_of_jointNormal_standardizedScoreCanonicalRestInputs_autoSFinite
      hJoint hInputs)
    hjust hr

set_option linter.style.longLine false in
/-- Standardized-score canonical-rest Kinal consequence: one overidentifying
restriction gives a finite first moment. -/
theorem twoSLSKinal_memLp_one_of_overidentified_of_jointNormal_standardizedScoreCanonicalRestInputs
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hInputs :
      TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd)
    (hover : Fintype.card k₂ < Fintype.card l₂) :
    MemLp
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      (1 : ℝ≥0∞) μ :=
  twoSLSKinalExactMomentIff_memLp_one_of_overidentified
    (twoSLSKinalExactMomentIff_of_jointNormal_standardizedScoreCanonicalRestInputs
      hJoint hInputs)
    hover

set_option linter.style.longLine false in
/-- Auto-`SFinite` version of
`twoSLSKinal_memLp_one_of_overidentified_of_jointNormal_standardizedScoreCanonicalRestInputs`. -/
theorem twoSLSKinal_memLp_one_of_overidentified_of_jointNormal_standardizedScoreCanonicalRestInputs_autoSFinite
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hInputs :
      TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd)
    (hover : Fintype.card k₂ < Fintype.card l₂) :
    MemLp
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      (1 : ℝ≥0∞) μ :=
  twoSLSKinalExactMomentIff_memLp_one_of_overidentified
    (twoSLSKinalExactMomentIff_of_jointNormal_standardizedScoreCanonicalRestInputs_autoSFinite
      hJoint hInputs)
    hover

set_option linter.style.longLine false in
/-- Standardized-score canonical-rest Kinal consequence: two overidentifying
restrictions give a finite second moment. -/
theorem twoSLSKinal_memLp_two_of_two_overidentifying_of_jointNormal_standardizedScoreCanonicalRestInputs
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hInputs :
      TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd)
    (hover2 : Fintype.card k₂ + 1 < Fintype.card l₂) :
    MemLp
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      (2 : ℝ≥0∞) μ :=
  twoSLSKinalExactMomentIff_memLp_two_of_two_overidentifying
    (twoSLSKinalExactMomentIff_of_jointNormal_standardizedScoreCanonicalRestInputs
      hJoint hInputs)
    hover2

set_option linter.style.longLine false in
/-- Auto-`SFinite` version of
`twoSLSKinal_memLp_two_of_two_overidentifying_of_jointNormal_standardizedScoreCanonicalRestInputs`. -/
theorem twoSLSKinal_memLp_two_of_two_overidentifying_of_jointNormal_standardizedScoreCanonicalRestInputs_autoSFinite
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hInputs :
      TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd)
    (hover2 : Fintype.card k₂ + 1 < Fintype.card l₂) :
    MemLp
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      (2 : ℝ≥0∞) μ :=
  twoSLSKinalExactMomentIff_memLp_two_of_two_overidentifying
    (twoSLSKinalExactMomentIff_of_jointNormal_standardizedScoreCanonicalRestInputs_autoSFinite
      hJoint hInputs)
    hover2

set_option linter.style.longLine false in
/-- Standardized-score canonical-rest Kinal consequence: with exactly one
overidentifying restriction, the endogenous 2SLS block has no finite second
moment. -/
theorem twoSLSKinal_not_memLp_two_of_one_overidentifying_of_jointNormal_standardizedScoreCanonicalRestInputs
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hInputs :
      TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd)
    (hover1 : Fintype.card l₂ = Fintype.card k₂ + 1) :
    ¬ MemLp
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      (2 : ℝ≥0∞) μ :=
  twoSLSKinalExactMomentIff_not_memLp_two_of_one_overidentifying
    (twoSLSKinalExactMomentIff_of_jointNormal_standardizedScoreCanonicalRestInputs
      hJoint hInputs)
    hover1

set_option linter.style.longLine false in
/-- Auto-`SFinite` version of
`twoSLSKinal_not_memLp_two_of_one_overidentifying_of_jointNormal_standardizedScoreCanonicalRestInputs`. -/
theorem twoSLSKinal_not_memLp_two_of_one_overidentifying_of_jointNormal_standardizedScoreCanonicalRestInputs_autoSFinite
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hInputs :
      TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd)
    (hover1 : Fintype.card l₂ = Fintype.card k₂ + 1) :
    ¬ MemLp
      (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
      (2 : ℝ≥0∞) μ :=
  twoSLSKinalExactMomentIff_not_memLp_two_of_one_overidentifying
    (twoSLSKinalExactMomentIff_of_jointNormal_standardizedScoreCanonicalRestInputs_autoSFinite
      hJoint hInputs)
    hover1

set_option linter.style.longLine false in
/-- Standardized-score canonical-rest Kinal consequence: with exactly one
overidentifying restriction, the endogenous 2SLS block has a finite first
moment but no finite second moment. -/
theorem twoSLSKinal_memLp_one_and_not_memLp_two_of_one_overidentifying_of_jointNormal_standardizedScoreCanonicalRestInputs
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    [SFinite (chiSquared (Fintype.card l₂ - Fintype.card k₂ + 1))]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hInputs :
      TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd)
    (hover1 : Fintype.card l₂ = Fintype.card k₂ + 1) :
    MemLp
        (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (1 : ℝ≥0∞) μ ∧
      ¬ MemLp
        (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (2 : ℝ≥0∞) μ :=
  twoSLSKinalExactMomentIff_memLp_one_and_not_memLp_two_of_one_overidentifying
    (twoSLSKinalExactMomentIff_of_jointNormal_standardizedScoreCanonicalRestInputs
      hJoint hInputs)
    hover1

set_option linter.style.longLine false in
/-- Auto-`SFinite` version of
`twoSLSKinal_memLp_one_and_not_memLp_two_of_one_overidentifying_of_jointNormal_standardizedScoreCanonicalRestInputs`. -/
theorem twoSLSKinal_memLp_one_and_not_memLp_two_of_one_overidentifying_of_jointNormal_standardizedScoreCanonicalRestInputs_autoSFinite
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X₁ : Ω → Matrix n k₁ ℝ} {Y₂ : Ω → Matrix n k₂ ℝ}
    {Z₂ : Ω → Matrix n l₂ ℝ} {Y₁ : Ω → n → ℝ}
    {Sigma : Matrix k₂ k₂ ℝ} {Rstd : Ω → Matrix l₂ k₂ ℝ}
    [Nonempty k₂]
    (hJoint : TwoSLSKinalJointNormalConditions μ X₁ Y₂ Z₂ Y₁)
    (hInputs :
      TwoSLSKinalJointNormalStandardizedScoreCanonicalRestInputs
        μ X₁ Y₂ Z₂ Y₁ Sigma Rstd)
    (hover1 : Fintype.card l₂ = Fintype.card k₂ + 1) :
    MemLp
        (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (1 : ℝ≥0∞) μ ∧
      ¬ MemLp
        (fun ω => twoSLSEndogenousBetaOrZero (X₁ ω) (Y₂ ω) (Z₂ ω) (Y₁ ω))
        (2 : ℝ≥0∞) μ :=
  twoSLSKinalExactMomentIff_memLp_one_and_not_memLp_two_of_one_overidentifying
    (twoSLSKinalExactMomentIff_of_jointNormal_standardizedScoreCanonicalRestInputs_autoSFinite
      hJoint hInputs)
    hover1

end KinalSupport

end HansenEconometrics
