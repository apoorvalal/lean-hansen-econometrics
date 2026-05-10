import HansenEconometrics.Chapter3FWL

open scoped Matrix

namespace HansenEconometrics
namespace Applications
namespace Angrist1998

open Matrix

variable {n c : Type*}
variable [Fintype n]

/-- A scalar treatment variable as a one-column regression design. -/
noncomputable def treatmentDesign (d : n → ℝ) : Matrix n Unit ℝ :=
  fun i _ => d i

/-- The coefficient on treatment in a regression of `y` on controls and treatment. -/
noncomputable def regressionCoefficient
    (controls : Matrix n c ℝ) (d y : n → ℝ)
    [Fintype c] [DecidableEq c]
    [Invertible ((Matrix.fromCols controls (treatmentDesign d))ᵀ *
      Matrix.fromCols controls (treatmentDesign d))] : ℝ :=
  fromColsRightBeta controls (treatmentDesign d) y ()

/-- The auxiliary FWL coefficient from regressing residualized outcomes on
residualized treatment. -/
noncomputable def residualizedCoefficient
    (controls : Matrix n c ℝ) (d y : n → ℝ)
    [DecidableEq n] [Fintype c] [DecidableEq c]
    [Invertible (controlsᵀ * controls)]
    [Invertible ((residualizedRegressors controls (treatmentDesign d))ᵀ *
      residualizedRegressors controls (treatmentDesign d))] : ℝ :=
  fwlBeta controls (treatmentDesign d) y ()

/--
Angrist (1998), Sections 2.1--2.2, algebraic core.

The coefficient on treatment in a regression with controls equals the coefficient obtained by
first residualizing both treatment and outcome with respect to the controls. When the controls are
saturated covariate cells, expanding this residualized scalar regression gives the familiar
conditional-variance weighting of covariate-specific treatment contrasts.
-/
theorem regressionCoefficient_eq_residualizedCoefficient
    (controls : Matrix n c ℝ) (d y : n → ℝ)
    [DecidableEq n] [Fintype c] [DecidableEq c]
    [Invertible (controlsᵀ * controls)]
    [Invertible ((Matrix.fromCols controls (treatmentDesign d))ᵀ *
      Matrix.fromCols controls (treatmentDesign d))]
    [Invertible ((residualizedRegressors controls (treatmentDesign d))ᵀ *
      residualizedRegressors controls (treatmentDesign d))] :
    regressionCoefficient controls d y = residualizedCoefficient controls d y := by
  unfold regressionCoefficient residualizedCoefficient
  exact congrFun (fromColsRightBeta_eq_fwlBeta controls (treatmentDesign d) y) ()

/--
Equivalent explicit partitioned-regression formula: the treatment coefficient is
`(D' M_X D)^{-1} D' M_X Y`, with `D` represented as a one-column matrix.
-/
theorem regressionCoefficient_eq_partitionedFormula
    (controls : Matrix n c ℝ) (d y : n → ℝ)
    [DecidableEq n] [Fintype c] [DecidableEq c]
    [Invertible (controlsᵀ * controls)]
    [Invertible ((Matrix.fromCols controls (treatmentDesign d))ᵀ *
      Matrix.fromCols controls (treatmentDesign d))]
    [Invertible ((residualizedRegressors controls (treatmentDesign d))ᵀ *
      residualizedRegressors controls (treatmentDesign d))] :
    regressionCoefficient controls d y =
      partitionedRightBetaFormula controls (treatmentDesign d) y () := by
  unfold regressionCoefficient
  exact congrFun (fromColsRightBeta_eq_partitionedRightBetaFormula
    controls (treatmentDesign d) y) ()

end Angrist1998
end Applications
end HansenEconometrics
