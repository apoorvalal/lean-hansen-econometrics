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

variable {g : Type*}
variable [Fintype g]

/-- Binary treatment indicator as a real-valued regressor. -/
def binaryTreatmentValue : Bool → ℝ
  | false => 0
  | true => 1

/-- Cell-level joint mass for cell `x` and treatment state `d`. -/
def cellJointMass (cellMass propensity : g → ℝ) (x : g) (d : Bool) : ℝ :=
  cellMass x * if d then propensity x else 1 - propensity x

/-- Cell-level conditional outcome mean by untreated/treated status. -/
def cellOutcomeMean (y0 y1 : g → ℝ) (x : g) (d : Bool) : ℝ :=
  if d then y1 x else y0 x

/-- Treatment residual after saturating on the cell indicators. -/
def cellTreatmentResidual (propensity : g → ℝ) (x : g) (d : Bool) : ℝ :=
  binaryTreatmentValue d - propensity x

/-- Angrist's overlap weight for a saturated covariate cell. -/
def overlapWeight (cellMass propensity : g → ℝ) (x : g) : ℝ :=
  cellMass x * propensity x * (1 - propensity x)

/-- Cell-specific treated-minus-untreated mean contrast. -/
def cellTreatmentEffect (y0 y1 : g → ℝ) (x : g) : ℝ :=
  y1 x - y0 x

/-- Numerator of the residualized-treatment regression after saturating on cells. -/
noncomputable def cellResidualizedTreatmentOutcomeMoment
    (cellMass propensity y0 y1 : g → ℝ) : ℝ :=
  ∑ x : g, ∑ d : Bool,
    cellJointMass cellMass propensity x d *
      cellTreatmentResidual propensity x d *
        cellOutcomeMean y0 y1 x d

/-- Denominator of the residualized-treatment regression after saturating on cells. -/
noncomputable def cellResidualizedTreatmentSecondMoment
    (cellMass propensity : g → ℝ) : ℝ :=
  ∑ x : g, ∑ d : Bool,
    cellJointMass cellMass propensity x d *
      (cellTreatmentResidual propensity x d) ^ 2

/-- Cell-level residualized-regression coefficient. -/
noncomputable def cellRegressionCoefficient
    (cellMass propensity y0 y1 : g → ℝ) : ℝ :=
  cellResidualizedTreatmentOutcomeMoment cellMass propensity y0 y1 /
    cellResidualizedTreatmentSecondMoment cellMass propensity

/-- Angrist's Section 2.2 overlap-weighted average of cell treatment effects. -/
noncomputable def overlapWeightedTreatmentEffect
    (cellMass propensity y0 y1 : g → ℝ) : ℝ :=
  (∑ x : g, overlapWeight cellMass propensity x * cellTreatmentEffect y0 y1 x) /
    ∑ x : g, overlapWeight cellMass propensity x

omit [Fintype g] in
/-- The overlap weight is nonnegative for a nonnegative cell mass and a propensity in `[0,1]`. -/
theorem overlapWeight_nonneg
    (cellMass propensity : g → ℝ) (x : g)
    (hm : 0 ≤ cellMass x) (hp0 : 0 ≤ propensity x) (hp1 : propensity x ≤ 1) :
    0 ≤ overlapWeight cellMass propensity x := by
  exact mul_nonneg (mul_nonneg hm hp0) (sub_nonneg.mpr hp1)

omit [Fintype g] in
/-- Cells with zero treatment probability receive zero overlap weight. -/
@[simp] theorem overlapWeight_of_propensity_eq_zero
    (cellMass propensity : g → ℝ) (x : g) (h : propensity x = 0) :
    overlapWeight cellMass propensity x = 0 := by
  simp [overlapWeight, h]

omit [Fintype g] in
/-- Cells with treatment probability one receive zero overlap weight. -/
@[simp] theorem overlapWeight_of_propensity_eq_one
    (cellMass propensity : g → ℝ) (x : g) (h : propensity x = 1) :
    overlapWeight cellMass propensity x = 0 := by
  simp [overlapWeight, h]

/--
After saturating on covariate cells, the residualized-treatment/outcome moment
is the sum of overlap weights times cell treatment contrasts.
-/
theorem cellResidualizedTreatmentOutcomeMoment_eq_overlap_sum
    (cellMass propensity y0 y1 : g → ℝ) :
    cellResidualizedTreatmentOutcomeMoment cellMass propensity y0 y1 =
      ∑ x : g, overlapWeight cellMass propensity x * cellTreatmentEffect y0 y1 x := by
  unfold cellResidualizedTreatmentOutcomeMoment overlapWeight cellTreatmentEffect
  refine Finset.sum_congr rfl ?_
  intro x _
  simp [cellJointMass, cellTreatmentResidual, binaryTreatmentValue, cellOutcomeMean]
  ring

/--
After saturating on covariate cells, the residualized-treatment second moment
is the sum of overlap weights.
-/
theorem cellResidualizedTreatmentSecondMoment_eq_overlap_sum
    (cellMass propensity : g → ℝ) :
    cellResidualizedTreatmentSecondMoment cellMass propensity =
      ∑ x : g, overlapWeight cellMass propensity x := by
  unfold cellResidualizedTreatmentSecondMoment overlapWeight
  refine Finset.sum_congr rfl ?_
  intro x _
  simp [cellJointMass, cellTreatmentResidual, binaryTreatmentValue]
  ring

/--
Angrist (1998), Section 2.2, saturated-cell regression-weight formula.

The regression coefficient after saturating on cells equals the overlap-weighted
average of cell-specific treated-minus-untreated mean contrasts. The overlap
weights are proportional to `mass(x) * p(x) * (1 - p(x))`.
-/
theorem cellRegressionCoefficient_eq_overlapWeightedTreatmentEffect
    (cellMass propensity y0 y1 : g → ℝ) :
    cellRegressionCoefficient cellMass propensity y0 y1 =
      overlapWeightedTreatmentEffect cellMass propensity y0 y1 := by
  unfold cellRegressionCoefficient overlapWeightedTreatmentEffect
  rw [cellResidualizedTreatmentOutcomeMoment_eq_overlap_sum,
    cellResidualizedTreatmentSecondMoment_eq_overlap_sum]

end Angrist1998
end Applications
end HansenEconometrics
