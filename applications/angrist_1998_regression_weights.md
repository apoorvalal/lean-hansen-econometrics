# Angrist 1998: Regression Weights

Source: `refs/angrist1988.pdf`, Joshua D. Angrist, "Estimating the Labor Market Impact of
Voluntary Military Service Using Social Security Data on Military Applicants," Econometrica,
1998. The local filename says `1988`, but the paper is the 1998 Econometrica article.

## Sections 2.1 and 2.2

Section 2.1 sets up potential outcomes $Y_0$ and $Y_1$, treatment $D$, and covariates $X$.
The target is the effect of treatment on the treated. Under conditional ignorability,
$(Y_1,Y_0) \perp D \mid X$, the treated effect can be written as a weighted average of
within-covariate treatment-control contrasts. The matching estimand weights each
covariate-specific contrast by the distribution of $X$ among treated units.

Section 2.2 compares that matching estimand with the coefficient on $D$ in a regression of
$Y$ on $D$ and controls for $X$. With heterogeneous treatment effects, the regression
coefficient is also a weighted average of covariate-specific effects, but it uses overlap
weights. In the saturated-control case, the weights are proportional to
$$
P(D=1 \mid X)(1-P(D=1 \mid X))P(X).
$$
Thus cells with no treatment variation get zero weight, and cells where treatment is close
to half treated receive relatively more weight than they do under treated-distribution
matching.

## Algebraic Claim

The deterministic algebra behind Section 2.2 is the Frisch-Waugh-Lovell theorem. Let
`controls` be the control design matrix, let `d` be the treatment vector, let `y` be the
outcome vector, and define the residual-maker
$$
M_X = I - X(X'X)^{-1}X'.
$$
If the relevant Gram matrices are invertible, the treatment coefficient from the full
regression on `[X D]` equals the coefficient from the auxiliary regression of residualized
outcomes on residualized treatment:
$$
\hat{\alpha}
= \operatorname{coef}_D(Y \sim X,D)
= \operatorname{coef}(M_XY \sim M_XD)
= (D'M_XD)^{-1}D'M_XY.
$$

When `controls` are saturated covariate-cell indicators, expanding $M_XD$ gives within-cell
treatment residuals $D_i - P(D=1 \mid X_i)$. The denominator $D'M_XD$ therefore aggregates
within-cell treatment variation, which is the source of Angrist's conditional-variance
regression weights. The causal interpretation still requires the potential-outcomes
assumptions from Section 2.1; the Lean result proved here is only the finite-sample
regression algebra.

## Lean Result

The application module is `applications/Angrist1998.lean`.

Key declarations:

- `treatmentDesign`: represents a scalar treatment vector as a one-column matrix.
- `regressionCoefficient`: the treatment coefficient from the full regression on controls
  and treatment.
- `residualizedCoefficient`: the FWL auxiliary coefficient from residualized treatment and
  residualized outcomes.
- `regressionCoefficient_eq_residualizedCoefficient`: proves the FWL identity specialized
  to Angrist's regression-weight setup.
- `regressionCoefficient_eq_partitionedFormula`: proves the displayed partitioned formula
  `(D' M_X D)^{-1} D' M_X Y` in the existing Hansen matrix notation.

## Lean Proof Walkthrough

The proof worked: `applications/Angrist1998.lean` compiles, and the top-level `lake build`
now builds the `applications` library as well as the core `HansenEconometrics` library.

The application module deliberately proves only a thin, Angrist-shaped wrapper around the
existing Hansen Chapter 3 FWL machinery. The reason is that Section 2.2's regression-weight
claim starts from a standard regression coefficient. Before expanding that coefficient into
cell weights, the first algebraic step is simply the FWL identity:
$$
\operatorname{coef}_D(Y \sim X,D)=\operatorname{coef}(M_XY \sim M_XD).
$$

The module starts with:

```lean
import HansenEconometrics.Chapter3FWL
```

This import supplies the existing finite-sample regression algebra:

- `Matrix.fromCols X1 X2`: the block design `[X1 X2]`.
- `fromColsRightBeta X1 X2 y`: the right-block coefficient from the full regression.
- `residualizedRegressors X1 X2`: the residualized right block `M1 X2`.
- `fwlBeta X1 X2 y`: the auxiliary coefficient from regressing `M1 y` on `M1 X2`.
- `partitionedRightBetaFormula X1 X2 y`: the explicit `(X2' M1 X2)^{-1} X2' M1 y`
  formula.
- `fromColsRightBeta_eq_fwlBeta`: Hansen's FWL coefficient theorem.
- `fromColsRightBeta_eq_partitionedRightBetaFormula`: Hansen's explicit
  partitioned-regression formula.

The application-level row type is `n`, and the control-column type is `c`:

```lean
variable {n c : Type*}
variable [Fintype n]
```

The rows must be finite because all regression objects are finite matrices. The control
type `c` is not declared finite globally; instead, the definitions and theorems request
`[Fintype c] [DecidableEq c]` exactly where matrix multiplication and block-column indexing
need them.

Angrist's treatment variable is scalar, while the Hansen FWL theorem expects a matrix block.
The bridge is a one-column design:

```lean
noncomputable def treatmentDesign (d : n → ℝ) : Matrix n Unit ℝ :=
  fun i _ => d i
```

The column index is `Unit`, which has exactly one element. Thus a vector-valued coefficient
indexed by `Unit` is a scalar coefficient in disguise. Evaluating that coefficient at `()`
extracts the scalar.

The full-regression treatment coefficient is:

```lean
noncomputable def regressionCoefficient
    (controls : Matrix n c ℝ) (d y : n → ℝ)
    [Fintype c] [DecidableEq c]
    [Invertible ((Matrix.fromCols controls (treatmentDesign d))ᵀ *
      Matrix.fromCols controls (treatmentDesign d))] : ℝ :=
  fromColsRightBeta controls (treatmentDesign d) y ()
```

Mathematically, this is the coefficient on `D` in the regression of `Y` on `[X D]`.
The invertibility assumption is the usual full-rank Gram condition for the full design.
The expression `fromColsRightBeta controls (treatmentDesign d) y` has type `Unit → ℝ`,
so applying it to `()` returns the one treatment coefficient.

The residualized coefficient is:

```lean
noncomputable def residualizedCoefficient
    (controls : Matrix n c ℝ) (d y : n → ℝ)
    [DecidableEq n] [Fintype c] [DecidableEq c]
    [Invertible (controlsᵀ * controls)]
    [Invertible ((residualizedRegressors controls (treatmentDesign d))ᵀ *
      residualizedRegressors controls (treatmentDesign d))] : ℝ :=
  fwlBeta controls (treatmentDesign d) y ()
```

This is the coefficient from regressing `M_XY` on `M_XD`. The extra assumptions say:

- `controlsᵀ * controls` is invertible, so the control residual-maker `M_X` is defined.
- `(M_XD)'(M_XD)` is invertible, so the auxiliary one-regressor regression is defined.
- `DecidableEq n` is needed because the annihilator matrix uses the identity matrix on rows.

The main theorem is:

```lean
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
```

The proof has two steps.

First, `unfold regressionCoefficient residualizedCoefficient` replaces the two
application-level names by their definitions. The goal becomes:

```lean
fromColsRightBeta controls (treatmentDesign d) y ()
  = fwlBeta controls (treatmentDesign d) y ()
```

Second, the existing Chapter 3 theorem

```lean
fromColsRightBeta_eq_fwlBeta controls (treatmentDesign d) y
```

proves equality of the full `Unit → ℝ` coefficient vectors:

```lean
fromColsRightBeta controls (treatmentDesign d) y
  = fwlBeta controls (treatmentDesign d) y
```

Since this is equality of functions, `congrFun ... ()` applies both sides to the unique
`Unit` value `()`. That extracts the scalar treatment coefficient and closes the goal.

The second theorem records the explicit display formula:

```lean
theorem regressionCoefficient_eq_partitionedFormula
    ...
    regressionCoefficient controls d y =
      partitionedRightBetaFormula controls (treatmentDesign d) y () := by
  unfold regressionCoefficient
  exact congrFun (fromColsRightBeta_eq_partitionedRightBetaFormula
    controls (treatmentDesign d) y) ()
```

This proof is identical in structure. After unfolding `regressionCoefficient`, the goal is
the scalar version of the already-proved partitioned-regression theorem. The theorem
`fromColsRightBeta_eq_partitionedRightBetaFormula` gives the vector identity, and
`congrFun ... ()` extracts the unique scalar coordinate. In mathematical notation, the
right side is:
$$
(D'M_XD)^{-1}D'M_XY.
$$

So the formalized result is not yet the fully expanded cell-weight expression
$$
\frac{E[E[Y_1-Y_0 \mid X]P(D=1 \mid X)(1-P(D=1 \mid X))]}
{E[P(D=1 \mid X)(1-P(D=1 \mid X))]}.
$$
What is now proved is the finite-sample regression-algebra engine from which that expression
is derived once the control design is specialized to saturated covariate cells and the
treatment vector is binary.

The next natural applications are `refs/regrank.pdf`, which studies regression-induced
ranking reversals, and `refs/2106.05024v5.pdf`, Goldsmith-Pinkham, Hull, and Kolesar's
"Contamination Bias in Linear Regressions."
