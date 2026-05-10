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

The next natural applications are `refs/regrank.pdf`, which studies regression-induced
ranking reversals, and `refs/2106.05024v5.pdf`, Goldsmith-Pinkham, Hull, and Kolesar's
"Contamination Bias in Linear Regressions."
