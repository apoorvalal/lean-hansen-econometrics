# Chapter 7 Cheat Ledger

This file tracks places where the current Chapter 7 development is still short
of a full Hansen-style theorem statement, meaning that Lean still relies on a
bridge assumption or has not yet packaged the final law in the intended public
form.

## Closed in this pass

### 1. Gaussian linear-image law for the Wald numerator

Closed by
[hasLaw_multivariateGaussian_zero_linearMap](../HansenEconometrics/ProbabilityUtils.lean).

LaTeX:

\[
Z \sim N(0,\Omega), \qquad A := RQ^{-1}
\]
\[
AZ \sim N(0, A \Omega A')
\]

In Chapter 7 this is used with

\[
\sqrt{n}(\hat\beta_n - \beta) \Rightarrow Q^{-1} Z
\]

to derive

\[
R \sqrt{n}(\hat\beta_n - \beta) \Rightarrow N(0, R V_\beta R'),
\qquad
V_\beta := Q^{-1}\Omega Q^{-1}.
\]

That closure now feeds the public wrappers
[linearMap_olsBetaStar_waldChiSquared_gaussian](../HansenEconometrics/Chapter7Asymptotics/Normality.lean)
and
[linearMap_olsBetaOrZero_waldChiSquared_gaussian](../HansenEconometrics/Chapter7Asymptotics/Normality.lean).

### 2. Concrete multivariate robust Wald wrappers

Closed for HC0 and HC1 by
[linearMap_olsHC0WaldStatisticStar_tendstoInDistribution_chiSquared](../HansenEconometrics/Chapter7Asymptotics/Normality.lean),
[linearMap_olsHC0WaldStatisticOrZero_tendstoInDistribution_chiSquared](../HansenEconometrics/Chapter7Asymptotics/Normality.lean),
[linearMap_olsHC1WaldStatisticStar_tendstoInDistribution_chiSquared](../HansenEconometrics/Chapter7Asymptotics/Normality.lean),
and
[linearMap_olsHC1WaldStatisticOrZero_tendstoInDistribution_chiSquared](../HansenEconometrics/Chapter7Asymptotics/Normality.lean).

LaTeX:

\[
\hat W_n
=
\bigl(R\sqrt{n}(\hat\beta_n-\beta)\bigr)'
\bigl(R\hat V_n R'\bigr)^{-1}
\bigl(R\sqrt{n}(\hat\beta_n-\beta)\bigr)
\Rightarrow \chi^2_r,
\]

with \(\hat V_n\) instantiated concretely as HC0 or HC1 and

\[
R \hat V_n R' \to_p R V_\beta R'.
\]

### 3. Multivariate homoskedastic Wald wrapper

Closed by
[linearMap_olsHomoskedasticWaldStatisticStar_tendstoInDistribution_chiSquared](../HansenEconometrics/Chapter7Asymptotics/Normality.lean),
[linearMap_olsHomoskedasticWaldStatisticOrZero_tendstoInDistribution_chiSquared](../HansenEconometrics/Chapter7Asymptotics/Normality.lean),
[linearMap_olsHomoskedasticWaldStatisticOrZero_tendstoInDistribution_chiSquared_of_scoreCovariance](../HansenEconometrics/Chapter7Asymptotics/Normality.lean),
and
[linearMap_olsHomoskedasticWaldStatisticOrZero_tendstoInDistribution_chiSquared_of_homoskedastic](../HansenEconometrics/Chapter7Asymptotics/Normality.lean).

LaTeX:

\[
\Omega = \sigma^2 Q
\quad\Longrightarrow\quad
V_\beta^0 = \sigma^2 Q^{-1} = Q^{-1}\Omega Q^{-1} = V_\beta
\]

\[
\hat W_n^0
=
\bigl(R\sqrt{n}(\hat\beta_n-\beta)\bigr)'
\bigl(R\hat V^{\,0}_{\beta,n}R'\bigr)^{-1}
\bigl(R\sqrt{n}(\hat\beta_n-\beta)\bigr)
\Rightarrow \chi^2_r.
\]

### 4. HC2 / HC3 residual absolute-weight closure

Closed by deriving the `O_p(1)` residual absolute-weight averages from the
existing HC0 convergence package. The key deterministic bound is

\[
\frac1n \sum_i \left|\hat e_i^2 X_{ia} X_{ib}\right|
\;\le\;
\frac1n \sum_i \hat e_i^2 X_{ia}^2
\;+\;
\frac1n \sum_i \hat e_i^2 X_{ib}^2,
\]

so each absolute residual-score average is dominated by two diagonal HC0
middle-matrix entries. Since those diagonal entries converge in probability to
finite constants, they are `O_p(1)`.

In Lean this is packaged through
[sampleScoreCovarianceResidualAbsWeightStar_le_diag_add](../HansenEconometrics/Chapter7Asymptotics/RobustCovariance.lean),
[sampleScoreCovarianceResidualAbsWeightStar_boundedInProbability_of_middle](../HansenEconometrics/Chapter7Asymptotics/RobustCovariance.lean),
and
[sampleScoreCovarianceResidualAbsWeightStar_boundedInProbability_of_bounded_weights](../HansenEconometrics/Chapter7Asymptotics/RobustCovariance.lean),
then fed into
[sampleScoreCovarianceHC2AdjustmentStar_stack_tendstoInMeasure_zero_of_bounded_weights_and_maxLeverage](../HansenEconometrics/Chapter7Asymptotics/RobustCovariance.lean)
and
[sampleScoreCovarianceHC3AdjustmentStar_stack_tendstoInMeasure_zero_of_bounded_weights_and_maxLeverage](../HansenEconometrics/Chapter7Asymptotics/RobustCovariance.lean),
with public HC2/HC3 covariance and Wald wrappers no longer assuming that
absolute-weight boundedness separately.

### 5. HC2 / HC3 adjustment measurability

Closed by deriving adjustment measurability directly from component
measurability. The key point is that each HC2/HC3 adjustment term is a finite
sum of measurable scalar weights

\[
h \mapsto (1-h)^{-1},
\qquad
h \mapsto (1-h)^{-2},
\]

applied to measurable leverage scores, multiplied by measurable residual-score
outer products. In Lean this is packaged through
[sampleScoreCovarianceLeverageAdjustedStar_stack_aestronglyMeasurable_of_components](../HansenEconometrics/Chapter7Asymptotics/RobustCovariance.lean),
[sampleScoreCovarianceHC2AdjustmentStar_stack_aestronglyMeasurable_of_components](../HansenEconometrics/Chapter7Asymptotics/RobustCovariance.lean),
[sampleScoreCovarianceHC3AdjustmentStar_stack_aestronglyMeasurable_of_components](../HansenEconometrics/Chapter7Asymptotics/RobustCovariance.lean),
[olsHC2CovarianceStar_stack_aestronglyMeasurable_of_components](../HansenEconometrics/Chapter7Asymptotics/RobustCovariance.lean),
and
[olsHC3CovarianceStar_stack_aestronglyMeasurable_of_components](../HansenEconometrics/Chapter7Asymptotics/RobustCovariance.lean).

The public HC2/HC3 covariance and Wald wrappers therefore no longer need a
separate `hAdj_meas` premise.

## Remaining cheats

### 1. Assumption-layer gap

This is not circular, but it is still stronger than the literal textbook
packaging. Several Chapter 7 public theorems use the repo’s sufficient
assumption bundles such as
[LeastSquaresConsistencyConditions](../HansenEconometrics/Chapter7Asymptotics/Consistency.lean),
[ErrorVarianceConsistencyConditions](../HansenEconometrics/Chapter7Asymptotics/Consistency.lean),
[ScoreCLTConditions](../HansenEconometrics/Chapter7Asymptotics/RobustCovariance.lean),
and
[RobustCovarianceConsistencyConditions](../HansenEconometrics/Chapter7Asymptotics/RobustCovariance.lean)
instead of the literal textbook iid assumptions.

Internally these are still implemented by the proof-engine bundles
`SampleMomentAssumption71`, `SampleVarianceAssumption74`,
`SampleCLTAssumption72`, and `SampleHC0Assumption76`.

That is a packaging gap, not a law-identification cheat.
