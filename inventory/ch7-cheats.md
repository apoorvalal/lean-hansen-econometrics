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

## Remaining cheats

### 1. HC2 / HC3 primitive-moment closure

The max-leverage half is now closed. Lean proves:

\[
\max_i h_{ii,n} \to_p 0
\Longrightarrow
\max_i \bigl|w_{n,i} - 1\bigr| = o_p(1),
\]

and then packages HC2/HC3 covariance and multivariate Wald wrappers from

\[
\max_i \bigl|w_{n,i} - 1\bigr| = o_p(1)
\quad\text{and}\quad
\frac{1}{n}\sum_i |\hat e_i^2 X_{ia} X_{ib}| = O_p(1).
\]

What remains is narrower: discharge the residual absolute-weight boundedness
hypothesis from primitive Hansen-style moment assumptions, and then remove the
technical adjustment-measurability premise if possible.

### 2. Assumption-layer gap

This is not circular, but it is still stronger than the literal textbook
packaging. Several Chapter 7 public theorems use the repo’s sufficient
assumption bundles such as
[SampleCLTAssumption72](../HansenEconometrics/Chapter7Asymptotics/Normality.lean)
instead of a theorem stated directly from the textbook iid assumptions.

That is a packaging gap, not a law-identification cheat.
