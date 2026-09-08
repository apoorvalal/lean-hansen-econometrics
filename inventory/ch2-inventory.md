# Chapter 2 Inventory and Crosswalk

This file is the canonical Chapter 2 note for:
- chapter status and next targets
- proof architecture / dependency notes
- textbook-to-Lean theorem crosswalk

## Scope

Target chapter:
- `chapters/02-conditional-expectation-and-projection.pdf`

Source text:
- [ch2_excerpt.txt](../textbook/ch02/ch2_excerpt.txt)

Lean files:
- [Chapter2CondExp.lean](../HansenEconometrics/Chapter2CondExp.lean)
- [Chapter2Variance.lean](../HansenEconometrics/Chapter2Variance.lean)
- [Chapter2LinearProjection.lean](../HansenEconometrics/Chapter2LinearProjection.lean)
- [Chapter2PotentialOutcomes.lean](../HansenEconometrics/Chapter2PotentialOutcomes.lean)
- reusable helpers in [ProbabilityUtils.lean](../HansenEconometrics/ProbabilityUtils.lean)

## Status

Current Lean coverage:
- conditional expectation backbone: simple LIE, tower property, conditioning theorem
- CEF error package: mean-zero and orthogonality facts
- conditional variance / total variance package
- best predictor theorem
- population linear projection algebra through Theorems 2.9 and 2.10
- potential-outcomes API for Section 2.30:
  observed outcomes, individual/average/conditional treatment effects, a Mathlib `CondIndepFun` CIA
  package, variable-facing CATE bridges for Theorem 2.12, branchwise observed-regression wrappers
  for conditioning on `(D, X)`, and thin pointwise `ACE(x)` / `m(1,x)-m(0,x)` surface bridges

Current strategy:
- prove the strongest sigma-algebra or abstract statement first
- add variable-facing or textbook-facing wrappers when they improve usability
- reuse Mathlib conditional-expectation and `L²` projection infrastructure where possible

Next likely Chapter 2 targets:
- decide whether any remaining Chapter 2 results are worth formalizing before moving on

## Proof Architecture

### Level 0: imported Mathlib primitives
- `MeasureTheory.integral_condExp`
- `MeasureTheory.condExp_condExp_of_le`
- `MeasureTheory.condExp_mul_of_aestronglyMeasurable_left`
- `MeasureTheory.condExp_of_stronglyMeasurable`
- `MeasureTheory.condExp_sub`

### Level 1: direct conditional-expectation specializations
- **T2.1** simple law of iterated expectations
- **T2.2** tower property for nested conditioning information
- **T2.3** conditioning theorem / pull-out property

### Level 2: CEF error package
Define:
- `e = Y - E[Y | m]`

Then prove:
- **T2.4.1** `E[e | m] = 0`
- **T2.4.2** `E[e] = 0`
- **T2.4.4** `E[g e] = 0` for `m`-measurable `g`

### Level 3: variance package
- expected conditional variance as expected squared CEF error
- **T2.8** law of total variance
- explained-variance corollary `Var[E[Y | m]] ≤ Var[Y]`

### Level 4: linear projection package
- **T2.9** core algebra:
  `β = QXX⁻¹ QXY`
- normal equations:
  `QXX β = QXY`
- orthogonality:
  `QXY - QXX β = 0`
- quadratic criterion simplification at `β`
- quadratic completion:
  `S(b) = S(β) + (b - β)' QXX (b - β)`
- best-linear-predictor minimization statement
- moment wrapper:
  `β = (E[XX'])⁻¹ E[XY]`
- **T2.10** coefficient formulas:
  `α = μY - μX' β`
  and
  `β = var[X]⁻¹ cov(X, Y)`

### Level 5: potential-outcomes package
Define:
- observed outcome `Y = Y(1)` on treated units and `Y = Y(0)` on untreated units
- individual treatment effect `Y(1) - Y(0)`
- average treatment effect `E[Y(1) - Y(0)]`
- conditional average treatment effect `E[Y(1) - Y(0) | X]`

Then prove:
- **D2.6/D2.7** `ATE = E[Y(1)] - E[Y(0)]`
- **D2.8** `CATE(X) = E[Y(1) | X] - E[Y(0) | X]`
- `ATE = E[CATE(X)]` by the tower property
- a Mathlib conditional-independence package for **D2.9/CIA**:
  if `D` is conditionally independent of each potential outcome given `X`, then the mean-independence
  bridge follows by the conditional-distribution characterization
- variable-facing **T2.12** bridges:
  if conditioning additionally on treatment does not change the potential-outcome conditional means,
  then the `(D, X)` potential-outcome contrast equals the CATE
- observed-regression branch identities:
  `E[Y | D, X]` equals the treated potential-outcome conditional mean on treated units and the
  untreated potential-outcome conditional mean on untreated units, with a CIA-facing wrapper

## Textbook-numbered Results

### T2.1 Simple Law of Iterated Expectations

Links:
- [Hansen excerpt](../textbook/ch02/ch2_excerpt.txt#L491)
- [Backend sigma-algebra theorem](../HansenEconometrics/Chapter2CondExp.lean#L18)

| LaTeX | Lean conclusion |
| --- | --- |
| $\int \mathbb{E}[Y \mid \mathcal{G}] \, d\mu = \int Y \, d\mu$ | <code>∫ ω, (μ[Y &#124; m]) ω ∂μ = ∫ ω, Y ω ∂μ</code> |

Notes:
- This remains a backend sigma-algebra theorem.

### T2.2 Tower Property

Links:
- [Hansen excerpt](../textbook/ch02/ch2_excerpt.txt#L543)
- [Variable-facing theorem](../HansenEconometrics/Chapter2CondExp.lean)
- [Backend sigma-algebra theorem](../HansenEconometrics/Chapter2CondExp.lean#L26)
- [Older `X₁, X₂` wrapper](../HansenEconometrics/Chapter2CondExp.lean#L37)

| LaTeX | Lean conclusion |
| --- | --- |
| $\mathbb{E}[\mathbb{E}[Y \mid \mathcal{G}_2] \mid \mathcal{G}_1] = \mathbb{E}[Y \mid \mathcal{G}_1]$ | <code>condExpOn μ (condExpOn μ Y X₂) X₁ =ᵐ[μ] condExpOn μ Y X₁</code> |

Notes:
- The public theorem is variable-facing and assumes `conditioningSpace X₁ ≤ conditioningSpace X₂`.
- The backend sigma-algebra theorem remains the proof substrate.

### T2.3 Conditioning Theorem

Links:
- [Hansen excerpt](../textbook/ch02/ch2_excerpt.txt#L587)
- [Variable-facing a.e. form](../HansenEconometrics/Chapter2CondExp.lean)
- [Variable-facing integrated form](../HansenEconometrics/Chapter2CondExp.lean)
- [Backend sigma-algebra form](../HansenEconometrics/Chapter2CondExp.lean#L54)

| LaTeX | Lean conclusion |
| --- | --- |
| $\mathbb{E}[gY \mid X] = g \, \mathbb{E}[Y \mid X]$ | <code>condExpOn μ (fun ω => g ω * Y ω) X =ᵐ[μ] fun ω => g ω * condExpOn μ Y X ω</code> |
| $\int gY \, d\mu = \int g \, \mathbb{E}[Y \mid X] \, d\mu$ | <code>∫ ω, g ω * Y ω ∂μ = ∫ ω, g ω * condExpOn μ Y X ω ∂μ</code> |

Notes:
- The backend theorem is still sigma-algebra based.

### T2.4 Properties of the CEF Error

Links:
- [Hansen excerpt](../textbook/ch02/ch2_excerpt.txt#L632)
- [T2.4.1 variable-facing theorem](../HansenEconometrics/Chapter2CondExp.lean)
- [T2.4.2 variable-facing theorem](../HansenEconometrics/Chapter2CondExp.lean)
- [T2.4.4 variable-facing theorem](../HansenEconometrics/Chapter2CondExp.lean)
- [Backend sigma-algebra proofs](../HansenEconometrics/Chapter2CondExp.lean#L78)

| LaTeX | Lean conclusion |
| --- | --- |
| $\mathbb{E}[e \mid X] = 0$ | <code>condExpOn μ (cefErrorOn μ Y X) X =ᵐ[μ] 0</code> |
| $\int e \, d\mu = 0$ | <code>∫ ω, cefErrorOn μ Y X ω ∂μ = 0</code> |
| $\int g(X) e \, d\mu = 0$ | <code>∫ ω, g ω * cefErrorOn μ Y X ω ∂μ = 0</code> |

### T2.5 Finite Regression-error Variance

Links:
- [Hansen excerpt](../textbook/ch02/ch2_excerpt.txt#L691)
- [Backend theorem](../HansenEconometrics/Chapter2Variance.lean#L28)
- [Public CEF error wrapper](../HansenEconometrics/ProbabilityUtils.lean)

| LaTeX | Lean conclusion |
| --- | --- |
| $\mathbb{E}[Y^2] < \infty \Longrightarrow \mathbb{E}[e^2] < \infty$ | <code>MemLp (cefError μ Y m) 2 μ</code> |

Notes:
- The theorem currently lives in the backend sigma-algebra layer.
- The public variable-facing error object is `cefErrorOn μ Y X`.

### T2.6 More Information Weakly Reduces Residual Variance

Links:
- [Hansen excerpt](../textbook/ch02/ch2_excerpt.txt#L711)
- [Variable-facing theorem](../HansenEconometrics/Chapter2Variance.lean)
- [Backend sigma-algebra theorem](../HansenEconometrics/Chapter2Variance.lean#L76)

| LaTeX | Lean conclusion |
| --- | --- |
| $\operatorname{Var}(Y - \mathbb{E}[Y \mid \mathcal{G}_2]) \le \operatorname{Var}(Y - \mathbb{E}[Y \mid \mathcal{G}_1])$ | <code>residualVarOn μ Y X₂ ≤ residualVarOn μ Y X₁</code> |

Notes:
- The public theorem is variable-facing and assumes `conditioningSpace X₁ ≤ conditioningSpace X₂`.
- The backend theorem remains stated directly in sigma-algebra language.

### T2.7 Conditional Expectation as Best Predictor

Links:
- [Hansen excerpt](../textbook/ch02/ch2_excerpt.txt#L778)
- [Variable-facing theorem](../HansenEconometrics/Chapter2CondExp.lean)
- [Backend sigma-algebra theorem](../HansenEconometrics/Chapter2CondExp.lean#L175)

| LaTeX | Lean conclusion |
| --- | --- |
| $\mathbb{E}[(Y - g(X))^2] \ge \mathbb{E}[(Y - \mathbb{E}[Y \mid X])^2]$ | <code>∫ ω, (Y ω - condExpOn μ Y X ω)^2 ∂μ ≤ ∫ ω, (Y ω - g ω)^2 ∂μ</code> |

Notes:
- The backend sigma-algebra theorem is still available when a later proof genuinely needs it.

### T2.8 Law of Total Variance

Links:
- [Hansen excerpt](../textbook/ch02/ch2_excerpt.txt#L847)
- [Variable-facing law of total variance](../HansenEconometrics/Chapter2Variance.lean)
- [Explained-variance bound](../HansenEconometrics/Chapter2Variance.lean)
- [Backend sigma-algebra theorem](../HansenEconometrics/Chapter2Variance.lean#L35)

| LaTeX | Lean conclusion |
| --- | --- |
| $\operatorname{Var}(Y) = \mathbb{E}[\operatorname{Var}(Y \mid X)] + \operatorname{Var}(\mathbb{E}[Y \mid X])$ | <code>μ[condVarOn μ Y X] + Var[condExpOn μ Y X; μ] = Var[Y; μ]</code> |

Notes:
- The explained-variance corollary is also available as
  `variance_condExpOn_le_variance`, while the main RV-facing variance-decomposition theorem is
  `law_total_variance_rv`.

### T2.9 Linear Projection Model

Links:
- [Hansen excerpt](../textbook/ch02/ch2_excerpt.txt#L1448)
- [Normal equations](../HansenEconometrics/Chapter2LinearProjection.lean#L25)
- [Orthogonality](../HansenEconometrics/Chapter2LinearProjection.lean#L34)
- [Criterion at `β`](../HansenEconometrics/Chapter2LinearProjection.lean#L52)
- [Quadratic completion](../HansenEconometrics/Chapter2LinearProjection.lean#L62)
- [Minimization](../HansenEconometrics/Chapter2LinearProjection.lean#L96)
- [Moment wrapper](../HansenEconometrics/Chapter2LinearProjection.lean#L108)

| LaTeX | Lean conclusion |
| --- | --- |
| $Q_{XX} \beta = Q_{XY}$ | <code>QXX *ᵥ linearProjectionBeta QXX QXY = QXY</code> |
| $Q_{XY} - Q_{XX} \beta = 0$ | <code>QXY - QXX *ᵥ linearProjectionBeta QXX QXY = 0</code> |
| $S(\beta) = Q_{YY} - \beta' Q_{XY}$ | <code>linearProjectionMSE QXX QXY QYY (linearProjectionBeta QXX QXY) = QYY - linearProjectionBeta QXX QXY ⬝ᵥ QXY</code> |
| $S(b) = S(\beta) + (b - \beta)' Q_{XX} (b - \beta)$ | <code>linearProjectionMSE QXX QXY QYY b =</code><br><code>linearProjectionMSE QXX QXY QYY (linearProjectionBeta QXX QXY)</code><br><code>+ (b - linearProjectionBeta QXX QXY) ⬝ᵥ (QXX *ᵥ (b - linearProjectionBeta QXX QXY))</code> |
| $S(\beta) \le S(b)$ | <code>linearProjectionMSE QXX QXY QYY (linearProjectionBeta QXX QXY) ≤ linearProjectionMSE QXX QXY QYY b</code> |
| If $EXX = E[XX']$, $EXY = E[XY]$, and $EY2 = E[Y^2]$, then $S(\beta) \le S(b)$ | <code>linearProjectionMSE EXX EXY EY2 (linearProjectionBeta EXX EXY) ≤ linearProjectionMSE EXX EXY EY2 b</code> |

Notes:
- The last row is the textbook moment wrapper for the minimization statement.
- Lean also includes the uniqueness result [`linearProjectionBeta_eq_of_MSE_eq`](../HansenEconometrics/Chapter2LinearProjection.lean#L119).

### T2.10 Regression Coefficients

Links:
- [Hansen excerpt](../textbook/ch02/ch2_excerpt.txt#L1765)
- [Intercept formula](../HansenEconometrics/Chapter2LinearProjection.lean#L160)
- [Slope formula](../HansenEconometrics/Chapter2LinearProjection.lean#L189)

| LaTeX | Lean conclusion |
| --- | --- |
| $\alpha = \mu_Y - \mu_X' \beta$ | <code>α = ∫ ω, Y ω ∂μ - meanVec μ X ⬝ᵥ β</code> |
| $\beta = \operatorname{var}[X]^{-1} \operatorname{cov}(X, Y)$ | <code>β = linearProjectionBeta (covMat μ X) (covVec μ X Y)</code> |

Notes:
- The slope formula is a covariance-form corollary of the earlier normal-equations theorem.

### D2.6-D2.9 Potential Outcomes and Conditional Independence

Links:
- [Hansen excerpt](../textbook/ch02/ch2_excerpt.txt#L2334)
- [Potential-outcomes definitions](../HansenEconometrics/Chapter2PotentialOutcomes.lean)

| LaTeX | Lean conclusion |
| --- | --- |
| $Y = Y(1)$ if $D=1$, and $Y = Y(0)$ if $D=0$ | <code>observedOutcome D Y0 Y1</code> |
| $C = Y(1) - Y(0)$ | <code>treatmentEffect Y0 Y1</code> |
| $ACE = E[Y(1)-Y(0)]$ | <code>averageTreatmentEffect μ Y0 Y1</code> |
| $ACE(X) = E[Y(1)-Y(0) \mid X]$ | <code>conditionalAverageTreatmentEffectOn μ Y0 Y1 X</code> |
| Pointwise $ACE(x)$ surface from conditional-mean versions | <code>conditionalAverageTreatmentEffectSurface m0 m1</code> |
| Pointwise observed-regression surface $m(d,x)$ | <code>observedRegressionSurface m0 m1</code> |
| Pointwise contrast $m(1,x)-m(0,x)$ | <code>observedRegressionTreatmentContrastSurface m</code> |
| CIA mean-independence consequence | <code>TreatmentMeanIndependentOn μ Y0 Y1 D X</code> |
| Variable-facing CIA package | <code>PotentialOutcomeCIAOn μ Y0 Y1 D X</code> |
| Observed-outcome regression on treatment and covariates | <code>condExpOn μ (observedOutcome D Y0 Y1) (fun ω => (D ω, X ω))</code> |

Notes:
- Hansen calls the population quantity the average causal effect, `ACE`. The Lean API uses the more
  common causal-inference name `averageTreatmentEffect`.
- The current Lean layer remains variable-facing and a.e.-based for conditional expectations. The
  pointwise surface definitions are thin notation bridges: once versions `m0` and `m1` of
  `E[Y(0) | X=x]` and `E[Y(1) | X=x]` are supplied, the API identifies their pullbacks with the
  existing a.e. CATE and observed-regression theorems.

### T2.12 Conditional Average Causal Effects

Links:
- [Hansen excerpt](../textbook/ch02/ch2_excerpt.txt#L2521)
- [Mean-independence bridge](../HansenEconometrics/Chapter2PotentialOutcomes.lean)

| LaTeX | Lean conclusion |
| --- | --- |
| $ACE = \int ACE(x) f(x)\,dx$ | <code>averageTreatmentEffect μ Y0 Y1 = ∫ ω, conditionalAverageTreatmentEffectOn μ Y0 Y1 X ω ∂μ</code> |
| Under the mean-independence consequence of CIA, the treatment-and-covariate potential-outcome contrast equals CATE | <code>conditionalPotentialOutcomeContrastOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ] conditionalAverageTreatmentEffectOn μ Y0 Y1 X</code> |
| Under the mean-independence consequence of CIA, CATE conditioned on treatment and covariates equals CATE conditioned on covariates | <code>conditionalAverageTreatmentEffectOn μ Y0 Y1 (fun ω => (D ω, X ω)) =ᵐ[μ] conditionalAverageTreatmentEffectOn μ Y0 Y1 X</code> |
| Observed-outcome regression on `(D, X)` splits by treatment branch into the corresponding potential-outcome conditional mean | <code>condExpOn_observedOutcome_treatment_covariates_eq_branch</code> |
| Under CIA, observed-outcome regression on `(D, X)` uses the `X`-conditioned potential-outcome mean on each treatment branch | <code>condExpOn_observedOutcome_treatment_covariates_eq_branch_of_CIA</code> |
| Given versions `m0,m1`, CATE pulls back from the pointwise surface `ACE(x)` | <code>conditionalAverageTreatmentEffectOn_eq_surface</code> |
| Given versions `m0,m1`, CATE also pulls back from the contrast `m(1,x)-m(0,x)` | <code>conditionalAverageTreatmentEffectOn_eq_observedRegressionTreatmentContrastSurface</code> |
| Given versions `m0,m1`, the observed regression on `(D,X)` pulls back from `m(d,x)` under CIA | <code>condExpOn_observedOutcome_treatment_covariates_eq_surface_of_CIA</code> |
| Under CIA, the treatment-and-covariate potential-outcome contrast equals CATE | <code>conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_cate_of_CIA</code> |
| Under CIA, CATE conditioned on treatment and covariates equals CATE conditioned on covariates | <code>conditionalAverageTreatmentEffectOn_treatment_covariates_eq_of_CIA</code> |

Notes:
- The conditional-expectation theorem is still variable-facing and a.e.-based. The pointwise
  `ACE(x)` and `m(1,x)-m(0,x)` declarations are supplied-surface bridges rather than a new
  regular-conditional-density construction.

## Lean-only Bridge Results

These theorems are not direct textbook labels, but they are the key translation lemmas between
Hansen's notation and the Lean formalization.

- [`condExp_apply`](../HansenEconometrics/ProbabilityUtils.lean):
  coordinate projection commutes with conditional expectation.
- [`condExp_apply_apply`](../HansenEconometrics/ProbabilityUtils.lean):
  entrywise conditional expectation for finite-dimensional arrays.
- [`integral_apply`](../HansenEconometrics/ProbabilityUtils.lean):
  coordinate projection commutes with integration.
- [`integral_apply_apply`](../HansenEconometrics/ProbabilityUtils.lean):
  entrywise integration for finite-dimensional arrays.
- [`condExpL2_minimal`](../HansenEconometrics/Chapter2CondExp.lean#L137):
  $\lVert Y - \mathbb{E}[Y \mid m] \rVert_2 \le \lVert Y - g \rVert_2$ in the $L^2$ projection language
  used by Mathlib.
- [`integral_condVar_eq_integral_cefError_sq`](../HansenEconometrics/Chapter2Variance.lean#L16):
  $\int \operatorname{Var}(Y \mid \mathcal{G}) \, d\mu = \int e^2 \, d\mu$.
- [`linearProjectionBeta_eq_of_normal_equations`](../HansenEconometrics/Chapter2LinearProjection.lean#L41):
  solves $Q_{XX} b = Q_{XY}$ as $b = Q_{XX}^{-1} Q_{XY}$.
- [`integral_dotProduct_eq_meanVec_dotProduct`](../HansenEconometrics/ProbabilityUtils.lean#L113):
  $\int X' b \, d\mu = (\int X \, d\mu)' b$.
- [`covVec_dotProduct_eq_covMat_mulVec`](../HansenEconometrics/ProbabilityUtils.lean#L129):
  $\operatorname{cov}(X, X' b) = \operatorname{covMat}(X) b$.
- [`covVec_affineModel`](../HansenEconometrics/ProbabilityUtils.lean#L145):
  reusable affine-model covariance decomposition.
- [`covVec_linearProjectionModel`](../HansenEconometrics/Chapter2LinearProjection.lean#L149):
  $\operatorname{cov}(X, \alpha + X' \beta + e) = \operatorname{covMat}(X)\beta +
  \operatorname{cov}(X, e)$.
- [`conditionalAverageTreatmentEffectOn_eq_conditionalPotentialOutcomeContrastOn`](../HansenEconometrics/Chapter2PotentialOutcomes.lean):
  $E[Y(1)-Y(0) \mid X] = E[Y(1) \mid X] - E[Y(0) \mid X]$.
- [`conditionalAverageTreatmentEffectSurface`](../HansenEconometrics/Chapter2PotentialOutcomes.lean),
  [`observedRegressionSurface`](../HansenEconometrics/Chapter2PotentialOutcomes.lean), and
  [`observedRegressionTreatmentContrastSurface`](../HansenEconometrics/Chapter2PotentialOutcomes.lean):
  pointwise notation bridges for `ACE(x)`, `m(d,x)`, and `m(1,x)-m(0,x)`.
- [`conditionalAverageTreatmentEffectOn_eq_surface`](../HansenEconometrics/Chapter2PotentialOutcomes.lean) and
  [`conditionalAverageTreatmentEffectOn_eq_observedRegressionTreatmentContrastSurface`](../HansenEconometrics/Chapter2PotentialOutcomes.lean):
  pull back supplied pointwise surfaces along `X` to the variable-facing CATE.
- [`averageTreatmentEffect_eq_integral_conditionalPotentialOutcomeContrastOn`](../HansenEconometrics/Chapter2PotentialOutcomes.lean):
  the a.e. Lean version of Hansen's identity `ACE = ∫ ACE(x) f(x) dx` after rewriting CATE as a
  difference of conditional potential-outcome means.
- [`conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_cate_of_meanIndependent`](../HansenEconometrics/Chapter2PotentialOutcomes.lean):
  mean-independence bridge from conditioning on `(D, X)` to the CATE.
- [`conditionalAverageTreatmentEffectOn_treatment_covariates_eq_of_meanIndependent`](../HansenEconometrics/Chapter2PotentialOutcomes.lean):
  direct CATE bridge from conditioning on `(D, X)` to conditioning on `X`.
- [`condExpOn_observedOutcome_treatment_covariates_eq_branch`](../HansenEconometrics/Chapter2PotentialOutcomes.lean):
  branchwise observed-regression decomposition for `E[Y | D, X]`.
- [`condExpOn_observedOutcome_treatment_covariates_eq_branch_of_meanIndependent`](../HansenEconometrics/Chapter2PotentialOutcomes.lean):
  mean-independence bridge from the observed regression on `(D, X)` to `X`-conditioned
  potential-outcome means.
- [`condExpOn_observedOutcome_treatment_covariates_eq_surface_of_CIA`](../HansenEconometrics/Chapter2PotentialOutcomes.lean):
  CIA-facing pullback of the pointwise observed-regression surface `m(d,x)`.
- [`PotentialOutcomeCIAOn.toTreatmentMeanIndependentOn`](../HansenEconometrics/Chapter2PotentialOutcomes.lean):
  discharges the mean-independence bridge from conditional independence of treatment and potential
  outcomes given covariates, using Mathlib's conditional-distribution characterization.
- [`conditionalPotentialOutcomeContrastOn_treatment_covariates_eq_cate_of_CIA`](../HansenEconometrics/Chapter2PotentialOutcomes.lean) and
  [`conditionalAverageTreatmentEffectOn_treatment_covariates_eq_of_CIA`](../HansenEconometrics/Chapter2PotentialOutcomes.lean):
  CIA-facing variable/a.e. CATE bridges for Hansen Theorem 2.12.
- [`condExpOn_observedOutcome_treatment_covariates_eq_branch_of_CIA`](../HansenEconometrics/Chapter2PotentialOutcomes.lean):
  CIA-facing observed-regression bridge for Hansen Theorem 2.12.

## Population partial-regression bridge

[PopulationFWL.lean](../HansenEconometrics/PopulationFWL.lean) extends the population
projection infrastructure to treatment regressors and a general control subspace
admitting an orthogonal projection. It does not change the Chapter 2 theorem APIs.
The reusable surface is also available through MetricsLib's regression facade.

| Lean-only bridge | Declaration |
|---|---|
| Residual Gram coefficient jointly minimizes the control/treatment loss | `PopulationFWL.minimizes` |
| Any minimizing fit has that same treatment coefficient | `PopulationFWL.coefficient_unique` |
| The criterion is an integral of squared errors on L² | `PopulationFWL.loss_eq_integral` |
| Population expected-square-error minimization | `PopulationFWL.minimizes_expected_sq_error` |
| Scalar FWL numerator/denominator representation | `PopulationFWL.coefficient_eq_auxiliaryResidual_ratio` |
| Auxiliary residual really partials out other treatments and controls | `PopulationFWL.auxiliaryResidual_projection` |

The causal interpretation of these coefficients belongs in applications. These
bridges impose no causal assumptions. Nonsingularity applies to the aggregate
residual Gram matrix; it is not an overlap assumption for each covariate value.
