import HansenEconometrics.Chapter7Asymptotics.Basic
import HansenEconometrics.Chapter7Asymptotics.Consistency
import HansenEconometrics.Chapter7Asymptotics.RobustCovariance
import HansenEconometrics.Chapter7Asymptotics.Normality
import HansenEconometrics.Chapter7Asymptotics.Inference

/-!
# Chapter 7 — Asymptotic Theory

This umbrella import exposes Hansen's Chapter 7 (Asymptotic Theory for Least Squares).
The implementation is split into `Basic`, `Consistency`, `RobustCovariance`,
`Normality`, and `Inference` submodules.

## Textbook theorem status

* **Theorem 7.1** — formalized for the totalized estimator `olsBetaStar` in
  `olsBetaStar_stack_tendstoInMeasure_beta` and for the ordinary-on-nonsingular
  wrapper `olsBetaOrZero` in `olsBetaOrZero_stack_tendstoInMeasure_beta`.
* **Theorem 7.2** — the score covariance matrix `Ω` is named as
  `scoreCovarianceMatrix`, with finite second-moment, positive-semidefinite,
  and scalar quadratic-form interfaces. The scalar projection CLT is formalized
  for every fixed direction, and the vector score CLT is packaged through the
  reusable Cramér-Wold bridge in
  `scoreVector_sampleCrossMoment_tendstoInDistribution_multivariateGaussian`.
* **Theorem 7.3** — asymptotic normality is formalized for scalar projections
  and for the vector totalized estimator. The vector theorem
  `olsBetaStar_vector_tendstoInDistribution_multivariateGaussian` feeds the
  proved vector score CLT into the random-inverse Slutsky bridge, and
  `olsBetaOrZero_vector_tendstoInDistribution_multivariateGaussian` gives the
  ordinary-on-nonsingular wrapper. The conditional `_of_scoreCLT` bridge lemmas
  remain available as reusable assembly pieces.
* **Theorem 7.4** — residual variance consistency is formalized for the
  totalized estimators `olsSigmaSqHatStar` and `olsS2Star` in
  `olsSigmaSqHatStar_tendstoInMeasure_errorVariance` and
  `olsS2Star_tendstoInMeasure_errorVariance`. The assumptions are packaged as
  `SampleVarianceAssumption74`, a moment-level sufficient condition extending
  `SampleMomentAssumption71` with the squared-error WLLN hypotheses.
* **Theorem 7.5** — homoskedastic plug-in covariance consistency is formalized
  for the totalized estimator `olsHomoskedasticCovarianceStar` in
  `olsHomoskedasticCovarianceStar_tendstoInMeasure`.
* **Theorem 7.6** — heteroskedastic HC0 covariance consistency is now
  formalized through the ideal true-error middle matrix and the sandwich CMT:
  `sampleScoreCovarianceIdeal_stack_tendstoInMeasure_scoreCovarianceMatrix`
  and `olsHeteroskedasticCovarianceIdealStar_tendstoInMeasure`. The feasible
  residual version is reduced to two explicit remainder controls via
  `sampleScoreCovarianceStar_linear_model`,
  `sampleScoreCovarianceStar_stack_tendstoInMeasure_scoreCovarianceMatrix_of_remainders`,
  and `olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_remainders`, and is
  proved under bounded empirical third/fourth weights in
  `olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_bounded_weights`.
  The residual middle-matrix measurability premise is discharged from component
  measurability in
  `olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_bounded_weights_and_components`.
  Remaining work: discharge the bounded-weight and component-measurability
  hypotheses from a more literal iid observation assumption.
* **Theorem 7.7** — HC1 has the same limit as HC0 in
  `olsHeteroskedasticCovarianceHC1Star_tendstoInMeasure_of_bounded_weights`,
  with residual-middle measurability discharged in
  `olsHeteroskedasticCovarianceHC1Star_tendstoInMeasure_of_bounded_weights_and_components`.
  HC2/HC3 are now defined with totalized leverage weights and have conditional
  sandwich assembly theorems factored through the generic leverage-adjusted
  middle-matrix engine
  `sampleScoreCovarianceLeverageAdjustedStar_stack_tendstoInMeasure_of_adjustment`
  and
  `olsHeteroskedasticCovarianceLeverageAdjustedStar_tendstoInMeasure_of_middle`,
  with matrix adjustment convergence reducible to scalar entries by
  `sampleScoreCovarianceLeverageAdjustmentStar_stack_tendstoInMeasure_zero_of_entries`.
  Scalar entry convergence is further reduced by
  `sampleScoreCovarianceLeverageAdjustmentEntryStar_tendstoInMeasure_zero_of_weight_norm`
  to a largest-adjustment-weight `oₚ(1)` condition times a bounded absolute
  residual-score average.
  The HC2/HC3 wrappers remain available as
  `olsHeteroskedasticCovarianceHC2Star_tendstoInMeasure_of_middle` and
  `olsHeteroskedasticCovarianceHC3Star_tendstoInMeasure_of_middle`. Remaining:
  prove the HC2/HC3 largest-adjustment-weight condition from max leverage, and
  discharge the bounded absolute residual-score averages from primitive moment
  assumptions.
* **Theorem 7.8** — the global continuous-mapping face for functions of
  parameters is formalized in `continuous_function_olsBetaStar_tendstoInMeasure`
  after proving `olsBetaStar_stack_aestronglyMeasurable`, with the
  ordinary-on-nonsingular wrapper handled by
  `continuous_function_olsBetaOrZero_tendstoInMeasure`. The textbook local
  continuity-at-`β` formulation is formalized in
  `continuousAt_function_olsBetaStar_tendstoInMeasure` and
  `continuousAt_function_olsBetaOrZero_tendstoInMeasure`.
* **Theorem 7.9** — the linear-functions projection face is formalized in
  `scoreProjection_linearMap_olsBetaStar_tendstoInDistribution_gaussian_covariance`
  and
  `scoreProjection_linearMap_olsBetaOrZero_tendstoInDistribution_gaussian_covariance`.
  Remaining: nonlinear differentiable delta method and vector packaging.
* **Theorem 7.10** — the fixed and random linear covariance
  continuous-mapping faces are formalized in
  `linearMapCovariance_tendstoInMeasure` and
  `randomLinearMapCovariance_tendstoInMeasure`, with concrete homoskedastic and
  HC0/HC1 fixed-linear-function wrappers in
  `linearMap_olsHomoskedasticCovarianceStar_tendstoInMeasure`,
  `linearMap_olsHC0CovarianceStar_tendstoInMeasure_of_bounded_weights_and_components`
  and
  `linearMap_olsHC1CovarianceStar_tendstoInMeasure_of_bounded_weights_and_components`.
* **Theorem 7.11** — the standard-error CMT is formalized in
  `linearMapCovarianceStdError_tendstoInMeasure`, with homoskedastic and HC0/HC1
  linear-function standard-error consistency and scalar t-statistic convergence
  theorems for both `olsBetaStar` and `olsBetaOrZero`. The displayed Gaussian
  ratio limit is now normalized to explicit standard-normal limits in
  `olsHomoskedasticLinearTStatisticStar_tendstoInDistribution_standardNormal`,
  `olsHC0LinearTStatisticStar_tendstoInDistribution_standardNormal`,
  `olsHC1LinearTStatisticStar_tendstoInDistribution_standardNormal`, and the
  corresponding `olsBetaOrZero` wrappers. Remaining: extend beyond fixed linear
  maps and package interval/Wald consequences.
* **Theorem 7.12** — the generic symmetric confidence-interval coverage bridge
  is formalized in
  `symmetricCI_coverage_tendsto_of_abs_tstat_of_nonpos_tendsto_zero`, building
  on absolute-value distributional limits for homoskedastic and HC0/HC1
  ordinary t-statistics and `mem_symmetric_ci_iff_abs_tstat_le`. The older
  pointwise-positivity bridge remains available as
  `symmetricCI_coverage_tendsto_of_abs_tstat`; the theorem-facing wrappers use
  convergence in probability of the standard error to show the nonpositive-SE
  bad event is negligible. The concrete homoskedastic ordinary-wrapper interval
  face from variable-facing homoskedasticity is formalized in
  `olsHomoskedasticLinearCIOrZero_coverage_tendsto_standardNormal_of_homoskedastic`,
  and the HC0 and HC1 faces in
  `olsHC0LinearCIOrZero_coverage_tendsto_standardNormal` and
  `olsHC1LinearCIOrZero_coverage_tendsto_standardNormal`.
* **Theorem 7.13** — the generic multivariate Wald continuous-mapping bridge is
  formalized in `waldQuadraticForm_tendstoInDistribution_of_vector_and_covariance`,
  the Lean-only named `χ²` law-identification wrapper is formalized in
  `waldQuadraticForm_tendstoInDistribution_chiSquared_of_limit_hasLaw`,
  the positive-definite Gaussian/Mahalanobis law bridge is formalized in
  `waldQuadraticForm_tendstoInDistribution_chiSquared_of_gaussian_mahalanobis`,
  and the public full-rank linear-Wald OLS wrappers
  `linearMap_olsBetaStar_waldChiSquared_gaussian` and
  `linearMap_olsBetaOrZero_waldChiSquared_gaussian` now consume the proved
  vector OLS CLT instead of assuming it. The conditional linear-Wald OLS bridge
  wrappers remain available as
  `linearMap_olsBetaStar_waldQuadraticForm_tendstoInDistribution_chiSquared_of_scoreCLT`
  and
  `linearMap_olsBetaOrZero_waldQuadraticForm_tendstoInDistribution_chiSquared_of_scoreCLT`,
  and scalar one-degree-of-freedom HC0/HC1 Wald faces are formalized as
  `olsHC0LinearWaldStatisticOrZero_tendstoInDistribution_chiSquared_one` and
  `olsHC1LinearWaldStatisticOrZero_tendstoInDistribution_chiSquared_one`.
  Remaining: discharge the Gaussian linear-map law/covariance identity and plug
  in concrete covariance-estimator consistency for the textbook multivariate
  theorem.
* **Theorem 7.14** — the full multivariate homoskedastic Wald theorem is
  pending, but the scalar one-degree-of-freedom face is formalized under the
  variable-facing homoskedasticity assumption
  `HomoskedasticErrorVariance` in
  `olsHomoskedasticLinearWaldStatisticOrZero_tendstoInDistribution_chiSquared_one_of_homoskedastic`.
  The Lean-only bridge
  `scoreCovarianceMatrix_eq_errorVariance_smul_popGram_of_homoskedastic`
  proves the reusable covariance identity `Ω = σ²Q`.
* **Theorem 7.16** — the probabilistic max-residual rate is pending, but the
  deterministic pointwise residual-error inequalities are formalized in
  `residualStar_sub_error_abs_le_card_mul_row_norm_mul_beta_error_norm` and
  `residual_sub_error_abs_le_card_mul_row_norm_mul_beta_error_norm`.
* **Theorem 7.17** — the probabilistic max-leverage rate is pending, but the
  finite-sample leverage trace/average identities and pointwise bounds are
  formalized in `sum_leverageStar_eq_card_of_nonsingular`,
  `average_leverageStar_eq_card_div_card_of_nonsingular`,
  `leverageStar_nonneg_of_nonsingular`, and `leverageStar_le_one_of_nonsingular`.
* **Theorem 7.15** — pending/signpost-only.

## Phase 1 — Deterministic scaffold

Finite-sample empirical moment objects and the algebraic Phase 1 identity
behind Theorem 7.1:

* `sampleGram X        = Xᵀ X / n`   — sample analogue of `Q := 𝔼[X Xᵀ]`
* `sampleCrossMoment X e = (Xᵀ e) / n` — sample analogue of `𝔼[X e]`
* `olsBeta_sub_eq_sampleGram_inv_mulVec_sampleCrossMoment`:
  `β̂ₙ − β = Q̂ₙ⁻¹ *ᵥ ĝₙ` under invertibility of `Xᵀ X`.

## Phase 2 — Stacking primitives

Bridge from a pointwise `ℕ`-indexed regressor/error sequence to a `Fin n`-row
design matrix at each sample point `ω`:

* `stackRegressors`, `stackErrors`, `stackOutcomes`
* `stack_linear_model` — `y = Xβ + e` pointwise lifts to the stacked form
* `sampleGram_stackRegressors_eq_avg` — sample Gram as `(1/n) ∑ Xᵢ Xᵢᵀ`
* `sampleCrossMoment_stackRegressors_stackErrors_eq_avg` — analogous
* Fin↔Finset.range summation bridges matching Mathlib's WLLN indexing.

## Phase 3 — Probabilistic consistency for a totalized estimator

`SampleMomentAssumption71` packages the moment-level independence,
integrability, nonsingularity, and orthogonality hypotheses used by the Lean
proof. These are sufficient for the current consistency argument, but they are
not a literal encoding of Hansen's iid sample assumption. The chain of
convergences is then assembled:

* `sampleGram_stackRegressors_tendstoInMeasure_popGram` — `Q̂ₙ →ₚ Q` via WLLN.
* `sampleCrossMoment_stackRegressors_stackErrors_tendstoInMeasure_zero` —
  `ĝₙ(e) →ₚ 0` via WLLN + orthogonality.
* `sampleGramInv_mulVec_sampleCrossMoment_e_tendstoInMeasure_zero` —
  `Q̂ₙ⁻¹ *ᵥ ĝₙ(e) →ₚ 0`, combining the previous two with the matrix-inverse
  CMT and the mulVec CMT from `AsymptoticUtils`.
* `olsBetaStar_stack_tendstoInMeasure_beta` — consistency of the totalized
  estimator `olsBetaStar`, which uses `Matrix.nonsingInv` and agrees with
  ordinary `olsBeta` on nonsingular samples.
* `olsBetaOrZero_stack_tendstoInMeasure_beta` — the same consistency result for
  a wrapper that evaluates ordinary `olsBeta` on nonsingular samples and `0`
  otherwise.

This is the current Lean version of the beginning of Chapter 7. A separate
literal dependent-type theorem for ordinary `olsBeta` would still need a way to
avoid forming the estimator on singular samples; `olsBetaOrZero` is the current
Lean interface for that high-probability nonsingularity event.

## Phase 4 — First CLT bridge

`SampleCLTAssumption72` strengthens the moment-level consistency assumptions
with full independence of the score vectors `eᵢXᵢ` and square integrability of
all scalar projections. The score covariance matrix `Ω` is exposed as
`scoreCovarianceMatrix`, with finite-entry and quadratic-form wrappers. The theorem
`scoreProjection_sum_tendstoInDistribution_gaussian` applies Mathlib's
one-dimensional central limit theorem to every fixed projection of the score.
`sqrt_smul_residual_tendstoInMeasure_zero` also records that the singular-event
OLS remainder is negligible after `√n` scaling, and
`sqrt_smul_olsBetaStar_sub_eq_sqrt_smul_residual_add_feasible_score`
decomposes `√n(β̂*ₙ - β)` into that residual plus the feasible leading score
term. `feasibleScore_eq_fixedScore_add_inverseGap` then isolates the exact
random-inverse gap left for Slutsky, and
`scoreProjection_sqrt_smul_olsBetaStar_sub_eq_residual_add_fixedScore_add_inverseGap`
records the resulting scalar-projection roadmap. Finally,
`scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_remainder`
applies Mathlib's Slutsky theorem once that scalar remainder is shown to be
`oₚ(1)`. The inverse-gap condition is discharged by combining
`scoreCoordinate_sampleCrossMoment_boundedInProbability` with the
coordinatewise product bridge, yielding
`scoreProjection_olsBetaStar_tendstoInDistribution_gaussian` as the current
main scalar-projection face of Hansen's asymptotic-normality theorem.

See also:
- [`AsymptoticUtils.lean`](./AsymptoticUtils.lean) — WLLN wrapper, CMT for
  convergence in measure, matrix-inverse and mulVec CMTs.
- [`LinearAlgebraUtils.lean`](./LinearAlgebraUtils.lean) — reusable finite-dimensional
  linear algebra identities, including `nonsingInv_smul`.
- [`Chapter3LeastSquaresAlgebra.lean`](./Chapter3LeastSquaresAlgebra.lean) —
  `olsBeta` and its total version `olsBetaStar`.
- [inventory/ch7-inventory.md](../inventory/ch7-inventory.md) — theorem inventory and crosswalk.
-/
