import Mathlib
import HansenEconometrics.Basic
import HansenEconometrics.LinearAlgebraUtils
import HansenEconometrics.Chapter3LeastSquaresAlgebra
import HansenEconometrics.Chapter4LeastSquaresRegression
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.ProbabilityUtils
import HansenEconometrics.ChiSquared

/-!
# Chapter 7 — Asymptotic Theory

This file formalizes Hansen's Chapter 7 (Asymptotic Theory for Least Squares)
in four layers:

## Textbook theorem status

* **Theorem 7.1** — formalized for the totalized estimator `olsBetaStar` in
  `olsBetaStar_stack_tendstoInMeasure_beta` and for the ordinary-on-nonsingular
  wrapper `olsBetaOrZero` in `olsBetaOrZero_stack_tendstoInMeasure_beta`.
* **Theorem 7.2** — projectionwise CLT and covariance-matrix faces landed. The
  theorem in the text has two parts, `Ω < ∞` and the vector score CLT
  `(1 / √n) ∑ Xᵢeᵢ ⇒ N(0, Ω)`. The current Lean state names `Ω` as
  `scoreCovarianceMatrix`, proves its finite second-moment / quadratic-form
  interfaces, and proves the scalar projection CLT for every fixed direction
  `a`, with the all-directions covariance signpost
  `scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian_covariance_all`.
  The literal vector-valued statement is still pending.
* **Theorem 7.3** — scalar projections of the totalized estimator
  `olsBetaStar` and the ordinary-on-nonsingular wrapper `olsBetaOrZero` are
  asymptotically normal. The proof now includes the inverse-gap/tightness
  bridge replacing `Q⁻¹` by `Q̂ₙ⁻¹`, covariance-matrix variance notation, and
  all-directions projection-family wrappers for both estimators. Generic
  matrix-vector distributional Slutsky bridges are now named in
  `matrixMulVec_tendstoInDistribution_of_vector_and_matrix` and
  `matrixInvMulVec_tendstoInDistribution_of_vector_and_matrix`, with the
  feasible leading-score vector bridge
  `feasibleScore_tendstoInDistribution_of_scoreCLT` and conditional vector OLS
  assembly `olsBetaStar_vector_tendstoInDistribution_of_scoreCLT` plus the
  ordinary-wrapper version
  `olsBetaOrZero_vector_tendstoInDistribution_of_scoreCLT`.
  The remaining textbook-facing work is vector/Cramér-Wold packaging.
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
  sandwich assembly theorems
  `olsHeteroskedasticCovarianceHC2Star_tendstoInMeasure_of_middle` and
  `olsHeteroskedasticCovarianceHC3Star_tendstoInMeasure_of_middle`. Remaining:
  prove the leverage-weighted middle matrices converge to `Ω`, typically via
  the max-leverage `oₚ(1)` theorem later in the chapter.
* **Theorem 7.8** — the global continuous-mapping face for functions of
  parameters is formalized in `continuous_function_olsBetaStar_tendstoInMeasure`
  after proving `olsBetaStar_stack_aestronglyMeasurable`, with the
  ordinary-on-nonsingular wrapper handled by
  `continuous_function_olsBetaOrZero_tendstoInMeasure`. Remaining:
  local continuity-at-`β`.
* **Theorem 7.9** — the linear-functions projection face is formalized in
  `scoreProjection_linearMap_olsBetaStar_tendstoInDistribution_gaussian_covariance`
  and
  `scoreProjection_linearMap_olsBetaOrZero_tendstoInDistribution_gaussian_covariance`.
  Remaining: nonlinear differentiable delta method and vector packaging.
* **Theorem 7.10** — the linear covariance continuous-mapping face is
  formalized in `linearMapCovariance_tendstoInMeasure`, with concrete
  homoskedastic and HC0/HC1 fixed-linear-function wrappers in
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
  is formalized in `symmetricCI_coverage_tendsto_of_abs_tstat`, building on
  absolute-value distributional limits for homoskedastic and HC0/HC1 ordinary
  t-statistics and `mem_symmetric_ci_iff_abs_tstat_le`. The standard-normal
  continuity-set side condition is discharged in `standardNormalAbs_frontier_Iic_null`
  and `symmetricCI_coverage_tendsto_of_abs_tstat_standardNormal`. The concrete
  homoskedastic ordinary-wrapper interval face is formalized in
  `olsHomoskedasticLinearCIOrZero_coverage_tendsto_standardNormal`, and the HC0
  face in `olsHC0LinearCIOrZero_coverage_tendsto_standardNormal`. Remaining:
  HC1 interval wrapper.
* **Theorem 7.13** — the generic multivariate Wald continuous-mapping bridge is
  formalized in `waldQuadraticForm_tendstoInDistribution_of_vector_and_covariance`,
  the named `χ²` law-identification wrapper is formalized in
  `waldQuadraticForm_tendstoInDistribution_chiSquared_of_limit_hasLaw`,
  and scalar one-degree-of-freedom HC0/HC1 Wald faces are formalized as
  `olsHC0LinearWaldStatisticOrZero_tendstoInDistribution_chiSquared_one` and
  `olsHC1LinearWaldStatisticOrZero_tendstoInDistribution_chiSquared_one`.
  Remaining: vector CLT/covariance packaging and final chi-square law
  identification for the textbook multivariate theorem.
* **Theorem 7.14** — the full multivariate homoskedastic Wald theorem is
  pending, but the scalar one-degree-of-freedom face is formalized under the
  moment-level homoskedastic bridge `Ω = σ²Q` in the
  `_of_scoreCovariance` homoskedastic Wald theorem.
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

open scoped Matrix Real

namespace HansenEconometrics

open Matrix

variable {n k : Type*}
variable [Fintype n] [Fintype k] [DecidableEq k]

/-- Hansen §7.2: the sample Gram matrix `Q̂ₙ := Xᵀ X / n`. -/
noncomputable def sampleGram (X : Matrix n k ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ • (Xᵀ * X)

/-- Hansen §7.2: the sample cross moment `g̑ₙ := (Xᵀ e) / n`. -/
noncomputable def sampleCrossMoment (X : Matrix n k ℝ) (e : n → ℝ) : k → ℝ :=
  (Fintype.card n : ℝ)⁻¹ • (Xᵀ *ᵥ e)

/-- Sample average of true squared errors, `n⁻¹∑ eᵢ²`. This is the first term in
Hansen's decomposition of `σ̂²`. -/
noncomputable def sampleErrorSecondMoment (e : n → ℝ) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * dotProduct e e

/-- Textbook-facing totalization of ordinary OLS: use `olsBeta` on nonsingular designs and
return `0` on singular designs. This exposes the ordinary-OLS formula on the high-probability
nonsingularity event while remaining a genuine random variable for every sample size. -/
noncomputable def olsBetaOrZero (X : Matrix n k ℝ) (y : n → ℝ) : k → ℝ :=
  by
    classical
    exact
      if h : IsUnit (Xᵀ * X).det then
        haveI : Invertible (Xᵀ * X) := Matrix.invertibleOfIsUnitDet
          (A := Xᵀ * X) h
        olsBeta X y
      else
        0

/-- `olsBetaOrZero` is exactly the previously used totalized estimator `olsBetaStar`. -/
theorem olsBetaOrZero_eq_olsBetaStar
    (X : Matrix n k ℝ) (y : n → ℝ) :
    olsBetaOrZero X y = olsBetaStar X y := by
  classical
  unfold olsBetaOrZero
  by_cases h : IsUnit (Xᵀ * X).det
  · rw [dif_pos h]
    letI : Invertible (Xᵀ * X) := Matrix.invertibleOfIsUnitDet (A := Xᵀ * X) h
    exact (olsBetaStar_eq_olsBeta X y).symm
  · rw [dif_neg h]
    unfold olsBetaStar
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.zero_mulVec]

/-- On nonsingular designs, `olsBetaOrZero` agrees with ordinary `olsBeta`. -/
theorem olsBetaOrZero_eq_olsBeta
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    olsBetaOrZero X y = olsBeta X y := by
  rw [olsBetaOrZero_eq_olsBetaStar, olsBetaStar_eq_olsBeta]

/-- Totalized OLS residuals, defined for every design matrix via `olsBetaStar`. -/
noncomputable def olsResidualStar (X : Matrix n k ℝ) (y : n → ℝ) : n → ℝ :=
  y - X *ᵥ olsBetaStar X y

/-- Hansen's `σ̂² = n⁻¹∑ êᵢ²`, using totalized OLS residuals. -/
noncomputable def olsSigmaSqHatStar (X : Matrix n k ℝ) (y : n → ℝ) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * dotProduct (olsResidualStar X y) (olsResidualStar X y)

/-- Hansen's `s² = (n-k)⁻¹∑ êᵢ²`, using totalized OLS residuals. -/
noncomputable def olsS2Star (X : Matrix n k ℝ) (y : n → ℝ) : ℝ :=
  ((Fintype.card n : ℝ) - Fintype.card k)⁻¹ *
    dotProduct (olsResidualStar X y) (olsResidualStar X y)

/-- **Theorem 7.4 residual expansion, pointwise form.**

Under the linear model, each totalized OLS residual is the structural error
minus the fitted coefficient error evaluated at that row:
`êᵢ = eᵢ - Xᵢ'(β̂* - β)`. -/
theorem olsResidualStar_linear_model_apply
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (i : n) :
    olsResidualStar X (X *ᵥ β + e) i =
      e i - X i ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β) := by
  unfold olsResidualStar
  have hrow :
      X i ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β) =
        (X *ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) i := by
    simp [Matrix.mulVec, dotProduct]
  rw [hrow, Matrix.mulVec_sub]
  simp
  ring

/-- **Theorem 7.4 residual expansion, vector form.**

This is the vector version of `êᵢ = eᵢ - Xᵢ'(β̂* - β)`, used before
summing squared residuals in the `σ̂²` consistency proof. -/
theorem olsResidualStar_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    olsResidualStar X (X *ᵥ β + e) =
      e - X *ᵥ (olsBetaStar X (X *ᵥ β + e) - β) := by
  ext i
  rw [olsResidualStar_linear_model_apply]
  simp [Matrix.mulVec, dotProduct]

/-- On nonsingular designs, totalized residuals agree with ordinary OLS residuals. -/
theorem olsResidualStar_eq_residual
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    olsResidualStar X y = residual X y := by
  unfold olsResidualStar residual fitted
  rw [olsBetaStar_eq_olsBeta]

omit [DecidableEq k] in
/-- Finite-dimensional dot products are bounded by sup norms, with the explicit
dimension factor used by the deterministic residual-uniformity layer. -/
theorem abs_dotProduct_le_card_mul_norm_mul_norm (x y : k → ℝ) :
    |x ⬝ᵥ y| ≤ (Fintype.card k : ℝ) * ‖x‖ * ‖y‖ := by
  calc
    |x ⬝ᵥ y|
        = |∑ j : k, x j * y j| := by simp [dotProduct]
    _ ≤ ∑ j : k, |x j * y j| := by
          simpa using
            (Finset.abs_sum_le_sum_abs (fun j : k => x j * y j) Finset.univ)
    _ ≤ ∑ _j : k, ‖x‖ * ‖y‖ := by
          refine Finset.sum_le_sum ?_
          intro j _
          rw [abs_mul]
          have hxj : |x j| ≤ ‖x‖ := by
            simpa [Real.norm_eq_abs] using norm_le_pi_norm x j
          have hyj : |y j| ≤ ‖y‖ := by
            simpa [Real.norm_eq_abs] using norm_le_pi_norm y j
          exact mul_le_mul hxj hyj (abs_nonneg _) (norm_nonneg _)
    _ = (Fintype.card k : ℝ) * ‖x‖ * ‖y‖ := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- **Hansen Theorem 7.16, deterministic pointwise residual bound.**

For the totalized estimator, the finite-sample residual error at row `i` is
bounded by the row norm times the coefficient error, with the explicit
finite-dimensional sup-norm factor. This is the pointwise algebra behind the
uniform residual consistency rate. -/
theorem residualStar_sub_error_abs_le_card_mul_row_norm_mul_beta_error_norm
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (i : n) :
    |olsResidualStar X (X *ᵥ β + e) i - e i| ≤
      (Fintype.card k : ℝ) * ‖X i‖ *
        ‖olsBetaStar X (X *ᵥ β + e) - β‖ := by
  let d : k → ℝ := olsBetaStar X (X *ᵥ β + e) - β
  have hres :
      olsResidualStar X (X *ᵥ β + e) i - e i = -(X i ⬝ᵥ d) := by
    rw [olsResidualStar_linear_model_apply]
    dsimp [d]
    ring
  rw [hres, abs_neg]
  exact abs_dotProduct_le_card_mul_norm_mul_norm (X i) d

/-- **Hansen Theorem 7.16, ordinary OLS pointwise residual bound.**

On nonsingular finite samples, the same pointwise residual-error inequality
holds for ordinary OLS residuals. -/
theorem residual_sub_error_abs_le_card_mul_row_norm_mul_beta_error_norm
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (i : n)
    [Invertible (Xᵀ * X)] :
    |residual X (X *ᵥ β + e) i - e i| ≤
      (Fintype.card k : ℝ) * ‖X i‖ *
        ‖olsBeta X (X *ᵥ β + e) - β‖ := by
  simpa [olsResidualStar_eq_residual, olsBetaStar_eq_olsBeta] using
    residualStar_sub_error_abs_le_card_mul_row_norm_mul_beta_error_norm
      (X := X) (β := β) (e := e) i

/-- **Theorem 7.4 residual expansion, squared pointwise form.**

This is Hansen equation (7.17) for the totalized estimator:
`êᵢ² = eᵢ² - 2 eᵢ Xᵢ'(β̂* - β) + (Xᵢ'(β̂* - β))²`. -/
theorem olsResidualStar_sq_linear_model_apply
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (i : n) :
    olsResidualStar X (X *ᵥ β + e) i ^ 2 =
      e i ^ 2 -
        2 * e i * (X i ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) +
          (X i ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) ^ 2 := by
  rw [olsResidualStar_linear_model_apply]
  ring

/-- **Theorem 7.4 residual sum-of-squares expansion, unscaled form.**

Writing `d = β̂* - β`, the totalized residual sum of squares is
`e'e - 2(X'e)'d + d'(X'X)d`. This is the matrix form behind Hansen's averaged
display (7.18). -/
theorem olsResidualStar_sumSquares_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    dotProduct (olsResidualStar X (X *ᵥ β + e))
        (olsResidualStar X (X *ᵥ β + e)) =
      dotProduct e e -
        2 * ((Xᵀ *ᵥ e) ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) +
          (olsBetaStar X (X *ᵥ β + e) - β) ⬝ᵥ
            ((Xᵀ * X) *ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) := by
  let d : k → ℝ := olsBetaStar X (X *ᵥ β + e) - β
  have hcross : e ⬝ᵥ (X *ᵥ d) = (Xᵀ *ᵥ e) ⬝ᵥ d := by
    rw [Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose]
  have hquad : (X *ᵥ d) ⬝ᵥ (X *ᵥ d) = d ⬝ᵥ ((Xᵀ * X) *ᵥ d) := by
    rw [Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose, Matrix.mulVec_mulVec,
      dotProduct_comm]
  rw [olsResidualStar_linear_model]
  change (e - X *ᵥ d) ⬝ᵥ (e - X *ᵥ d) =
    e ⬝ᵥ e - 2 * ((Xᵀ *ᵥ e) ⬝ᵥ d) + d ⬝ᵥ ((Xᵀ * X) *ᵥ d)
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hcross,
    dotProduct_comm (X *ᵥ d) e, hcross, hquad]
  ring

/-- **Theorem 7.4 `σ̂²` decomposition for the totalized estimator.**

This is Hansen display (7.18) in sample-moment notation:
`σ̂² = n⁻¹e'e - 2 ĝₙ(e)'(β̂* - β) + (β̂* - β)'Q̂ₙ(β̂* - β)`. -/
theorem olsSigmaSqHatStar_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    olsSigmaSqHatStar X (X *ᵥ β + e) =
      (Fintype.card n : ℝ)⁻¹ * dotProduct e e -
        2 * (sampleCrossMoment X e ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) +
          (olsBetaStar X (X *ᵥ β + e) - β) ⬝ᵥ
            (sampleGram X *ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) := by
  let d : k → ℝ := olsBetaStar X (X *ᵥ β + e) - β
  unfold olsSigmaSqHatStar
  rw [olsResidualStar_sumSquares_linear_model]
  change (Fintype.card n : ℝ)⁻¹ *
      (dotProduct e e - 2 * ((Xᵀ *ᵥ e) ⬝ᵥ d) + d ⬝ᵥ ((Xᵀ * X) *ᵥ d)) =
    (Fintype.card n : ℝ)⁻¹ * dotProduct e e -
      2 * (sampleCrossMoment X e ⬝ᵥ d) + d ⬝ᵥ (sampleGram X *ᵥ d)
  simp [sampleCrossMoment, sampleGram, Matrix.smul_mulVec, mul_add, mul_sub, smul_eq_mul]
  ring

/-- **Theorem 7.4 degrees-of-freedom bridge.**

For nonempty samples, Hansen's `s²` estimator is the degrees-of-freedom rescaling
`(n/(n-k)) σ̂²` of the average squared residual estimator. -/
theorem olsS2Star_eq_card_div_df_mul_olsSigmaSqHatStar
    (X : Matrix n k ℝ) (y : n → ℝ) [Nonempty n] :
    olsS2Star X y =
      ((Fintype.card n : ℝ) / ((Fintype.card n : ℝ) - Fintype.card k)) *
        olsSigmaSqHatStar X y := by
  have hn : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold olsS2Star olsSigmaSqHatStar
  rw [div_eq_mul_inv]
  let a : ℝ := Fintype.card n
  let b : ℝ := (Fintype.card n : ℝ) - Fintype.card k
  let R : ℝ := dotProduct (olsResidualStar X y) (olsResidualStar X y)
  have ha : a ≠ 0 := by simp [a, hn]
  change b⁻¹ * R = (a * b⁻¹) * (a⁻¹ * R)
  calc
    b⁻¹ * R = (a * a⁻¹) * (b⁻¹ * R) := by rw [mul_inv_cancel₀ ha, one_mul]
    _ = (a * b⁻¹) * (a⁻¹ * R) := by ring

omit [Fintype k] [DecidableEq k] in
/-- Scaling `Q̂ₙ` by the sample size recovers the unnormalized Gram `Xᵀ X`. -/
theorem smul_card_sampleGram (X : Matrix n k ℝ) [Nonempty n] :
    (Fintype.card n : ℝ) • sampleGram X = Xᵀ * X := by
  have hne : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold sampleGram
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul]

omit [Fintype k] [DecidableEq k] in
/-- Scaling `g̑ₙ` by the sample size recovers `Xᵀ e`. -/
theorem smul_card_sampleCrossMoment (X : Matrix n k ℝ) (e : n → ℝ) [Nonempty n] :
    (Fintype.card n : ℝ) • sampleCrossMoment X e = Xᵀ *ᵥ e := by
  have hne : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold sampleCrossMoment
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul]

/-- If `Xᵀ X` is invertible and the sample is nonempty, `Q̂ₙ` is invertible, with
inverse `n · (Xᵀ X)⁻¹`. -/
noncomputable instance sampleGram.invertible
    (X : Matrix n k ℝ) [Nonempty n] [Invertible (Xᵀ * X)] :
    Invertible (sampleGram X) := by
  have hne : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨(Fintype.card n : ℝ) • ⅟ (Xᵀ * X), ?_, ?_⟩
  · unfold sampleGram
    rw [Matrix.smul_mul, Matrix.mul_smul, invOf_mul_self,
        smul_smul, mul_inv_cancel₀ hne, one_smul]
  · unfold sampleGram
    rw [Matrix.smul_mul, Matrix.mul_smul, mul_invOf_self,
        smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- Explicit formula for the inverse of the sample Gram matrix. -/
theorem invOf_sampleGram
    (X : Matrix n k ℝ) [Nonempty n] [Invertible (Xᵀ * X)] :
    ⅟ (sampleGram X) = (Fintype.card n : ℝ) • ⅟ (Xᵀ * X) := rfl

/-- Hansen §7.2 deterministic identity:
in the linear model `Y = X β + e`, the OLS error decomposes as
`β̂ₙ - β = Q̂ₙ⁻¹ *ᵥ g̑ₙ`. This is the algebraic engine behind
Theorem 7.1 (Consistency of Least Squares). -/
theorem olsBeta_sub_eq_sampleGram_inv_mulVec_sampleCrossMoment
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ)
    [Nonempty n] [Invertible (Xᵀ * X)] :
    olsBeta X (X *ᵥ β + e) - β = ⅟ (sampleGram X) *ᵥ sampleCrossMoment X e := by
  have hne : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcore : olsBeta X (X *ᵥ β + e) - β = (⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ e) := by
    rw [olsBeta_linear_decomposition]; abel
  rw [hcore, invOf_sampleGram]
  unfold sampleCrossMoment
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul,
      smul_smul, mul_inv_cancel₀ hne, one_smul]

section Stacking

variable {Ω : Type*} {k : Type*} [Fintype k] [DecidableEq k]

/-- Stack the first `n` observations of an `ℕ`-indexed regressor sequence into an
`Fin n`-row design matrix at a fixed sample point `ω`. -/
def stackRegressors (X : ℕ → Ω → (k → ℝ)) (n : ℕ) (ω : Ω) : Matrix (Fin n) k ℝ :=
  Matrix.of fun i j => X i.val ω j

/-- Stack the first `n` scalar errors into a `Fin n`-indexed vector. -/
def stackErrors (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Fin n → ℝ :=
  fun i => e i.val ω

/-- Stack the first `n` outcomes into a `Fin n`-indexed vector. -/
def stackOutcomes (y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Fin n → ℝ :=
  fun i => y i.val ω

omit [DecidableEq k] in
/-- Pointwise linear model implies stacked linear model: if `yᵢ = Xᵢ·β + eᵢ`
for each `i`, then
`stackOutcomes y n ω = stackRegressors X n ω *ᵥ β + stackErrors e n ω`. -/
theorem stack_linear_model
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (y : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) :
    stackOutcomes y n ω = stackRegressors X n ω *ᵥ β + stackErrors e n ω := by
  funext i
  simp [stackOutcomes, stackRegressors, stackErrors, Matrix.mulVec, Matrix.of_apply,
        dotProduct, hmodel i.val ω]

omit [Fintype k] [DecidableEq k] in
/-- The unnormalized Gram matrix of the stacked design is the sum of rank-1 outer
products of each row. -/
theorem stackRegressors_transpose_mul_self_eq_sum
    (X : ℕ → Ω → (k → ℝ)) (n : ℕ) (ω : Ω) :
    (stackRegressors X n ω)ᵀ * stackRegressors X n ω =
      ∑ i : Fin n, Matrix.vecMulVec (X i.val ω) (X i.val ω) := by
  ext a b
  simp [stackRegressors, Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]

omit [Fintype k] [DecidableEq k] in
/-- The sample Gram matrix of the stacked design equals the sample mean of rank-1
outer products `Xᵢ Xᵢᵀ`. -/
theorem sampleGram_stackRegressors_eq_avg
    (X : ℕ → Ω → (k → ℝ)) (n : ℕ) (ω : Ω) :
    sampleGram (stackRegressors X n ω) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, Matrix.vecMulVec (X i.val ω) (X i.val ω) := by
  unfold sampleGram
  rw [stackRegressors_transpose_mul_self_eq_sum]
  simp [Fintype.card_fin]

omit [Fintype k] [DecidableEq k] in
/-- The unnormalized cross moment of the stacked design with stacked errors
equals the sum of error-weighted regressor vectors. -/
theorem stackRegressors_transpose_mulVec_stackErrors_eq_sum
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (stackRegressors X n ω)ᵀ *ᵥ stackErrors e n ω =
      ∑ i : Fin n, e i.val ω • X i.val ω := by
  funext a
  simp [stackRegressors, stackErrors, Matrix.mulVec, dotProduct, mul_comm]

omit [Fintype k] [DecidableEq k] in
/-- The sample cross moment of the stacked design with stacked errors equals the
sample mean of error-weighted regressors. -/
theorem sampleCrossMoment_stackRegressors_stackErrors_eq_avg
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, e i.val ω • X i.val ω := by
  unfold sampleCrossMoment
  rw [stackRegressors_transpose_mulVec_stackErrors_eq_sum]
  simp [Fintype.card_fin]

omit [Fintype k] [DecidableEq k] in
/-- Bridge `Fin n` summation to `Finset.range n` summation for outer products of
regressors — matches the indexing of Mathlib's WLLN. -/
theorem sum_fin_eq_sum_range_vecMulVec
    (X : ℕ → Ω → (k → ℝ)) (n : ℕ) (ω : Ω) :
    (∑ i : Fin n, Matrix.vecMulVec (X i.val ω) (X i.val ω)) =
      ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω) :=
  Fin.sum_univ_eq_sum_range (fun i => Matrix.vecMulVec (X i ω) (X i ω)) n

omit [Fintype k] [DecidableEq k] in
/-- Bridge `Fin n` summation to `Finset.range n` summation for error-weighted
regressors — matches the indexing of Mathlib's WLLN. -/
theorem sum_fin_eq_sum_range_smul
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (∑ i : Fin n, e i.val ω • X i.val ω) =
      ∑ i ∈ Finset.range n, e i ω • X i ω :=
  Fin.sum_univ_eq_sum_range (fun i => e i ω • X i ω) n

omit [Fintype k] [DecidableEq k] in
/-- The Hansen CLT scaling `√n · ĝₙ(e)` equals the normalized score sum
`(1 / √n) ∑_{i<n} eᵢXᵢ`, including the harmless `n = 0` totalized case. -/
theorem sqrt_smul_sampleCrossMoment_stackRegressors_stackErrors_eq_inv_sqrt_sum
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Real.sqrt (n : ℝ) • sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) =
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i ∈ Finset.range n, e i ω • X i ω := by
  rw [sampleCrossMoment_stackRegressors_stackErrors_eq_avg, sum_fin_eq_sum_range_smul]
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hnpos
    have hscale : Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ = (Real.sqrt (n : ℝ))⁻¹ := by
      have hsqr_mul : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
        exact Real.mul_self_sqrt hnpos.le
      calc
        Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ =
            Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ))⁻¹ := by
          rw [hsqr_mul]
        _ = (Real.sqrt (n : ℝ))⁻¹ := by
          field_simp [hsqrt_ne]
    rw [smul_smul, hscale]

omit [Fintype k] [DecidableEq k] in
/-- The stacked true squared-error average is the range-indexed average used by
Mathlib's WLLN. -/
theorem sampleErrorSecondMoment_stackErrors_eq_avg
    (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    sampleErrorSecondMoment (stackErrors e n ω) =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, e i ω ^ 2 := by
  unfold sampleErrorSecondMoment stackErrors
  rw [Fintype.card_fin]
  congr 1
  simp only [dotProduct, pow_two]
  exact Fin.sum_univ_eq_sum_range (fun i => e i ω * e i ω) n

omit [DecidableEq k] in
/-- **Linear-model decomposition of the sample cross moment.**
Under the linear model `yᵢ = Xᵢ·β + eᵢ`, the stacked cross moment splits as
`ĝₙ(y) = Q̂ₙ β + ĝₙ(e)`. This is the algebraic engine that, combined with F2,
decomposes `olsBetaStar − β` into the error-driven term `Q̂ₙ⁻¹ *ᵥ ĝₙ(e)` plus a
residual supported on the singular event `{Q̂ₙ not invertible}`. -/
theorem sampleCrossMoment_stackOutcomes_linear_model
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (y : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) :
    sampleCrossMoment (stackRegressors X n ω) (stackOutcomes y n ω) =
      sampleGram (stackRegressors X n ω) *ᵥ β +
        sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) := by
  rw [stack_linear_model X e y β hmodel]
  unfold sampleCrossMoment sampleGram
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, smul_add, ← Matrix.smul_mulVec]

/-- **Theorem 7.4 `σ̂²` decomposition for stacked samples.**

Under the linear model, the residual average `σ̂²` splits into the true
squared-error average plus the two Hansen remainder terms. -/
theorem olsSigmaSqHatStar_stack_linear_model
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (y : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) :
    olsSigmaSqHatStar (stackRegressors X n ω) (stackOutcomes y n ω) =
      sampleErrorSecondMoment (stackErrors e n ω) -
        2 * (sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) ⬝ᵥ
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) +
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) ⬝ᵥ
            (sampleGram (stackRegressors X n ω) *ᵥ
              (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) := by
  rw [stack_linear_model X e y β hmodel, olsSigmaSqHatStar_linear_model]
  rfl

/-- **Unconditional sample-moment form of `olsBetaStar`.**
For every sample size `n` and every `ω`,
`olsBetaStar X y = Q̂ₙ⁻¹ *ᵥ ĝₙ(y)`, where `Q̂ₙ = n⁻¹ Xᵀ X` and `ĝₙ(y) = n⁻¹ Xᵀ y`.
Unlike Phase 1's `olsBeta_sub_eq_sampleGram_inv_mulVec_sampleCrossMoment`, this
version uses `Matrix.nonsingInv` throughout and so holds on *all* of `Ω`,
including the null event `{Q̂ₙ singular}` where both sides collapse to `0`. -/
theorem olsBetaStar_stack_eq_sampleGramInv_mulVec_sampleCrossMoment
    (X : ℕ → Ω → (k → ℝ)) (y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) =
      (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
        sampleCrossMoment (stackRegressors X n ω) (stackOutcomes y n ω) := by
  unfold olsBetaStar sampleGram sampleCrossMoment
  rw [nonsingInv_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
      Fintype.card_fin]
  by_cases hn : n = 0
  · subst hn
    have h0 : ((stackRegressors X 0 ω)ᵀ *ᵥ (stackOutcomes y 0 ω)) = 0 := by
      funext j
      simp [Matrix.mulVec, dotProduct]
    rw [h0, Matrix.mulVec_zero, smul_zero]
  · have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [inv_inv, mul_inv_cancel₀ hne, one_smul]

/-- **Unconditional residual identity.** Under `yᵢ = Xᵢ·β + eᵢ`,
`β̂ₙ − β − Q̂ₙ⁻¹ *ᵥ ĝₙ(e) = (Q̂ₙ⁻¹ * Q̂ₙ − 1) *ᵥ β`. On the event
`{Q̂ₙ invertible}` the RHS is `0` (since `Q̂ₙ⁻¹ * Q̂ₙ = 1`); off it, `Q̂ₙ⁻¹ = 0`
by `Matrix.nonsing_inv_apply_not_isUnit`, so the RHS is `−β`. The identity
itself holds on all of `Ω`. -/
theorem olsBetaStar_sub_identity
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (y : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) :
    olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β
      - (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) =
      ((sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω) - 1) *ᵥ β := by
  rw [olsBetaStar_stack_eq_sampleGramInv_mulVec_sampleCrossMoment,
      sampleCrossMoment_stackOutcomes_linear_model X e y β hmodel,
      Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

end Stacking

section Assumption71

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.Elementwise Function Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {k : Type*} [Fintype k] [DecidableEq k]

omit [DecidableEq k] in
/-- Borel σ-algebra on `Matrix k k ℝ` inherited from the elementwise-L∞ norm.
Section-scoped so the choice of norm stays local. -/
@[reducible]
private noncomputable def matrixBorelMeasurableSpace :
    MeasurableSpace (Matrix k k ℝ) := borel _

attribute [local instance] matrixBorelMeasurableSpace

omit [Fintype k] [DecidableEq k] in
private lemma matrixBorelSpace : BorelSpace (Matrix k k ℝ) := ⟨rfl⟩

attribute [local instance] matrixBorelSpace

/-- Moment-level sufficient assumptions for the current Chapter 7.1 consistency proof.

This deliberately packages only the transformed sequences needed by the WLLN steps:
outer products `Xᵢ Xᵢᵀ` and cross products `eᵢ Xᵢ`. It is implied by suitable iid
sample assumptions, but it is not itself a literal encoding of Hansen
Assumption 7.1. -/
structure SampleMomentAssumption71 (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) where
  /-- Pairwise independence of the outer-product sequence `X i (X i)ᵀ`. -/
  indep_outer :
    Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => Matrix.vecMulVec (X i ω) (X i ω)))
  /-- Pairwise independence of the cross-product sequence `e i • X i`. -/
  indep_cross :
    Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • X i ω))
  /-- Identical distribution of the outer products. -/
  ident_outer : ∀ i,
    IdentDistrib (fun ω => Matrix.vecMulVec (X i ω) (X i ω))
                 (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ μ
  /-- Identical distribution of the cross products. -/
  ident_cross : ∀ i,
    IdentDistrib (fun ω => e i ω • X i ω) (fun ω => e 0 ω • X 0 ω) μ μ
  /-- Second moments on `X` (so `X Xᵀ` is integrable). -/
  int_outer : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ
  /-- First-moment integrability of `e X`. -/
  int_cross : Integrable (fun ω => e 0 ω • X 0 ω) μ
  /-- Population Gram matrix `Q := 𝔼[X Xᵀ]` is nonsingular. -/
  Q_nonsing : IsUnit (μ[fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)]).det
  /-- Population orthogonality `𝔼[e X] = 0`. -/
  orthogonality : μ[fun ω => e 0 ω • X 0 ω] = 0

/-- Additional squared-error WLLN assumptions used for Hansen Theorem 7.4.

The textbook Assumption 7.1 implies these for iid observations with finite
second moments; this structure records exactly what the current Lean proof
needs for the residual-variance consistency layer. -/
structure SampleVarianceAssumption74 (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    extends SampleMomentAssumption71 μ X e where
  /-- Pairwise independence of the true squared-error sequence. -/
  indep_error_sq : Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω ^ 2))
  /-- Identical distribution of the true squared errors. -/
  ident_error_sq : ∀ i,
    IdentDistrib (fun ω => e i ω ^ 2) (fun ω => e 0 ω ^ 2) μ μ
  /-- Integrability of the true squared error. -/
  int_error_sq : Integrable (fun ω => e 0 ω ^ 2) μ

/-- The population Gram matrix `Q := 𝔼[X Xᵀ]`. -/
noncomputable def popGram (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) : Matrix k k ℝ :=
  μ[fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)]

omit [DecidableEq k] in
/-- The population Gram matrix is symmetric whenever the outer product is integrable. -/
theorem popGram_isSymm
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ))
    (hX : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ) :
    (popGram μ X).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  calc
    (popGram μ X) j i
        = ∫ ω, (Matrix.vecMulVec (X 0 ω) (X 0 ω)) j i ∂μ := by
          rw [popGram]
          exact integral_apply_apply
            (μ := μ) (f := fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) hX j i
    _ = ∫ ω, (Matrix.vecMulVec (X 0 ω) (X 0 ω)) i j ∂μ := by
          congr with ω
          simp [Matrix.vecMulVec_apply, mul_comm]
    _ = (popGram μ X) i j := by
          rw [popGram]
          exact (integral_apply_apply
            (μ := μ) (f := fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) hX i j).symm

/-- The totalized inverse of the population Gram matrix is symmetric. -/
theorem popGram_inv_isSymm
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ))
    (hX : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ) :
    ((popGram μ X)⁻¹).IsSymm :=
  (popGram_isSymm μ X hX).inv

/-- The textbook error variance `σ² := E[e²]` used in Theorem 7.4. -/
noncomputable def errorVariance (μ : Measure Ω) (e : ℕ → Ω → ℝ) : ℝ :=
  μ[fun ω => e 0 ω ^ 2]

/-- **WLLN for the sample Gram.** Under the moment-level assumptions, the sample
Gram matrix of the stacked design converges in probability to the population Gram `Q`. -/
theorem sampleGram_stackRegressors_tendstoInMeasure_popGram
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) :
    TendstoInMeasure μ
      (fun n ω => sampleGram (stackRegressors X n ω))
      atTop
      (fun _ => popGram μ X) := by
  have hfun_eq : (fun n ω => sampleGram (stackRegressors X n ω)) =
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
        ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
    funext n ω
    rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
  rw [hfun_eq]
  exact tendstoInMeasure_wlln
    (fun i ω => Matrix.vecMulVec (X i ω) (X i ω))
    h.int_outer h.indep_outer h.ident_outer

/-- Measurability of the stacked sample Gram under the Chapter 7.1 moment layer. -/
theorem sampleGram_stackRegressors_aestronglyMeasurable
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (n : ℕ) :
    AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
  have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
      (fun ω => (n : ℝ)⁻¹ •
        ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
    funext ω
    rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
  rw [hform]
  refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
  refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
  exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable

/-- **CMT for the inverse sample Gram.** Under the moment-level assumptions,
`Q̂ₙ⁻¹ →ₚ Q⁻¹`. -/
theorem sampleGramInv_stackRegressors_tendstoInMeasure_popGramInv
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) :
    TendstoInMeasure μ
      (fun n ω => (sampleGram (stackRegressors X n ω))⁻¹)
      atTop (fun _ => (popGram μ X)⁻¹) := by
  have hGram := sampleGram_stackRegressors_tendstoInMeasure_popGram h
  have hGram_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    intro n
    exact sampleGram_stackRegressors_aestronglyMeasurable h n
  exact tendstoInMeasure_matrix_inv hGram_meas hGram (fun _ => h.Q_nonsing)

/-- **WLLN for the sample cross moment.** Under the moment-level assumptions, the sample
cross moment `ĝₙ = n⁻¹ ∑ eᵢ Xᵢ` of the stacked design converges in probability to
`0`, since the population cross moment `𝔼[e X] = 0` by the orthogonality axiom. -/
theorem sampleCrossMoment_stackRegressors_stackErrors_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) :
    TendstoInMeasure μ
      (fun n ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop
      (fun _ => 0) := by
  have hfun_eq : (fun n ω => sampleCrossMoment (stackRegressors X n ω)
        (stackErrors e n ω)) =
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
        ∑ i ∈ Finset.range n, e i ω • X i ω) := by
    funext n ω
    rw [sampleCrossMoment_stackRegressors_stackErrors_eq_avg,
        sum_fin_eq_sum_range_smul]
  rw [hfun_eq, show (fun _ : Ω => (0 : k → ℝ)) =
      (fun _ : Ω => μ[fun ω => e 0 ω • X 0 ω]) by rw [h.orthogonality]]
  exact tendstoInMeasure_wlln
    (fun i ω => e i ω • X i ω)
    h.int_cross h.indep_cross h.ident_cross

/-- **Theorem 7.4 squared-error WLLN.**

Under the 7.4 squared-error assumptions, the sample average of the true squared
errors converges in probability to `σ² = E[e₀²]`. -/
theorem sampleErrorSecondMoment_stackErrors_tendstoInMeasure_errorVariance
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) :
    TendstoInMeasure μ
      (fun n ω => sampleErrorSecondMoment (stackErrors e n ω))
      atTop
      (fun _ => errorVariance μ e) := by
  have hfun_eq : (fun n ω => sampleErrorSecondMoment (stackErrors e n ω)) =
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, e i ω ^ 2) := by
    funext n ω
    rw [sampleErrorSecondMoment_stackErrors_eq_avg]
  rw [hfun_eq]
  simpa [errorVariance, smul_eq_mul] using
    tendstoInMeasure_wlln
      (fun i ω => e i ω ^ 2)
      h.int_error_sq h.indep_error_sq h.ident_error_sq

/-- Centered form of the Theorem 7.4 squared-error WLLN. -/
theorem sampleErrorSecondMoment_stackErrors_sub_errorVariance_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) :
    TendstoInMeasure μ
      (fun n ω => sampleErrorSecondMoment (stackErrors e n ω) - errorVariance μ e)
      atTop
      (fun _ => 0) := by
  have hraw :=
    sampleErrorSecondMoment_stackErrors_tendstoInMeasure_errorVariance
      (μ := μ) (X := X) (e := e) h
  rw [tendstoInMeasure_iff_dist] at hraw ⊢
  intro ε hε
  simpa [Real.dist_eq, sub_eq_add_neg, abs_sub_comm] using hraw ε hε

/-- **Theorem 7.4 conditional `σ̂²` consistency assembly.**

Once Hansen's two residual-decomposition remainders are known to be `oₚ(1)`,
the centered residual average `σ̂² - σ²` is `oₚ(1)`. The remaining work for the
unconditional Theorem 7.4 statement is to discharge `hcross` and `hquad` from
Theorem 7.1 consistency and the sample-moment WLLNs. -/
theorem olsSigmaSqHatStar_sub_errorVariance_tendstoInMeasure_zero_of_remainders
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hcross : TendstoInMeasure μ
      (fun n ω =>
        -2 * (sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) ⬝ᵥ
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
      atTop (fun _ => 0))
    (hquad : TendstoInMeasure μ
      (fun n ω =>
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) ⬝ᵥ
          (sampleGram (stackRegressors X n ω) *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsSigmaSqHatStar (stackRegressors X n ω) (stackOutcomes y n ω) -
          errorVariance μ e)
      atTop
      (fun _ => 0) := by
  have herr :=
    sampleErrorSecondMoment_stackErrors_sub_errorVariance_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) h
  have hsum :=
    TendstoInMeasure.add_zero_real
      (TendstoInMeasure.add_zero_real herr hcross) hquad
  refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  change sampleErrorSecondMoment (stackErrors e n ω) - errorVariance μ e +
        -2 * (sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) ⬝ᵥ
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) +
        ((olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) ⬝ᵥ
          (sampleGram (stackRegressors X n ω) *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) =
      olsSigmaSqHatStar (stackRegressors X n ω) (stackOutcomes y n ω) -
        errorVariance μ e
  rw [olsSigmaSqHatStar_stack_linear_model X e y β hmodel]
  ring

/-- **Theorem 7.4 conditional `σ̂²` consistency.**

This is the uncentered presentation of
`olsSigmaSqHatStar_sub_errorVariance_tendstoInMeasure_zero_of_remainders`:
`σ̂² →ₚ σ²`, conditional on the two residual-decomposition remainders being
`oₚ(1)`. -/
theorem olsSigmaSqHatStar_tendstoInMeasure_errorVariance_of_remainders
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hcross : TendstoInMeasure μ
      (fun n ω =>
        -2 * (sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) ⬝ᵥ
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
      atTop (fun _ => 0))
    (hquad : TendstoInMeasure μ
      (fun n ω =>
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) ⬝ᵥ
          (sampleGram (stackRegressors X n ω) *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => olsSigmaSqHatStar (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop
      (fun _ => errorVariance μ e) := by
  have hsub :=
    olsSigmaSqHatStar_sub_errorVariance_tendstoInMeasure_zero_of_remainders
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel hcross hquad
  rw [tendstoInMeasure_iff_dist] at hsub ⊢
  intro ε hε
  simpa [Real.dist_eq, sub_eq_add_neg, abs_sub_comm] using hsub ε hε

/-- **Core stochastic transform — convergence of the OLS-error term.**
Under the moment-level assumptions, the sequence `Q̂ₙ⁻¹ *ᵥ ĝₙ(e)` — which is the
deterministic RHS of the Phase 1 OLS-error identity `β̂ₙ − β = Q̂ₙ⁻¹ *ᵥ ĝₙ(e)`
(valid on the event `{Q̂ₙ invertible}`) — converges in probability to `0`.

Proof chain:
* Task 9: `Q̂ₙ →ₚ Q`.
* Task 7: composed with Task 9 and `h.Q_nonsing`, this gives `Q̂ₙ⁻¹ →ₚ Q⁻¹`.
* Task 10: `ĝₙ(e) →ₚ 0`.
* `tendstoInMeasure_mulVec` joins these to `Q̂ₙ⁻¹ *ᵥ ĝₙ(e) →ₚ Q⁻¹ *ᵥ 0 = 0`.

This theorem is the core stochastic term in the consistency proof below. -/
theorem sampleGramInv_mulVec_sampleCrossMoment_e_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) :
    TendstoInMeasure μ
      (fun n ω =>
        (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop
      (fun _ => (0 : k → ℝ)) := by
  have hGram := sampleGram_stackRegressors_tendstoInMeasure_popGram h
  have hCross := sampleCrossMoment_stackRegressors_stackErrors_tendstoInMeasure_zero h
  -- Measurability of sampleGram via (1/n) • ∑ Xᵢ Xᵢᵀ
  have hGram_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    intro n
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hCross_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) μ := by
    intro n
    have hform : (fun ω => sampleCrossMoment (stackRegressors X n ω)
          (stackErrors e n ω)) =
        (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, e i ω • X i ω) := by
      funext ω
      rw [sampleCrossMoment_stackRegressors_stackErrors_eq_avg,
          sum_fin_eq_sum_range_smul]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_cross i).integrable_iff.mpr h.int_cross).aestronglyMeasurable
  have hInv : TendstoInMeasure μ
      (fun n ω => (sampleGram (stackRegressors X n ω))⁻¹)
      atTop (fun _ => (popGram μ X)⁻¹) :=
    tendstoInMeasure_matrix_inv hGram_meas hGram (fun _ => h.Q_nonsing)
  have hInv_meas : ∀ n, AEStronglyMeasurable
      (fun ω => (sampleGram (stackRegressors X n ω))⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (hGram_meas n)
  have hmulVec := tendstoInMeasure_mulVec hInv_meas hCross_meas hInv hCross
  simpa using hmulVec

/-- **Measure of the singular event vanishes asymptotically.**
Under the moment-level assumptions, `μ {ω | Q̂ₙ(ω) is singular} → 0`.

Proof chain:
* Task 9: `Q̂ₙ →ₚ Q`.
* CMT on `Matrix.det` (continuous): `det Q̂ₙ →ₚ det Q`.
* `det Q ≠ 0` by `h.Q_nonsing`, so `ε := |det Q|/2 > 0`.
* On the singular event, `det Q̂ₙ(ω) = 0`, so `edist 0 (det Q) = |det Q| ≥ ε`.
* Monotonicity: `μ {singular} ≤ μ {|det Q̂ₙ − det Q| ≥ ε} → 0`. -/
theorem measure_sampleGram_singular_tendsto_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) :
    Tendsto (fun n => μ {ω | ¬ IsUnit (sampleGram (stackRegressors X n ω)).det})
      atTop (𝓝 0) := by
  have hGram := sampleGram_stackRegressors_tendstoInMeasure_popGram h
  have hGram_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    intro n
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hDet : TendstoInMeasure μ
      (fun n ω => (sampleGram (stackRegressors X n ω)).det)
      atTop (fun _ => (popGram μ X).det) :=
    tendstoInMeasure_continuous_comp hGram_meas hGram
      (Continuous.matrix_det continuous_id)
  have hqne : (popGram μ X).det ≠ 0 := h.Q_nonsing.ne_zero
  set ε : ℝ := |(popGram μ X).det| / 2 with hε_def
  have hε_pos : 0 < ε := half_pos (abs_pos.mpr hqne)
  have hε_le : ε ≤ |(popGram μ X).det| := by
    rw [hε_def]; linarith [abs_nonneg ((popGram μ X).det)]
  have hmeas_eps := hDet (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε_pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmeas_eps
    (fun _ => zero_le _) (fun n => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq, isUnit_iff_ne_zero, not_not] at hω
  simp only [Set.mem_setOf_eq, hω, edist_dist, Real.dist_eq, zero_sub, abs_neg]
  exact ENNReal.ofReal_le_ofReal hε_le

/-- **Residual convergence in probability.** Under the moment-level assumptions and
the linear model `yᵢ = Xᵢ·β + eᵢ`, the residual
`β̂ₙ − β − Q̂ₙ⁻¹ *ᵥ ĝₙ(e)` converges to `0` in probability.

On the event `{Q̂ₙ invertible}`, this residual is identically `0` by
`olsBetaStar_sub_identity` + `nonsing_inv_mul`. The complement event has
vanishing measure by `measure_sampleGram_singular_tendsto_zero` (F4). -/
theorem residual_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω =>
        olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
          (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop (fun _ => (0 : k → ℝ)) := by
  have hsingular := measure_sampleGram_singular_tendsto_zero h
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsingular
    (fun _ => zero_le _) (fun n => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro hunit
  have hR : olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
      (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
        sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) = 0 := by
    rw [olsBetaStar_sub_identity X e y β hmodel,
        Matrix.nonsing_inv_mul _ hunit, sub_self, Matrix.zero_mulVec]
  rw [hR, edist_self] at hω
  exact absurd hω (not_le.mpr hε)

/-- **Scaled residual convergence in probability.** The same high-probability
invertibility argument kills the residual after multiplying by `√n`.

This is the singular-event remainder needed before the feasible OLS CLT can be
assembled: on `{Q̂ₙ invertible}` the residual is exactly zero, while the
singular event still has probability tending to zero. No rate is needed. -/
theorem sqrt_smul_residual_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
            (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)))
      atTop (fun _ => (0 : k → ℝ)) := by
  have hsingular := measure_sampleGram_singular_tendsto_zero h
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsingular
    (fun _ => zero_le _) (fun n => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro hunit
  have hR : olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
      (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
        sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) = 0 := by
    rw [olsBetaStar_sub_identity X e y β hmodel,
        Matrix.nonsing_inv_mul _ hunit, sub_self, Matrix.zero_mulVec]
  rw [hR, smul_zero, edist_self] at hω
  exact absurd hω (not_le.mpr hε)

/-- **Scalar projection of the scaled residual is negligible.** For every fixed
projection vector `a`, the scalar projection of the singular-event residual is
`oₚ(1)`.

This is the projectionwise form needed by the Cramér-Wold-facing CLT layer. -/
theorem scoreProjection_sqrt_smul_residual_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β a : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
            (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0) := by
  have hsingular := measure_sampleGram_singular_tendsto_zero h
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsingular
    (fun _ => zero_le _) (fun n => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro hunit
  have hR : olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
      (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
        sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) = 0 := by
    rw [olsBetaStar_sub_identity X e y β hmodel,
        Matrix.nonsing_inv_mul _ hunit, sub_self, Matrix.zero_mulVec]
  rw [hR, smul_zero] at hω
  simp only [zero_dotProduct, edist_self] at hω
  exact absurd hω (not_le.mpr hε)

/-- **Scaled totalized OLS decomposition.**
The centered and scaled total estimator splits into the singular-event residual
plus the feasible leading score term:
`√n(β̂*ₙ - β) = √n·Rₙ + Q̂ₙ⁻¹ *ᵥ (√n·ĝₙ(e))`.

This is pure deterministic algebra. The preceding theorem proves
`√n·Rₙ →ₚ 0`; the remaining Chapter 7 CLT work is to transfer the score CLT
through the random inverse `Q̂ₙ⁻¹`. -/
theorem sqrt_smul_olsBetaStar_sub_eq_sqrt_smul_residual_add_feasible_score
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β : k → ℝ) (n : ℕ) (ω : Ω) :
    Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) =
      Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
            (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) +
        (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) := by
  rw [Matrix.mulVec_smul]
  have hsplit : olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β =
      (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
        (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) +
      (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
        sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) := by
    abel
  calc
    Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)
        = Real.sqrt (n : ℝ) •
          ((olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
              (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
                sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) +
            (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) := by
            exact congrArg (fun v : k → ℝ => Real.sqrt (n : ℝ) • v) hsplit
    _ = Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
            (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) +
        Real.sqrt (n : ℝ) •
          ((sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) := by
        rw [smul_add]

/-- **Vector Slutsky residual for totalized OLS.**

The difference between the scaled totalized OLS error and the feasible leading
score `Q̂ₙ⁻¹√nĝₙ(e)` is `oₚ(1)`. This is the vector form needed by Mathlib's
distributional Slutsky theorem. -/
theorem sqrt_smul_olsBetaStar_sub_sub_feasibleScore_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) -
          (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
            (Real.sqrt (n : ℝ) •
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)))
      atTop (fun _ => (0 : k → ℝ)) := by
  have hres := sqrt_smul_residual_tendstoInMeasure_zero
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel
  refine hres.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  change
    Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
          (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) =
      Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) -
        (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
  rw [Matrix.mulVec_smul, smul_sub]

/-- **Feasible leading-term decomposition.**
The feasible leading score term is the fixed-`Q⁻¹` leading term plus the
random-inverse gap:
`Q̂ₙ⁻¹√nĝₙ(e) = Q⁻¹√nĝₙ(e) + (Q̂ₙ⁻¹ - Q⁻¹)√nĝₙ(e)`.

This names the exact remainder that the remaining Slutsky/tightness argument
must show is negligible. -/
theorem feasibleScore_eq_fixedScore_add_inverseGap
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (n : ℕ) (ω : Ω) :
    (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) =
      (popGram μ X)⁻¹ *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) +
        ((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) := by
  rw [Matrix.sub_mulVec]
  abel

/-- **Random-weight form of the inverse-gap projection.**
The scalar inverse-gap term can be viewed as the scaled score projected against
the random weight `(Q̂ₙ⁻¹ - Q⁻¹)ᵀa`.

This is the deterministic algebra behind the remaining tightness/product step:
the weight should converge to zero in probability, while the scaled score is
tight by the CLT. -/
theorem inverseGapProjection_eq_scoreProjection_randomWeight
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (a : k → ℝ) (n : ℕ) (ω : Ω) :
    (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a =
      (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) ⬝ᵥ
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹)ᵀ *ᵥ a) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose, dotProduct_comm]

/-- **Random inverse-gap weight converges to zero.**
For a fixed projection vector `a`, the random weight
`(Q̂ₙ⁻¹ - Q⁻¹)ᵀa` converges to zero in probability.

This is the deterministic-continuous-mapping half of the inverse-gap product
argument; the other half is boundedness in probability of the scaled score. -/
theorem inverseGapWeight_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (a : k → ℝ) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹)ᵀ *ᵥ a))
      atTop (fun _ => 0) := by
  have hInv := sampleGramInv_stackRegressors_tendstoInMeasure_popGramInv h
  have hGram_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    intro n
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hInv_meas : ∀ n, AEStronglyMeasurable
      (fun ω => (sampleGram (stackRegressors X n ω))⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (hGram_meas n)
  have hcont : Continuous
      (fun M : Matrix k k ℝ => (M - (popGram μ X)⁻¹)ᵀ *ᵥ a) := by
    fun_prop
  have hmap := tendstoInMeasure_continuous_comp hInv_meas hInv hcont
  simpa using hmap

/-- Coordinate form of `inverseGapWeight_tendstoInMeasure_zero`. -/
theorem inverseGapWeight_coord_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (a : k → ℝ) (j : k) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹)ᵀ *ᵥ a) j)
      atTop (fun _ => 0) := by
  exact TendstoInMeasure.pi_apply (inverseGapWeight_tendstoInMeasure_zero h a) j

/-- **Coordinatewise inverse-gap Slutsky bridge.**
For a fixed projection vector `a`, the inverse-gap projection is `oₚ(1)` once
each coordinate of the random weight `(Q̂ₙ⁻¹ - Q⁻¹)ᵀa` is `oₚ(1)` and each
coordinate of the scaled score `√n·ĝₙ(e)` is `Oₚ(1)`.

This is the product-rule heart of the remaining proof of Hansen Theorem 7.3:
after `inverseGapProjection_eq_scoreProjection_randomWeight`, the inverse gap
is a finite sum of coordinate products. -/
theorem inverseGapProjection_tendstoInMeasure_zero_of_coord
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (a : k → ℝ)
    (hweight : ∀ j : k,
      TendstoInMeasure μ
        (fun (n : ℕ) ω =>
          (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹)ᵀ *ᵥ a) j)
        atTop (fun _ => 0))
    (hscoreBounded : ∀ j : k,
      BoundedInProbability μ
        (fun (n : ℕ) ω =>
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) j)) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0) := by
  let score : ℕ → Ω → k → ℝ := fun n ω =>
    Real.sqrt (n : ℝ) •
      sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)
  let weight : ℕ → Ω → k → ℝ := fun n ω =>
    (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹)ᵀ *ᵥ a)
  have hprod : ∀ j ∈ (Finset.univ : Finset k),
      TendstoInMeasure μ (fun n ω => weight n ω j * score n ω j)
        atTop (fun _ => 0) := by
    intro j _
    exact TendstoInMeasure.mul_boundedInProbability
      (by simpa [weight] using hweight j)
      (by simpa [score] using hscoreBounded j)
  have hsum := tendstoInMeasure_finset_sum_zero_real (μ := μ)
    (s := (Finset.univ : Finset k))
    (X := fun j n ω => weight n ω j * score n ω j) hprod
  refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  dsimp [score, weight]
  rw [inverseGapProjection_eq_scoreProjection_randomWeight (μ := μ) (X := X) (e := e) a n ω]
  simp [dotProduct, mul_comm]

/-- **Inverse-gap projection from scaled-score boundedness.**
For a fixed projection vector `a`, the inverse-gap projection is `oₚ(1)` once
each coordinate of the scaled score `√n·ĝₙ(e)` is `Oₚ(1)`.

The random-weight side is now discharged by
`inverseGapWeight_coord_tendstoInMeasure_zero`; the remaining theorem-facing
task is supplying score boundedness, which `SampleCLTAssumption72` later
provides via the scalar score CLT. -/
theorem inverseGapProjection_tendstoInMeasure_zero_of_scoreBounded
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (a : k → ℝ)
    (hscoreBounded : ∀ j : k,
      BoundedInProbability μ
        (fun (n : ℕ) ω =>
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) j)) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0) := by
  exact inverseGapProjection_tendstoInMeasure_zero_of_coord a
    (fun j => inverseGapWeight_coord_tendstoInMeasure_zero h a j)
    hscoreBounded

/-- **Scalar-projection decomposition for the totalized OLS CLT.**
For every fixed projection vector `a`, the scaled totalized OLS error decomposes
into:

1. the scaled singular-event residual projection,
2. the fixed-`Q⁻¹` score projection with the known scalar CLT,
3. the random-inverse gap projection still left for Slutsky/tightness.

This is the exact algebraic roadmap for the remaining proof of Hansen's
Theorem 7.3. -/
theorem scoreProjection_sqrt_smul_olsBetaStar_sub_eq_residual_add_fixedScore_add_inverseGap
    {μ : Measure Ω} {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    {y : ℕ → Ω → ℝ} (β a : k → ℝ) (n : ℕ) (ω : Ω) :
    (Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a =
      (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
            (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a +
        (Real.sqrt (n : ℝ) •
          ((popGram μ X)⁻¹ *ᵥ
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a +
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a := by
  rw [sqrt_smul_olsBetaStar_sub_eq_sqrt_smul_residual_add_feasible_score,
      feasibleScore_eq_fixedScore_add_inverseGap (μ := μ), Matrix.mulVec_smul,
      add_dotProduct, add_dotProduct]
  ring

/-- **Scalar Slutsky remainder from the inverse gap.**
For a fixed projection vector `a`, the difference between the scaled totalized
OLS projection and the fixed-`Q⁻¹` score projection is `oₚ(1)` once the
random-inverse gap projection is `oₚ(1)`.

The scaled residual part is already controlled by
`scoreProjection_sqrt_smul_residual_tendstoInMeasure_zero`; this theorem makes
the remaining target exactly the inverse-gap/tightness step. -/
theorem scoreProjection_olsBetaStar_remainder_tendstoInMeasure_zero_of_inverseGap
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (β a : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hinvGap : TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a -
          (Real.sqrt (n : ℝ) •
            ((popGram μ X)⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0) := by
  let residual : ℕ → Ω → ℝ := fun n ω =>
    (Real.sqrt (n : ℝ) •
      (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β -
        (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a
  let gap : ℕ → Ω → ℝ := fun n ω =>
    (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
      (Real.sqrt (n : ℝ) •
        sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a
  have hresConv : TendstoInMeasure μ residual atTop (fun _ => 0) := by
    simpa [residual] using
      scoreProjection_sqrt_smul_residual_tendstoInMeasure_zero β a h hmodel
  have hgapConv : TendstoInMeasure μ gap atTop (fun _ => 0) := by
    simpa [gap] using hinvGap
  have hsumConv : TendstoInMeasure μ (fun n ω => residual n ω + gap n ω)
      atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_dist] at hresConv hgapConv ⊢
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    have hsum := (hresConv (ε / 2) hε2).add (hgapConv (ε / 2) hε2)
    have hsum0 : Tendsto
        (fun (n : ℕ) =>
          μ {ω | ε / 2 ≤ dist (residual n ω) 0} +
          μ {ω | ε / 2 ≤ dist (gap n ω) 0})
        atTop (𝓝 0) := by
      simpa using hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum0
      (fun _ => zero_le _) (fun n => ?_)
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    by_cases hres_big : ε / 2 ≤ dist (residual n ω) 0
    · exact Or.inl hres_big
    · right
      by_contra hgap_small_not
      have hres_small : dist (residual n ω) 0 < ε / 2 := not_le.mp hres_big
      have hgap_small : dist (gap n ω) 0 < ε / 2 := not_le.mp hgap_small_not
      have htri : dist (residual n ω + gap n ω) 0 ≤
          dist (residual n ω) 0 + dist (gap n ω) 0 := by
        rw [Real.dist_eq, Real.dist_eq, Real.dist_eq]
        simpa using abs_add_le (residual n ω) (gap n ω)
      have hlt : dist (residual n ω + gap n ω) 0 < ε := by linarith
      exact (not_le.mpr hlt) hω
  refine hsumConv.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  dsimp [residual, gap]
  rw [scoreProjection_sqrt_smul_olsBetaStar_sub_eq_residual_add_fixedScore_add_inverseGap]
  ring

/-- **Consistency of the totalized least-squares estimator.**
Under the moment-level assumptions above and the linear model `yᵢ = Xᵢ·β + eᵢ`,
the total OLS estimator `β̂*ₙ := (Xᵀ X)⁺ Xᵀ y` (using `Matrix.nonsingInv`)
converges in probability to `β`.

Proof chain:
* F2: `β̂*ₙ = Q̂ₙ⁻¹ *ᵥ ĝₙ(y)` pointwise.
* F3: `ĝₙ(y) = Q̂ₙ β + ĝₙ(e)` under the linear model.
* F6: residual `β̂*ₙ − β − Q̂ₙ⁻¹ *ᵥ ĝₙ(e) →ₚ 0` (it vanishes on the invertibility
  event, whose complement has measure → 0 by F4).
* Task 11: `Q̂ₙ⁻¹ *ᵥ ĝₙ(e) →ₚ 0`.
* F5 (twice): residual + error term + β →ₚ 0 + 0 + β = β.
* Pointwise algebra: the sum equals `β̂*ₙ`. -/
theorem olsBetaStar_stack_tendstoInMeasure_beta
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => β) := by
  have hGram_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    intro n
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hCrossE_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) μ := by
    intro n
    have hform : (fun ω => sampleCrossMoment (stackRegressors X n ω)
          (stackErrors e n ω)) =
        (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, e i ω • X i ω) := by
      funext ω
      rw [sampleCrossMoment_stackRegressors_stackErrors_eq_avg,
          sum_fin_eq_sum_range_smul]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_cross i).integrable_iff.mpr h.int_cross).aestronglyMeasurable
  have hInv_meas : ∀ n, AEStronglyMeasurable
      (fun ω => (sampleGram (stackRegressors X n ω))⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (hGram_meas n)
  have hCoreMV_meas : ∀ n, AEStronglyMeasurable
      (fun ω => (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) μ := by
    intro n
    have hprod := (hInv_meas n).prodMk (hCrossE_meas n)
    exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable hprod
  have hR'_meas : ∀ n, AEStronglyMeasurable
      (fun ω => ((sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω) - 1) *ᵥ β) μ := by
    intro n
    have hmat_mul : AEStronglyMeasurable
        (fun ω => (sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω)) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        ((hInv_meas n).prodMk (hGram_meas n))
    have hmat_sub : AEStronglyMeasurable
        (fun ω => (sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω) - 1) μ :=
      hmat_mul.sub aestronglyMeasurable_const
    exact (Continuous.matrix_mulVec continuous_id continuous_const).comp_aestronglyMeasurable
      hmat_sub
  -- R'_n →ₚ 0 via F6 + the residual identity
  have hF6 := residual_tendstoInMeasure_zero β h hmodel
  have hR' : TendstoInMeasure μ
      (fun n ω => ((sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω) - 1) *ᵥ β)
      atTop (fun _ => (0 : k → ℝ)) :=
    hF6.congr_left (fun n => ae_of_all μ (fun ω =>
      olsBetaStar_sub_identity X e y β hmodel n ω))
  -- Q̂ₙ⁻¹ *ᵥ ĝₙ(e) →ₚ 0 (Task 11)
  have hCore := sampleGramInv_mulVec_sampleCrossMoment_e_tendstoInMeasure_zero h
  -- R'_n + Q̂ₙ⁻¹ *ᵥ ĝₙ(e) →ₚ 0
  have hSum := tendstoInMeasure_add hR'_meas hCoreMV_meas hR' hCore
  simp only [add_zero] at hSum
  -- (R'_n + Q̂ₙ⁻¹ *ᵥ ĝₙ(e)) + β →ₚ β
  have hConst : TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => β) atTop (fun _ => β) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all μ (fun _ => tendsto_const_nhds))
  have hSumPlus := tendstoInMeasure_add
    (fun n => (hR'_meas n).add (hCoreMV_meas n))
    (fun _ => aestronglyMeasurable_const)
    hSum hConst
  simp only [zero_add] at hSumPlus
  -- Congr to olsBetaStar via the residual identity
  refine hSumPlus.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  simp only [Pi.add_apply]
  have hident := olsBetaStar_sub_identity X e y β hmodel n ω
  rw [← hident]; abel

/-- **AEMeasurability of the totalized OLS estimator.**

Under the moment assumptions and pointwise linear model, each stacked
`olsBetaStar` random vector is a.e. strongly measurable. This is the
measurability input needed to apply continuous-mapping theorems directly to
functions of `β̂*ₙ`. -/
theorem olsBetaStar_stack_aestronglyMeasurable
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    ∀ n, AEStronglyMeasurable
      (fun ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  intro n
  have hGram_meas : AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hCrossE_meas : AEStronglyMeasurable
      (fun ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) μ := by
    have hform : (fun ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) =
        (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, e i ω • X i ω) := by
      funext ω
      rw [sampleCrossMoment_stackRegressors_stackErrors_eq_avg,
          sum_fin_eq_sum_range_smul]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_cross i).integrable_iff.mpr h.int_cross).aestronglyMeasurable
  have hInv_meas : AEStronglyMeasurable
      (fun ω => (sampleGram (stackRegressors X n ω))⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hGram_meas
  have hGramBeta_meas : AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω) *ᵥ β) μ :=
    (Continuous.matrix_mulVec continuous_id continuous_const).comp_aestronglyMeasurable
      hGram_meas
  have hMiddle_meas : AEStronglyMeasurable
      (fun ω =>
        sampleGram (stackRegressors X n ω) *ᵥ β +
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) μ :=
    hGramBeta_meas.add hCrossE_meas
  have hRhs_meas : AEStronglyMeasurable
      (fun ω =>
        (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          (sampleGram (stackRegressors X n ω) *ᵥ β +
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) μ := by
    have hprod := hInv_meas.prodMk hMiddle_meas
    exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable hprod
  refine hRhs_meas.congr (ae_of_all μ (fun ω => ?_))
  change
    (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
        (sampleGram (stackRegressors X n ω) *ᵥ β +
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) =
      olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)
  rw [← sampleCrossMoment_stackOutcomes_linear_model X e y β hmodel,
      ← olsBetaStar_stack_eq_sampleGramInv_mulVec_sampleCrossMoment X y n ω]

/-- **Hansen Theorem 7.8, continuous functions of totalized OLS.**

For any globally continuous parameter transform `φ`, consistency of the
totalized OLS estimator transfers to `φ(β̂*ₙ) →ₚ φ(β)`. This is the direct
continuous-mapping-theorem face of Hansen's functions-of-parameters section;
local-at-`β` and delta-method refinements remain separate future work. -/
theorem continuous_function_olsBetaStar_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {F : Type*} [PseudoEMetricSpace F] [TopologicalSpace.PseudoMetrizableSpace F]
    (φ : (k → ℝ) → F) (hφ : Continuous φ) :
    TendstoInMeasure μ
      (fun n ω => φ (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)))
      atTop (fun _ => φ β) := by
  exact tendstoInMeasure_continuous_comp
    (olsBetaStar_stack_aestronglyMeasurable
      (μ := μ) (X := X) (e := e) (y := y) β h hmodel)
    (olsBetaStar_stack_tendstoInMeasure_beta
      (μ := μ) (X := X) (e := e) (y := y) β h hmodel)
    hφ

/-- **Hansen Theorem 7.8 for ordinary OLS on nonsingular samples.**

The same continuous-function consistency statement holds for `olsBetaOrZero`,
the wrapper that agrees with ordinary OLS on nonsingular samples and with
`olsBetaStar` unconditionally. -/
theorem continuous_function_olsBetaOrZero_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {F : Type*} [PseudoEMetricSpace F] [TopologicalSpace.PseudoMetrizableSpace F]
    (φ : (k → ℝ) → F) (hφ : Continuous φ) :
    TendstoInMeasure μ
      (fun n ω => φ (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)))
      atTop (fun _ => φ β) := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    continuous_function_olsBetaStar_tendstoInMeasure
      (μ := μ) (X := X) (e := e) (y := y) β h hmodel φ hφ

/-- **Theorem 7.1 ordinary-OLS-on-nonsingular-samples consistency.**

The textbook-facing wrapper `olsBetaOrZero` equals ordinary `olsBeta` whenever
the sample Gram is nonsingular and equals `olsBetaStar` unconditionally, so the
totalized consistency theorem transfers directly. -/
theorem olsBetaOrZero_stack_tendstoInMeasure_beta
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω => olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => β) := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    olsBetaStar_stack_tendstoInMeasure_beta
      (μ := μ) (X := X) (e := e) (y := y) β h hmodel

/-- **Theorem 7.4 cross remainder.**

The cross term in the residual-variance expansion is negligible:
`-2 ĝₙ(e)'(β̂*ₙ - β) = oₚ(1)`. It follows coordinatewise from the sample
cross-moment WLLN, Theorem 7.1 consistency, and the finite dot-product
`oₚ(1)·oₚ(1)` rule. -/
theorem olsSigmaSqHatStar_crossRemainder_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω =>
        -2 * (sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) ⬝ᵥ
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
      atTop (fun _ => 0) := by
  have hCross :=
    sampleCrossMoment_stackRegressors_stackErrors_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71
  have hBeta :=
    olsBetaStar_stack_tendstoInMeasure_beta
      (μ := μ) (X := X) (e := e) (y := y) β
      h.toSampleMomentAssumption71 hmodel
  have hCrossCoord : ∀ j : k,
      TendstoInMeasure μ
        (fun n ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) j)
        atTop (fun _ => 0) := by
    intro j
    exact TendstoInMeasure.pi_apply hCross j
  have hBetaCoord : ∀ j : k,
      TendstoInMeasure μ
        (fun n ω =>
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) j)
        atTop (fun _ => 0) := by
    intro j
    have hj := TendstoInMeasure.pi_apply hBeta j
    have hcenter := TendstoInMeasure.sub_limit_zero_real hj
    simpa [Pi.sub_apply] using hcenter
  have hdot := tendstoInMeasure_dotProduct_zero_real (μ := μ)
    (X := fun n ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
    (Y := fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)
    hCrossCoord hBetaCoord
  simpa using TendstoInMeasure.const_mul_zero_real (μ := μ) (-2) hdot

/-- **Theorem 7.4 Gram-weighted estimation error.**

The sample Gram times the estimation error is negligible:
`Q̂ₙ(β̂*ₙ - β) = oₚ(1)`. The proof is coordinatewise: each summand is
`Q̂ₙ,jl dₙ,l = (Q̂ₙ,jl - Q_jl)dₙ,l + Q_jl dₙ,l`, with both terms `oₚ(1)`. -/
theorem sampleGram_mulVec_olsBetaStar_sub_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleGram (stackRegressors X n ω) *ᵥ
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun _ => 0) := by
  let Qhat : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    sampleGram (stackRegressors X n ω)
  let d : ℕ → Ω → k → ℝ := fun n ω =>
    olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β
  have hGram := sampleGram_stackRegressors_tendstoInMeasure_popGram
    (μ := μ) (X := X) (e := e) h
  have hBeta := olsBetaStar_stack_tendstoInMeasure_beta
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel
  have hDiffCoord : ∀ l : k,
      TendstoInMeasure μ (fun n ω => d n ω l) atTop (fun _ => 0) := by
    intro l
    have hl := TendstoInMeasure.pi_apply hBeta l
    have hcenter := TendstoInMeasure.sub_limit_zero_real hl
    simpa [d, Pi.sub_apply] using hcenter
  have hGramCoord : ∀ j l : k,
      TendstoInMeasure μ (fun n ω => Qhat n ω j l)
        atTop (fun _ => (popGram μ X) j l) := by
    intro j l
    exact TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hGram j) l
  have hCoord : ∀ j : k,
      TendstoInMeasure μ (fun n ω => (Qhat n ω *ᵥ d n ω) j)
        atTop (fun _ => 0) := by
    intro j
    have hterm : ∀ l ∈ (Finset.univ : Finset k),
        TendstoInMeasure μ (fun n ω => Qhat n ω j l * d n ω l)
          atTop (fun _ => 0) := by
      intro l _
      have hQcenter := TendstoInMeasure.sub_limit_zero_real (hGramCoord j l)
      have hcenterProd := TendstoInMeasure.mul_zero_real hQcenter (hDiffCoord l)
      have hconstProd := TendstoInMeasure.const_mul_zero_real
        (μ := μ) ((popGram μ X) j l) (hDiffCoord l)
      have hsum := TendstoInMeasure.add_zero_real hcenterProd hconstProd
      refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
      dsimp [Qhat, d]
      ring
    have hsum := tendstoInMeasure_finset_sum_zero_real (μ := μ)
      (s := (Finset.univ : Finset k))
      (X := fun l n ω => Qhat n ω j l * d n ω l) hterm
    refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
    simp [Qhat, d, Matrix.mulVec, dotProduct]
  simpa [Qhat, d] using tendstoInMeasure_pi (μ := μ) hCoord

/-- **Theorem 7.4 quadratic remainder.**

The quadratic term in the residual-variance expansion is negligible:
`(β̂*ₙ - β)'Q̂ₙ(β̂*ₙ - β) = oₚ(1)`. -/
theorem olsSigmaSqHatStar_quadraticRemainder_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω =>
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) ⬝ᵥ
          (sampleGram (stackRegressors X n ω) *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)))
      atTop (fun _ => 0) := by
  let d : ℕ → Ω → k → ℝ := fun n ω =>
    olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β
  let Qd : ℕ → Ω → k → ℝ := fun n ω =>
    sampleGram (stackRegressors X n ω) *ᵥ d n ω
  have hBeta := olsBetaStar_stack_tendstoInMeasure_beta
    (μ := μ) (X := X) (e := e) (y := y) β
    h.toSampleMomentAssumption71 hmodel
  have hDiffCoord : ∀ j : k,
      TendstoInMeasure μ (fun n ω => d n ω j) atTop (fun _ => 0) := by
    intro j
    have hj := TendstoInMeasure.pi_apply hBeta j
    have hcenter := TendstoInMeasure.sub_limit_zero_real hj
    simpa [d, Pi.sub_apply] using hcenter
  have hQd := sampleGram_mulVec_olsBetaStar_sub_tendstoInMeasure_zero
    (μ := μ) (X := X) (e := e) (y := y)
    h.toSampleMomentAssumption71 β hmodel
  have hQdCoord : ∀ j : k,
      TendstoInMeasure μ (fun n ω => Qd n ω j) atTop (fun _ => 0) := by
    intro j
    simpa [Qd, d] using TendstoInMeasure.pi_apply hQd j
  have hdot := tendstoInMeasure_dotProduct_zero_real (μ := μ)
    (X := d) (Y := Qd) hDiffCoord hQdCoord
  simpa [d, Qd] using hdot

/-- **Theorem 7.4 centered residual-variance consistency.**

Under the squared-error WLLN assumptions and the linear model,
`σ̂²ₙ - σ² = oₚ(1)` for the totalized OLS residual average. -/
theorem olsSigmaSqHatStar_sub_errorVariance_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω =>
        olsSigmaSqHatStar (stackRegressors X n ω) (stackOutcomes y n ω) -
          errorVariance μ e)
      atTop (fun _ => 0) := by
  exact olsSigmaSqHatStar_sub_errorVariance_tendstoInMeasure_zero_of_remainders
    (μ := μ) (X := X) (e := e) (y := y) h β hmodel
    (olsSigmaSqHatStar_crossRemainder_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel)
    (olsSigmaSqHatStar_quadraticRemainder_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel)

/-- **Theorem 7.4 residual-variance consistency.**

Under the squared-error WLLN assumptions and the linear model, the totalized
OLS residual average `σ̂²ₙ` converges in probability to `σ² = E[e₀²]`. -/
theorem olsSigmaSqHatStar_tendstoInMeasure_errorVariance
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω => olsSigmaSqHatStar (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop
      (fun _ => errorVariance μ e) := by
  exact olsSigmaSqHatStar_tendstoInMeasure_errorVariance_of_remainders
    (μ := μ) (X := X) (e := e) (y := y) h β hmodel
    (olsSigmaSqHatStar_crossRemainder_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel)
    (olsSigmaSqHatStar_quadraticRemainder_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel)

/-- **Theorem 7.4 centered degrees-of-freedom variance consistency.**

The degrees-of-freedom adjusted totalized residual variance satisfies
`s²ₙ - σ² = oₚ(1)`. -/
theorem olsS2Star_sub_errorVariance_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω =>
        olsS2Star (stackRegressors X n ω) (stackOutcomes y n ω) -
          errorVariance μ e)
      atTop (fun _ => 0) := by
  let r : ℕ → ℝ := fun n =>
    (n : ℝ) * ((n : ℝ) - (Fintype.card k : ℝ))⁻¹
  let sigmaHat : ℕ → Ω → ℝ := fun n ω =>
    olsSigmaSqHatStar (stackRegressors X n ω) (stackOutcomes y n ω)
  have hSigmaCentered :=
    olsSigmaSqHatStar_sub_errorVariance_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden : Tendsto
      (fun n : ℕ => (n : ℝ) - (Fintype.card k : ℝ)) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(Fintype.card k : ℝ)) hn
  have hrSub : Tendsto (fun n => r n - 1) atTop (𝓝 0) := by
    have hsmall : Tendsto
        (fun n : ℕ => (Fintype.card k : ℝ) /
          ((n : ℝ) - (Fintype.card k : ℝ))) atTop (𝓝 0) :=
      hden.const_div_atTop (Fintype.card k : ℝ)
    have heq : (fun n => r n - 1) =ᶠ[atTop]
        (fun n : ℕ => (Fintype.card k : ℝ) /
          ((n : ℝ) - (Fintype.card k : ℝ))) := by
      filter_upwards [eventually_gt_atTop (Fintype.card k)] with n hn_gt
      have hden_ne : (n : ℝ) - (Fintype.card k : ℝ) ≠ 0 := by
        have hgt : (Fintype.card k : ℝ) < (n : ℝ) := by
          exact_mod_cast hn_gt
        linarith
      dsimp [r]
      field_simp [hden_ne]
      ring
    rw [tendsto_congr' heq]
    exact hsmall
  have hr : Tendsto r atTop (𝓝 1) := by
    have hadd := hrSub.add_const 1
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hadd
  have hbound : ∀ᶠ n in atTop, |r n| ≤ 2 := by
    have hnear : ∀ᶠ n in atTop, dist (r n) 1 < 1 :=
      eventually_atTop.2 ((Metric.tendsto_atTop.1 hr) 1 one_pos)
    filter_upwards [hnear] with n hn_near
    have habs : |r n - 1| < 1 := by
      simpa [Real.dist_eq] using hn_near
    have hleft := (abs_lt.mp habs).1
    have hright := (abs_lt.mp habs).2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hscaledCentered : TendstoInMeasure μ
      (fun n ω => r n * (sigmaHat n ω - errorVariance μ e))
      atTop (fun _ => 0) := by
    exact TendstoInMeasure.mul_deterministic_bounded_zero_real
      (μ := μ) (M := 2) (by norm_num) hbound
      (by simpa [sigmaHat] using hSigmaCentered)
  have hdetReal : Tendsto
      (fun n => (r n - 1) * errorVariance μ e) atTop (𝓝 0) := by
    simpa using hrSub.mul tendsto_const_nhds
  have hdetMeasure : TendstoInMeasure μ
      (fun n (_ : Ω) => (r n - 1) * errorVariance μ e)
      atTop (fun _ => 0) :=
    tendstoInMeasure_const_real (μ := μ) hdetReal
  have hscaled :=
    TendstoInMeasure.add_zero_real hscaledCentered hdetMeasure
  have hcenter : TendstoInMeasure μ
      (fun n ω => r n * sigmaHat n ω - errorVariance μ e)
      atTop (fun _ => 0) := by
    refine hscaled.congr_left (fun n => ae_of_all μ (fun ω => ?_))
    ring
  refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hcenter
  filter_upwards [eventually_gt_atTop 0] with n hn_pos
  exact ae_of_all μ (fun ω => by
    haveI : Nonempty (Fin n) := ⟨⟨0, hn_pos⟩⟩
    dsimp [r, sigmaHat]
    rw [olsS2Star_eq_card_div_df_mul_olsSigmaSqHatStar]
    simp [Fintype.card_fin, div_eq_mul_inv])

/-- **Theorem 7.4 degrees-of-freedom variance consistency.**

Under the squared-error WLLN assumptions and the linear model, the
degrees-of-freedom adjusted totalized residual variance `s²ₙ` converges in
probability to `σ² = E[e₀²]`. -/
theorem olsS2Star_tendstoInMeasure_errorVariance
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω => olsS2Star (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop
      (fun _ => errorVariance μ e) := by
  exact TendstoInMeasure.of_sub_limit_zero_real
    (olsS2Star_sub_errorVariance_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel)

/-- Hansen's homoskedastic asymptotic covariance matrix
`V⁰_β := σ² Q⁻¹`. -/
noncomputable def homoskedasticAsymptoticCovariance
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) : Matrix k k ℝ :=
  errorVariance μ e • (popGram μ X)⁻¹

/-- The totalized plug-in estimator `V̂⁰_β := s² Q̂⁻¹` for Hansen Theorem 7.5. -/
noncomputable def olsHomoskedasticCovarianceStar
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  olsS2Star X y • (sampleGram X)⁻¹

/-- **Hansen Theorem 7.5, totalized homoskedastic covariance consistency.**

Under the variance-estimator assumptions and the linear model, the plug-in
homoskedastic covariance estimator `V̂⁰_β = s² Q̂⁻¹` converges in probability to
`V⁰_β = σ² Q⁻¹`. -/
theorem olsHomoskedasticCovarianceStar_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHomoskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => homoskedasticAsymptoticCovariance μ X e) := by
  let s2 : ℕ → Ω → ℝ := fun n ω =>
    olsS2Star (stackRegressors X n ω) (stackOutcomes y n ω)
  let invGram : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    (sampleGram (stackRegressors X n ω))⁻¹
  have hs2 := olsS2Star_tendstoInMeasure_errorVariance
    (μ := μ) (X := X) (e := e) (y := y) h β hmodel
  have hInv := sampleGramInv_stackRegressors_tendstoInMeasure_popGramInv
    (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71
  have hEntry : ∀ i j : k,
      TendstoInMeasure μ
        (fun n ω => s2 n ω * invGram n ω i j)
        atTop
        (fun _ => errorVariance μ e * ((popGram μ X)⁻¹) i j) := by
    intro i j
    have hInvCoord : TendstoInMeasure μ
        (fun n ω => invGram n ω i j)
        atTop (fun _ => ((popGram μ X)⁻¹) i j) := by
      simpa [invGram] using
        TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hInv i) j
    exact TendstoInMeasure.mul_limits_real
      (by simpa [s2] using hs2) hInvCoord
  refine tendstoInMeasure_pi (μ := μ) (fun i => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun j => ?_)
  simpa [olsHomoskedasticCovarianceStar, homoskedasticAsymptoticCovariance,
    s2, invGram, Pi.smul_apply, smul_eq_mul] using hEntry i j

/-- AEMeasurability of the totalized homoskedastic covariance estimator from
component measurability. -/
theorem olsHomoskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω =>
        olsHomoskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  intro n
  have hBeta_meas := olsBetaStar_stack_aestronglyMeasurable
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel n
  have hGram_meas : AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hInv_meas : AEStronglyMeasurable
      (fun ω => (sampleGram (stackRegressors X n ω))⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hGram_meas
  have hdot_fixed_cont : Continuous (fun x : k → ℝ => x ⬝ᵥ β) := by
    simpa [dotProduct] using
      (continuous_finset_sum Finset.univ
        (fun i _ => (continuous_apply i).mul continuous_const))
  have hdot_pair_cont : Continuous (fun p : (k → ℝ) × (k → ℝ) => p.1 ⬝ᵥ p.2) := by
    simpa [dotProduct] using
      (continuous_finset_sum Finset.univ
        (fun i _ =>
          ((continuous_apply i).comp continuous_fst).mul
            ((continuous_apply i).comp continuous_snd)))
  have hres : ∀ i : Fin n, AEStronglyMeasurable
      (fun ω =>
        olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i) μ := by
    intro i
    have hXrow : AEStronglyMeasurable (fun ω => stackRegressors X n ω i) μ := by
      simpa [stackRegressors] using hX_meas i.val
    have hYrow : AEStronglyMeasurable (fun ω => stackOutcomes y n ω i) μ := by
      have hYexpr : AEStronglyMeasurable
          (fun ω => X i.val ω ⬝ᵥ β + e i.val ω) μ :=
        (hdot_fixed_cont.comp_aestronglyMeasurable (hX_meas i.val)).add (he_meas i.val)
      refine hYexpr.congr (ae_of_all μ (fun ω => ?_))
      simpa [stackOutcomes] using (hmodel i.val ω).symm
    have hfit : AEStronglyMeasurable
        (fun ω =>
          stackRegressors X n ω i ⬝ᵥ
            olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)) μ :=
      hdot_pair_cont.comp_aestronglyMeasurable (hXrow.prodMk hBeta_meas)
    have hres_exp : AEStronglyMeasurable
        (fun ω =>
          stackOutcomes y n ω i -
            stackRegressors X n ω i ⬝ᵥ
              olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)) μ :=
      hYrow.sub hfit
    refine hres_exp.congr (ae_of_all μ (fun ω => ?_))
    simp [olsResidualStar, Matrix.mulVec, dotProduct]
  have hss : AEStronglyMeasurable
      (fun ω =>
        dotProduct
          (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω))
          (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω))) μ := by
    simpa [dotProduct] using
      Finset.aestronglyMeasurable_fun_sum (Finset.univ : Finset (Fin n))
        (fun i _ => (hres i).mul (hres i))
  have hs2 : AEStronglyMeasurable
      (fun ω =>
        olsS2Star (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
    simpa [olsS2Star] using
      hss.const_mul (((Fintype.card (Fin n) : ℝ) - Fintype.card k)⁻¹)
  simpa [olsHomoskedasticCovarianceStar] using hs2.smul hInv_meas

/-- **AEMeasurability of the scaled totalized-OLS projection.**

The final random variable in the scalar OLS CLT is measurable under the
sample-moment hypotheses and the pointwise linear model. The proof avoids a
standalone measurability theorem for `olsBetaStar` by rewriting
`olsBetaStar - β` with `olsBetaStar_sub_identity` into the measurable
sample-Gram and sample-score pieces. -/
theorem scoreProjection_sqrt_smul_olsBetaStar_sub_aemeasurable
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    ∀ (n : ℕ), AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a) μ := by
  intro n
  have hGram_meas : AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hCrossE_meas : AEStronglyMeasurable
      (fun ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) μ := by
    have hform : (fun ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) =
        (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, e i ω • X i ω) := by
      funext ω
      rw [sampleCrossMoment_stackRegressors_stackErrors_eq_avg,
          sum_fin_eq_sum_range_smul]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_cross i).integrable_iff.mpr h.int_cross).aestronglyMeasurable
  have hInv_meas : AEStronglyMeasurable
      (fun ω => (sampleGram (stackRegressors X n ω))⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hGram_meas
  have hCoreMV_meas : AEStronglyMeasurable
      (fun ω => (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) μ := by
    have hprod := hInv_meas.prodMk hCrossE_meas
    exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable hprod
  have hR'_meas : AEStronglyMeasurable
      (fun ω => ((sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω) - 1) *ᵥ β) μ := by
    have hmat_mul : AEStronglyMeasurable
        (fun ω => (sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω)) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hInv_meas.prodMk hGram_meas)
    have hmat_sub : AEStronglyMeasurable
        (fun ω => (sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω) - 1) μ :=
      hmat_mul.sub aestronglyMeasurable_const
    exact (Continuous.matrix_mulVec continuous_id continuous_const).comp_aestronglyMeasurable
      hmat_sub
  have hvec_meas : AEStronglyMeasurable
      (fun ω =>
        Real.sqrt (n : ℝ) •
          (((sampleGram (stackRegressors X n ω))⁻¹ *
              sampleGram (stackRegressors X n ω) - 1) *ᵥ β +
            (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) μ :=
    AEStronglyMeasurable.const_smul (hR'_meas.add hCoreMV_meas) (Real.sqrt (n : ℝ))
  have hdot_cont : Continuous (fun v : k → ℝ => v ⬝ᵥ a) := by
    simpa [dotProduct] using
      (continuous_finset_sum Finset.univ
        (fun i _ => (continuous_apply i).mul continuous_const))
  have hproj_meas : AEStronglyMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ) •
          (((sampleGram (stackRegressors X n ω))⁻¹ *
              sampleGram (stackRegressors X n ω) - 1) *ᵥ β +
            (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a) μ :=
    hdot_cont.comp_aestronglyMeasurable hvec_meas
  refine hproj_meas.aemeasurable.congr (ae_of_all μ (fun ω => ?_))
  have hvec : olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β =
      ((sampleGram (stackRegressors X n ω))⁻¹ *
          sampleGram (stackRegressors X n ω) - 1) *ᵥ β +
        (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) := by
    have hident := olsBetaStar_sub_identity X e y β hmodel n ω
    rw [← hident]
    abel
  exact congrArg (fun v : k → ℝ => (Real.sqrt (n : ℝ) • v) ⬝ᵥ a) hvec.symm

end Assumption71

section Assumption72

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.Elementwise Function Topology ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {k : Type*} [Fintype k] [DecidableEq k]

omit [DecidableEq k] in
/-- Borel σ-algebra on `Matrix k k ℝ` inherited from the elementwise-L∞ norm,
reintroduced for the Chapter 7.2+ covariance-matrix random variables. -/
@[reducible]
private noncomputable def matrixBorelMeasurableSpace72 :
    MeasurableSpace (Matrix k k ℝ) := borel _

attribute [local instance] matrixBorelMeasurableSpace72

omit [Fintype k] [DecidableEq k] in
private lemma matrixBorelSpace72 : BorelSpace (Matrix k k ℝ) := ⟨rfl⟩

attribute [local instance] matrixBorelSpace72

/-- Strengthening of the Chapter 7.1 moment assumptions for the first CLT bridge.

Mathlib currently supplies a one-dimensional iid CLT. To use it for Hansen's
vector score `eᵢXᵢ`, we ask for full independence of those score vectors and
square integrability of every fixed scalar projection. The resulting theorem is
the scalar-projection/Cramér-Wold face of Hansen Assumption 7.2. -/
structure SampleCLTAssumption72 (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    extends SampleMomentAssumption71 μ X e where
  /-- Full independence of the score-vector sequence `e i • X i`. -/
  iIndep_cross : iIndepFun (fun i ω => e i ω • X i ω) μ
  /-- Square integrability of every scalar projection of the score vector. -/
  memLp_cross_projection :
    ∀ a : k → ℝ, MemLp (fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a) 2 μ

omit [DecidableEq k] in
/-- Measurability of a fixed dot-product projection on finite-dimensional vectors. -/
private theorem measurable_dotProduct_right (a : k → ℝ) :
    Measurable (fun v : k → ℝ => v ⬝ᵥ a) := by
  classical
  simpa [dotProduct] using
    (continuous_finset_sum Finset.univ
      (fun i _ => (continuous_apply i).mul continuous_const)).measurable

/-- The scalar score projection has mean zero under the orthogonality axiom. -/
private theorem scoreProjection_integral_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (a : k → ℝ) :
    μ[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a] = 0 := by
  have hdot := integral_dotProduct_eq_meanVec_dotProduct
    (μ := μ) (X := fun ω => e 0 ω • X 0 ω) a
    (fun i => Integrable.eval h.int_cross i)
  simpa [meanVec, h.orthogonality] using hdot

/-- Coordinate square-integrability of the score vector under Assumption 7.2. -/
theorem scoreCoordinate_memLp_two
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (j : k) :
    MemLp (fun ω => (e 0 ω • X 0 ω) j) 2 μ := by
  classical
  have hproj := h.memLp_cross_projection (Pi.single j 1)
  simpa [dotProduct_single_one] using hproj

/-- Vector square-integrability of the score vector under Assumption 7.2. -/
theorem scoreVector_memLp_two
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) :
    MemLp (fun ω => e 0 ω • X 0 ω) 2 μ :=
  MemLp.of_eval (fun j => scoreCoordinate_memLp_two (μ := μ) (X := X) (e := e) h j)

/-- Hansen's score covariance matrix `Ω := Var(e₀X₀)`. Under the population
orthogonality condition this agrees entrywise with `E[e₀² X₀ X₀']`. -/
noncomputable def scoreCovarianceMatrix
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) : Matrix k k ℝ :=
  covMat μ (fun ω => e 0 ω • X 0 ω)

/-- Scalar asymptotic variance of the projection `a'√n(β̂ₙ - β)`:
`((Q⁻¹)'a)' Ω ((Q⁻¹)'a)`. This avoids needing to prove symmetry of `Q⁻¹`
before stating the scalar CLT in textbook covariance notation. -/
noncomputable def olsProjectionAsymptoticVariance
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    (a : k → ℝ) : ℝ :=
  let b := ((popGram μ X)⁻¹)ᵀ *ᵥ a
  b ⬝ᵥ (scoreCovarianceMatrix μ X e *ᵥ b)

/-- **Theorem 7.2 finite second-moment face.**

Every entry of the score second-moment matrix
`E[(e₀X₀)_j (e₀X₀)_ℓ]` is finite. This is the Lean-facing version of the
textbook statement that the asymptotic covariance matrix `Ω` has finite
entries under Assumption 7.2. -/
theorem scoreSecondMoment_integrable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (j l : k) :
    Integrable (fun ω => (e 0 ω • X 0 ω) j * (e 0 ω • X 0 ω) l) μ := by
  exact (scoreCoordinate_memLp_two (μ := μ) (X := X) (e := e) h j).integrable_mul
    (scoreCoordinate_memLp_two (μ := μ) (X := X) (e := e) h l)

omit [Fintype k] [DecidableEq k] in
/-- The score covariance matrix is symmetric. -/
theorem scoreCovarianceMatrix_isSymm
    {μ : Measure Ω}
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} :
    (scoreCovarianceMatrix μ X e).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro j l
  simp [scoreCovarianceMatrix, covMat, ProbabilityTheory.covariance_comm]

/-- **Theorem 7.2 covariance-matrix face.**

The variance of every scalar projection of the score vector is the quadratic
form of Hansen's score covariance matrix `Ω`. This is the matrix-language
version of the scalar variance appearing in the one-dimensional CLT below. -/
theorem scoreProjection_variance_eq_quadraticScoreCovariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ) :
    Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a; μ] =
      a ⬝ᵥ (scoreCovarianceMatrix μ X e *ᵥ a) := by
  exact variance_dotProduct_eq_dotProduct_covMat_mulVec
    (μ := μ) (X := fun ω => e 0 ω • X 0 ω) a
    (fun j => scoreCoordinate_memLp_two (μ := μ) (X := X) (e := e) h j)

/-- Hansen's score covariance matrix has nonnegative quadratic forms under Assumption 7.2. -/
theorem scoreCovarianceMatrix_quadratic_nonneg
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ) :
    0 ≤ a ⬝ᵥ (scoreCovarianceMatrix μ X e *ᵥ a) := by
  rw [← scoreProjection_variance_eq_quadraticScoreCovariance
    (μ := μ) (X := X) (e := e) h a]
  exact ProbabilityTheory.variance_nonneg _ _

/-- Hansen's score covariance matrix `Ω` is positive semidefinite. -/
theorem scoreCovarianceMatrix_posSemidef
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) :
    (scoreCovarianceMatrix μ X e).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · simpa [Matrix.IsHermitian] using (scoreCovarianceMatrix_isSymm
      (μ := μ) (X := X) (e := e)).eq
  · intro a
    simpa using scoreCovarianceMatrix_quadratic_nonneg
      (μ := μ) (X := X) (e := e) h a

/-- The scalar OLS projection asymptotic variance is nonnegative. -/
theorem olsProjectionAsymptoticVariance_nonneg
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ) :
    0 ≤ olsProjectionAsymptoticVariance μ X e a := by
  exact scoreCovarianceMatrix_quadratic_nonneg
    (μ := μ) (X := X) (e := e) h (((popGram μ X)⁻¹)ᵀ *ᵥ a)

/-- Under the Chapter 7 orthogonality condition, each entry of `Ω` is the corresponding
score second moment. -/
theorem scoreCovarianceMatrix_apply_eq_secondMoment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (j l : k) :
    scoreCovarianceMatrix μ X e j l =
      ∫ ω, (e 0 ω • X 0 ω) j * (e 0 ω • X 0 ω) l ∂μ := by
  have hmean_j : μ[fun ω => (e 0 ω • X 0 ω) j] = 0 := by
    have hcoord := congrFun h.toSampleMomentAssumption71.orthogonality j
    rw [← integral_apply (μ := μ) (f := fun ω => e 0 ω • X 0 ω)
      h.toSampleMomentAssumption71.int_cross j]
    exact hcoord
  have hmean_l : μ[fun ω => (e 0 ω • X 0 ω) l] = 0 := by
    have hcoord := congrFun h.toSampleMomentAssumption71.orthogonality l
    rw [← integral_apply (μ := μ) (f := fun ω => e 0 ω • X 0 ω)
      h.toSampleMomentAssumption71.int_cross l]
    exact hcoord
  rw [scoreCovarianceMatrix, covMat, ProbabilityTheory.covariance_eq_sub
    (scoreCoordinate_memLp_two (μ := μ) (X := X) (e := e) h j)
    (scoreCoordinate_memLp_two (μ := μ) (X := X) (e := e) h l),
    hmean_j, hmean_l]
  simp [Pi.mul_apply]

/-- Hansen's true-error second-moment matrix `E[e₀² X₀X₀']`, equal to `Ω`
under orthogonality. We represent it as the outer product of the score vector
`e₀X₀`; entrywise this is the textbook `E[e₀² X₀j X₀ℓ]`. -/
noncomputable def scoreSecondMomentMatrix
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) : Matrix k k ℝ :=
  μ[fun ω => Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω)]

/-- The true-error score covariance sample average:
`n⁻¹∑ eᵢ² XᵢXᵢ'`, represented as `n⁻¹∑(eᵢXᵢ)(eᵢXᵢ)'`. This is the
first term in Hansen's proof of Theorem 7.6. -/
noncomputable def sampleScoreCovarianceIdeal (X : Matrix n k ℝ) (e : n → ℝ) :
    Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n, Matrix.vecMulVec (e i • X i) (e i • X i)

/-- The HC0 score covariance sample average using totalized OLS residuals:
`n⁻¹∑ êᵢ² XᵢXᵢ'`, represented as residual-score outer products. -/
noncomputable def sampleScoreCovarianceStar (X : Matrix n k ℝ) (y : n → ℝ) :
    Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n, Matrix.vecMulVec (olsResidualStar X y i • X i) (olsResidualStar X y i • X i)

/-- **Measurability of the feasible HC0 middle matrix from component measurability.**

If the individual regressors and errors are a.e. strongly measurable, then the
residual HC0 middle matrix `n⁻¹∑ êᵢ²XᵢXᵢ'` is a.e. strongly measurable. This is
a sufficient condition for the measurability premise in the feasible HC0
sandwich theorems. -/
theorem sampleScoreCovarianceStar_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleMomentAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  intro n
  have hBeta_meas := olsBetaStar_stack_aestronglyMeasurable
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel n
  have hdot_fixed_cont : Continuous (fun x : k → ℝ => x ⬝ᵥ β) := by
    simpa [dotProduct] using
      (continuous_finset_sum Finset.univ
        (fun i _ => (continuous_apply i).mul continuous_const))
  have hdot_pair_cont : Continuous (fun p : (k → ℝ) × (k → ℝ) => p.1 ⬝ᵥ p.2) := by
    simpa [dotProduct] using
      (continuous_finset_sum Finset.univ
        (fun i _ =>
          ((continuous_apply i).comp continuous_fst).mul
            ((continuous_apply i).comp continuous_snd)))
  have houter_cont : Continuous (fun v : k → ℝ => Matrix.vecMulVec v v) := by
    refine continuous_pi (fun a => ?_)
    refine continuous_pi (fun b => ?_)
    simpa [Matrix.vecMulVec_apply] using
      (continuous_apply a).mul (continuous_apply b)
  have hterm : ∀ i : Fin n, AEStronglyMeasurable
      (fun ω =>
        Matrix.vecMulVec
          (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i •
            stackRegressors X n ω i)
          (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i •
            stackRegressors X n ω i)) μ := by
    intro i
    have hXrow : AEStronglyMeasurable (fun ω => stackRegressors X n ω i) μ := by
      simpa [stackRegressors] using hX_meas i.val
    have hYrow : AEStronglyMeasurable (fun ω => stackOutcomes y n ω i) μ := by
      have hYexpr : AEStronglyMeasurable
          (fun ω => X i.val ω ⬝ᵥ β + e i.val ω) μ :=
        (hdot_fixed_cont.comp_aestronglyMeasurable (hX_meas i.val)).add (he_meas i.val)
      refine hYexpr.congr (ae_of_all μ (fun ω => ?_))
      simpa [stackOutcomes] using (hmodel i.val ω).symm
    have hfit : AEStronglyMeasurable
        (fun ω =>
          stackRegressors X n ω i ⬝ᵥ
            olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)) μ :=
      hdot_pair_cont.comp_aestronglyMeasurable (hXrow.prodMk hBeta_meas)
    have hres_exp : AEStronglyMeasurable
        (fun ω =>
          stackOutcomes y n ω i -
            stackRegressors X n ω i ⬝ᵥ
              olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω)) μ :=
      hYrow.sub hfit
    have hres : AEStronglyMeasurable
        (fun ω => olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i) μ := by
      refine hres_exp.congr (ae_of_all μ (fun ω => ?_))
      simp [olsResidualStar, Matrix.mulVec, dotProduct]
    have hscore : AEStronglyMeasurable
        (fun ω =>
          olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i •
            stackRegressors X n ω i) μ :=
      hres.smul hXrow
    exact houter_cont.comp_aestronglyMeasurable hscore
  have hsum : AEStronglyMeasurable
      (fun ω =>
        ∑ i : Fin n,
          Matrix.vecMulVec
            (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i •
              stackRegressors X n ω i)
            (olsResidualStar (stackRegressors X n ω) (stackOutcomes y n ω) i •
              stackRegressors X n ω i)) μ := by
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => hterm i)
  simpa [sampleScoreCovarianceStar] using
    AEStronglyMeasurable.const_smul hsum ((Fintype.card (Fin n) : ℝ)⁻¹)

/-- Totalized leverage `hᵢᵢ = xᵢ' (X'X)⁻¹ xᵢ` used by HC2/HC3.

This mirrors the textbook hat-matrix diagonal but uses the total matrix inverse,
so it is defined even on singular finite samples. -/
noncomputable def leverageStar (X : Matrix n k ℝ) (i : n) : ℝ :=
  X i ⬝ᵥ ((Xᵀ * X)⁻¹ *ᵥ X i)

/-- On nonsingular samples, the totalized leverage is the usual hat-matrix diagonal. -/
theorem leverageStar_eq_hatMatrix_diag
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] (i : n) :
    leverageStar X i = hatMatrix X i i := by
  unfold leverageStar hatMatrix
  rw [← invOf_eq_nonsing_inv, Matrix.dotProduct_mulVec]
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.transpose_apply]

/-- On nonsingular samples, leverage scores are nonnegative. -/
theorem leverageStar_nonneg_of_nonsingular
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] (i : n) :
    0 ≤ leverageStar X i := by
  classical
  rw [leverageStar_eq_hatMatrix_diag]
  exact diag_nonneg_of_symm_idempotent
    (hatMatrix X) (hatMatrix_transpose X) (hatMatrix_idempotent X) i

/-- On nonsingular samples, leverage scores are bounded above by one. -/
theorem leverageStar_le_one_of_nonsingular
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] (i : n) :
    leverageStar X i ≤ 1 := by
  classical
  have hdiag_nonneg : 0 ≤ annihilatorMatrix X i i :=
    diag_nonneg_of_symm_idempotent
      (annihilatorMatrix X) (annihilatorMatrix_transpose X)
      (annihilatorMatrix_idempotent X) i
  have hdiag_eq : annihilatorMatrix X i i = 1 - hatMatrix X i i := by
    simp [annihilatorMatrix, Matrix.sub_apply]
  rw [leverageStar_eq_hatMatrix_diag]
  linarith

/-- **Hansen Theorem 7.17, finite-sample leverage trace identity.**

On nonsingular samples, the totalized leverages sum to the number of regressors,
because they are the diagonal entries of the hat matrix. -/
theorem sum_leverageStar_eq_card_of_nonsingular
    (X : Matrix n k ℝ) [Invertible (Xᵀ * X)] :
    ∑ i : n, leverageStar X i = (Fintype.card k : ℝ) := by
  calc
    ∑ i : n, leverageStar X i
        = ∑ i : n, hatMatrix X i i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [leverageStar_eq_hatMatrix_diag]
    _ = Matrix.trace (hatMatrix X) := by
          simp [Matrix.trace]
    _ = (Fintype.card k : ℝ) := by
          simpa using hatMatrix_trace (X := X)

/-- **Hansen Theorem 7.17, average leverage identity.**

The sample average of the nonsingular leverage diagonal is `k / n`. This is the
finite-sample identity behind the asymptotic max-leverage discussion. -/
theorem average_leverageStar_eq_card_div_card_of_nonsingular
    (X : Matrix n k ℝ) [Nonempty n] [Invertible (Xᵀ * X)] :
    (Fintype.card n : ℝ)⁻¹ * ∑ i : n, leverageStar X i =
      (Fintype.card k : ℝ) / (Fintype.card n : ℝ) := by
  have hn : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [sum_leverageStar_eq_card_of_nonsingular]
  field_simp [hn]

/-- The HC2 residual-score covariance middle matrix
`n⁻¹∑ êᵢ²/(1-hᵢᵢ) · xᵢxᵢ'`, totalized through `leverageStar`. -/
noncomputable def sampleScoreCovarianceHC2Star (X : Matrix n k ℝ) (y : n → ℝ) :
    Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n,
      ((1 - leverageStar X i)⁻¹ * (olsResidualStar X y i) ^ 2) •
        Matrix.vecMulVec (X i) (X i)

/-- The HC3 residual-score covariance middle matrix
`n⁻¹∑ êᵢ²/(1-hᵢᵢ)² · xᵢxᵢ'`, totalized through `leverageStar`. -/
noncomputable def sampleScoreCovarianceHC3Star (X : Matrix n k ℝ) (y : n → ℝ) :
    Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n,
      (((1 - leverageStar X i)⁻¹) ^ 2 * (olsResidualStar X y i) ^ 2) •
        Matrix.vecMulVec (X i) (X i)

/-- HC2-minus-HC0 middle-matrix adjustment. Proving this is `oₚ(1)` is the
leverage-specific part of HC2 consistency. -/
noncomputable def sampleScoreCovarianceHC2AdjustmentStar
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  sampleScoreCovarianceHC2Star X y - sampleScoreCovarianceStar X y

/-- HC3-minus-HC0 middle-matrix adjustment. Proving this is `oₚ(1)` is the
leverage-specific part of HC3 consistency. -/
noncomputable def sampleScoreCovarianceHC3AdjustmentStar
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  sampleScoreCovarianceHC3Star X y - sampleScoreCovarianceStar X y

set_option linter.flexible false in
/-- **HC2 leverage-adjustment expansion, entrywise form.**

The HC2-minus-HC0 middle matrix is the sample average with scalar weight
`(1-hᵢᵢ)⁻¹ - 1` multiplying the usual residual-score outer product. -/
theorem sampleScoreCovarianceHC2AdjustmentStar_apply
    (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) :
    sampleScoreCovarianceHC2AdjustmentStar X y a b =
      (Fintype.card n : ℝ)⁻¹ *
        ∑ i : n, (((1 - leverageStar X i)⁻¹ - 1) *
          (olsResidualStar X y i) ^ 2 * X i a * X i b) := by
  simp [sampleScoreCovarianceHC2AdjustmentStar, sampleScoreCovarianceHC2Star,
    sampleScoreCovarianceStar, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

set_option linter.flexible false in
/-- **HC3 leverage-adjustment expansion, entrywise form.**

The HC3-minus-HC0 middle matrix is the sample average with scalar weight
`(1-hᵢᵢ)⁻² - 1` multiplying the usual residual-score outer product. -/
theorem sampleScoreCovarianceHC3AdjustmentStar_apply
    (X : Matrix n k ℝ) (y : n → ℝ) (a b : k) :
    sampleScoreCovarianceHC3AdjustmentStar X y a b =
      (Fintype.card n : ℝ)⁻¹ *
        ∑ i : n, ((((1 - leverageStar X i)⁻¹) ^ 2 - 1) *
          (olsResidualStar X y i) ^ 2 * X i a * X i b) := by
  simp [sampleScoreCovarianceHC3AdjustmentStar, sampleScoreCovarianceHC3Star,
    sampleScoreCovarianceStar, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

/-- **Theorem 7.6 residual-score expansion, entrywise form.**

Under the linear model, each residual score outer product decomposes into the
true-error score outer product, a cross term, and a quadratic estimation-error
term. This is the per-observation algebra behind feasible HC0 consistency. -/
theorem residualScoreOuter_linear_model_apply
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) (i : n) (a b : k) :
    Matrix.vecMulVec
        (olsResidualStar X (X *ᵥ β + e) i • X i)
        (olsResidualStar X (X *ᵥ β + e) i • X i) a b =
      Matrix.vecMulVec (e i • X i) (e i • X i) a b -
        (2 * e i * (X i ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β))) *
          Matrix.vecMulVec (X i) (X i) a b +
        (X i ⬝ᵥ (olsBetaStar X (X *ᵥ β + e) - β)) ^ 2 *
          Matrix.vecMulVec (X i) (X i) a b := by
  rw [olsResidualStar_linear_model_apply]
  simp [Matrix.vecMulVec_apply]
  ring

/-- Cross remainder in the HC0 residual-score expansion. -/
noncomputable def sampleScoreCovarianceCrossRemainder
    (X : Matrix n k ℝ) (e : n → ℝ) (d : k → ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n, (2 * e i * (X i ⬝ᵥ d)) • Matrix.vecMulVec (X i) (X i)

/-- Empirical third-moment weight multiplying one coordinate of `β̂ - β` in the
HC0 cross remainder. -/
noncomputable def sampleScoreCovarianceCrossWeight
    (X : Matrix n k ℝ) (e : n → ℝ) (a b l : k) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * ∑ i : n, 2 * e i * X i l * X i a * X i b

set_option linter.flexible false in
omit [DecidableEq k] in
/-- Coordinate representation of the HC0 cross remainder as coefficient error
times empirical third-moment weights. -/
theorem sampleScoreCovarianceCrossRemainder_apply_eq_sum_weight
    (X : Matrix n k ℝ) (e : n → ℝ) (d : k → ℝ) (a b : k) :
    sampleScoreCovarianceCrossRemainder X e d a b =
      ∑ l : k, d l * sampleScoreCovarianceCrossWeight X e a b l := by
  classical
  unfold sampleScoreCovarianceCrossRemainder sampleScoreCovarianceCrossWeight
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, dotProduct,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [Finset.sum_comm]

/-- Quadratic estimation-error remainder in the HC0 residual-score expansion. -/
noncomputable def sampleScoreCovarianceQuadraticRemainder
    (X : Matrix n k ℝ) (d : k → ℝ) : Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ∑ i : n, (X i ⬝ᵥ d) ^ 2 • Matrix.vecMulVec (X i) (X i)

/-- Empirical fourth-moment weight multiplying a pair of coefficient-error
coordinates in the HC0 quadratic remainder. -/
noncomputable def sampleScoreCovarianceQuadraticWeight
    (X : Matrix n k ℝ) (a b l m : k) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * ∑ i : n, X i l * X i m * X i a * X i b

set_option linter.flexible false in
omit [DecidableEq k] in
/-- Coordinate representation of the HC0 quadratic remainder as products of
coefficient errors times empirical fourth-moment weights. -/
theorem sampleScoreCovarianceQuadraticRemainder_apply_eq_sum_weight
    (X : Matrix n k ℝ) (d : k → ℝ) (a b : k) :
    sampleScoreCovarianceQuadraticRemainder X d a b =
      ∑ l : k, ∑ m : k,
        d l * d m * sampleScoreCovarianceQuadraticWeight X a b l m := by
  classical
  unfold sampleScoreCovarianceQuadraticRemainder sampleScoreCovarianceQuadraticWeight
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, dotProduct,
    Finset.mul_sum, pow_two, mul_assoc, mul_left_comm, mul_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]

/-- **Theorem 7.6 residual-score expansion, sample-average form.**

Under the linear model, the residual HC0 middle matrix equals the true-error
middle matrix minus a cross remainder plus a quadratic estimation-error
remainder. -/
theorem sampleScoreCovarianceStar_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) :
    sampleScoreCovarianceStar X (X *ᵥ β + e) =
      sampleScoreCovarianceIdeal X e -
        sampleScoreCovarianceCrossRemainder X e
          (olsBetaStar X (X *ᵥ β + e) - β) +
        sampleScoreCovarianceQuadraticRemainder X
          (olsBetaStar X (X *ᵥ β + e) - β) := by
  ext a b
  simp [sampleScoreCovarianceStar, sampleScoreCovarianceIdeal,
    sampleScoreCovarianceCrossRemainder, sampleScoreCovarianceQuadraticRemainder,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, Finset.mul_sum]
  ring_nf
  simp_rw [olsResidualStar_sq_linear_model_apply X β e]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [dotProduct_sub]
  ring_nf

/-- Additional WLLN assumptions for the true-error HC0 score covariance average. -/
structure SampleHC0Assumption76 (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ)
    extends SampleCLTAssumption72 μ X e where
  /-- Pairwise independence of the true-error score outer products. -/
  indep_score_outer : Pairwise ((· ⟂ᵢ[μ] ·) on
    (fun i ω => Matrix.vecMulVec (e i ω • X i ω) (e i ω • X i ω)))
  /-- Identical distribution of the true-error score outer products. -/
  ident_score_outer : ∀ i,
    IdentDistrib
      (fun ω => Matrix.vecMulVec (e i ω • X i ω) (e i ω • X i ω))
      (fun ω => Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω)) μ μ
  /-- Integrability of the true-error score outer product. -/
  int_score_outer :
    Integrable (fun ω => Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω)) μ

omit [Fintype k] [DecidableEq k] in
/-- The ideal HC0 score covariance average of stacked samples is the range-indexed
sample mean used by the WLLN. -/
theorem sampleScoreCovarianceIdeal_stack_eq_avg
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    sampleScoreCovarianceIdeal (stackRegressors X n ω) (stackErrors e n ω) =
      (n : ℝ)⁻¹ •
        ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (e i ω • X i ω) (e i ω • X i ω) := by
  unfold sampleScoreCovarianceIdeal stackErrors stackRegressors
  rw [Fintype.card_fin]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun i => Matrix.vecMulVec (e i ω • X i ω) (e i ω • X i ω)) n

/-- Under the HC0 WLLN assumptions, the true-error score covariance average
converges to `E[e₀²X₀X₀']`. -/
theorem sampleScoreCovarianceIdeal_stack_tendstoInMeasure_scoreSecondMomentMatrix
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) :
    TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceIdeal (stackRegressors X n ω) (stackErrors e n ω))
      atTop
      (fun _ => scoreSecondMomentMatrix μ X e) := by
  have hfun_eq : (fun n ω =>
        sampleScoreCovarianceIdeal (stackRegressors X n ω) (stackErrors e n ω)) =
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ •
        ∑ i ∈ Finset.range n,
          Matrix.vecMulVec (e i ω • X i ω) (e i ω • X i ω)) := by
    funext n ω
    rw [sampleScoreCovarianceIdeal_stack_eq_avg]
  rw [hfun_eq]
  exact tendstoInMeasure_wlln
    (fun i ω => Matrix.vecMulVec (e i ω • X i ω) (e i ω • X i ω))
    h.int_score_outer h.indep_score_outer h.ident_score_outer

/-- Under the HC0 assumptions and orthogonality, `E[e₀²X₀X₀']` is Hansen's
score covariance matrix `Ω`. -/
theorem scoreSecondMomentMatrix_eq_scoreCovarianceMatrix
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) :
    scoreSecondMomentMatrix μ X e = scoreCovarianceMatrix μ X e := by
  ext j l
  calc
    scoreSecondMomentMatrix μ X e j l
        = ∫ ω, (Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω)) j l ∂μ := by
          unfold scoreSecondMomentMatrix
          exact integral_apply_apply (μ := μ)
            (f := fun ω => Matrix.vecMulVec (e 0 ω • X 0 ω) (e 0 ω • X 0 ω))
            h.int_score_outer j l
    _ = ∫ ω, (e 0 ω • X 0 ω) j * (e 0 ω • X 0 ω) l ∂μ := by
          rfl
    _ = scoreCovarianceMatrix μ X e j l := by
          exact (scoreCovarianceMatrix_apply_eq_secondMoment
            (μ := μ) (X := X) (e := e) h.toSampleCLTAssumption72 j l).symm

/-- **Theorem 7.6 ideal-`Ω` WLLN.**

The true-error HC0 score covariance average converges in probability to Hansen's
score covariance matrix `Ω`. This is the first, WLLN-driven term in the proof
of heteroskedastic covariance consistency. -/
theorem sampleScoreCovarianceIdeal_stack_tendstoInMeasure_scoreCovarianceMatrix
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) :
    TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceIdeal (stackRegressors X n ω) (stackErrors e n ω))
      atTop
      (fun _ => scoreCovarianceMatrix μ X e) := by
  simpa [scoreSecondMomentMatrix_eq_scoreCovarianceMatrix (μ := μ) (X := X) (e := e) h]
    using sampleScoreCovarianceIdeal_stack_tendstoInMeasure_scoreSecondMomentMatrix
      (μ := μ) (X := X) (e := e) h

/-- **Hansen Theorem 7.6, residual HC0 middle-matrix assembly.**

If the cross and quadratic residual-score remainders in
`sampleScoreCovarianceStar_linear_model` are `oₚ(1)`, then the feasible HC0
middle matrix `n⁻¹∑êᵢ²XᵢXᵢ'` converges in probability to `Ω`. -/
theorem sampleScoreCovarianceStar_stack_tendstoInMeasure_scoreCovarianceMatrix_of_remainders
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hCross : TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceCrossRemainder
          (stackRegressors X n ω) (stackErrors e n ω)
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun _ => 0))
    (hQuad : TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticRemainder
          (stackRegressors X n ω)
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e) := by
  let ideal : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    sampleScoreCovarianceIdeal (stackRegressors X n ω) (stackErrors e n ω)
  let cross : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    sampleScoreCovarianceCrossRemainder
      (stackRegressors X n ω) (stackErrors e n ω)
      (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)
  let quad : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    sampleScoreCovarianceQuadraticRemainder
      (stackRegressors X n ω)
      (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)
  have hIdeal := sampleScoreCovarianceIdeal_stack_tendstoInMeasure_scoreCovarianceMatrix
    (μ := μ) (X := X) (e := e) h
  refine tendstoInMeasure_pi (μ := μ) (fun a => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun b => ?_)
  have hIdeal_ab : TendstoInMeasure μ
      (fun n ω => ideal n ω a b) atTop
      (fun _ => scoreCovarianceMatrix μ X e a b) := by
    simpa [ideal] using TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hIdeal a) b
  have hCross_ab : TendstoInMeasure μ
      (fun n ω => cross n ω a b) atTop (fun _ => 0) := by
    simpa [cross] using TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hCross a) b
  have hQuad_ab : TendstoInMeasure μ
      (fun n ω => quad n ω a b) atTop (fun _ => 0) := by
    simpa [quad] using TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hQuad a) b
  have hCentered := TendstoInMeasure.sub_limit_zero_real hIdeal_ab
  have hSub := TendstoInMeasure.sub_zero_real hCentered hCross_ab
  have hAdd := TendstoInMeasure.add_zero_real hSub hQuad_ab
  refine TendstoInMeasure.of_sub_limit_zero_real ?_
  refine hAdd.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  have hstack := stack_linear_model X e y β hmodel n ω
  have hexp := sampleScoreCovarianceStar_linear_model
    (stackRegressors X n ω) β (stackErrors e n ω)
  calc
    (ideal n ω a b - scoreCovarianceMatrix μ X e a b) -
        cross n ω a b + quad n ω a b
        =
        (ideal n ω - cross n ω + quad n ω) a b -
          scoreCovarianceMatrix μ X e a b := by
          simp [Matrix.sub_apply, Matrix.add_apply]
          ring
    _ = sampleScoreCovarianceStar (stackRegressors X n ω) (stackOutcomes y n ω) a b -
        scoreCovarianceMatrix μ X e a b := by
          rw [hstack, hexp]
          simp [ideal, cross, quad, hstack]

/-- **Theorem 7.6 cross-remainder control.**

If each empirical third-moment weight in the HC0 cross remainder is bounded in
probability, consistency of `β̂*` makes the cross remainder `oₚ(1)`. -/
theorem sampleScoreCovarianceCrossRemainder_stack_tendstoInMeasure_zero_of_bounded_weights
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceCrossRemainder
          (stackRegressors X n ω) (stackErrors e n ω)
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun _ => 0) := by
  have hBeta := olsBetaStar_stack_tendstoInMeasure_beta
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel
  refine tendstoInMeasure_pi (μ := μ) (fun a => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun b => ?_)
  have hTerm : ∀ l ∈ (Finset.univ : Finset k),
      TendstoInMeasure μ
        (fun n ω =>
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) l *
            sampleScoreCovarianceCrossWeight
              (stackRegressors X n ω) (stackErrors e n ω) a b l)
        atTop (fun _ => 0) := by
    intro l _
    have hBeta_l : TendstoInMeasure μ
        (fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) l)
        atTop (fun _ => β l) := by
      simpa using TendstoInMeasure.pi_apply hBeta l
    have hd_l : TendstoInMeasure μ
        (fun n ω =>
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) l)
        atTop (fun _ => 0) := by
      simpa [Pi.sub_apply] using TendstoInMeasure.sub_limit_zero_real hBeta_l
    exact TendstoInMeasure.mul_boundedInProbability hd_l (hWeight a b l)
  have hsum := tendstoInMeasure_finset_sum_zero_real (μ := μ)
    (s := (Finset.univ : Finset k))
    (X := fun l n ω =>
      (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) l *
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l)
    hTerm
  refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  exact (sampleScoreCovarianceCrossRemainder_apply_eq_sum_weight
    (stackRegressors X n ω) (stackErrors e n ω)
    (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) a b).symm

/-- **Theorem 7.6 quadratic-remainder control.**

If each empirical fourth-moment weight in the HC0 quadratic remainder is bounded
in probability, consistency of `β̂*` makes the quadratic remainder `oₚ(1)`. -/
theorem sampleScoreCovarianceQuadraticRemainder_stack_tendstoInMeasure_zero_of_bounded_weights
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticRemainder
          (stackRegressors X n ω)
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun _ => 0) := by
  let d : ℕ → Ω → k → ℝ := fun n ω =>
    olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β
  have hBeta := olsBetaStar_stack_tendstoInMeasure_beta
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel
  have hd : ∀ l : k, TendstoInMeasure μ (fun n ω => d n ω l) atTop (fun _ => 0) := by
    intro l
    have hBeta_l : TendstoInMeasure μ
        (fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) l)
        atTop (fun _ => β l) := by
      simpa using TendstoInMeasure.pi_apply hBeta l
    simpa [d, Pi.sub_apply] using TendstoInMeasure.sub_limit_zero_real hBeta_l
  refine tendstoInMeasure_pi (μ := μ) (fun a => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun b => ?_)
  have hInner : ∀ l ∈ (Finset.univ : Finset k),
      TendstoInMeasure μ
        (fun n ω => ∑ m : k,
          d n ω l * d n ω m *
            sampleScoreCovarianceQuadraticWeight
              (stackRegressors X n ω) a b l m)
        atTop (fun _ => 0) := by
    intro l _
    have hTerm : ∀ m ∈ (Finset.univ : Finset k),
        TendstoInMeasure μ
          (fun n ω =>
            d n ω l * d n ω m *
              sampleScoreCovarianceQuadraticWeight
                (stackRegressors X n ω) a b l m)
          atTop (fun _ => 0) := by
      intro m _
      have hprod := TendstoInMeasure.mul_zero_real (hd l) (hd m)
      exact TendstoInMeasure.mul_boundedInProbability hprod (hWeight a b l m)
    simpa using tendstoInMeasure_finset_sum_zero_real (μ := μ)
      (s := (Finset.univ : Finset k))
      (X := fun m n ω =>
        d n ω l * d n ω m *
          sampleScoreCovarianceQuadraticWeight
            (stackRegressors X n ω) a b l m)
      hTerm
  have hsum := tendstoInMeasure_finset_sum_zero_real (μ := μ)
    (s := (Finset.univ : Finset k))
    (X := fun l n ω => ∑ m : k,
      d n ω l * d n ω m *
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)
    hInner
  refine hsum.congr_left (fun n => ae_of_all μ (fun ω => ?_))
  exact (sampleScoreCovarianceQuadraticRemainder_apply_eq_sum_weight
    (stackRegressors X n ω) (d n ω) a b).symm

/-- **Hansen Theorem 7.6, residual HC0 middle matrix under bounded weights.**

The feasible HC0 middle matrix converges to `Ω` when the empirical third- and
fourth-moment weights appearing in the residual-score remainders are bounded in
probability. -/
theorem sampleScoreCovarianceStar_stack_tendstoInMeasure_scoreCovarianceMatrix_of_bounded_weights
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e) := by
  have hCross :=
    sampleScoreCovarianceCrossRemainder_stack_tendstoInMeasure_zero_of_bounded_weights
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hCrossWeight
  have hQuad :=
    sampleScoreCovarianceQuadraticRemainder_stack_tendstoInMeasure_zero_of_bounded_weights
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hQuadWeight
  exact sampleScoreCovarianceStar_stack_tendstoInMeasure_scoreCovarianceMatrix_of_remainders
    (μ := μ) (X := X) (e := e) (y := y) h β hmodel hCross hQuad

/-- **Hansen Theorem 7.7, HC2 middle matrix from HC0 plus adjustment.**

If the feasible HC0 middle matrix converges to `Ω` and the HC2 leverage
adjustment is `oₚ(1)`, then the HC2 middle matrix also converges to `Ω`. This
isolates the exact leverage remainder left for the HC2 proof. -/
theorem sampleScoreCovarianceHC2Star_stack_tendstoInMeasure_scoreCovarianceMatrix_of_adjustment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hHC0_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hAdj_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC2AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hHC0 : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e))
    (hAdj : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceHC2AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceHC2Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e) := by
  have hsum := tendstoInMeasure_add hHC0_meas hAdj_meas hHC0 hAdj
  simpa [sampleScoreCovarianceHC2AdjustmentStar, sub_eq_add_neg, add_assoc,
    add_comm, add_left_comm] using hsum

/-- **Hansen Theorem 7.7, HC3 middle matrix from HC0 plus adjustment.**

If the feasible HC0 middle matrix converges to `Ω` and the HC3 leverage
adjustment is `oₚ(1)`, then the HC3 middle matrix also converges to `Ω`. -/
theorem sampleScoreCovarianceHC3Star_stack_tendstoInMeasure_scoreCovarianceMatrix_of_adjustment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hHC0_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hAdj_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC3AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hHC0 : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e))
    (hAdj : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceHC3AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceHC3Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e) := by
  have hsum := tendstoInMeasure_add hHC0_meas hAdj_meas hHC0 hAdj
  simpa [sampleScoreCovarianceHC3AdjustmentStar, sub_eq_add_neg, add_assoc,
    add_comm, add_left_comm] using hsum

/-- Hansen's heteroskedastic asymptotic covariance matrix
`V_β := Q⁻¹ Ω Q⁻¹`. -/
noncomputable def heteroskedasticAsymptoticCovariance
    (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) : Matrix k k ℝ :=
  (popGram μ X)⁻¹ * scoreCovarianceMatrix μ X e * (popGram μ X)⁻¹

/-- **Homoskedastic covariance bridge.**

If the score covariance satisfies the homoskedastic moment identity
`Ω = σ² Q`, then Hansen's homoskedastic asymptotic covariance `σ²Q⁻¹`
equals the robust sandwich covariance `Q⁻¹ΩQ⁻¹`. -/
theorem homoskedasticAsymptoticCovariance_eq_heteroskedasticAsymptoticCovariance
    {μ : Measure Ω}
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (hQ : IsUnit (popGram μ X).det)
    (hΩ : scoreCovarianceMatrix μ X e = errorVariance μ e • popGram μ X) :
    homoskedasticAsymptoticCovariance μ X e =
      heteroskedasticAsymptoticCovariance μ X e := by
  let Q : Matrix k k ℝ := popGram μ X
  let σ2 : ℝ := errorVariance μ e
  calc
    homoskedasticAsymptoticCovariance μ X e
        = σ2 • Q⁻¹ := by
          simp [homoskedasticAsymptoticCovariance, Q, σ2]
    _ = Q⁻¹ * (σ2 • Q) * Q⁻¹ := by
          have hright : Q⁻¹ * (σ2 • Q) * Q⁻¹ = σ2 • Q⁻¹ := by
            rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.nonsing_inv_mul Q hQ]
            simp
          exact hright.symm
    _ = heteroskedasticAsymptoticCovariance μ X e := by
          simp [heteroskedasticAsymptoticCovariance, hΩ, Q, σ2, Matrix.mul_assoc]

/-- The scalar projection variance agrees with the sandwich covariance quadratic form. -/
theorem olsProjectionAsymptoticVariance_eq_quadratic_heteroskedasticAsymptoticCovariance
    {μ : Measure Ω}
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (hX : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ)
    (a : k → ℝ) :
    olsProjectionAsymptoticVariance μ X e a =
      a ⬝ᵥ (heteroskedasticAsymptoticCovariance μ X e *ᵥ a) := by
  let A : Matrix k k ℝ := (popGram μ X)⁻¹
  let Ωm : Matrix k k ℝ := scoreCovarianceMatrix μ X e
  have hA : Aᵀ = A := (popGram_inv_isSymm μ X hX).eq
  calc
    olsProjectionAsymptoticVariance μ X e a
        = (A *ᵥ a) ⬝ᵥ (Ωm *ᵥ (A *ᵥ a)) := by
          simp [olsProjectionAsymptoticVariance, A, Ωm, hA]
    _ = (Matrix.vecMul a A) ⬝ᵥ (Ωm *ᵥ (A *ᵥ a)) := by
          rw [vecMul_eq_mulVec_transpose, hA]
    _ = a ⬝ᵥ (A *ᵥ (Ωm *ᵥ (A *ᵥ a))) := by
          rw [← Matrix.dotProduct_mulVec]
    _ = a ⬝ᵥ ((A * Ωm * A) *ᵥ a) := by
          simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = a ⬝ᵥ (heteroskedasticAsymptoticCovariance μ X e *ᵥ a) := by
          simp [heteroskedasticAsymptoticCovariance, A, Ωm, Matrix.mul_assoc]

/-- Linear-map scalar quadratic forms match the corresponding OLS projection variance. -/
theorem linearMapCovariance_quadratic_eq_olsProjectionAsymptoticVariance
    {μ : Measure Ω}
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q]
    (hX : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ)
    (R : Matrix q k ℝ) (c : q → ℝ) :
    c ⬝ᵥ ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) *ᵥ c) =
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ c) := by
  rw [olsProjectionAsymptoticVariance_eq_quadratic_heteroskedasticAsymptoticCovariance hX]
  let V : Matrix k k ℝ := heteroskedasticAsymptoticCovariance μ X e
  calc
    c ⬝ᵥ ((R * V * Rᵀ) *ᵥ c)
        = c ⬝ᵥ (R *ᵥ (V *ᵥ (Rᵀ *ᵥ c))) := by
          simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (Rᵀ *ᵥ c) ⬝ᵥ (V *ᵥ (Rᵀ *ᵥ c)) := by
          rw [Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose]
    _ = (Rᵀ *ᵥ c) ⬝ᵥ
        (heteroskedasticAsymptoticCovariance μ X e *ᵥ (Rᵀ *ᵥ c)) := by
          simp [V]

/-- For a one-row linear map, the sole sandwich-covariance entry is the projection variance. -/
theorem linearMapCovariance_unit_apply_eq_olsProjectionAsymptoticVariance
    {μ : Measure Ω}
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (hX : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ)
    (R : Matrix Unit k ℝ) :
    (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () =
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) := by
  simpa [dotProduct, Matrix.mulVec] using
    linearMapCovariance_quadratic_eq_olsProjectionAsymptoticVariance
      (μ := μ) (X := X) (e := e) hX R (fun _ : Unit => 1)

/-- **Generic sandwich CMT for Chapter 7 covariance estimators.**

Any totalized covariance estimator with middle matrix converging in probability
to `Ω` inherits the sandwich probability limit `Q⁻¹ Ω Q⁻¹`. This factors the
shared continuous-mapping step out of HC0/HC1/HC2/HC3-style estimators, leaving
each theorem to prove only the consistency of its own middle matrix. -/
theorem sandwichCovarianceStar_tendstoInMeasure_of_middle
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e)
    {middle : ℕ → Ω → Matrix k k ℝ}
    (hmiddle_meas : ∀ n, AEStronglyMeasurable (middle n) μ)
    (hmiddle : TendstoInMeasure μ middle atTop
      (fun _ => scoreCovarianceMatrix μ X e)) :
    TendstoInMeasure μ
      (fun n ω =>
        (sampleGram (stackRegressors X n ω))⁻¹ * middle n ω *
          (sampleGram (stackRegressors X n ω))⁻¹)
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  let invGram : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    (sampleGram (stackRegressors X n ω))⁻¹
  have hGram_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    intro n
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hInv_meas : ∀ n, AEStronglyMeasurable (invGram n) μ := by
    intro n
    exact aestronglyMeasurable_matrix_inv (hGram_meas n)
  have hInv := sampleGramInv_stackRegressors_tendstoInMeasure_popGramInv
    (μ := μ) (X := X) (e := e) h
  have hLeft := tendstoInMeasure_matrix_mul
    (μ := μ) (A := invGram) (B := middle)
    (Ainf := fun _ : Ω => (popGram μ X)⁻¹)
    (Binf := fun _ : Ω => scoreCovarianceMatrix μ X e)
    hInv_meas hmiddle_meas (by simpa [invGram] using hInv) hmiddle
  have hLeft_meas : ∀ n, AEStronglyMeasurable (fun ω => invGram n ω * middle n ω) μ := by
    intro n
    have hprod : AEStronglyMeasurable (fun ω => (invGram n ω, middle n ω)) μ :=
      (hInv_meas n).prodMk (hmiddle_meas n)
    have hcont : Continuous (fun p : Matrix k k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  have hFull := tendstoInMeasure_matrix_mul
    (μ := μ) (A := fun n ω => invGram n ω * middle n ω) (B := invGram)
    (Ainf := fun _ : Ω => (popGram μ X)⁻¹ * scoreCovarianceMatrix μ X e)
    (Binf := fun _ : Ω => (popGram μ X)⁻¹)
    hLeft_meas hInv_meas
    (by simpa [Matrix.mul_assoc] using hLeft) (by simpa [invGram] using hInv)
  simpa [heteroskedasticAsymptoticCovariance, invGram, Matrix.mul_assoc] using hFull

omit [DecidableEq k] in
/-- **Hansen Theorem 7.10, linear covariance continuous mapping.**

If a covariance estimator `V̂β` converges in probability to `Vβ`, then the
linear-function covariance estimator `R V̂β R'` converges to `R Vβ R'`. This is
the matrix CMT core behind covariance estimation for fixed linear functions of
parameters. -/
theorem linearMapCovariance_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {q : Type*} [Fintype q]
    {Vhat : ℕ → Ω → Matrix k k ℝ} {V : Matrix k k ℝ}
    (R : Matrix q k ℝ)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V)) :
    TendstoInMeasure μ
      (fun n ω => R * Vhat n ω * Rᵀ)
      atTop (fun _ => R * V * Rᵀ) := by
  have hR_meas : ∀ _ : ℕ, AEStronglyMeasurable (fun _ : Ω => R) μ :=
    fun _ => aestronglyMeasurable_const
  have hR_conv : TendstoInMeasure μ
      (fun _ : ℕ => fun _ : Ω => R) atTop (fun _ : Ω => R) :=
    tendstoInMeasure_of_tendsto_ae hR_meas
      (ae_of_all μ (fun _ => tendsto_const_nhds))
  have hRt_meas : ∀ _ : ℕ, AEStronglyMeasurable (fun _ : Ω => Rᵀ) μ :=
    fun _ => aestronglyMeasurable_const
  have hRt_conv : TendstoInMeasure μ
      (fun _ : ℕ => fun _ : Ω => Rᵀ) atTop (fun _ : Ω => Rᵀ) :=
    tendstoInMeasure_of_tendsto_ae hRt_meas
      (ae_of_all μ (fun _ => tendsto_const_nhds))
  have hLeft := tendstoInMeasure_matrix_mul_rect
    (μ := μ)
    (A := fun _ : ℕ => fun _ : Ω => R)
    (B := Vhat)
    (Ainf := fun _ : Ω => R)
    (Binf := fun _ : Ω => V)
    hR_meas hV_meas hR_conv hV
  have hLeft_meas : ∀ n, AEStronglyMeasurable (fun ω => R * Vhat n ω) μ := by
    intro n
    have hprod : AEStronglyMeasurable (fun ω => (R, Vhat n ω)) μ :=
      aestronglyMeasurable_const.prodMk (hV_meas n)
    have hcont : Continuous (fun p : Matrix q k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  have hFull := tendstoInMeasure_matrix_mul_rect
    (μ := μ)
    (A := fun n ω => R * Vhat n ω)
    (B := fun _ : ℕ => fun _ : Ω => Rᵀ)
    (Ainf := fun _ : Ω => R * V)
    (Binf := fun _ : Ω => Rᵀ)
    hLeft_meas hRt_meas hLeft hRt_conv
  simpa [Matrix.mul_assoc] using hFull

omit [DecidableEq k] in
/-- AEMeasurability of a fixed linear covariance transform `R V Rᵀ`. -/
theorem linearMapCovariance_aestronglyMeasurable
    {μ : Measure Ω}
    {q : Type*}
    {Vhat : Ω → Matrix k k ℝ}
    (R : Matrix q k ℝ)
    (hV_meas : AEStronglyMeasurable Vhat μ) :
    AEStronglyMeasurable (fun ω => R * Vhat ω * Rᵀ) μ := by
  have hLeft : AEStronglyMeasurable (fun ω => R * Vhat ω) μ := by
    have hprod : AEStronglyMeasurable (fun ω => (R, Vhat ω)) μ :=
      aestronglyMeasurable_const.prodMk hV_meas
    have hcont : Continuous (fun p : Matrix q k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  have hprod : AEStronglyMeasurable (fun ω => (R * Vhat ω, Rᵀ)) μ :=
    hLeft.prodMk aestronglyMeasurable_const
  have hcont : Continuous (fun p : Matrix q k ℝ × Matrix k q ℝ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  exact hcont.comp_aestronglyMeasurable hprod

omit [DecidableEq k] in
/-- **Hansen §7.11, asymptotic standard-error CMT.**

If `R V̂β Rᵀ` estimates the asymptotic covariance of a fixed linear function
`R β`, then the square root of any diagonal element converges to the matching
population standard-error scale. This is the standard-error continuous-mapping
face used before forming t-statistics. -/
theorem linearMapCovarianceStdError_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {q : Type*} [Finite q]
    {Vhat : ℕ → Ω → Matrix k k ℝ} {V : Matrix k k ℝ}
    (R : Matrix q k ℝ) (j : q)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V)) :
    TendstoInMeasure μ
      (fun n ω => Real.sqrt ((R * Vhat n ω * Rᵀ) j j))
      atTop (fun _ => Real.sqrt ((R * V * Rᵀ) j j)) := by
  letI : Fintype q := Fintype.ofFinite q
  have hCov := linearMapCovariance_tendstoInMeasure
    (μ := μ) (R := R) hV_meas hV
  have hCov_meas : ∀ n, AEStronglyMeasurable
      (fun ω => R * Vhat n ω * Rᵀ) μ :=
    fun n => linearMapCovariance_aestronglyMeasurable
      (μ := μ) (R := R) (hV_meas n)
  have hentry_meas : ∀ n, AEStronglyMeasurable
      (fun ω => (R * Vhat n ω * Rᵀ) j j) μ := by
    intro n
    have hentry_cont : Continuous (fun M : Matrix q q ℝ => M j j) :=
      (continuous_apply j).comp (continuous_apply j)
    exact hentry_cont.comp_aestronglyMeasurable (hCov_meas n)
  have hentry : TendstoInMeasure μ
      (fun n ω => (R * Vhat n ω * Rᵀ) j j)
      atTop (fun _ => (R * V * Rᵀ) j j) :=
    TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hCov j) j
  exact tendstoInMeasure_continuous_comp hentry_meas hentry Real.continuous_sqrt

/-- **Hansen Theorem 7.10, homoskedastic covariance for fixed linear functions.**

For a fixed linear map `R`, the totalized homoskedastic plug-in covariance
estimator for `R β` converges to `R V⁰β Rᵀ`. -/
theorem linearMap_olsHomoskedasticCovarianceStar_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q]
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    TendstoInMeasure μ
      (fun n ω =>
        R * olsHomoskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)
      atTop (fun _ => R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) := by
  have hV_meas :=
    olsHomoskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hV :=
    olsHomoskedasticCovarianceStar_tendstoInMeasure
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel
  exact linearMapCovariance_tendstoInMeasure
    (μ := μ) (R := R)
    (Vhat := fun n ω =>
      olsHomoskedasticCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
    (V := homoskedasticAsymptoticCovariance μ X e)
    hV_meas hV

/-- **Hansen §7.11/§7.17, homoskedastic standard errors for fixed linear functions.**

The square root of a diagonal element of `R V̂⁰β Rᵀ` converges to the
corresponding population homoskedastic scale. -/
theorem olsHomoskedasticLinearStdErrorStar_tendstoInMeasure
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Finite q]
    (h : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ) (j : q)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    TendstoInMeasure μ
      (fun n ω =>
        Real.sqrt ((R * olsHomoskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) j j))
      atTop (fun _ =>
        Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) j j)) := by
  have hV_meas :=
    olsHomoskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hV :=
    olsHomoskedasticCovarianceStar_tendstoInMeasure
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel
  exact linearMapCovarianceStdError_tendstoInMeasure
    (μ := μ) (R := R) (j := j)
    (Vhat := fun n ω =>
      olsHomoskedasticCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
    (V := homoskedasticAsymptoticCovariance μ X e)
    hV_meas hV

/-- **Scalar Slutsky division with a positive denominator limit.**

If `Xₙ ⇒ Z` and `Yₙ →ₚ c` for `c > 0`, then `Xₙ / Yₙ ⇒ Z / c`.
The proof clips the denominator at `c / 2` to get a globally continuous map,
then removes the clip because the event `Yₙ < c / 2` has vanishing
probability. -/
theorem tendstoInDistribution_div_of_tendstoInMeasure_const_pos
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hX : TendstoInDistribution X atTop Z (fun _ => μ) ν)
    (hY : TendstoInMeasure μ Y atTop (fun _ => c))
    (hY_meas : ∀ n, AEMeasurable (Y n) μ)
    (hdiv_meas : ∀ n, AEMeasurable (fun ω => X n ω / Y n ω) μ) :
    TendstoInDistribution
      (fun n ω => X n ω / Y n ω)
      atTop (fun ω => Z ω / c) (fun _ => μ) ν := by
  let c₂ : ℝ := c / 2
  have hc₂ : 0 < c₂ := by positivity
  have hmax_c : max c c₂ = c := by
    have hc₂_le_c : c₂ ≤ c := by
      dsimp [c₂]
      linarith
    exact max_eq_left hc₂_le_c
  have hg : Continuous (fun p : ℝ × ℝ => p.1 / max p.2 c₂) := by
    refine continuous_fst.div (continuous_snd.max continuous_const) ?_
    intro p
    exact ne_of_gt (lt_of_lt_of_le hc₂ (le_max_right p.2 c₂))
  have hclip : TendstoInDistribution
      (fun n ω => X n ω / max (Y n ω) c₂)
      atTop (fun ω => Z ω / c) (fun _ => μ) ν := by
    have hraw := hX.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ => p.1 / max p.2 c₂) hg hY hY_meas
    simpa [Function.comp_def, c₂, hmax_c] using hraw
  have hdiff : TendstoInMeasure μ
      (fun n ω => X n ω / Y n ω - X n ω / max (Y n ω) c₂)
      atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have hYdist := hY
    rw [tendstoInMeasure_iff_dist] at hYdist
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hYdist c₂ hc₂) (fun _ => zero_le _) (fun n => ?_)
    refine measure_mono (fun ω hω => ?_)
    by_contra hnot
    have hdist_lt : dist (Y n ω) c < c₂ := not_le.mp hnot
    have hY_gt : c₂ < Y n ω := by
      rw [Real.dist_eq] at hdist_lt
      have hbounds := abs_lt.mp hdist_lt
      have hc_sub : c - c₂ = c₂ := by
        dsimp [c₂]
        ring
      linarith [hbounds.1, hc_sub]
    have hmax : max (Y n ω) c₂ = Y n ω := max_eq_left hY_gt.le
    have hdiff_zero : X n ω / Y n ω - X n ω / max (Y n ω) c₂ = 0 := by
      simp [hmax]
    have hε_le_zero : ε ≤ 0 := by
      simpa [Real.dist_eq, hdiff_zero] using hω
    exact (not_le_of_gt hε) hε_le_zero
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun n ω => X n ω / max (Y n ω) c₂)
    (Y := fun n ω => X n ω / Y n ω)
    (Z := fun ω => Z ω / c)
    hclip hdiff hdiv_meas

/-- A zero-mean Gaussian with variance `c²`, divided by positive `c`, is standard normal. -/
theorem hasLaw_gaussianReal_div_const_standard
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {Z : Ω' → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hZ : HasLaw Z (gaussianReal 0 (c ^ 2).toNNReal) ν) :
    HasLaw (fun ω => Z ω / c) (gaussianReal 0 1) ν := by
  have hdiv := gaussianReal_div_const hZ c
  convert hdiv using 1
  · rw [gaussianReal_ext_iff]
    constructor
    · simp
    · rw [Real.toNNReal_of_nonneg (sq_nonneg c)]
      ext
      simp [hc.ne']

/-- Version of Gaussian normalization with an explicitly identified variance. -/
theorem hasLaw_gaussianReal_div_const_standard_of_variance_eq
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {Z : Ω' → ℝ} {σ2 c : ℝ}
    (hc : 0 < c)
    (hσ : σ2 = c ^ 2)
    (hZ : HasLaw Z (gaussianReal 0 σ2.toNNReal) ν) :
    HasLaw (fun ω => Z ω / c) (gaussianReal 0 1) ν := by
  have hZ' : HasLaw Z (gaussianReal 0 (c ^ 2).toNNReal) ν := by
    rwa [hσ] at hZ
  exact hasLaw_gaussianReal_div_const_standard hc hZ'

/-- Scaling the identity under a standard normal law gives a zero-mean Gaussian
with variance `c²`. -/
theorem hasLaw_const_mul_id_gaussianReal_of_variance_eq
    {σ2 c : ℝ}
    (hσ : σ2 = c ^ 2) :
    HasLaw (fun x : ℝ => c * x) (gaussianReal 0 σ2.toNNReal) (gaussianReal 0 1) := by
  have hid : HasLaw (fun x : ℝ => x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 1))
  have hscale := gaussianReal_const_mul hid c
  convert hscale using 1
  · rw [gaussianReal_ext_iff]
    constructor
    · ring
    · rw [hσ, Real.toNNReal_of_nonneg (sq_nonneg c)]
      simp

omit [Fintype k] [DecidableEq k] in
/-- **Hansen Theorem 7.3/7.13, generic matrix-vector distributional CMT.**

If a vector statistic `Tₙ` converges in distribution to `Z` and a random matrix
`Aₙ` converges in probability to a constant matrix `A`, then the transformed
statistic `AₙTₙ` converges in distribution to `AZ`. This is the vector Slutsky
bridge used to move from score CLTs to feasible OLS and Wald statistics. -/
theorem matrixMulVec_tendstoInDistribution_of_vector_and_matrix
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {q : Type*} [Fintype q]
    {T : ℕ → Ω → q → ℝ} {Z : Ω' → q → ℝ}
    {Ahat : ℕ → Ω → Matrix q q ℝ} {A : Matrix q q ℝ}
    (hT : TendstoInDistribution T atTop Z (fun _ => μ) ν)
    (hA_meas : ∀ n, AEStronglyMeasurable (Ahat n) μ)
    (hA : TendstoInMeasure μ Ahat atTop (fun _ => A)) :
    TendstoInDistribution
      (fun n ω => Ahat n ω *ᵥ T n ω)
      atTop (fun ω => A *ᵥ Z ω) (fun _ => μ) ν := by
  letI : BorelSpace (Matrix q q ℝ) := ⟨rfl⟩
  have hA_meas' : ∀ n, AEMeasurable (Ahat n) μ :=
    fun n => (hA_meas n).aemeasurable
  have hcont : Continuous (fun p : (q → ℝ) × Matrix q q ℝ => p.2 *ᵥ p.1) :=
    Continuous.matrix_mulVec continuous_snd continuous_fst
  have hraw := hT.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : (q → ℝ) × Matrix q q ℝ => p.2 *ᵥ p.1)
    hcont hA hA_meas'
  simpa [Function.comp_def] using hraw

omit [Fintype k] [DecidableEq k] in
/-- **Hansen Theorem 7.3/7.13, inverse matrix-vector distributional CMT.**

If `Tₙ ⇒ Z`, `Aₙ →ₚ A`, and the limiting matrix `A` is nonsingular, then
`Aₙ⁻¹Tₙ ⇒ A⁻¹Z`. This is the reusable random-inverse Slutsky bridge needed for
the feasible OLS leading term `Q̂ₙ⁻¹√nĝₙ(e)`. -/
theorem matrixInvMulVec_tendstoInDistribution_of_vector_and_matrix
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {q : Type*} [Fintype q] [DecidableEq q]
    {T : ℕ → Ω → q → ℝ} {Z : Ω' → q → ℝ}
    {Ahat : ℕ → Ω → Matrix q q ℝ} {A : Matrix q q ℝ}
    (hT : TendstoInDistribution T atTop Z (fun _ => μ) ν)
    (hA_meas : ∀ n, AEStronglyMeasurable (Ahat n) μ)
    (hA : TendstoInMeasure μ Ahat atTop (fun _ => A))
    (hA_nonsing : IsUnit A.det) :
    TendstoInDistribution
      (fun n ω => (Ahat n ω)⁻¹ *ᵥ T n ω)
      atTop (fun ω => A⁻¹ *ᵥ Z ω) (fun _ => μ) ν := by
  letI : BorelSpace (Matrix q q ℝ) := ⟨rfl⟩
  have hInv : TendstoInMeasure μ
      (fun n ω => (Ahat n ω)⁻¹) atTop (fun _ => A⁻¹) :=
    tendstoInMeasure_matrix_inv (μ := μ) hA_meas hA (fun _ => hA_nonsing)
  have hInv_meas : ∀ n, AEStronglyMeasurable (fun ω => (Ahat n ω)⁻¹) μ :=
    fun n => aestronglyMeasurable_matrix_inv (hA_meas n)
  exact matrixMulVec_tendstoInDistribution_of_vector_and_matrix
    (μ := μ) (ν := ν) (T := T) (Z := Z)
    (Ahat := fun n ω => (Ahat n ω)⁻¹) (A := A⁻¹)
    hT hInv_meas hInv

omit [Fintype k] [DecidableEq k] in
/-- **Hansen Theorem 7.13, conditional multivariate Wald CMT.**

If a scaled vector statistic `Tₙ` converges in distribution to `Z` and the
plug-in covariance matrix `V̂ₙ` converges in probability to a nonsingular
constant `V`, then the Wald quadratic form formed with `V̂ₙ⁻¹` converges in
distribution to the matching population quadratic form. This is the generic
continuous-mapping/Slutsky bridge needed before the final chi-square law
identification. -/
theorem waldQuadraticForm_tendstoInDistribution_of_vector_and_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {q : Type*} [Fintype q] [DecidableEq q]
    {T : ℕ → Ω → q → ℝ} {Z : Ω' → q → ℝ}
    {Vhat : ℕ → Ω → Matrix q q ℝ} {V : Matrix q q ℝ}
    (hT : TendstoInDistribution T atTop Z (fun _ => μ) ν)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det) :
    TendstoInDistribution
      (fun n ω => T n ω ⬝ᵥ ((Vhat n ω)⁻¹ *ᵥ T n ω))
      atTop
      (fun ω => Z ω ⬝ᵥ (V⁻¹ *ᵥ Z ω))
      (fun _ => μ) ν := by
  letI : BorelSpace (Matrix q q ℝ) := ⟨rfl⟩
  have hInv : TendstoInMeasure μ
      (fun n ω => (Vhat n ω)⁻¹) atTop (fun _ => V⁻¹) :=
    tendstoInMeasure_matrix_inv (μ := μ) hV_meas hV (fun _ => hV_nonsing)
  have hInv_meas : ∀ n, AEMeasurable (fun ω => (Vhat n ω)⁻¹) μ :=
    fun n => (aestronglyMeasurable_matrix_inv (hV_meas n)).aemeasurable
  have hdot : Continuous (fun p : (q → ℝ) × (q → ℝ) => p.1 ⬝ᵥ p.2) := by
    classical
    simpa [dotProduct] using
      (continuous_finset_sum Finset.univ (fun i _ =>
        (((continuous_apply i).comp continuous_fst).mul
          ((continuous_apply i).comp continuous_snd))))
  have hmulVec : Continuous
      (fun p : (q → ℝ) × Matrix q q ℝ => p.2 *ᵥ p.1) :=
    Continuous.matrix_mulVec continuous_snd continuous_fst
  have hquad : Continuous
      (fun p : (q → ℝ) × Matrix q q ℝ => p.1 ⬝ᵥ (p.2 *ᵥ p.1)) :=
    hdot.comp (continuous_fst.prodMk hmulVec)
  have hraw := hT.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : (q → ℝ) × Matrix q q ℝ => p.1 ⬝ᵥ (p.2 *ᵥ p.1))
    hquad hInv hInv_meas
  simpa [Function.comp_def] using hraw

/-- Infeasible totalized HC0 sandwich estimator using true errors:
`Q̂⁻¹ (n⁻¹∑eᵢ²XᵢXᵢ') Q̂⁻¹`. -/
noncomputable def olsHeteroskedasticCovarianceIdealStar
    (X : Matrix n k ℝ) (e : n → ℝ) : Matrix k k ℝ :=
  (sampleGram X)⁻¹ * sampleScoreCovarianceIdeal X e * (sampleGram X)⁻¹

/-- Feasible totalized HC0 sandwich estimator using OLS residuals:
`Q̂⁻¹ (n⁻¹∑êᵢ²XᵢXᵢ') Q̂⁻¹`. -/
noncomputable def olsHeteroskedasticCovarianceStar
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  (sampleGram X)⁻¹ * sampleScoreCovarianceStar X y * (sampleGram X)⁻¹

/-- Totalized HC1 asymptotic sandwich estimator:
`(n / (n-k)) V̂_HC0`. -/
noncomputable def olsHeteroskedasticCovarianceHC1Star
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  ((Fintype.card n : ℝ) / (Fintype.card n - Fintype.card k : ℝ)) •
    olsHeteroskedasticCovarianceStar X y

/-- Totalized HC2 asymptotic sandwich estimator. -/
noncomputable def olsHeteroskedasticCovarianceHC2Star
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  (sampleGram X)⁻¹ * sampleScoreCovarianceHC2Star X y * (sampleGram X)⁻¹

/-- Totalized HC3 asymptotic sandwich estimator. -/
noncomputable def olsHeteroskedasticCovarianceHC3Star
    (X : Matrix n k ℝ) (y : n → ℝ) : Matrix k k ℝ :=
  (sampleGram X)⁻¹ * sampleScoreCovarianceHC3Star X y * (sampleGram X)⁻¹

/-- **Hansen Theorem 7.6, ideal sandwich consistency.**

The infeasible heteroskedastic sandwich estimator built from true errors
converges in probability to `Q⁻¹ Ω Q⁻¹`. This isolates the sandwich CMT from
the separate residual-substitution step needed for the feasible HC0 estimator. -/
theorem olsHeteroskedasticCovarianceIdealStar_tendstoInMeasure
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceIdealStar
          (stackRegressors X n ω) (stackErrors e n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  let invGram : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    (sampleGram (stackRegressors X n ω))⁻¹
  let scoreCov : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    sampleScoreCovarianceIdeal (stackRegressors X n ω) (stackErrors e n ω)
  have hGram_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    intro n
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.toSampleMomentAssumption71.ident_outer i).integrable_iff.mpr
      h.toSampleMomentAssumption71.int_outer).aestronglyMeasurable
  have hInv_meas : ∀ n, AEStronglyMeasurable (invGram n) μ := by
    intro n
    exact aestronglyMeasurable_matrix_inv (hGram_meas n)
  have hScore_meas : ∀ n, AEStronglyMeasurable (scoreCov n) μ := by
    intro n
    have hform : scoreCov n =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n,
            Matrix.vecMulVec (e i ω • X i ω) (e i ω • X i ω)) := by
      funext ω
      dsimp [scoreCov]
      rw [sampleScoreCovarianceIdeal_stack_eq_avg]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_score_outer i).integrable_iff.mpr h.int_score_outer).aestronglyMeasurable
  have hInv := sampleGramInv_stackRegressors_tendstoInMeasure_popGramInv
    (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71
  have hScore := sampleScoreCovarianceIdeal_stack_tendstoInMeasure_scoreCovarianceMatrix
    (μ := μ) (X := X) (e := e) h
  have hLeft := tendstoInMeasure_matrix_mul
    (μ := μ) (A := invGram) (B := scoreCov)
    (Ainf := fun _ : Ω => (popGram μ X)⁻¹)
    (Binf := fun _ : Ω => scoreCovarianceMatrix μ X e)
    hInv_meas hScore_meas (by simpa [invGram] using hInv) (by simpa [scoreCov] using hScore)
  have hLeft_meas : ∀ n, AEStronglyMeasurable (fun ω => invGram n ω * scoreCov n ω) μ := by
    intro n
    have hprod : AEStronglyMeasurable (fun ω => (invGram n ω, scoreCov n ω)) μ :=
      (hInv_meas n).prodMk (hScore_meas n)
    have hcont : Continuous (fun p : Matrix k k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  have hFull := tendstoInMeasure_matrix_mul
    (μ := μ) (A := fun n ω => invGram n ω * scoreCov n ω) (B := invGram)
    (Ainf := fun _ : Ω => (popGram μ X)⁻¹ * scoreCovarianceMatrix μ X e)
    (Binf := fun _ : Ω => (popGram μ X)⁻¹)
    hLeft_meas hInv_meas
    (by simpa [Matrix.mul_assoc] using hLeft) (by simpa [invGram] using hInv)
  simpa [olsHeteroskedasticCovarianceIdealStar, heteroskedasticAsymptoticCovariance,
    invGram, scoreCov, Matrix.mul_assoc] using hFull

/-- **Hansen Theorem 7.6, feasible sandwich assembly.**

Once the residual HC0 middle matrix `n⁻¹∑êᵢ²XᵢXᵢ'` is known to converge in
probability to `Ω`, the totalized feasible sandwich estimator converges to
`Q⁻¹ Ω Q⁻¹`. The remaining feasible-HC0 work is therefore the residual
substitution theorem for the middle matrix. -/
theorem olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_scoreCovariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e)
    (hScore_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hScore : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  let invGram : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    (sampleGram (stackRegressors X n ω))⁻¹
  let scoreCov : ℕ → Ω → Matrix k k ℝ := fun n ω =>
    sampleScoreCovarianceStar (stackRegressors X n ω) (stackOutcomes y n ω)
  have hGram_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    intro n
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hInv_meas : ∀ n, AEStronglyMeasurable (invGram n) μ := by
    intro n
    exact aestronglyMeasurable_matrix_inv (hGram_meas n)
  have hScore_meas' : ∀ n, AEStronglyMeasurable (scoreCov n) μ := by
    intro n
    simpa [scoreCov] using hScore_meas n
  have hInv := sampleGramInv_stackRegressors_tendstoInMeasure_popGramInv
    (μ := μ) (X := X) (e := e) h
  have hLeft := tendstoInMeasure_matrix_mul
    (μ := μ) (A := invGram) (B := scoreCov)
    (Ainf := fun _ : Ω => (popGram μ X)⁻¹)
    (Binf := fun _ : Ω => scoreCovarianceMatrix μ X e)
    hInv_meas hScore_meas' (by simpa [invGram] using hInv) (by simpa [scoreCov] using hScore)
  have hLeft_meas : ∀ n, AEStronglyMeasurable (fun ω => invGram n ω * scoreCov n ω) μ := by
    intro n
    have hprod : AEStronglyMeasurable (fun ω => (invGram n ω, scoreCov n ω)) μ :=
      (hInv_meas n).prodMk (hScore_meas' n)
    have hcont : Continuous (fun p : Matrix k k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  have hFull := tendstoInMeasure_matrix_mul
    (μ := μ) (A := fun n ω => invGram n ω * scoreCov n ω) (B := invGram)
    (Ainf := fun _ : Ω => (popGram μ X)⁻¹ * scoreCovarianceMatrix μ X e)
    (Binf := fun _ : Ω => (popGram μ X)⁻¹)
    hLeft_meas hInv_meas
    (by simpa [Matrix.mul_assoc] using hLeft) (by simpa [invGram] using hInv)
  simpa [olsHeteroskedasticCovarianceStar, heteroskedasticAsymptoticCovariance,
    invGram, scoreCov, Matrix.mul_assoc] using hFull

/-- **Hansen Theorem 7.6, feasible HC0 sandwich modulo remainder controls.**

The feasible totalized HC0 sandwich estimator is consistent once the residual
HC0 cross and quadratic middle-matrix remainders are controlled. -/
theorem olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_remainders
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hScore_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hCross : TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceCrossRemainder
          (stackRegressors X n ω) (stackErrors e n ω)
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun _ => 0))
    (hQuad : TendstoInMeasure μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticRemainder
          (stackRegressors X n ω)
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  have hScore :=
    sampleScoreCovarianceStar_stack_tendstoInMeasure_scoreCovarianceMatrix_of_remainders
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel hCross hQuad
  exact olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_scoreCovariance
    (μ := μ) (X := X) (e := e) (y := y) h.toSampleMomentAssumption71
    hScore_meas hScore

/-- **Hansen Theorem 7.6, feasible HC0 sandwich under bounded weights.**

The feasible totalized HC0 sandwich estimator converges to `Q⁻¹ Ω Q⁻¹` under
the HC0 WLLN assumptions, bounded empirical third/fourth weights for the
residual remainders, and measurability of the residual HC0 middle matrix. -/
theorem olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_bounded_weights
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hScore_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  have hCross :=
    sampleScoreCovarianceCrossRemainder_stack_tendstoInMeasure_zero_of_bounded_weights
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hCrossWeight
  have hQuad :=
    sampleScoreCovarianceQuadraticRemainder_stack_tendstoInMeasure_zero_of_bounded_weights
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hQuadWeight
  exact olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_remainders
    (μ := μ) (X := X) (e := e) (y := y) h β hmodel hScore_meas hCross hQuad

/-- **Hansen Theorem 7.6, feasible HC0 sandwich under component measurability.**

This version derives the residual HC0 middle-matrix measurability premise from
component measurability of the regressors and errors, leaving only the empirical
third/fourth bounded-weight hypotheses as explicit stochastic remainder
controls. -/
theorem olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_bounded_weights_and_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  have hScore_meas :=
    sampleScoreCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y) β h.toSampleMomentAssumption71 hmodel
      hX_meas he_meas
  exact olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_bounded_weights
    (μ := μ) (X := X) (e := e) (y := y)
    h β hmodel hScore_meas hCrossWeight hQuadWeight

/-- AEMeasurability of the totalized feasible HC0 sandwich estimator from
component measurability. -/
theorem olsHeteroskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω =>
        olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  intro n
  let invGram : Ω → Matrix k k ℝ := fun ω =>
    (sampleGram (stackRegressors X n ω))⁻¹
  let scoreCov : Ω → Matrix k k ℝ := fun ω =>
    sampleScoreCovarianceStar (stackRegressors X n ω) (stackOutcomes y n ω)
  have hGram_meas : AEStronglyMeasurable
      (fun ω => sampleGram (stackRegressors X n ω)) μ := by
    have hform : (fun ω => sampleGram (stackRegressors X n ω)) =
        (fun ω => (n : ℝ)⁻¹ •
          ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
      funext ω
      rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
    rw [hform]
    refine AEStronglyMeasurable.const_smul ?_ ((n : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.ident_outer i).integrable_iff.mpr h.int_outer).aestronglyMeasurable
  have hInv_meas : AEStronglyMeasurable invGram μ := by
    exact aestronglyMeasurable_matrix_inv hGram_meas
  have hScore_meas : AEStronglyMeasurable scoreCov μ := by
    have hScore :=
      sampleScoreCovarianceStar_stack_aestronglyMeasurable_of_components
        (μ := μ) (X := X) (e := e) (y := y) β h hmodel hX_meas he_meas n
    simpa [scoreCov] using hScore
  have hLeft : AEStronglyMeasurable (fun ω => invGram ω * scoreCov ω) μ := by
    have hprod : AEStronglyMeasurable (fun ω => (invGram ω, scoreCov ω)) μ :=
      hInv_meas.prodMk hScore_meas
    have hcont : Continuous (fun p : Matrix k k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  have hFull : AEStronglyMeasurable
      (fun ω => invGram ω * scoreCov ω * invGram ω) μ := by
    have hprod : AEStronglyMeasurable
        (fun ω => (invGram ω * scoreCov ω, invGram ω)) μ :=
      hLeft.prodMk hInv_meas
    have hcont : Continuous (fun p : Matrix k k ℝ × Matrix k k ℝ => p.1 * p.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hcont.comp_aestronglyMeasurable hprod
  simpa [olsHeteroskedasticCovarianceStar, invGram, scoreCov, Matrix.mul_assoc] using hFull

/-- **Hansen Theorem 7.10, HC0 covariance for fixed linear functions.**

For a fixed linear map `R`, the totalized feasible HC0 covariance estimator for
`R β` converges to `R Vβ Rᵀ` once the existing HC0 bounded-weight assumptions
and component measurability hypotheses are available. -/
theorem linearMap_olsHC0CovarianceStar_tendstoInMeasure_of_bounded_weights_and_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q]
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        R * olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)
      atTop (fun _ => R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) := by
  have hV_meas :=
    olsHeteroskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hV :=
    olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_bounded_weights_and_components
      (μ := μ) (X := X) (e := e) (y := y)
      h β hmodel hX_meas he_meas hCrossWeight hQuadWeight
  exact linearMapCovariance_tendstoInMeasure
    (μ := μ) (R := R)
    (Vhat := fun n ω =>
      olsHeteroskedasticCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
    (V := heteroskedasticAsymptoticCovariance μ X e)
    hV_meas hV

/-- **Hansen §7.11, HC0 standard errors for fixed linear functions.**

For a fixed linear map `R`, the square root of any diagonal element of the
totalized feasible HC0 covariance estimator for `R β` converges to the matching
population scale. -/
theorem olsHC0LinearStdErrorStar_tendstoInMeasure_of_bounded_weights_and_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Finite q]
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ) (j : q)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        Real.sqrt ((R * olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) j j))
      atTop (fun _ =>
        Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) j j)) := by
  have hV_meas :=
    olsHeteroskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hV :=
    olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_bounded_weights_and_components
      (μ := μ) (X := X) (e := e) (y := y)
      h β hmodel hX_meas he_meas hCrossWeight hQuadWeight
  exact linearMapCovarianceStdError_tendstoInMeasure
    (μ := μ) (R := R) (j := j)
    (Vhat := fun n ω =>
      olsHeteroskedasticCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
    (V := heteroskedasticAsymptoticCovariance μ X e)
    hV_meas hV

/-- **Hansen Theorem 7.7, HC1 sandwich under bounded weights.**

The totalized HC1 sandwich estimator has the same probability limit as HC0,
because the finite-sample degrees-of-freedom multiplier `n/(n-k)` tends to `1`. -/
theorem olsHeteroskedasticCovarianceHC1Star_tendstoInMeasure_of_bounded_weights
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hScore_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  let r : ℕ → ℝ := fun n =>
    (n : ℝ) / ((n : ℝ) - (Fintype.card k : ℝ))
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden : Tendsto
      (fun n : ℕ => (n : ℝ) - (Fintype.card k : ℝ)) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(Fintype.card k : ℝ)) hn
  have hrSub : Tendsto (fun n => r n - 1) atTop (𝓝 0) := by
    have hsmall : Tendsto
        (fun n : ℕ => (Fintype.card k : ℝ) /
          ((n : ℝ) - (Fintype.card k : ℝ))) atTop (𝓝 0) :=
      hden.const_div_atTop (Fintype.card k : ℝ)
    have heq : (fun n => r n - 1) =ᶠ[atTop]
        (fun n : ℕ => (Fintype.card k : ℝ) /
          ((n : ℝ) - (Fintype.card k : ℝ))) := by
      filter_upwards [eventually_gt_atTop (Fintype.card k)] with n hn_gt
      have hden_ne : (n : ℝ) - (Fintype.card k : ℝ) ≠ 0 := by
        have hgt : (Fintype.card k : ℝ) < (n : ℝ) := by
          exact_mod_cast hn_gt
        linarith
      dsimp [r]
      field_simp [hden_ne]
      ring
    rw [tendsto_congr' heq]
    exact hsmall
  have hr : Tendsto r atTop (𝓝 1) := by
    have hadd := hrSub.add_const 1
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hadd
  have hHC0 := olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_bounded_weights
    (μ := μ) (X := X) (e := e) (y := y)
    h β hmodel hScore_meas hCrossWeight hQuadWeight
  refine tendstoInMeasure_pi (μ := μ) (fun a => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun b => ?_)
  have hHC0_ab : TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceStar
          (stackRegressors X n ω) (stackOutcomes y n ω) a b)
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e a b) := by
    simpa using TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hHC0 a) b
  have hrMeasure : TendstoInMeasure μ
      (fun n (_ : Ω) => r n) atTop (fun _ => 1) :=
    tendstoInMeasure_const_real (μ := μ) hr
  have hprod := TendstoInMeasure.mul_limits_real hrMeasure hHC0_ab
  simpa [olsHeteroskedasticCovarianceHC1Star, r, Matrix.smul_apply, smul_eq_mul,
    Fintype.card_fin, div_eq_mul_inv] using hprod

/-- **Hansen Theorem 7.7, HC1 sandwich under component measurability.**

This is the HC1 analogue of
`olsHeteroskedasticCovarianceStar_tendstoInMeasure_of_bounded_weights_and_components`:
component measurability supplies the feasible HC0 middle-matrix measurability
needed by the HC1 assembly theorem. -/
theorem olsHeteroskedasticCovarianceHC1Star_tendstoInMeasure_of_bounded_weights_and_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  have hScore_meas :=
    sampleScoreCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y) β h.toSampleMomentAssumption71 hmodel
      hX_meas he_meas
  exact olsHeteroskedasticCovarianceHC1Star_tendstoInMeasure_of_bounded_weights
    (μ := μ) (X := X) (e := e) (y := y)
    h β hmodel hScore_meas hCrossWeight hQuadWeight

/-- AEMeasurability of the totalized HC1 sandwich estimator from component
measurability. -/
theorem olsHC1CovarianceStar_stack_aestronglyMeasurable_of_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ n, AEStronglyMeasurable
      (fun ω =>
        olsHeteroskedasticCovarianceHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
  intro n
  have hHC0 :=
    olsHeteroskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel hX_meas he_meas n
  simpa [olsHeteroskedasticCovarianceHC1Star] using
    hHC0.const_smul
      ((Fintype.card (Fin n) : ℝ) / (Fintype.card (Fin n) - Fintype.card k : ℝ))

/-- **Hansen Theorem 7.10, HC1 covariance for fixed linear functions.**

For a fixed linear map `R`, the totalized HC1 covariance estimator for `R β`
has the same `R Vβ Rᵀ` limit as HC0 under the bounded-weight and component
measurability hypotheses. -/
theorem linearMap_olsHC1CovarianceStar_tendstoInMeasure_of_bounded_weights_and_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q]
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        R * olsHeteroskedasticCovarianceHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ)
      atTop (fun _ => R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) := by
  have hV_meas :=
    olsHC1CovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hV :=
    olsHeteroskedasticCovarianceHC1Star_tendstoInMeasure_of_bounded_weights_and_components
      (μ := μ) (X := X) (e := e) (y := y)
      h β hmodel hX_meas he_meas hCrossWeight hQuadWeight
  exact linearMapCovariance_tendstoInMeasure
    (μ := μ) (R := R)
    (Vhat := fun n ω =>
      olsHeteroskedasticCovarianceHC1Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
    (V := heteroskedasticAsymptoticCovariance μ X e)
    hV_meas hV

/-- **Hansen §7.11, HC1 standard errors for fixed linear functions.**

For a fixed linear map `R`, the square root of any diagonal element of the
totalized HC1 covariance estimator for `R β` converges to the same population
scale as HC0. -/
theorem olsHC1LinearStdErrorStar_tendstoInMeasure_of_bounded_weights_and_components
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Finite q]
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ) (j : q)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m)) :
    TendstoInMeasure μ
      (fun n ω =>
        Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
          (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) j j))
      atTop (fun _ =>
        Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) j j)) := by
  have hV_meas :=
    olsHC1CovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hV :=
    olsHeteroskedasticCovarianceHC1Star_tendstoInMeasure_of_bounded_weights_and_components
      (μ := μ) (X := X) (e := e) (y := y)
      h β hmodel hX_meas he_meas hCrossWeight hQuadWeight
  exact linearMapCovarianceStdError_tendstoInMeasure
    (μ := μ) (R := R) (j := j)
    (Vhat := fun n ω =>
      olsHeteroskedasticCovarianceHC1Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
    (V := heteroskedasticAsymptoticCovariance μ X e)
    hV_meas hV

/-- **Hansen Theorem 7.7, conditional HC2 sandwich assembly.**

Once the HC2 leverage-weighted middle matrix is known to converge in
probability to `Ω`, the totalized HC2 sandwich estimator converges to
`Q⁻¹ Ω Q⁻¹`. The remaining HC2 work is the leverage argument showing that
`(1-hᵢᵢ)⁻¹` is asymptotically harmless. -/
theorem olsHeteroskedasticCovarianceHC2Star_tendstoInMeasure_of_middle
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e)
    (hHC2_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC2Star
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hHC2 : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceHC2Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceHC2Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  exact sandwichCovarianceStar_tendstoInMeasure_of_middle
    (μ := μ) (X := X) (e := e) h
    (middle := fun n ω => sampleScoreCovarianceHC2Star
      (stackRegressors X n ω) (stackOutcomes y n ω))
    hHC2_meas hHC2

/-- **Hansen Theorem 7.7, conditional HC3 sandwich assembly.**

Once the HC3 leverage-weighted middle matrix is known to converge in
probability to `Ω`, the totalized HC3 sandwich estimator converges to
`Q⁻¹ Ω Q⁻¹`. The remaining HC3 work is the stronger leverage-weight argument
for `(1-hᵢᵢ)⁻²`. -/
theorem olsHeteroskedasticCovarianceHC3Star_tendstoInMeasure_of_middle
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleMomentAssumption71 μ X e)
    (hHC3_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC3Star
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hHC3 : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceHC3Star
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => scoreCovarianceMatrix μ X e)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceHC3Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  exact sandwichCovarianceStar_tendstoInMeasure_of_middle
    (μ := μ) (X := X) (e := e) h
    (middle := fun n ω => sampleScoreCovarianceHC3Star
      (stackRegressors X n ω) (stackOutcomes y n ω))
    hHC3_meas hHC3

/-- **Hansen Theorem 7.7, HC2 sandwich modulo leverage adjustment.**

The totalized HC2 sandwich estimator is consistent once HC0 is controlled by
the bounded-weight hypotheses and the HC2-minus-HC0 leverage adjustment is
`oₚ(1)`. -/
theorem olsHeteroskedasticCovarianceHC2Star_tendstoInMeasure_of_bounded_weights_and_adjustment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hHC0_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hAdj_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC2AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hAdj : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceHC2AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceHC2Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  have hHC0 :=
    sampleScoreCovarianceStar_stack_tendstoInMeasure_scoreCovarianceMatrix_of_bounded_weights
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel hCrossWeight hQuadWeight
  have hHC2 :=
    sampleScoreCovarianceHC2Star_stack_tendstoInMeasure_scoreCovarianceMatrix_of_adjustment
      (μ := μ) (X := X) (e := e) (y := y) hHC0_meas hAdj_meas hHC0 hAdj
  have hHC2_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC2Star
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
    intro n
    have hsum : AEStronglyMeasurable
        (fun ω =>
          sampleScoreCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) +
            sampleScoreCovarianceHC2AdjustmentStar
              (stackRegressors X n ω) (stackOutcomes y n ω)) μ :=
      (hHC0_meas n).add (hAdj_meas n)
    simpa [sampleScoreCovarianceHC2AdjustmentStar, sub_eq_add_neg, add_assoc,
      add_comm, add_left_comm] using hsum
  exact olsHeteroskedasticCovarianceHC2Star_tendstoInMeasure_of_middle
    (μ := μ) (X := X) (e := e) (y := y)
    h.toSampleMomentAssumption71 hHC2_meas hHC2

/-- **Hansen Theorem 7.7, HC3 sandwich modulo leverage adjustment.**

The totalized HC3 sandwich estimator is consistent once HC0 is controlled by
the bounded-weight hypotheses and the HC3-minus-HC0 leverage adjustment is
`oₚ(1)`. -/
theorem olsHeteroskedasticCovarianceHC3Star_tendstoInMeasure_of_bounded_weights_and_adjustment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hHC0_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hAdj_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC3AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hAdj : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceHC3AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceHC3Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  have hHC0 :=
    sampleScoreCovarianceStar_stack_tendstoInMeasure_scoreCovarianceMatrix_of_bounded_weights
      (μ := μ) (X := X) (e := e) (y := y) h β hmodel hCrossWeight hQuadWeight
  have hHC3 :=
    sampleScoreCovarianceHC3Star_stack_tendstoInMeasure_scoreCovarianceMatrix_of_adjustment
      (μ := μ) (X := X) (e := e) (y := y) hHC0_meas hAdj_meas hHC0 hAdj
  have hHC3_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC3Star
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ := by
    intro n
    have hsum : AEStronglyMeasurable
        (fun ω =>
          sampleScoreCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) +
            sampleScoreCovarianceHC3AdjustmentStar
              (stackRegressors X n ω) (stackOutcomes y n ω)) μ :=
      (hHC0_meas n).add (hAdj_meas n)
    simpa [sampleScoreCovarianceHC3AdjustmentStar, sub_eq_add_neg, add_assoc,
      add_comm, add_left_comm] using hsum
  exact olsHeteroskedasticCovarianceHC3Star_tendstoInMeasure_of_middle
    (μ := μ) (X := X) (e := e) (y := y)
    h.toSampleMomentAssumption71 hHC3_meas hHC3

/-- **Hansen Theorem 7.7, HC2 sandwich modulo leverage adjustment and component measurability.**

Component measurability supplies the HC0 middle-matrix measurability needed by
the HC2 adjustment theorem; the leverage-adjustment measurability and
`oₚ(1)` convergence remain explicit. -/
theorem olsHeteroskedasticCovarianceHC2Star_tendstoInMeasure_of_components_and_adjustment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hAdj_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC2AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hAdj : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceHC2AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceHC2Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  have hHC0_meas :=
    sampleScoreCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y) β h.toSampleMomentAssumption71 hmodel
      hX_meas he_meas
  exact olsHeteroskedasticCovarianceHC2Star_tendstoInMeasure_of_bounded_weights_and_adjustment
    (μ := μ) (X := X) (e := e) (y := y)
    h β hmodel hHC0_meas hAdj_meas hCrossWeight hQuadWeight hAdj

/-- **Hansen Theorem 7.7, HC3 sandwich modulo leverage adjustment and component measurability.**

Component measurability supplies the HC0 middle-matrix measurability needed by
the HC3 adjustment theorem; the leverage-adjustment measurability and
`oₚ(1)` convergence remain explicit. -/
theorem olsHeteroskedasticCovarianceHC3Star_tendstoInMeasure_of_components_and_adjustment
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hAdj_meas : ∀ n, AEStronglyMeasurable
      (fun ω => sampleScoreCovarianceHC3AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω)) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hAdj : TendstoInMeasure μ
      (fun n ω => sampleScoreCovarianceHC3AdjustmentStar
        (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        olsHeteroskedasticCovarianceHC3Star
          (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop (fun _ => heteroskedasticAsymptoticCovariance μ X e) := by
  have hHC0_meas :=
    sampleScoreCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y) β h.toSampleMomentAssumption71 hmodel
      hX_meas he_meas
  exact olsHeteroskedasticCovarianceHC3Star_tendstoInMeasure_of_bounded_weights_and_adjustment
    (μ := μ) (X := X) (e := e) (y := y)
    h β hmodel hHC0_meas hAdj_meas hCrossWeight hQuadWeight hAdj

omit [DecidableEq k] in
/-- Move a fixed matrix multiplication from the left side of a dot product to the right side. -/
private theorem mulVec_dotProduct_right {q : Type*} [Fintype q]
    (M : Matrix q k ℝ) (v : k → ℝ) (a : q → ℝ) :
    (M *ᵥ v) ⬝ᵥ a = v ⬝ᵥ (Mᵀ *ᵥ a) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose, dotProduct_comm]

/-- **Hansen Theorem 7.2, scalar-projection score CLT.**

For every fixed vector `a`, the projected score sum
`(1 / √n) ∑_{i<n} (eᵢXᵢ)·a` converges in distribution to the Gaussian with the
matching scalar variance. This is the one-dimensional CLT supplied by Mathlib,
specialized to the score projections that appear in OLS asymptotic normality.

This is not yet the literal vector-valued statement of Theorem 7.2, nor does it
separately expose the textbook `Ω < ∞` conclusion. It is the Cramér-Wold-facing
piece needed to build that vector theorem. -/
theorem scoreProjection_sum_tendstoInDistribution_gaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a; μ]).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt (n : ℝ))⁻¹ *
        ∑ i ∈ Finset.range n, (e i ω • X i ω) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hdot_meas := measurable_dotProduct_right (k := k) a
  have hident_scalar : ∀ i,
      IdentDistrib (fun ω => (e i ω • X i ω) ⬝ᵥ a)
        (fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a) μ μ := by
    intro i
    simpa [Function.comp_def] using h.ident_cross i |>.comp hdot_meas
  have hindep_scalar :
      iIndepFun (fun i ω => (e i ω • X i ω) ⬝ᵥ a) μ := by
    simpa [Function.comp_def] using
      h.iIndep_cross.comp (fun _ v => v ⬝ᵥ a) (fun _ => hdot_meas)
  have hmean := scoreProjection_integral_zero (μ := μ)
    (X := X) (e := e) h.toSampleMomentAssumption71 a
  have hmean_integral :
      (∫ ω, (e 0 ω • X 0 ω) ⬝ᵥ a ∂μ) = 0 := by
    simpa using hmean
  have hclt := ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub
    (P := μ) (P' := ν) (X := fun i ω => (e i ω • X i ω) ⬝ᵥ a)
    (Y := Z) hZ (h.memLp_cross_projection a) hindep_scalar hident_scalar
  convert hclt using 2 with n ω
  funext ω
  rw [hmean_integral]
  ring

/-- **Hansen Theorem 7.2 in sample-score notation, scalar-projection form.**

This is the same CLT as `scoreProjection_sum_tendstoInDistribution_gaussian`,
rewritten in Hansen's notation as `√n · ĝₙ(e)` where
`ĝₙ(e) = n⁻¹∑ eᵢXᵢ`.

Status: this is the main formalized face of Theorem 7.2 at present. The full
vector-valued CLT is still pending. -/
theorem scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a; μ]).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hsum := scoreProjection_sum_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) h a hZ
  convert hsum using 2 with n
  funext ω
  rw [sqrt_smul_sampleCrossMoment_stackRegressors_stackErrors_eq_inv_sqrt_sum]
  simp [sum_dotProduct, smul_eq_mul]

/-- **Hansen Theorem 7.2, scalar-projection score CLT with `Ω`.**

This is `scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian`
with the Gaussian variance rewritten as the quadratic form
`a' Ω a`, where `Ω = scoreCovarianceMatrix μ X e`. -/
theorem scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (a ⬝ᵥ (scoreCovarianceMatrix μ X e *ᵥ a)).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hZ' : HasLaw Z
      (gaussianReal 0 (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a; μ]).toNNReal) ν := by
    rw [scoreProjection_variance_eq_quadraticScoreCovariance
      (μ := μ) (X := X) (e := e) h a]
    exact hZ
  exact scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) h a hZ'

/-- **Hansen Theorem 7.2, all scalar projections with `Ω`.**

This packages the current Cramér-Wold-facing endpoint: for every fixed
direction `a`, the scalar projection of `√n · ĝₙ(e)` has Gaussian limit with
variance `a' Ω a`.  The remaining gap to the literal textbook statement is the
reverse Cramér-Wold/vector-valued convergence wrapper. -/
theorem scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian_covariance_all
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e)
    {Z : (k → ℝ) → Ω' → ℝ}
    (hZ : ∀ a : k → ℝ,
      HasLaw (Z a)
        (gaussianReal 0 (a ⬝ᵥ (scoreCovarianceMatrix μ X e *ᵥ a)).toNNReal) ν) :
    ∀ a : k → ℝ,
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) ⬝ᵥ a)
        atTop (Z a) (fun _ => μ) ν :=
  fun a =>
    scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian_covariance
      (μ := μ) (ν := ν) (X := X) (e := e) h a (hZ a)

/-- **Hansen Theorem 7.3, feasible leading-score vector Slutsky bridge.**

Conditional on a vector-valued score CLT for `√n · ĝₙ(e)`, the feasible OLS
leading term formed with the random inverse Gram matrix satisfies
`Q̂ₙ⁻¹√nĝₙ(e) ⇒ Q⁻¹Z`. This is the vector version of the inverse-gap step:
the remaining full OLS theorem only has to add the already-negligible
singular-event residual. -/
theorem feasibleScore_tendstoInDistribution_of_scoreCLT
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    {Zscore : Ω' → k → ℝ}
    (h : SampleMomentAssumption71 μ X e)
    (hScore : TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop Zscore (fun _ => μ) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)))
      atTop
      (fun ω => (popGram μ X)⁻¹ *ᵥ Zscore ω)
      (fun _ => μ) ν := by
  exact matrixInvMulVec_tendstoInDistribution_of_vector_and_matrix
    (μ := μ) (ν := ν)
    (T := fun (n : ℕ) ω =>
      Real.sqrt (n : ℝ) •
        sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
    (Z := Zscore)
    (Ahat := fun n ω => sampleGram (stackRegressors X n ω))
    (A := popGram μ X)
    hScore (fun n => sampleGram_stackRegressors_aestronglyMeasurable h n)
    (sampleGram_stackRegressors_tendstoInMeasure_popGram h) h.Q_nonsing

/-- **Hansen Theorem 7.3, conditional vector OLS Slutsky assembly.**

If the vector score has a distributional limit `Zscore`, then the scaled
totalized OLS estimator has the transformed limit `Q⁻¹Zscore`. The theorem is
conditional only on the vector-valued score CLT; the random inverse and the
singular-event residual are discharged here. -/
theorem olsBetaStar_vector_tendstoInDistribution_of_scoreCLT
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {Zscore : Ω' → k → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hScore : TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop Zscore (fun _ => μ) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop
      (fun ω => (popGram μ X)⁻¹ *ᵥ Zscore ω)
      (fun _ => μ) ν := by
  have hFeasible := feasibleScore_tendstoInDistribution_of_scoreCLT
    (μ := μ) (ν := ν) (X := X) (e := e) (Zscore := Zscore) h hScore
  have hResidual :=
    sqrt_smul_olsBetaStar_sub_sub_feasibleScore_tendstoInMeasure_zero
      (μ := μ) (X := X) (e := e) (y := y) β h hmodel
  have hBeta_meas := olsBetaStar_stack_aestronglyMeasurable
    (μ := μ) (X := X) (e := e) (y := y) β h hmodel
  have hY_meas : ∀ n : ℕ, AEMeasurable
      (fun ω =>
        Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) μ := by
    intro n
    exact (AEStronglyMeasurable.const_smul
      ((hBeta_meas n).sub aestronglyMeasurable_const) (Real.sqrt (n : ℝ))).aemeasurable
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (n : ℕ) ω =>
      (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)))
    (Y := fun (n : ℕ) ω =>
      Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))
    (Z := fun ω => (popGram μ X)⁻¹ *ᵥ Zscore ω)
    hFeasible hResidual hY_meas

/-- **Hansen Theorem 7.3, ordinary-wrapper conditional vector OLS CLT.**

The same conditional vector asymptotic-normality bridge holds for
`olsBetaOrZero`, the ordinary-OLS wrapper that agrees with `olsBetaStar`
pointwise. -/
theorem olsBetaOrZero_vector_tendstoInDistribution_of_scoreCLT
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {Zscore : Ω' → k → ℝ}
    (h : SampleMomentAssumption71 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hScore : TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop Zscore (fun _ => μ) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))
      atTop
      (fun ω => (popGram μ X)⁻¹ *ᵥ Zscore ω)
      (fun _ => μ) ν := by
  have hstar := olsBetaStar_vector_tendstoInDistribution_of_scoreCLT
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
    (Zscore := Zscore) h β hmodel hScore
  refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) hstar
  intro n
  exact ae_of_all μ (fun ω => by
    change
      Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β) =
        Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)
    rw [olsBetaOrZero_eq_olsBetaStar])

/-- **Scaled-score coordinate boundedness from Theorem 7.2.**

Each coordinate of `√n · ĝₙ(e)` is `Oₚ(1)`.  This is the tightness corollary
of the scalar-projection score CLT, using the coordinate basis vector
`Pi.single j 1` and the general fact that real convergence in distribution
implies boundedness in probability. -/
theorem scoreCoordinate_sampleCrossMoment_boundedInProbability
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (j : k) :
    BoundedInProbability μ
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) j) := by
  classical
  let a : k → ℝ := Pi.single j 1
  let σ2 : NNReal := (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ a; μ]).toNNReal
  have hZ : HasLaw (fun x : ℝ => x) (gaussianReal 0 σ2) (gaussianReal 0 σ2) := by
    simpa [id] using (HasLaw.id (μ := gaussianReal 0 σ2))
  have hclt := scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian
    (μ := μ) (ν := gaussianReal 0 σ2) (X := X) (e := e) h a hZ
  have hcoord : TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) j)
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 σ2) := by
    simpa [a, dotProduct_single_one] using hclt
  exact BoundedInProbability.of_tendstoInDistribution hcoord

/-- **Inverse-gap projection under the Chapter 7.2 CLT assumptions.**

For every fixed projection vector `a`, the feasible-inverse correction
`(Q̂ₙ⁻¹ - Q⁻¹)√nĝₙ(e)` is `oₚ(1)` after scalar projection. This packages the
coordinatewise product rule with score-coordinate tightness from the CLT. -/
theorem inverseGapProjection_tendstoInMeasure_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0) := by
  exact inverseGapProjection_tendstoInMeasure_zero_of_scoreBounded
    (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71 a
    (fun j => scoreCoordinate_sampleCrossMoment_boundedInProbability
      (μ := μ) (X := X) (e := e) h j)

/-- **Scalar totalized-OLS Slutsky remainder under the Chapter 7.2 CLT assumptions.**

The difference between the scaled totalized-OLS projection and its fixed-`Q⁻¹`
score approximation is `oₚ(1)`. This is the direct remainder statement used by
the final scalar CLT. -/
theorem scoreProjection_olsBetaStar_remainder_tendstoInMeasure_zero
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a -
          (Real.sqrt (n : ℝ) •
            ((popGram μ X)⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0) := by
  exact scoreProjection_olsBetaStar_remainder_tendstoInMeasure_zero_of_inverseGap
    (μ := μ) (X := X) (e := e) (y := y) β a h.toSampleMomentAssumption71 hmodel
    (inverseGapProjection_tendstoInMeasure_zero (μ := μ) (X := X) (e := e) h a)

/-- **CLT for scalar projections of the infeasible leading OLS term.**

Applying the fixed population inverse `Q⁻¹` to `√n · ĝₙ(e)` preserves the
scalar-projection CLT, with the projection vector transformed to `(Q⁻¹)ᵀa`.
The remaining feasible-OLS step is replacing this fixed inverse with the random
`Q̂ₙ⁻¹`, i.e. the multivariate Slutsky/tightness bridge. -/
theorem scoreProjection_popGramInv_mulVec_sampleCrossMoment_tendstoInDistribution_gaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          ((popGram μ X)⁻¹ *ᵥ
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hscore := scoreProjection_sampleCrossMoment_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) h (((popGram μ X)⁻¹)ᵀ *ᵥ a) hZ
  convert hscore using 2 with n
  funext ω
  rw [← Matrix.mulVec_smul, mulVec_dotProduct_right]

/-- **CLT for scalar projections of the infeasible leading OLS term, with `Ω`.**

This is the fixed-`Q⁻¹` leading-term CLT with the Gaussian variance rewritten
as `((Q⁻¹)'a)' Ω ((Q⁻¹)'a)`. -/
theorem scoreProjection_popGramInv_tendstoInDistribution_gaussian_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (a : k → ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (olsProjectionAsymptoticVariance μ X e a).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          ((popGram μ X)⁻¹ *ᵥ
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hZ' : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν := by
    rw [scoreProjection_variance_eq_quadraticScoreCovariance
      (μ := μ) (X := X) (e := e) h (((popGram μ X)⁻¹)ᵀ *ᵥ a)]
    simpa [olsProjectionAsymptoticVariance] using hZ
  exact scoreProjection_popGramInv_mulVec_sampleCrossMoment_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) h a hZ'

/-- **Conditional scalar-projection OLS CLT for the totalized estimator.**
Once the scalar Slutsky remainder
`√n(β̂*ₙ - β)·a - √n(Q⁻¹ ĝₙ(e))·a` is known to be `oₚ(1)`, the fixed-`Q⁻¹`
score CLT transfers to the scalar projection of the totalized OLS estimator.

The deterministic roadmap above reduces this remainder to the scaled residual
plus the random-inverse gap; the residual is already controlled, so this
conditional theorem isolates the inverse-gap input used by the later
unconditional scalar result. -/
theorem scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_remainder
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β a : k → ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν)
    (hremainder : TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a -
          (Real.sqrt (n : ℝ) •
            ((popGram μ X)⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0))
    (hfinal_meas : ∀ (n : ℕ), AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a) μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hfixed := scoreProjection_popGramInv_mulVec_sampleCrossMoment_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) h a hZ
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (n : ℕ) ω =>
      (Real.sqrt (n : ℝ) •
        ((popGram μ X)⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
    (Y := fun (n : ℕ) ω =>
      (Real.sqrt (n : ℝ) •
        (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
    (Z := Z) hfixed hremainder hfinal_meas

/-- **Scalar-projection OLS CLT from the inverse-gap condition.**
For every fixed projection vector `a`, the totalized OLS estimator has the
fixed-`Q⁻¹` Gaussian scalar limit once the random-inverse gap projection is
`oₚ(1)`.

This theorem combines the scaled residual control, the inverse-gap reduction,
and Mathlib's Slutsky theorem. It is retained as a useful conditional bridge;
the theorem below discharges the inverse-gap hypothesis from tightness of the
scaled score and `Q̂ₙ⁻¹ →ₚ Q⁻¹`. -/
theorem scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_inverseGap
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν)
    (hinvGap : TendstoInMeasure μ
      (fun (n : ℕ) ω =>
        (((sampleGram (stackRegressors X n ω))⁻¹ - (popGram μ X)⁻¹) *ᵥ
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))) ⬝ᵥ a)
      atTop (fun _ => 0))
    (hfinal_meas : ∀ (n : ℕ), AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a) μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hremainder :=
    scoreProjection_olsBetaStar_remainder_tendstoInMeasure_zero_of_inverseGap
      (μ := μ) (X := X) (e := e) (y := y) β a h.toSampleMomentAssumption71
      hmodel hinvGap
  exact scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_remainder
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hZ hremainder hfinal_meas

/-- **Scalar-projection OLS CLT from scaled-score boundedness.**
For every fixed projection vector `a`, the totalized OLS estimator has the
fixed-`Q⁻¹` Gaussian scalar limit once the scaled score coordinates are
`Oₚ(1)`.

Compared with
`scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_inverseGap`,
this theorem discharges the random-inverse gap using the product-rule bridge
and `Q̂ₙ⁻¹ →ₚ Q⁻¹`. The final theorem below obtains `hscoreBounded` from the
score CLT/tightness layer. -/
theorem scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_scoreBounded
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν)
    (hscoreBounded : ∀ j : k,
      BoundedInProbability μ
        (fun (n : ℕ) ω =>
          (Real.sqrt (n : ℝ) •
            sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) j))
    (hfinal_meas : ∀ (n : ℕ), AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a) μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hinvGap :=
    inverseGapProjection_tendstoInMeasure_zero_of_scoreBounded
      (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71 a hscoreBounded
  exact scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_inverseGap
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel hZ hinvGap hfinal_meas

/-- **Hansen Theorem 7.3, scalar-projection totalized-OLS CLT.**

For every fixed projection vector `a`, the scaled totalized OLS error has the
Gaussian limit obtained from the fixed-`Q⁻¹` score projection. Compared with
the previous conditional variants, the inverse-gap/tightness premise is now
fully discharged from Theorem 7.2's score CLT. The remaining textbook-facing
work is the vector Cramér-Wold packaging; the ordinary-on-nonsingular wrapper
is handled by the covariance-form theorem below. -/
theorem scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_finalMeas
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν)
    (hfinal_meas : ∀ (n : ℕ), AEMeasurable
      (fun ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a) μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  exact scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_scoreBounded
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel hZ
    (fun j => scoreCoordinate_sampleCrossMoment_boundedInProbability
      (μ := μ) (X := X) (e := e) h j)
    hfinal_meas

/-- **Hansen Theorem 7.3, scalar-projection totalized-OLS CLT.**

This version has no separate measurability premise: the final projection is
measurable by `scoreProjection_sqrt_smul_olsBetaStar_sub_aemeasurable`. -/
theorem scoreProjection_olsBetaStar_tendstoInDistribution_gaussian
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  exact scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_finalMeas
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel hZ
    (scoreProjection_sqrt_smul_olsBetaStar_sub_aemeasurable
      (μ := μ) (X := X) (e := e) (y := y) h.toSampleMomentAssumption71 β a hmodel)

/-- **Hansen Theorem 7.3, scalar-projection totalized-OLS CLT with `Ω`.**

This restates the final scalar totalized-OLS CLT using the named asymptotic
variance `((Q⁻¹)'a)' Ω ((Q⁻¹)'a)`. -/
theorem scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (olsProjectionAsymptoticVariance μ X e a).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  have hZ' : HasLaw Z
      (gaussianReal 0
        (Var[fun ω => (e 0 ω • X 0 ω) ⬝ᵥ ((popGram μ X)⁻¹)ᵀ *ᵥ a; μ]).toNNReal)
      ν := by
    rw [scoreProjection_variance_eq_quadraticScoreCovariance
      (μ := μ) (X := X) (e := e) h (((popGram μ X)⁻¹)ᵀ *ᵥ a)]
    simpa [olsProjectionAsymptoticVariance] using hZ
  exact scoreProjection_olsBetaStar_tendstoInDistribution_gaussian
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel hZ'

/-- **Hansen Theorem 7.9, scalar projections of linear functions of OLS.**

For a fixed matrix `R`, every scalar projection of
`√n · R(β̂*ₙ - β)` is asymptotically normal. This is the linear-functions
special case of the delta-method theorem, obtained by applying the already
proved scalar OLS CLT in the transformed direction `Rᵀc`. -/
theorem scoreProjection_linearMap_olsBetaStar_tendstoInDistribution_gaussian_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q]
    (h : SampleCLTAssumption72 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ) (c : q → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ c)).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ c)
      atTop Z (fun _ => μ) ν := by
  have hbase := scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_covariance
    (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
    h β (Rᵀ *ᵥ c) hmodel hZ
  convert hbase using 2 with n
  funext ω
  rw [← Matrix.mulVec_smul, mulVec_dotProduct_right]

/-- **Hansen Theorem 7.9 for ordinary OLS on nonsingular samples, linear-function face.**

The same scalar-projection CLT for fixed linear maps holds for `olsBetaOrZero`,
which agrees definitionally with `olsBetaStar` in the totalized interface. -/
theorem scoreProjection_linearMap_olsBetaOrZero_tendstoInDistribution_gaussian_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    {q : Type*} [Fintype q]
    (h : SampleCLTAssumption72 μ X e) (β : k → ℝ)
    (R : Matrix q k ℝ) (c : q → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ c)).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ c)
      atTop Z (fun _ => μ) ν := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    scoreProjection_linearMap_olsBetaStar_tendstoInDistribution_gaussian_covariance
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      h β R c hmodel hZ

/-- **Standard-normal law for the scalar linear t-statistic limit.**

The scalar linear-function CLT produces a Gaussian numerator with variance
`r Vβ r'`. Dividing by the positive population standard error therefore has
standard normal law. -/
theorem olsLinearTStatisticLimit_hasLaw_standard
    {μ : Measure Ω}
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (hX : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ)
    (R : Matrix Unit k ℝ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    HasLaw
      (fun ω =>
        Z ω / Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ()))
      (gaussianReal 0 1) ν := by
  let c : ℝ := Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  have hentry_pos : 0 < (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () := by
    exact Real.sqrt_pos.mp hse_pos
  have hc : 0 < c := by
    simpa [c] using hse_pos
  have hentry_eq :
      (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () =
        olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) :=
    linearMapCovariance_unit_apply_eq_olsProjectionAsymptoticVariance
      (μ := μ) (X := X) (e := e) hX R
  have hσ :
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) = c ^ 2 := by
    calc
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))
          = (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () :=
            hentry_eq.symm
      _ = c ^ 2 := by
            simpa [c] using (Real.sq_sqrt hentry_pos.le).symm
  simpa [c] using
    hasLaw_gaussianReal_div_const_standard_of_variance_eq
      (ν := ν) (Z := Z) hc hσ hZ

/-- Continuous mapping theorem for absolute values of real distributional limits. -/
theorem tendstoInDistribution_abs_real
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {T : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hT : TendstoInDistribution T atTop Z P ν) :
    TendstoInDistribution (fun n ω => |T n ω|) atTop (fun ω => |Z ω|) P ν := by
  simpa [Function.comp_def] using hT.continuous_comp continuous_abs

/-- Relabel a real distributional limit by its law.

If `Tₙ ⇒ Z` under an auxiliary probability space and `Z` has law `η`, then
`Tₙ ⇒ id` under `η`. This is the bookkeeping step used to turn limiting random
variables such as Gaussian quadratic forms into named limit laws such as
`χ²(r)`. -/
theorem tendstoInDistribution_id_of_hasLaw_limit_real
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {ν : Measure Ω'} [IsProbabilityMeasure ν] {η : Measure ℝ} [IsProbabilityMeasure η]
    {T : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (hT : TendstoInDistribution T atTop Z P ν)
    (hZ : HasLaw Z η ν) :
    TendstoInDistribution T atTop (fun x : ℝ => x) P η := by
  refine ⟨hT.forall_aemeasurable, ?_, ?_⟩
  · fun_prop
  · have htarget :
      (⟨ν.map Z, Measure.isProbabilityMeasure_map hT.aemeasurable_limit⟩ :
          ProbabilityMeasure ℝ) =
        ⟨η.map (fun x : ℝ => x), Measure.isProbabilityMeasure_map (by fun_prop)⟩ := by
      apply Subtype.ext
      simp [hZ.map_eq]
    simpa [htarget] using hT.tendsto

omit [Fintype k] [DecidableEq k] in
/-- **Hansen Theorem 7.13, multivariate Wald `χ²` law identification.**

The generic Wald CMT gives convergence to the limiting quadratic form. If that
limiting quadratic form is known to have `χ²(r)` law, this theorem restates the
convergence directly with the named chi-squared limit. The remaining textbook
work is to prove the appropriate multivariate Gaussian quadratic-form law for
the OLS limit in each covariance setting. -/
theorem waldQuadraticForm_tendstoInDistribution_chiSquared_of_limit_hasLaw
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {q : Type*} [Fintype q] [DecidableEq q]
    {r : ℕ} [Fact (0 < r)]
    {T : ℕ → Ω → q → ℝ} {Z : Ω' → q → ℝ}
    {Vhat : ℕ → Ω → Matrix q q ℝ} {V : Matrix q q ℝ}
    (hT : TendstoInDistribution T atTop Z (fun _ => μ) ν)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V))
    (hV_nonsing : IsUnit V.det)
    (hLaw : HasLaw
      (fun ω => Z ω ⬝ᵥ (V⁻¹ *ᵥ Z ω)) (chiSquared r) ν) :
    TendstoInDistribution
      (fun n ω => T n ω ⬝ᵥ ((Vhat n ω)⁻¹ *ᵥ T n ω))
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared r) := by
  have hquad := waldQuadraticForm_tendstoInDistribution_of_vector_and_covariance
    (μ := μ) (ν := ν) (T := T) (Z := Z) (Vhat := Vhat) (V := V)
    hT hV_meas hV hV_nonsing
  exact tendstoInDistribution_id_of_hasLaw_limit_real hquad hLaw

/-- The absolute standard-normal law has no atom at the frontier of `(-∞, c]`. -/
theorem standardNormalAbs_frontier_Iic_null (crit : ℝ) :
    ((gaussianReal 0 1).map (fun x : ℝ => |x|)) (frontier (Set.Iic crit)) = 0 := by
  rw [frontier_Iic]
  rw [Measure.map_apply continuous_abs.measurable (measurableSet_singleton crit)]
  have hpre_subset :
      (fun x : ℝ => |x|) ⁻¹' ({crit} : Set ℝ) ⊆
        ({crit} ∪ {-crit} : Set ℝ) := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp only [Set.mem_union, Set.mem_singleton_iff]
    by_cases hx_nonneg : 0 ≤ x
    · left
      simpa [abs_of_nonneg hx_nonneg] using hx
    · right
      have hx_neg : x < 0 := lt_of_not_ge hx_nonneg
      have hneg : -x = crit := by
        simpa [abs_of_neg hx_neg] using hx
      linarith
  haveI : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (μ := 0) (v := 1) (by norm_num)
  exact measure_mono_null hpre_subset
    (measure_union_null (measure_singleton crit) (measure_singleton (-crit)))

/-- Squaring a standard-normal distributional limit gives a `χ²(1)` limit. -/
theorem tendstoInDistribution_sq_standardNormal_chiSquared_one
    {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {T : ℕ → Ω → ℝ}
    (hT : TendstoInDistribution T atTop (fun x : ℝ => x) P (gaussianReal 0 1)) :
    TendstoInDistribution (fun n ω => (T n ω) ^ 2) atTop
      (fun x : ℝ => x) P (chiSquared 1) := by
  have hsquare := hT.continuous_comp (by fun_prop : Continuous (fun x : ℝ => x ^ 2))
  refine ⟨?_, ?_, ?_⟩
  · simpa [Function.comp_def] using hsquare.forall_aemeasurable
  · fun_prop
  · convert hsquare.tendsto using 2
    · ext s hs
      simp [Function.comp_def, gaussianReal_map_sq_eq_chiSquared_one]

omit [DecidableEq k] in
/-- One-row linear maps turn scaled parameter errors into scaled scalar errors.

This is the algebraic bridge between the existing t-statistic numerator
`√n • R(β̂-β)` and the confidence-interval expression `√n(θ̂-θ)`. -/
theorem linearMapUnit_smul_sub_dot_one
    (R : Matrix Unit k ℝ) (b β : k → ℝ) (root : ℝ) :
    (root • (R *ᵥ (b - β))) ⬝ᵥ (fun _ : Unit => 1) =
      root * (((R *ᵥ b) ⬝ᵥ (fun _ : Unit => 1)) -
        ((R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1))) := by
  rw [Matrix.mulVec_sub, smul_dotProduct, sub_dotProduct]
  simp [smul_eq_mul]

/-- Scaling by positive standard-error and root factors preserves absolute-value inequalities. -/
theorem abs_scaled_error_div_le_iff
    {d root se crit : ℝ}
    (hroot : 0 < root) (hse : 0 < se) :
    |root * d / se| ≤ crit ↔ |d| ≤ crit * se / root := by
  rw [abs_div, abs_mul, abs_of_pos hroot, abs_of_pos hse]
  constructor
  · intro h
    have hmul : root * |d| ≤ crit * se := (div_le_iff₀ hse).mp h
    exact (le_div_iff₀ hroot).mpr (by simpa [mul_comm] using hmul)
  · intro h
    have hmul' : |d| * root ≤ crit * se := (le_div_iff₀ hroot).mp h
    have hmul : root * |d| ≤ crit * se := by
      simpa [mul_comm] using hmul'
    exact (div_le_iff₀ hse).mpr hmul

/-- Symmetric confidence-interval membership is equivalent to an absolute t-statistic bound. -/
theorem mem_symmetric_ci_iff_abs_tstat_le
    {θ θhat root se crit : ℝ}
    (hroot : 0 < root) (hse : 0 < se) :
    θ ∈ Set.Icc (θhat - crit * se / root) (θhat + crit * se / root) ↔
      |root * (θhat - θ) / se| ≤ crit := by
  rw [← Set.mem_Icc_iff_abs_le
    (x := θhat) (y := θ) (z := crit * se / root)]
  exact (abs_scaled_error_div_le_iff
    (d := θhat - θ) (root := root) (se := se) (crit := crit) hroot hse).symm

/-- **Hansen Theorem 7.12, generic symmetric confidence-interval coverage bridge.**

If the absolute t-statistic converges to `|N(0,1)|`, then the probability that
the true scalar parameter lies in the usual symmetric interval converges to the
absolute-standard-normal mass below the critical value, at every continuity
critical value. Positivity of the root and standard error is needed only
eventually, so finite initial sample sizes are ignored by the limit. -/
theorem symmetricCI_coverage_tendsto_of_abs_tstat
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ crit : ℝ}
    {θhat se : ℕ → Ω → ℝ} {root : ℕ → ℝ}
    (hroot : ∀ᶠ n in atTop, 0 < root n)
    (hse : ∀ᶠ n in atTop, ∀ ω, 0 < se n ω)
    (hT : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1))
    (hcrit : ((gaussianReal 0 1).map (fun x : ℝ => |x|))
      (frontier (Set.Iic crit)) = 0) :
    Tendsto
      (fun n => μ {ω | θ ∈ Set.Icc
        (θhat n ω - crit * se n ω / root n)
        (θhat n ω + crit * se n ω / root n)})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  have hevent :=
    TendstoInDistribution.tendsto_measure_preimage_of_null_frontier_real
      hT
      (E := Set.Iic crit) measurableSet_Iic hcrit
  refine hevent.congr' ?_
  filter_upwards [hroot, hse] with n hnroot hnse
  congr 1
  ext ω
  have hiff := mem_symmetric_ci_iff_abs_tstat_le
    (θ := θ) (θhat := θhat n ω) (root := root n)
    (se := se n ω) (crit := crit) hnroot (hnse ω)
  simpa [Set.mem_Iic] using hiff.symm

/-- Version of `symmetricCI_coverage_tendsto_of_abs_tstat` with the standard-normal
continuity-set side condition already discharged. -/
theorem symmetricCI_coverage_tendsto_of_abs_tstat_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θ crit : ℝ}
    {θhat se : ℕ → Ω → ℝ} {root : ℕ → ℝ}
    (hroot : ∀ᶠ n in atTop, 0 < root n)
    (hse : ∀ᶠ n in atTop, ∀ ω, 0 < se n ω)
    (hT : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1)) :
    Tendsto
      (fun n => μ {ω | θ ∈ Set.Icc
        (θhat n ω - crit * se n ω / root n)
        (θhat n ω + crit * se n ω / root n)})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) :=
  symmetricCI_coverage_tendsto_of_abs_tstat
    (μ := μ) (θ := θ) (crit := crit)
    hroot hse hT (standardNormalAbs_frontier_Iic_null crit)

/-- **Hansen §7.17, homoskedastic t-statistic for a scalar linear function.**

For a one-dimensional fixed linear map `R`, the homoskedastic-studentized
totalized OLS linear function converges to the Gaussian linear-function limit
divided by the homoskedastic population standard-error scale. -/
theorem olsHomoskedasticLinearTStatisticStar_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : SampleCLTAssumption72 μ X e)
    (hvar : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
            Real.sqrt ((R * olsHomoskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop
      (fun ω =>
        Z ω / Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ()))
      (fun _ => μ) ν := by
  let c : ℝ := Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHomoskedasticCovarianceStar
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let num : ℕ → Ω → ℝ := fun n ω =>
    ((Real.sqrt (n : ℝ) •
      (R *ᵥ (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
        (fun _ : Unit => 1))
  have hnum : TendstoInDistribution num atTop Z (fun _ => μ) ν := by
    simpa [num] using
      scoreProjection_linearMap_olsBetaStar_tendstoInDistribution_gaussian_covariance
        (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
        hclt β R (fun _ : Unit => 1) hmodel hZ
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHomoskedasticLinearStdErrorStar_tendstoInMeasure
        (μ := μ) (X := X) (e := e) (y := y)
        hvar β R () hmodel hX_meas he_meas
  have hV_meas :=
    olsHomoskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      hvar.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hse_meas : ∀ n, AEMeasurable (se n) μ := by
    intro n
    have hcov : AEStronglyMeasurable
        (fun ω =>
          R * olsHomoskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) μ :=
      linearMapCovariance_aestronglyMeasurable
        (μ := μ) (R := R) (hV_meas n)
    have hentry_cont : Continuous (fun M : Matrix Unit Unit ℝ => M () ()) :=
      (continuous_apply ()).comp (continuous_apply ())
    have hsqrt_cont : Continuous (fun M : Matrix Unit Unit ℝ => Real.sqrt (M () ())) :=
      Real.continuous_sqrt.comp hentry_cont
    exact (hsqrt_cont.comp_aestronglyMeasurable hcov).aemeasurable
  have hratio_meas : ∀ n, AEMeasurable (fun ω => num n ω / se n ω) μ :=
    fun n => (hnum.forall_aemeasurable n).div (hse_meas n)
  have hratio := tendstoInDistribution_div_of_tendstoInMeasure_const_pos
    (μ := μ) (ν := ν) (X := num) (Y := se) (Z := Z) (c := c)
    (by simpa [c] using hse_pos) hnum hse hse_meas hratio_meas
  simpa [num, se, c] using hratio

/-- **Hansen Theorem 7.14, scalar homoskedastic t-statistic with standard normal limit.**

If the homoskedastic asymptotic covariance equals the robust sandwich
covariance, the scalar homoskedastic t-statistic has the standard-normal limit.
This is the one-dimensional t-statistic face behind the homoskedastic Wald
statistic. -/
theorem olsHomoskedasticLinearTStatisticStar_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : SampleCLTAssumption72 μ X e)
    (hvar : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoskedasticAsymptoticCovariance μ X e =
      heteroskedasticAsymptoticCovariance μ X e)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHomoskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  let c : ℝ := Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  have hentry_pos : 0 < (R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () () := by
    exact Real.sqrt_pos.mp hse_pos
  have hentry_eq :
      (R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () () =
        olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) := by
    rw [hVeq]
    exact linearMapCovariance_unit_apply_eq_olsProjectionAsymptoticVariance
      (μ := μ) (X := X) (e := e) hclt.toSampleMomentAssumption71.int_outer R
  have hσ :
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) = c ^ 2 := by
    calc
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))
          = (R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () () :=
            hentry_eq.symm
      _ = c ^ 2 := by
            simpa [c] using (Real.sq_sqrt hentry_pos.le).symm
  have hZ : HasLaw (fun x : ℝ => c * x)
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      (gaussianReal 0 1) :=
    hasLaw_const_mul_id_gaussianReal_of_variance_eq hσ
  have hbase := olsHomoskedasticLinearTStatisticStar_tendstoInDistribution
    (μ := μ) (ν := gaussianReal 0 1) (X := X) (e := e) (y := y)
    hclt hvar β R hmodel hX_meas he_meas hZ hse_pos
  convert hbase using 2
  · rename_i x
    dsimp [c]
    exact (mul_div_cancel_left₀ x hse_pos.ne').symm

/-- **Hansen §7.17 for ordinary OLS on nonsingular samples, homoskedastic face.**

The homoskedastic-studentized scalar linear t-statistic transfers from the
totalized estimator to the ordinary-on-nonsingular wrapper `olsBetaOrZero`. -/
theorem olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : SampleCLTAssumption72 μ X e)
    (hvar : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHomoskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop
      (fun ω =>
        Z ω / Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ()))
      (fun _ => μ) ν := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    olsHomoskedasticLinearTStatisticStar_tendstoInDistribution
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      hclt hvar β R hmodel hX_meas he_meas hZ hse_pos

/-- **Hansen Theorem 7.14 for ordinary OLS, homoskedastic standard-normal face.** -/
theorem olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : SampleCLTAssumption72 μ X e)
    (hvar : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoskedasticAsymptoticCovariance μ X e =
      heteroskedasticAsymptoticCovariance μ X e)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHomoskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    olsHomoskedasticLinearTStatisticStar_tendstoInDistribution_standardNormal
      (μ := μ) (X := X) (e := e) (y := y)
      hclt hvar β R hmodel hX_meas he_meas hVeq hse_pos

/-- Absolute-value CMT for the ordinary homoskedastic scalar t-statistic. -/
theorem olsHomoskedasticLinearTStatisticOrZero_abs_tendstoInDistribution_standardNormalAbs
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : SampleCLTAssumption72 μ X e)
    (hvar : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoskedasticAsymptoticCovariance μ X e =
      heteroskedasticAsymptoticCovariance μ X e)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        abs
          (((Real.sqrt (n : ℝ) •
            (R *ᵥ
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
              (fun _ : Unit => 1)) /
            Real.sqrt ((R * olsHomoskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())))
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
  simpa using
    tendstoInDistribution_abs_real
      (olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        hclt hvar β R hmodel hX_meas he_meas hVeq hse_pos)

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.12, homoskedastic confidence-interval coverage.**

For a one-row linear restriction, the ordinary-wrapper homoskedastic symmetric
confidence interval has limiting coverage equal to the absolute standard-normal
mass below the critical value. Sample standard-error positivity is assumed only
eventually, matching the generic interval bridge. -/
theorem olsHomoskedasticLinearCIOrZero_coverage_tendsto_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : SampleCLTAssumption72 μ X e)
    (hvar : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ) (crit : ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoskedasticAsymptoticCovariance μ X e =
      heteroskedasticAsymptoticCovariance μ X e)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ()))
    (hse_sample_pos : ∀ᶠ n in atTop, ∀ ω,
      0 < Real.sqrt ((R * olsHomoskedasticCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())) :
    Tendsto
      (fun n => μ {ω |
        (R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1) ∈ Set.Icc
          (((R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
              (fun _ : Unit => 1)) -
            crit * Real.sqrt ((R * olsHomoskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()) /
              Real.sqrt (n : ℝ))
          (((R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
              (fun _ : Unit => 1)) +
            crit * Real.sqrt ((R * olsHomoskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()) /
              Real.sqrt (n : ℝ))})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  let θ : ℝ := (R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1)
  let θhat : ℕ → Ω → ℝ := fun n ω =>
    (R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
      (fun _ : Unit => 1)
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHomoskedasticCovarianceStar
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let root : ℕ → ℝ := fun n => Real.sqrt (n : ℝ)
  have hroot : ∀ᶠ n in atTop, 0 < root n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.sqrt_pos.mpr hnpos
  have hAbs := olsHomoskedasticLinearTStatisticOrZero_abs_tendstoInDistribution_standardNormalAbs
    (μ := μ) (X := X) (e := e) (y := y)
    hclt hvar β R hmodel hX_meas he_meas hVeq hse_pos
  have hGeneric : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
    refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) hAbs
    intro n
    exact ae_of_all μ (fun ω => by
      dsimp [θ, θhat, se, root]
      rw [linearMapUnit_smul_sub_dot_one])
  simpa [θ, θhat, se, root] using
    symmetricCI_coverage_tendsto_of_abs_tstat_standardNormal
      (μ := μ) (θ := θ) (crit := crit)
      (θhat := θhat) (se := se) (root := root)
      hroot hse_sample_pos hGeneric

/-- **Hansen Theorem 7.14, scalar one-degree-of-freedom homoskedastic Wald statistic.**

Under the explicit covariance bridge `V⁰β = Vβ`, the scalar homoskedastic Wald
statistic for ordinary OLS converges to `χ²(1)`. -/
theorem olsHomoskedasticLinearWaldStatisticOrZero_tendstoInDistribution_chiSquared_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : SampleCLTAssumption72 μ X e)
    (hvar : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hVeq : homoskedasticAsymptoticCovariance μ X e =
      heteroskedasticAsymptoticCovariance μ X e)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHomoskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())) ^ 2)
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) := by
  simpa using
    tendstoInDistribution_sq_standardNormal_chiSquared_one
      (olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        hclt hvar β R hmodel hX_meas he_meas hVeq hse_pos)

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.14, moment-level homoskedastic t-statistic face.**

If the homoskedastic score-covariance identity `Ω = σ²Q` is available, the
ordinary-wrapper scalar homoskedastic t-statistic has a standard-normal limit. -/
theorem olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution_standardNormal_of_scoreCovariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : SampleCLTAssumption72 μ X e)
    (hvar : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hΩ : scoreCovarianceMatrix μ X e = errorVariance μ e • popGram μ X)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHomoskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  have hQ : IsUnit (popGram μ X).det := by
    simpa [popGram] using hvar.toSampleMomentAssumption71.Q_nonsing
  exact olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution_standardNormal
    (μ := μ) (X := X) (e := e) (y := y)
    hclt hvar β R hmodel hX_meas he_meas
    (homoskedasticAsymptoticCovariance_eq_heteroskedasticAsymptoticCovariance
      (μ := μ) (X := X) (e := e) hQ hΩ)
    hse_pos

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.14, moment-level scalar homoskedastic Wald statistic.**

If `Ω = σ²Q`, the scalar one-degree-of-freedom homoskedastic Wald statistic for
ordinary OLS converges to `χ²(1)`. -/
theorem olsHomoskedasticLinearWaldStatisticOrZero_tendstoInDistribution_chiSquared_one_of_scoreCovariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (hclt : SampleCLTAssumption72 μ X e)
    (hvar : SampleVarianceAssumption74 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hΩ : scoreCovarianceMatrix μ X e = errorVariance μ e • popGram μ X)
    (hse_pos : 0 <
      Real.sqrt ((R * homoskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHomoskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())) ^ 2)
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) := by
  simpa using
    tendstoInDistribution_sq_standardNormal_chiSquared_one
      (olsHomoskedasticLinearTStatisticOrZero_tendstoInDistribution_standardNormal_of_scoreCovariance
        (μ := μ) (X := X) (e := e) (y := y)
        hclt hvar β R hmodel hX_meas he_meas hΩ hse_pos)

/-- **Hansen Theorem 7.11, HC0 t-statistic for a scalar linear function.**

For a one-dimensional fixed linear map `R`, the HC0-studentized totalized OLS
linear function converges in distribution to the Gaussian linear-function limit
divided by the population standard-error scale. A final law-normalization
corollary can turn this displayed limit into `N(0,1)` once the scalar variance
is identified with the corresponding diagonal of `R Vβ Rᵀ`. -/
theorem olsHC0LinearTStatisticStar_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
            Real.sqrt ((R * olsHeteroskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop
      (fun ω =>
        Z ω / Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ()))
      (fun _ => μ) ν := by
  let c : ℝ := Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHeteroskedasticCovarianceStar
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let num : ℕ → Ω → ℝ := fun n ω =>
    ((Real.sqrt (n : ℝ) •
      (R *ᵥ (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
        (fun _ : Unit => 1))
  have hnum : TendstoInDistribution num atTop Z (fun _ => μ) ν := by
    simpa [num] using
      scoreProjection_linearMap_olsBetaStar_tendstoInDistribution_gaussian_covariance
        (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
        h.toSampleCLTAssumption72 β R (fun _ : Unit => 1) hmodel hZ
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHC0LinearStdErrorStar_tendstoInMeasure_of_bounded_weights_and_components
        (μ := μ) (X := X) (e := e) (y := y)
        h β R () hmodel hX_meas he_meas hCrossWeight hQuadWeight
  have hV_meas :=
    olsHeteroskedasticCovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hse_meas : ∀ n, AEMeasurable (se n) μ := by
    intro n
    have hcov : AEStronglyMeasurable
        (fun ω =>
          R * olsHeteroskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) μ :=
      linearMapCovariance_aestronglyMeasurable
        (μ := μ) (R := R) (hV_meas n)
    have hentry_cont : Continuous (fun M : Matrix Unit Unit ℝ => M () ()) :=
      (continuous_apply ()).comp (continuous_apply ())
    have hsqrt_cont : Continuous (fun M : Matrix Unit Unit ℝ => Real.sqrt (M () ())) :=
      Real.continuous_sqrt.comp hentry_cont
    exact (hsqrt_cont.comp_aestronglyMeasurable hcov).aemeasurable
  have hratio_meas : ∀ n, AEMeasurable (fun ω => num n ω / se n ω) μ :=
    fun n => (hnum.forall_aemeasurable n).div (hse_meas n)
  have hratio := tendstoInDistribution_div_of_tendstoInMeasure_const_pos
    (μ := μ) (ν := ν) (X := num) (Y := se) (Z := Z) (c := c)
    (by simpa [c] using hse_pos) hnum hse hse_meas hratio_meas
  simpa [num, se, c] using hratio

/-- **Hansen Theorem 7.11, HC0 scalar t-statistic with standard normal limit.**

This is the textbook-facing form of the HC0 studentized scalar linear-function
CLT: the target is the identity random variable under `N(0,1)`. -/
theorem olsHC0LinearTStatisticStar_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHeteroskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  let c : ℝ := Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  have hentry_pos : 0 < (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () := by
    exact Real.sqrt_pos.mp hse_pos
  have hentry_eq :
      (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () =
        olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) :=
    linearMapCovariance_unit_apply_eq_olsProjectionAsymptoticVariance
      (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71.int_outer R
  have hσ :
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) = c ^ 2 := by
    calc
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))
          = (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () :=
            hentry_eq.symm
      _ = c ^ 2 := by
            simpa [c] using (Real.sq_sqrt hentry_pos.le).symm
  have hZ : HasLaw (fun x : ℝ => c * x)
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      (gaussianReal 0 1) :=
    hasLaw_const_mul_id_gaussianReal_of_variance_eq hσ
  have hbase := olsHC0LinearTStatisticStar_tendstoInDistribution
    (μ := μ) (ν := gaussianReal 0 1) (X := X) (e := e) (y := y)
    h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hZ hse_pos
  convert hbase using 2
  · rename_i x
    dsimp [c]
    exact (mul_div_cancel_left₀ x hse_pos.ne').symm

/-- **Hansen Theorem 7.11 for ordinary OLS on nonsingular samples, HC0 face.**

The HC0-studentized scalar linear t-statistic transfers from `olsBetaStar` to
`olsBetaOrZero`, the ordinary-OLS wrapper used on nonsingular sample-Gram
events. -/
theorem olsHC0LinearTStatisticOrZero_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHeteroskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop
      (fun ω =>
        Z ω / Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ()))
      (fun _ => μ) ν := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    olsHC0LinearTStatisticStar_tendstoInDistribution
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hZ hse_pos

/-- **Hansen Theorem 7.11 for ordinary OLS, HC0 standard-normal face.** -/
theorem olsHC0LinearTStatisticOrZero_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHeteroskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    olsHC0LinearTStatisticStar_tendstoInDistribution_standardNormal
      (μ := μ) (X := X) (e := e) (y := y)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos

/-- Absolute-value CMT for the ordinary HC0 scalar t-statistic. -/
theorem olsHC0LinearTStatisticOrZero_abs_tendstoInDistribution_standardNormalAbs
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        abs
          (((Real.sqrt (n : ℝ) •
            (R *ᵥ
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
              (fun _ : Unit => 1)) /
            Real.sqrt ((R * olsHeteroskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())))
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
  simpa using
    tendstoInDistribution_abs_real
      (olsHC0LinearTStatisticOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos)

set_option linter.style.longLine false in
/-- **Hansen Theorem 7.12, HC0 confidence-interval coverage.**

The ordinary-wrapper HC0 symmetric confidence interval for a one-row linear
restriction has limiting coverage given by the absolute standard-normal mass
below `crit`, conditional on eventual positivity of the sample HC0 standard
error. -/
theorem olsHC0LinearCIOrZero_coverage_tendsto_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ) (crit : ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ()))
    (hse_sample_pos : ∀ᶠ n in atTop, ∀ ω,
      0 < Real.sqrt ((R * olsHeteroskedasticCovarianceStar
        (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())) :
    Tendsto
      (fun n => μ {ω |
        (R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1) ∈ Set.Icc
          (((R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
              (fun _ : Unit => 1)) -
            crit * Real.sqrt ((R * olsHeteroskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()) /
              Real.sqrt (n : ℝ))
          (((R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
              (fun _ : Unit => 1)) +
            crit * Real.sqrt ((R * olsHeteroskedasticCovarianceStar
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()) /
              Real.sqrt (n : ℝ))})
      atTop
      (𝓝 (((gaussianReal 0 1).map (fun x : ℝ => |x|)) (Set.Iic crit))) := by
  let θ : ℝ := (R *ᵥ β) ⬝ᵥ (fun _ : Unit => 1)
  let θhat : ℕ → Ω → ℝ := fun n ω =>
    (R *ᵥ olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω)) ⬝ᵥ
      (fun _ : Unit => 1)
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHeteroskedasticCovarianceStar
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let root : ℕ → ℝ := fun n => Real.sqrt (n : ℝ)
  have hroot : ∀ᶠ n in atTop, 0 < root n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.sqrt_pos.mpr hnpos
  have hAbs := olsHC0LinearTStatisticOrZero_abs_tendstoInDistribution_standardNormalAbs
    (μ := μ) (X := X) (e := e) (y := y)
    h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos
  have hGeneric : TendstoInDistribution
      (fun n ω => |root n * (θhat n ω - θ) / se n ω|)
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
    refine TendstoInDistribution.congr ?_ (EventuallyEq.rfl) hAbs
    intro n
    exact ae_of_all μ (fun ω => by
      dsimp [θ, θhat, se, root]
      rw [linearMapUnit_smul_sub_dot_one])
  simpa [θ, θhat, se, root] using
    symmetricCI_coverage_tendsto_of_abs_tstat_standardNormal
      (μ := μ) (θ := θ) (crit := crit)
      (θhat := θhat) (se := se) (root := root)
      hroot hse_sample_pos hGeneric

/-- Scalar one-degree-of-freedom HC0 Wald statistic for ordinary OLS. -/
theorem olsHC0LinearWaldStatisticOrZero_tendstoInDistribution_chiSquared_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHeteroskedasticCovarianceStar
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())) ^ 2)
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) := by
  simpa using
    tendstoInDistribution_sq_standardNormal_chiSquared_one
      (olsHC0LinearTStatisticOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos)

/-- **Hansen Theorem 7.11, HC1 t-statistic for a scalar linear function.**

This is the HC1 analogue of
`olsHC0LinearTStatisticStar_tendstoInDistribution`: the studentized totalized
OLS linear function converges to the same Gaussian limit divided by the
population standard-error scale. -/
theorem olsHC1LinearTStatisticStar_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
            Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop
      (fun ω =>
        Z ω / Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ()))
      (fun _ => μ) ν := by
  let c : ℝ := Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  let se : ℕ → Ω → ℝ := fun n ω =>
    Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
      (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())
  let num : ℕ → Ω → ℝ := fun n ω =>
    ((Real.sqrt (n : ℝ) •
      (R *ᵥ (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
        (fun _ : Unit => 1))
  have hnum : TendstoInDistribution num atTop Z (fun _ => μ) ν := by
    simpa [num] using
      scoreProjection_linearMap_olsBetaStar_tendstoInDistribution_gaussian_covariance
        (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
        h.toSampleCLTAssumption72 β R (fun _ : Unit => 1) hmodel hZ
  have hse : TendstoInMeasure μ se atTop (fun _ => c) := by
    simpa [se, c] using
      olsHC1LinearStdErrorStar_tendstoInMeasure_of_bounded_weights_and_components
        (μ := μ) (X := X) (e := e) (y := y)
        h β R () hmodel hX_meas he_meas hCrossWeight hQuadWeight
  have hV_meas :=
    olsHC1CovarianceStar_stack_aestronglyMeasurable_of_components
      (μ := μ) (X := X) (e := e) (y := y)
      h.toSampleMomentAssumption71 β hmodel hX_meas he_meas
  have hse_meas : ∀ n, AEMeasurable (se n) μ := by
    intro n
    have hcov : AEStronglyMeasurable
        (fun ω =>
          R * olsHeteroskedasticCovarianceHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) μ :=
      linearMapCovariance_aestronglyMeasurable
        (μ := μ) (R := R) (hV_meas n)
    have hentry_cont : Continuous (fun M : Matrix Unit Unit ℝ => M () ()) :=
      (continuous_apply ()).comp (continuous_apply ())
    have hsqrt_cont : Continuous (fun M : Matrix Unit Unit ℝ => Real.sqrt (M () ())) :=
      Real.continuous_sqrt.comp hentry_cont
    exact (hsqrt_cont.comp_aestronglyMeasurable hcov).aemeasurable
  have hratio_meas : ∀ n, AEMeasurable (fun ω => num n ω / se n ω) μ :=
    fun n => (hnum.forall_aemeasurable n).div (hse_meas n)
  have hratio := tendstoInDistribution_div_of_tendstoInMeasure_const_pos
    (μ := μ) (ν := ν) (X := num) (Y := se) (Z := Z) (c := c)
    (by simpa [c] using hse_pos) hnum hse hse_meas hratio_meas
  simpa [num, se, c] using hratio

/-- **Hansen Theorem 7.11, HC1 scalar t-statistic with standard normal limit.**

This is the HC1 analogue of
`olsHC0LinearTStatisticStar_tendstoInDistribution_standardNormal`. -/
theorem olsHC1LinearTStatisticStar_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  let c : ℝ := Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())
  have hentry_pos : 0 < (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () := by
    exact Real.sqrt_pos.mp hse_pos
  have hentry_eq :
      (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () =
        olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) :=
    linearMapCovariance_unit_apply_eq_olsProjectionAsymptoticVariance
      (μ := μ) (X := X) (e := e) h.toSampleMomentAssumption71.int_outer R
  have hσ :
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1)) = c ^ 2 := by
    calc
      olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))
          = (R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () () :=
            hentry_eq.symm
      _ = c ^ 2 := by
            simpa [c] using (Real.sq_sqrt hentry_pos.le).symm
  have hZ : HasLaw (fun x : ℝ => c * x)
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      (gaussianReal 0 1) :=
    hasLaw_const_mul_id_gaussianReal_of_variance_eq hσ
  have hbase := olsHC1LinearTStatisticStar_tendstoInDistribution
    (μ := μ) (ν := gaussianReal 0 1) (X := X) (e := e) (y := y)
    h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hZ hse_pos
  convert hbase using 2
  · rename_i x
    dsimp [c]
    exact (mul_div_cancel_left₀ x hse_pos.ne').symm

/-- **Hansen Theorem 7.11 for ordinary OLS on nonsingular samples, HC1 face.**

The HC1-studentized scalar linear t-statistic transfers from `olsBetaStar` to
the ordinary-on-nonsingular wrapper `olsBetaOrZero`. -/
theorem olsHC1LinearTStatisticOrZero_tendstoInDistribution
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0
        (olsProjectionAsymptoticVariance μ X e (Rᵀ *ᵥ (fun _ : Unit => 1))).toNNReal)
      ν)
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop
      (fun ω =>
        Z ω / Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ()))
      (fun _ => μ) ν := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    olsHC1LinearTStatisticStar_tendstoInDistribution
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hZ hse_pos

/-- **Hansen Theorem 7.11 for ordinary OLS, HC1 standard-normal face.** -/
theorem olsHC1LinearTStatisticOrZero_tendstoInDistribution_standardNormal
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        ((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ()))
      atTop (fun x : ℝ => x) (fun _ => μ) (gaussianReal 0 1) := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    olsHC1LinearTStatisticStar_tendstoInDistribution_standardNormal
      (μ := μ) (X := X) (e := e) (y := y)
      h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos

/-- Absolute-value CMT for the ordinary HC1 scalar t-statistic. -/
theorem olsHC1LinearTStatisticOrZero_abs_tendstoInDistribution_standardNormalAbs
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        abs
          (((Real.sqrt (n : ℝ) •
            (R *ᵥ
              (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
              (fun _ : Unit => 1)) /
            Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
              (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())))
      atTop (fun x : ℝ => |x|) (fun _ => μ) (gaussianReal 0 1) := by
  simpa using
    tendstoInDistribution_abs_real
      (olsHC1LinearTStatisticOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos)

/-- Scalar one-degree-of-freedom HC1 Wald statistic for ordinary OLS. -/
theorem olsHC1LinearWaldStatisticOrZero_tendstoInDistribution_chiSquared_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleHC0Assumption76 μ X e) (β : k → ℝ)
    (R : Matrix Unit k ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX_meas : ∀ i, AEStronglyMeasurable (X i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hCrossWeight : ∀ a b l : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceCrossWeight
          (stackRegressors X n ω) (stackErrors e n ω) a b l))
    (hQuadWeight : ∀ a b l m : k, BoundedInProbability μ
      (fun n ω =>
        sampleScoreCovarianceQuadraticWeight
          (stackRegressors X n ω) a b l m))
    (hse_pos : 0 <
      Real.sqrt ((R * heteroskedasticAsymptoticCovariance μ X e * Rᵀ) () ())) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (((Real.sqrt (n : ℝ) •
          (R *ᵥ
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β))) ⬝ᵥ
            (fun _ : Unit => 1)) /
          Real.sqrt ((R * olsHeteroskedasticCovarianceHC1Star
            (stackRegressors X n ω) (stackOutcomes y n ω) * Rᵀ) () ())) ^ 2)
      atTop (fun x : ℝ => x) (fun _ => μ) (chiSquared 1) := by
  simpa using
    tendstoInDistribution_sq_standardNormal_chiSquared_one
      (olsHC1LinearTStatisticOrZero_tendstoInDistribution_standardNormal
        (μ := μ) (X := X) (e := e) (y := y)
        h β R hmodel hX_meas he_meas hCrossWeight hQuadWeight hse_pos)

/-- **Hansen Theorem 7.3, all scalar projections for totalized OLS with `Ω`.**

For every fixed direction `a`, the scaled totalized OLS error has Gaussian
limit with asymptotic variance `((Q⁻¹)'a)' Ω ((Q⁻¹)'a)`. This is the complete
projection-family form currently available before the vector/Cramér-Wold
wrapper is formalized. -/
theorem scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_covariance_all
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : (k → ℝ) → Ω' → ℝ}
    (hZ : ∀ a : k → ℝ,
      HasLaw (Z a)
        (gaussianReal 0 (olsProjectionAsymptoticVariance μ X e a).toNNReal) ν) :
    ∀ a : k → ℝ,
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          (Real.sqrt (n : ℝ) •
            (olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
        atTop (Z a) (fun _ => μ) ν :=
  fun a =>
    scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_covariance
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel (hZ a)

/-- **Hansen Theorem 7.3 for ordinary OLS on nonsingular samples, scalar-projection form.**

This transfers the scalar totalized-OLS CLT to `olsBetaOrZero`, which is ordinary
`olsBeta` on the nonsingular sample-Gram event and `0` otherwise. -/
theorem scoreProjection_olsBetaOrZero_tendstoInDistribution_gaussian_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β a : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : Ω' → ℝ}
    (hZ : HasLaw Z
      (gaussianReal 0 (olsProjectionAsymptoticVariance μ X e a).toNNReal) ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω =>
        (Real.sqrt (n : ℝ) •
          (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
      atTop Z (fun _ => μ) ν := by
  simpa [olsBetaOrZero_eq_olsBetaStar] using
    scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_covariance
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel hZ

/-- **Hansen Theorem 7.3, all scalar projections for ordinary OLS on nonsingular samples.**

This is the textbook-facing projection-family form for `olsBetaOrZero`: for
every fixed direction `a`, ordinary OLS on the nonsingular sample-Gram event has
the same scalar Gaussian limit as the totalized estimator. -/
theorem scoreProjection_olsBetaOrZero_tendstoInDistribution_gaussian_covariance_all
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure Ω'} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ}
    (h : SampleCLTAssumption72 μ X e) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    {Z : (k → ℝ) → Ω' → ℝ}
    (hZ : ∀ a : k → ℝ,
      HasLaw (Z a)
        (gaussianReal 0 (olsProjectionAsymptoticVariance μ X e a).toNNReal) ν) :
    ∀ a : k → ℝ,
      TendstoInDistribution
        (fun (n : ℕ) ω =>
          (Real.sqrt (n : ℝ) •
            (olsBetaOrZero (stackRegressors X n ω) (stackOutcomes y n ω) - β)) ⬝ᵥ a)
        atTop (Z a) (fun _ => μ) ν :=
  fun a =>
    scoreProjection_olsBetaOrZero_tendstoInDistribution_gaussian_covariance
      (μ := μ) (ν := ν) (X := X) (e := e) (y := y) h β a hmodel (hZ a)

end Assumption72

end HansenEconometrics
