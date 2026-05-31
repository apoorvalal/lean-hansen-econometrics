import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.UniformOn
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.AsymptoticUtils.MaxBounds
import HansenEconometrics.BootstrapUtils
import HansenEconometrics.Chapter6Asymptotics
import HansenEconometrics.Chapter7Asymptotics.Inference
import HansenEconometrics.ProbabilityUtils

/-!
# Chapter 10 — Resampling Methods

This module starts the theorem-facing Chapter 10 API for Hansen's resampling
methods.  The initial public surface covers the bootstrap convergence notions
used throughout the chapter:

* `chapter10_bootstrap_convergence_in_probability_of_convergence_in_probability`
  is Hansen Theorem 10.1.
* `chapter10_bootstrap_continuous_mapping_probability` is Hansen Theorem 10.3.
* `chapter10_bootstrap_lipschitz_mapping_probability` is the reusable
  Lipschitz mapping bridge used by Slutsky and Delta-method theorem wrappers.
* `chapter10_bootstrap_wlln_centered_of_tail_bound` is the reusable
  conditional-Markov bridge for the centered conclusion of Hansen Theorem 10.2.
* `chapter10_bootstrap_wlln_level_from_centered` is the Slutsky/addition step
  in Hansen Theorem 10.2: centered bootstrap WLLN plus the ordinary WLLN gives
  bootstrap convergence of the sample mean to the population mean.
* `chapter10_bootstrap_wlln_centered_of_second_moment_bound` is the
  Chebyshev/Marcinkiewicz bridge that turns Hansen's empirical second-moment
  bound into the centered conclusion of Theorem 10.2.
* `chapter10_bootstrap_wlln_centered_real_of_conditional_variance_bound` is the
  scalar conditional-Chebyshev constructor for the same Theorem 10.2 step.
* `chapter10_bootstrap_wlln_centered_of_l2_eLpNorm_bound` is the vector-valued
  conditional Markov constructor from a bootstrap `L²` seminorm bound.
* `bootstrapTailProb_zero_le_integral_norm_sq_div` and
  `chapter10_bootstrap_wlln_centered_of_integral_norm_sq_bound` are the
  textbook-facing vector second-moment bridges for Theorem 10.2.
* `chapter10_bootstrap_wlln_level_real_of_conditional_variance_bound` and
  `chapter10_bootstrap_wlln_level_of_l2_eLpNorm_bound` package centered
  constructors with the ordinary WLLN to give the level conclusion of Theorem
  10.2; `chapter10_bootstrap_wlln_level_of_integral_norm_sq_bound` is the
  corresponding vector second-moment level wrapper.
* `TendstoInBootstrapProbabilityIndexed` and
  `chapter10_indexed_bootstrap_wlln_centered_finSucc_resampleMean` provide the
  sample-size-indexed ordinary nonparametric-bootstrap version with resampling
  spaces `Fin (n+1) -> Fin (n+1)`, with
  `chapter10_indexed_bootstrap_wlln_centered_real_finSucc_resampleMean` as the
  scalar specialization;
  `chapter10_indexed_bootstrap_wlln_level_finSucc_resampleMean` packages the
  corresponding level conclusion, with
  `chapter10_indexed_bootstrap_wlln_level_real_finSucc_resampleMean` as the
  scalar specialization.
* `chapter10_indexed_bootstrap_continuous_mapping_probability` is the
  sample-size-indexed form of Hansen Theorem 10.3.
  `TendstoInBootstrapProbabilityIndexed.prodMk`, `.add`, `.neg`, and `.sub`
  are the indexed algebra constructors for product, sum, negation, and
  difference statistics.
* `TendstoInBootstrapDistribution` is Hansen Definition 10.2 for
  finite-dimensional random vectors, stated in the chapter-facing CDF form.
* `TendstoInBootstrapDistribution.of_tendsto_cdf` and congruence lemmas expose
  the reusable CDF bridge needed by later bootstrap CLT and delta-method
  wrappers.
* `chapter10_bootstrap_clt_gaussian_of_tendsto_cdf` is the Gaussian CDF wrapper
  for Hansen Theorem 10.4.
* `chapter10_bootstrap_clt_gaussian_of_weakDistribution` is the corresponding
  weak-distribution Gaussian wrapper, using null frontiers of coordinate lower
  orthants to recover Hansen Definition 10.2.
* `chapter10_bootstrap_clt_gaussian_of_weakDistribution_posDef` is the
  positive-definite covariance specialization matching Hansen Theorem 10.4.
* `multivariateGaussian_coordinateLE_frontier_null_of_posDef` supplies those
  Gaussian lower-orthant null-frontier premises from positive definite
  covariance matrices.
* `TendstoInBootstrapWeakDistribution` is a bounded-continuous-test-function
  backend for bootstrap distributional convergence, used by the distributional
  continuous-mapping theorem.
* `TendstoInBootstrapWeakDistributionIndexed` is the sample-size-indexed weak
  backend for ordinary nonparametric bootstrap laws whose resampling space
  varies with `n`.
* `TendstoInBootstrapWeakDistribution.congr` gives pointwise congruence for
  that weak backend.
* `bootstrapEventProbability` and
  `TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_boundedContinuous_sandwich`
  provide the Portmanteau-style event-probability bridge from bounded-continuous
  lower/upper sandwiches.
* `boundedContinuous_event_sandwich_of_null_frontier` constructs those
  bounded-continuous event sandwiches from a null-frontier hypothesis on the
  limit law.
* `boundedContinuous_event_integral_sandwich` and
  `bootstrapEventProbability_sandwich_of_boundedContinuous_event_sandwich`
  turn pointwise event-indicator sandwiches into conditional bootstrap integral
  sandwiches.
* `TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_null_frontier`
  and `chapter10_bootstrap_continuous_mapping_event_probability_of_null_frontier`
  combine the weak-distribution bridge with the null-frontier sandwich
  constructor.
* `TendstoInBootstrapWeakDistribution.bootstrapVectorCDF_tendsto_of_null_frontier`
  and `TendstoInBootstrapDistribution.of_weakDistribution_null_frontiers` connect
  the bounded-continuous weak-convergence layer back to Hansen's coordinate-CDF
  Definition 10.2.
* `TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers`
  gives the same weak-to-CDF bridge for sample-size-dependent bootstrap spaces.
* `TendstoInBootstrapWeakDistribution.integral_realClip_tendsto` and
  `TendstoInBootstrapWeakDistribution.integral_realClip_sq_tendsto` turn weak
  bootstrap convergence into clipped first- and second-moment convergence for
  Hansen Theorem 10.9, with indexed counterparts for sample-size-dependent
  bootstrap spaces.
* `TendstoInBootstrapWeakDistribution.integral_tendsto_of_realClip_tails` and
  `TendstoInBootstrapWeakDistribution.integral_sq_tendsto_of_realClip_tails`
  add the UI/tail unclipping step for the first two moments, also in indexed
  form.
* `TendstoInBootstrapWeakDistribution.integral_tendsto_of_realClip_tailProb`
  and `TendstoInBootstrapWeakDistribution.integral_sq_tendsto_of_realClip_tailProb`
  provide the probability-mode version of that unclipping step, also in indexed
  form.
* `bootstrapMeanReal_realClip_tails_of_tail_integrals` and
  `bootstrapSecondMomentReal_realClip_tails_of_tail_integrals` turn concrete
  first- and second-tail integral controls into those unclipping premises.
* `bootstrapTailAbsIntegral_tendsto_zero_of_tailSqIntegral` uses squared-tail
  control at thresholds at least one to supply first-tail control.
* `chapter10_bootstrap_continuous_mapping_distribution` is the globally
  continuous face of Hansen Theorem 10.5.
* `chapter10_indexed_bootstrap_continuous_mapping_distribution` is the
  sample-size-indexed weak-convergence face of Hansen Theorem 10.5.
* `chapter10_bootstrap_continuous_mapping_distribution_of_null_frontiers` and
  `chapter10_bootstrap_ae_continuous_mapping_distribution_of_null_frontiers`
  and their indexed counterparts are the corresponding finite-dimensional CDF
  faces under null-frontier hypotheses for transformed lower orthants.
* `chapter10_bootstrap_continuous_mapping_event_probability` is the globally
  continuous event-probability face of Hansen Theorem 10.5, with an indexed
  counterpart for sample-size-dependent bootstrap spaces.
* `BootstrapAEMappingPremise` records the textbook measurability and
  a.e.-continuity condition for Hansen Theorem 10.5, with global continuity as
  a constructor; the corresponding
  `chapter10_bootstrap_ae_continuous_mapping_event_probability_of_null_frontier`
  wrapper and its indexed counterpart apply the null-frontier event-probability
  bridge once transformed weak convergence has been supplied.
* `chapter10_bootstrap_delta_method_linear` and
  `chapter10_bootstrap_delta_method_gaussian` are the linear-image and
  Gaussian covariance faces of Hansen Theorem 10.6, with
  `chapter10_bootstrap_delta_method_gaussian_distribution` exposing the
  corresponding Hansen Definition 10.2 CDF surface. Indexed counterparts cover
  sample-size-dependent bootstrap spaces.
* `chapter10_bootstrap_smooth_function_gaussian_of_linearization` and
  `chapter10_bootstrap_smooth_function_gaussian_distribution_of_linearization`
  are the weak and CDF smooth-function Gaussian wrappers for Hansen Theorem
  10.7 once the bootstrap statistic has been reduced to its
  derivative-linearized form, with indexed analogues for varying resampling
  spaces.
* `TendstoInBootstrapWeakDistribution.of_integral_difference_zero` and
  `chapter10_bootstrap_smooth_function_gaussian_of_integral_linearization`
  transfer a bootstrap weak limit across a nonlinear linearization when every
  bounded-continuous test-function integral differs by `oₚ(1)`; indexed
  versions provide the same route for sample-size-dependent spaces.
* `TendstoInBootstrapWeakDistribution.integral_tendsto_of_boundedContinuous_sandwich`
  and `TendstoInBootstrapWeakDistribution.map_of_boundedContinuous_sandwich`
  transfer weak bootstrap convergence through bounded-continuous sandwich
  approximations, with indexed counterparts.
* `TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_integral_diff`,
  `TendstoInBootstrapWeakDistribution.bootstrapVectorCDF_tendsto_of_integral_diff`,
  `TendstoInBootstrapDistribution.of_weakDistribution_integral_diff`, and their
  indexed counterparts
  push that same linearization transfer through null-frontier event probabilities
  and Hansen's coordinate-CDF API.
* `finiteReplicationMeanReal_tendsto_of_integral_sq_error_le_inv` and its
  moment/covariance wrappers turn bounded-trimmed finite-replication WLLN
  `L²` error bounds into the moment premises used in Hansen Theorem 10.11.
* `integral_uniformOn_univ_eq_card_inv_smul_sum` is the finite empirical mean
  identity behind equations (10.10) and (10.12).
* `empiricalMean`, `empiricalBootstrapResampleMean`,
  `integral_uniformOn_fun_eval_eq_empiricalMean`,
  `integral_empiricalBootstrapResampleMean_eq_of_coord_integrals`, and
  `integral_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_zero` provide
  the finite-resampling sample-mean API used by the concrete Theorem 10.2 path.
* `integral_norm_sq_uniformOn_univ_eq_card_inv_smul_sum` and
  `memLp_two_uniformOn_univ` are finite empirical squared-norm helpers used by
  the concrete Theorem 10.2 second-moment route.
* `variance_uniformOn_univ_eq_card_inv_smul_sum_sq_centered` is the scalar
  finite empirical variance identity behind equation (10.11).
* `variance_empiricalBootstrapResampleMean_uniformOn_fun_eq_inv_card_mul` and
  `integral_sq_resampleMean_sub_empiricalMean_le_inv_card_mul_secondMoment`
  provide the scalar bootstrap sample-mean variance and second-moment bound
  behind equation (10.13) and the Theorem 10.2 proof.
* `covMat_uniformOn_univ_eq_card_inv_smul_sum_centered` is the
  finite-dimensional empirical covariance matrix identity behind (10.11).
* `covMat_empiricalBootstrapResampleMean_uniformOn_fun_eq_inv_card_smul`,
  `trace_covMat_resampleMean_eq_inv_card_mul`, and
  `trace_covMat_resampleMean_le_inv_card_mul_secondMoment` provide the
  finite-dimensional covariance and trace forms of equation (10.13), while
  `integral_norm_sq_resampleMean_sub_empiricalMean_le_secondMoment` gives the
  Euclidean norm second-moment bound used in the vector Theorem 10.2 proof.
  `integral_norm_sq_finSucc_resampleMean_sub_empiricalMean_le_marcinkiewicz`
  packages that finite result in the `Fin (n+1)` Marcinkiewicz scale used by
  the indexed centered WLLN.
* `CDFQuantileBracket`, `tendstoInMeasure_quantile_of_cdf_brackets`,
  `scalarCDF`, `bootstrapScalarCDF`, and
  `bootstrapScalarQuantile_tendsto_of_cdf_brackets`
  provide the pointwise-CDF bracketing route from bootstrap CDF convergence to
  endpoint and critical-value convergence for Theorems 10.13, 10.14, and 10.16.
  `TendstoInBootstrapDistribution.bootstrapScalarCDF_tendsto_unit` extracts
  scalar CDF convergence from the one-dimensional Definition 10.2 API, while
  `bootstrapScalarQuantile_tendsto_of_bootstrapDistribution_unit` and
  `bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit`
  feed that bridge directly into quantile convergence.
  `scalarCDF_mono`, `bootstrapScalarCDF_mono`, and the finite-measure
  lower-quantile wrappers discharge the ordinary CDF monotonicity premise.
  `scalarCDF_id_eq_cdf` and the law-CDF lower-quantile wrappers connect the
  scalar bridge to Mathlib's `cdf η` notation used by the coverage theorems;
  the Definition 10.2-facing coverage/test wrappers compose this bridge with
  the percentile, percentile-`t`, and critical-value results.
  `bootstrapScalarCDF_eq_cdf_map` and
  `bootstrapScalarCDF_local_right_lt_of_aemeasurable` discharge the
  right-local CDF bracketing premise from a.e. measurability, while the
  probability-level lower-quantile wrappers also discharge nonemptiness and
  boundedness at levels `0 < p < 1`.
  The probability-level percentile, percentile-`t`, and critical-value wrappers
  apply those discharged quantile premises directly to Theorems 10.13, 10.14,
  and 10.16.
  Their indexed counterparts expose the same local-limit-CDF and strict-CDF
  routes for sample-size-dependent bootstrap spaces.
  `bootstrapScalarQuantileIndexed_*` and
  `bootstrapScalarLowerQuantileIndexed_*` mirror the fixed-space scalar
  quantile backend for indexed bootstrap laws.
  The two-sided critical-value route also has local-limit-CDF bracket variants,
  avoiding a global strict-CDF assumption for absolute-statistic laws.
  `strictMono_cdf_brackets` and the corresponding strict-CDF quantile wrappers
  package the common `G(q) = p` plus strict-monotonicity calibration.
  `lowerCDFQuantile`, `lowerCDFQuantile_bracket_of_stieltjesFunction`, and
  `bootstrapScalarLowerQuantile_tendsto_of_strictMono_cdf` add the concrete
  lower-generalized-inverse route for right-continuous CDFs.
* `chapter10_marcinkiewicz_wlln_natPower_of_uniformIntegrable` is the
  natural-power face of Hansen Theorem 10.20.
* `chapter10_marcinkiewicz_wlln_rpow_of_uniformIntegrable` is Hansen Theorem
  10.20 in its real-exponent `r > 1` form.
* `chapter10_bootstrap_smooth_variance_consistency` is the plug-in covariance
  continuous-mapping bridge behind Hansen Theorem 10.8.
* `chapter10_bootstrap_smooth_variance_consistency_of_components` derives the
  Theorem 10.8 bridge from separate bootstrap convergence of the plug-in
  Jacobian and covariance inputs. The continuous-plugin and indexed
  counterparts cover stochastic plug-ins obtained by applying continuous maps
  to a bootstrap statistic, including sample-size-dependent bootstrap spaces.
* `chapter10_bootstrap_variance_consistency_of_moment_convergence` is the
  moment-convergence bridge behind Hansen Theorem 10.9; the indexed
  counterpart uses `bootstrapMeanRealIndexed`,
  `bootstrapSecondMomentRealIndexed`, and `bootstrapVarianceRealIndexed`.
* `chapter10_bootstrap_variance_consistency_of_weak_distribution_realClip_tails`
  derives that bridge's moment premises from bootstrap weak convergence plus
  first/second clipping-tail controls, with an indexed counterpart for
  sample-size-dependent bootstrap spaces.
* `chapter10_bootstrap_variance_consistency_of_weak_distribution_tail_integrals`
  packages the same Theorem 10.9 conclusion from concrete first/second
  tail-integral controls.
* `chapter10_bootstrap_variance_consistency_of_weak_distribution_square_tail_integrals`
  reduces that conclusion to a single squared-tail-integral condition, the
  measure-theoretic core of Hansen's uniform-square-integrability step.
* `chapter10_bootstrap_variance_consistency_of_weak_distribution_uniform_square_tail`
  states the Theorem 10.9 conclusion from the textbook-style uniform
  square-tail condition: for every tolerance, a squared tail is small in
  probability at a large threshold; the indexed counterpart covers
  sample-size-dependent bootstrap spaces.
* `BootstrapUniformSquareTail` and
  `BootstrapUniformSquareTailIndexed` expose that long tail condition as a
  reusable theorem-facing assumption.
* `chapter10_bootstrap_mean_tendsto_of_weak_distribution_uniform_square_tail`
  and `chapter10_bootstrap_secondMoment_tendsto_of_weak_distribution_uniform_square_tail`
  expose the conditional moment convergence pieces used by the Theorem 10.9
  variance bridge, with indexed counterparts for sample-size-dependent spaces.
* `chapter10_bootstrap_meanVec_tendsto_of_weak_distribution_of_uniformSquareTail`
  is the finite-dimensional coordinatewise mean-vector version used by the
  covariance and trimmed-variance layers.
* `chapter10_bootstrap_crossMomentMat_tendsto_of_weak_distribution_of_uniformSquareTail`
  derives finite-dimensional conditional cross-moment convergence from scalar
  uniform-square-tail conditions on coordinates and coordinate sums.
* `chapter10_smooth_bootstrap_variance_consistency_of_moment_convergence` is
  the smooth-function variance-consistency wrapper for Hansen Theorem 10.10.
* `chapter10_trimmedBootstrapVariance_tendsto_of_moments` is the trimmed
  conditional covariance bridge behind Hansen Theorem 10.12.
* `norm_trimmedBootstrapStatistic_le_of_nonneg` and its indexed counterpart
  expose the pointwise threshold bound for Hansen's trimmed bootstrap statistic.
* `chapter10_bootstrap_covarianceMat_tendsto_of_zero_mean_moments` exposes the
  centered covariance-matrix target directly from zero conditional means and
  cross-moment convergence.
* `chapter10_bootstrap_regression_theta_gaussian` and
  `chapter10_bootstrap_regression_theta_gaussian_distribution` are
  regression-facing weak and CDF Gaussian wrappers for Hansen Theorem 10.18;
  indexed counterparts cover sample-size-dependent bootstrap spaces.
  `chapter10_bootstrap_regression_trimmedVariance_tendsto` is the corresponding
  variance wrapper for Hansen Theorem 10.19, with an indexed trimmed-covariance
  counterpart.
* `chapter10_finiteReplicationVariance_tendsto_of_moments` is the
  finite-replication variance moment bridge behind Hansen Theorem 10.11; the
  centered scalar wrapper states the same result for Hansen's displayed
  `1 / (B - 1)` estimator.
* `chapter10_finiteReplicationVariance_tendsto_of_bootstrap_variance` and
  `chapter10_finiteReplicationVariance_tendsto_of_weak_distribution_uniformSquareTail`
  combine finite-replication simulation error with the conditional-bootstrap
  variance consistency layer from Hansen Theorem 10.9, with indexed
  counterparts for sample-size-dependent bootstrap spaces; the moment-premise
  and centered-scalar wrappers expose the same transfer directly from
  conditional bootstrap mean/second-moment convergence and Hansen's displayed
  `1 / (B - 1)` estimator.
* `chapter10_finiteReplicationCovarianceMat_tendsto_of_moments` is the
  finite-dimensional covariance-matrix bridge behind Hansen Theorem 10.11.
* `chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_moments` is the
  textbook-centered finite-replication covariance-matrix bridge for Theorem
  10.11.
* `chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance`
  combines finite-replication covariance simulation error with conditional
  bootstrap covariance consistency, with indexed counterparts for
  sample-size-dependent bootstrap spaces. Weak/uniform-square-tail wrappers
  compose this transfer with the Theorem 10.9 conditional covariance layer.
  Scalar and matrix moment-premise wrappers expose the same transfer directly
  from conditional bootstrap mean and cross-moment convergence, with indexed
  mean-vector/cross-moment/covariance bridges and zero-mean specializations for
  centered targets. The trimmed zero-mean wrapper exposes
  the Theorem 10.12 target covariance directly, with indexed trimmed
  finite-replication counterparts.
* `chapter10_percentileCI_coverage_tendsto_of_joint_quantile_limit` is the
  coverage bridge behind Hansen Theorem 10.13.
* `percentileCoverageVector_tendstoInDistribution_of_components` assembles the
  joint convergence premise for that bridge from scalar estimator-error
  convergence and endpoint convergence in probability.
* `chapter10_percentileCI_coverage_tendsto` is the calibrated percentile
  coverage wrapper, with scalar-event support from
  `percentileCoverageLimit_measure_set_eq` and
  `chapter10_percentileCI_coverage_tendsto_of_scalar_limit_coverage`.
* `percentileCoverage_frontier_null_of_boundary_null` and
  `chapter10_percentileCI_coverage_tendsto_of_scalar_limit` replace the
  percentile vector-frontier premise with scalar endpoint-boundary null mass.
* `percentileCoverage_scalar_event_eq_law` and
  `chapter10_percentileCI_coverage_tendsto_of_limit_law` state the percentile
  calibration through the non-atomic law of the scalar limit statistic.
* `chapter10_percentileCI_coverage_tendsto_of_limit_law_cdf` is the CDF-mass
  specialization of that law-level percentile calibration.
* `chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_limit_law_cdf`
  is the endpoint-CDF form with limiting coverage `1 - α`.
* `chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_components_law_cdf`
  combines componentwise Slutsky convergence with the endpoint-CDF calibration;
  `chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf`
  is the symmetric `[-q, q]` endpoint specialization.
* `chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles`
  identifies those symmetric percentile endpoints as original-scale shifts of
  lower generalized inverses of conditional bootstrap CDFs.
* `chapter10_percentileTCI_coverage_tendsto_of_joint_quantile_limit` is the
  percentile-`t` coverage bridge behind Hansen Theorem 10.14.
* `percentileTCoverageVector_tendstoInDistribution_of_components` assembles
  the joint convergence premise from sample t-ratio convergence and endpoint
  convergence in probability.
* `percentileTCoverageLimit_measure_set_eq` and
  `chapter10_percentileTCI_coverage_tendsto_of_scalar_limit_coverage` rewrite
  the percentile-`t` limit vector event as the scalar event `qL <= ξ <= qU`.
* `percentileTCoverage_frontier_null_of_boundary_null` and
  `chapter10_percentileTCI_coverage_tendsto_of_scalar_limit` replace the
  percentile-`t` vector-frontier premise with scalar endpoint-boundary null
  mass.
* `percentileTCoverage_scalar_event_eq_law` and
  `chapter10_percentileTCI_coverage_tendsto_of_limit_law` state the
  percentile-`t` calibration through the non-atomic law of the scalar limit
  t-ratio.
* `chapter10_percentileTCI_coverage_tendsto_of_limit_law_cdf` is the CDF-mass
  specialization of the percentile-`t` law-level calibration.
* `chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_limit_law_cdf`
  is the endpoint-CDF form with limiting coverage `1 - α`.
* `chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_law_cdf`
  combines componentwise Slutsky convergence with the endpoint-CDF calibration;
  `chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf`
  is the symmetric `[-q, q]` endpoint specialization.
* `chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles`
  identifies those symmetric percentile-`t` endpoints as lower generalized
  inverses of conditional bootstrap CDFs.
* `chapter10_bootstrap_abs_test_rejectionProb_tendsto_of_joint_critical_value_limit`
  is the bootstrap-test critical-value bridge behind Hansen Theorem 10.16.
* `bootstrapAbsTestVector_tendstoInDistribution_of_components` assembles the
  joint convergence premise from statistic convergence and critical-value
  convergence in probability.
* `bootstrapAbsTestLimit_measure_rejectionSet_eq` and
  `chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_scalar_limit_rejection`
  rewrite the bootstrap-test limit vector event as the scalar rejection event
  `q < |ξ|`.
* `bootstrapAbsTest_frontier_null_of_boundary_null` and
  `chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_scalar_limit`
  replace the bootstrap-test vector-frontier premise with scalar critical-value
  boundary null mass.
* `bootstrapAbsTest_scalar_rejection_eq_law` and
  `chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_limit_law` state
  bootstrap-test calibration through the non-atomic law of the scalar limit
  statistic.
* `chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_limit_law_cdf`
  states the same two-sided test calibration in CDF-increment form.
* `chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_limit_law_cdf_endpoints`
  is the endpoint-CDF form with limiting size `α`.
* `chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_components_law_cdf_endpoints`
  combines componentwise Slutsky convergence with the endpoint-CDF calibration.
* `chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_lowerQuantile`
  identifies the bootstrap critical value as a lower generalized inverse of a
  conditional bootstrap CDF.
* `chapter10_percentileT_secondOrder_interval_expansion` reuses the Chapter 7
  Edgeworth interface to expose the symmetric percentile-`t` refinement behind
  Hansen Theorem 10.15.
* `secondOrder_scaled_probability_transfer` and
  `chapter10_percentileT_secondOrder_interval_expansion_of_transfer` transfer
  that refinement from fixed symmetric critical values to random/bootstrap
  percentile-`t` intervals when the replacement error is `o(n⁻¹)`.
* `chapter10_abs_test_secondOrder_rejection_expansion` gives the fixed-critical
  two-sided rejection-probability Edgeworth expansion used in Hansen Theorem
  10.17.
* `chapter10_abs_test_secondOrder_rejection_expansion_of_transfer` transfers
  that fixed-critical refinement to random/bootstrap critical values when the
  replacement error is `o(n⁻¹)`.

The concrete nonparametric-bootstrap sample-mean, CLT, variance, percentile,
and regression results are built on top of this two-probability-space layer.
Detailed theorem-by-theorem status lives in `inventory/ch10-inventory.md`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix Matrix.Norms.Elementwise

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

section EmpiricalDistribution

variable {ι : Type*} [MeasurableSpace ι] [Fintype ι]

/-- Uniform sampling from a finite empirical support is normalized counting
measure. -/
theorem uniformOn_univ_eq_inv_card_smul_count :
    (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
      ((Fintype.card ι : ℝ≥0∞)⁻¹) • Measure.count := by
  ext s hs
  rw [ProbabilityTheory.uniformOn_univ, Measure.smul_apply]
  simp [ENNReal.div_eq_inv_mul]

variable [MeasurableSingletonClass ι]

/-- Finite-sample empirical mean. -/
noncomputable def empiricalMean
    [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : ι → E) : E :=
  ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, Y i

/-- Mean of a bootstrap resample indexed by `κ`.

The map `I ωs t` is the original observation selected by bootstrap draw `t` at
resampling point `ωs`.  For the ordinary nonparametric bootstrap, `Ωs` is a
finite function space and `I ωs t = ωs t`. -/
noncomputable def empiricalBootstrapResampleMean
    {κ : Type*} [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : ι → E) (I : Ωs → κ → ι) (ωs : Ωs) : E :=
  ((Fintype.card κ : ℝ)⁻¹) • ∑ t, Y (I ωs t)

/-- Empirical mean identity for one bootstrap draw.

For any finite empirical support, integrating a statistic under the uniform
resampling law equals the finite-sample average.  This is the measure-theoretic
form of Hansen's equations (10.10) and (10.12). -/
theorem integral_uniformOn_univ_eq_card_inv_smul_sum
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : ι → E) :
    ∫ i, Y i ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, Y i := by
  rw [uniformOn_univ_eq_inv_card_smul_count, integral_smul_measure, integral_count]

/-- Empirical mean identity using the canonical `empiricalMean` API. -/
theorem integral_uniformOn_univ_eq_empiricalMean
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : ι → E) :
    ∫ i, Y i ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
      empiricalMean Y :=
  integral_uniformOn_univ_eq_card_inv_smul_sum Y

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Coordinate marginal identity for finite uniform resampling.

If a bootstrap resampling point is a function `κ → ι`, drawn uniformly from
all such functions, then each coordinate has the empirical uniform law on
`ι`.  This is the finite-support marginal calculation behind Hansen's
nonparametric bootstrap equations (10.10) and (10.12). -/
theorem integral_uniformOn_fun_eval_eq_empiricalMean
    {κ : Type*} [MeasurableSpace (κ → ι)] [Finite κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : ι → E) (t : κ) :
    ∫ ωs : κ → ι, Y (ωs t)
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      empiricalMean Y := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  rw [integral_uniformOn_univ_eq_card_inv_smul_sum, empiricalMean]
  have hsum :
      (∑ ωs : κ → ι, Y (ωs t)) =
        (Fintype.card ι ^ (Fintype.card κ - 1)) • ∑ i, Y i := by
    simpa [Fintype.piFinset_univ] using
      (Fintype.sum_piFinset_apply (f := Y) (s := (Finset.univ : Finset ι)) (i := t))
  rw [hsum]
  rw [← Nat.cast_smul_eq_nsmul ℝ (Fintype.card ι ^ (Fintype.card κ - 1))
      (∑ i, Y i), smul_smul]
  have hι_ne : (Fintype.card ι : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hκ_card : (Fintype.card κ - 1) + 1 = Fintype.card κ :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)
  have hfun_card :
      (Fintype.card (κ → ι) : ℝ) =
        (Fintype.card ι : ℝ) ^ Fintype.card κ := by
    exact_mod_cast (Fintype.card_fun (α := κ) (β := ι))
  have hpow_succ :
      (Fintype.card ι : ℝ) ^ Fintype.card κ =
        (Fintype.card ι : ℝ) ^ (Fintype.card κ - 1) *
          (Fintype.card ι : ℝ) := by
    calc
      (Fintype.card ι : ℝ) ^ Fintype.card κ =
          (Fintype.card ι : ℝ) ^ ((Fintype.card κ - 1) + 1) := by
            rw [hκ_card]
      _ = (Fintype.card ι : ℝ) ^ (Fintype.card κ - 1) *
          (Fintype.card ι : ℝ) := by
            rw [pow_succ]
  have hcoeff :
      ((Fintype.card (κ → ι) : ℝ≥0∞)⁻¹).toReal *
          ((Fintype.card ι ^ (Fintype.card κ - 1) : ℕ) : ℝ) =
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal := by
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_pow]
    rw [hfun_card, hpow_succ]
    field_simp [hι_ne, pow_ne_zero _ hι_ne]
  rw [hcoeff]

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- If every bootstrap draw coordinate has the same conditional mean, then the
bootstrap resample mean has that conditional mean.

This is the finite-resampling linearity bridge used before specializing the
coordinate marginal law to uniform resampling from the empirical support. -/
theorem integral_empiricalBootstrapResampleMean_eq_of_coord_integrals
    {κ : Type*} [Fintype κ] [Nonempty κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure Ωs} {Y : ι → E} {I : Ωs → κ → ι} {m : E}
    (hInt : ∀ t, Integrable (fun ωs => Y (I ωs t)) P)
    (hcoord : ∀ t, ∫ ωs, Y (I ωs t) ∂P = m) :
    ∫ ωs, empiricalBootstrapResampleMean Y I ωs ∂P = m := by
  change ∫ ωs, ((Fintype.card κ : ℝ)⁻¹) • ∑ t, Y (I ωs t) ∂P = m
  rw [integral_smul]
  rw [integral_finset_sum]
  · simp_rw [hcoord]
    rw [Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℝ (Fintype.card κ) m, smul_smul]
    have hcard_ne : (Fintype.card κ : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [inv_mul_cancel₀ hcard_ne, one_smul]
  · intro t _ht
    exact hInt t

omit [MeasurableSpace ι] [Fintype ι] [MeasurableSingletonClass ι] in
/-- Centered version of
`integral_empiricalBootstrapResampleMean_eq_of_coord_integrals`.

If every bootstrap draw coordinate has conditional mean `m`, then the resample
mean centered at `m` has conditional mean zero. -/
theorem integral_empiricalBootstrapResampleMean_sub_eq_zero_of_coord_integrals
    {κ : Type*} [Fintype κ] [Nonempty κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : Measure Ωs} [IsProbabilityMeasure P]
    {Y : ι → E} {I : Ωs → κ → ι} {m : E}
    (hInt : ∀ t, Integrable (fun ωs => Y (I ωs t)) P)
    (hcoord : ∀ t, ∫ ωs, Y (I ωs t) ∂P = m) :
    ∫ ωs, empiricalBootstrapResampleMean Y I ωs - m ∂P = 0 := by
  have hmean :
      ∫ ωs, empiricalBootstrapResampleMean Y I ωs ∂P = m :=
    integral_empiricalBootstrapResampleMean_eq_of_coord_integrals
      (P := P) (Y := Y) (I := I) (m := m) hInt hcoord
  have hresampleInt :
      Integrable (fun ωs => empiricalBootstrapResampleMean Y I ωs) P := by
    change Integrable
      (fun ωs => ((Fintype.card κ : ℝ)⁻¹) • ∑ t, Y (I ωs t)) P
    exact Integrable.smul ((Fintype.card κ : ℝ)⁻¹)
      (integrable_finset_sum (s := Finset.univ)
        (f := fun t ωs => Y (I ωs t)) (fun t _ht => hInt t))
  rw [integral_sub hresampleInt (integrable_const m), hmean]
  simp

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Mean of the ordinary finite nonparametric bootstrap sample mean.

When the bootstrap resampling point is a function `κ → ι` drawn uniformly from
all resamples, the conditional mean of the resample mean is exactly the
finite-sample empirical mean.  This specializes the coordinate marginal law to
the textbook resample-mean object in Hansen's equations (10.10) and (10.12). -/
theorem integral_empiricalBootstrapResampleMean_uniformOn_fun_eq_empiricalMean
    {κ : Type*} [MeasurableSpace (κ → ι)] [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : ι → E) :
    ∫ ωs : κ → ι, empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      empiricalMean Y := by
  classical
  exact integral_empiricalBootstrapResampleMean_eq_of_coord_integrals
    (P := (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)))
    (Y := Y) (I := fun ωs t => ωs t) (m := empiricalMean Y)
    (fun _t => Integrable.of_finite)
    (fun t => integral_uniformOn_fun_eval_eq_empiricalMean (Y := Y) t)

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Centered mean of the ordinary finite nonparametric bootstrap sample mean.

The resample mean, centered at the empirical mean, has conditional mean zero
under the finite uniform law over all resamples. -/
theorem integral_empiricalBootstrapResampleMean_uniformOn_fun_sub_eq_zero
    {κ : Type*} [MeasurableSpace (κ → ι)] [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : ι → E) :
    ∫ ωs : κ → ι,
        empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      0 := by
  classical
  exact integral_empiricalBootstrapResampleMean_sub_eq_zero_of_coord_integrals
    (P := (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)))
    (Y := Y) (I := fun ωs t => ωs t) (m := empiricalMean Y)
    (fun _t => Integrable.of_finite)
    (fun t => integral_uniformOn_fun_eval_eq_empiricalMean (Y := Y) t)

/-- Finite empirical second-moment identity for one bootstrap draw.

Under uniform resampling from a finite empirical support, the conditional
expectation of the squared norm is the finite-sample average of squared norms.
This is the norm-valued companion to Hansen's equations (10.10) and (10.12). -/
theorem integral_norm_sq_uniformOn_univ_eq_card_inv_smul_sum
    [NormedAddCommGroup E] (Y : ι → E) :
    ∫ i, ‖Y i‖ ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, ‖Y i‖ ^ 2 :=
  integral_uniformOn_univ_eq_card_inv_smul_sum (E := ℝ)
    (fun i => ‖Y i‖ ^ 2)

/-- Finite empirical second-moment bound from a pointwise norm envelope. -/
theorem integral_norm_sq_uniformOn_univ_le_card_inv_smul_sum_sq_of_norm_le
    [NormedAddCommGroup E] (Y : ι → E) (u : ι → ℝ)
    (hY : ∀ i, ‖Y i‖ ≤ |u i|) :
    ∫ i, ‖Y i‖ ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) ≤
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, u i ^ 2 := by
  rw [integral_norm_sq_uniformOn_univ_eq_card_inv_smul_sum]
  have hsum : ∑ i, ‖Y i‖ ^ 2 ≤ ∑ i, u i ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hsq := pow_le_pow_left₀ (norm_nonneg (Y i)) (hY i) 2
    simpa [sq_abs] using hsq
  rw [smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left hsum ENNReal.toReal_nonneg

/-- Centered finite empirical squared-norm identity.

This specializes the squared-norm identity to deviations from the empirical
mean, the one-draw calculation that feeds the vector Theorem 10.2
second-moment bound. -/
theorem integral_norm_sq_centered_uniformOn_univ_eq_card_inv_smul_sum
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (Y : ι → E) :
    ∫ i, ‖Y i - ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j‖ ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal •
        ∑ i, ‖Y i - ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j‖ ^ 2 :=
  integral_norm_sq_uniformOn_univ_eq_card_inv_smul_sum
    (fun i => Y i - ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j)

/-- Centered finite empirical second-moment bound from a pointwise envelope. -/
theorem integral_norm_sq_centered_uniformOn_univ_le_card_inv_smul_sum_sq_of_norm_le
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Y : ι → E) (u : ι → ℝ)
    (hY :
      ∀ i,
        ‖Y i - ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j‖ ≤ |u i|) :
    ∫ i, ‖Y i - ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j‖ ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) ≤
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, u i ^ 2 :=
  integral_norm_sq_uniformOn_univ_le_card_inv_smul_sum_sq_of_norm_le
    (fun i => Y i - ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j)
    u hY

omit [Fintype ι] in
/-- Every finite empirical statistic is square-integrable under uniform
resampling from a nonempty support. -/
theorem memLp_two_uniformOn_univ [Finite ι] [Nonempty ι]
    [NormedAddCommGroup E] (Y : ι → E) :
    MemLp Y 2 (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) := by
  exact ⟨AEStronglyMeasurable.of_discrete,
    eLpNorm_lt_top_of_finite
      (f := Y) (p := (2 : ℝ≥0∞))
      (μ := (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι))⟩

/-- Scalar empirical variance identity for one bootstrap draw.

This is the scalar version of Hansen's exact bootstrap covariance formula
(10.11): under uniform resampling from a finite empirical support, the
variance is the average squared deviation from the empirical mean. -/
theorem variance_uniformOn_univ_eq_card_inv_smul_sum_sq_centered
    (Y : ι → ℝ) :
    Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)] =
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal •
        ∑ i, (Y i -
          ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j) ^ 2 := by
  have hmean :
      ∫ i, Y i ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j :=
    integral_uniformOn_univ_eq_card_inv_smul_sum Y
  rw [ProbabilityTheory.variance_eq_integral (measurable_of_finite Y).aemeasurable, hmean]
  exact integral_uniformOn_univ_eq_card_inv_smul_sum
    (fun i => (Y i - ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j) ^ 2)

omit [Fintype ι] in
/-- Scalar variance of the ordinary finite nonparametric bootstrap sample mean.

This is the scalar form of Hansen equation (10.13): the conditional variance
of the bootstrap sample mean is the empirical one-draw variance divided by the
number of bootstrap draws. -/
theorem variance_empiricalBootstrapResampleMean_uniformOn_fun_eq_inv_card_mul
    {κ : Type*} [Fintype κ] [Nonempty κ] [Finite ι] [Nonempty ι]
    (Y : ι → ℝ) :
    Var[fun ωs : κ → ι => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs;
        (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))] =
      (Fintype.card κ : ℝ)⁻¹ *
        Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)] := by
  classical
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let c : ℝ := (Fintype.card κ : ℝ)⁻¹
  have hPκ : Pκ = Measure.pi (fun _ : κ => Pι) := by
    simpa [Pκ, Pι] using
      (ProbabilityTheory.uniformOn_pi (Ω := ι) (ι := κ)
        (f := fun _ : κ => (Set.univ : Set ι)))
  have hmem : ∀ t : κ, MemLp Y 2 Pι := fun _ =>
    memLp_two_uniformOn_univ (Y := Y)
  have hvarsum :
      Var[(∑ t, fun ωs : κ → ι => Y (ωs t)); Measure.pi (fun _ : κ => Pι)] =
        ∑ _t : κ, Var[Y; Pι] := by
    simpa using
      (ProbabilityTheory.variance_sum_pi
        (Ω := fun _ : κ => ι) (μ := fun _ : κ => Pι)
        (X := fun _ : κ => Y) hmem)
  have hsumvar :
      (∑ _t : κ, Var[Y; Pι]) = (Fintype.card κ : ℝ) * Var[Y; Pι] := by
    simp
  have hsample :
      (fun ωs : κ → ι =>
          empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs) =
        fun ωs : κ → ι => c * (∑ t, fun ωs : κ → ι => Y (ωs t)) ωs := by
    ext ωs
    simp [empiricalBootstrapResampleMean, c]
  calc
    Var[fun ωs : κ → ι => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs; Pκ]
        = Var[fun ωs : κ → ι => c * (∑ t, fun ωs : κ → ι => Y (ωs t)) ωs; Pκ] := by
          rw [hsample]
    _ = Var[fun ωs : κ → ι => c * (∑ t, fun ωs : κ → ι => Y (ωs t)) ωs;
          Measure.pi (fun _ : κ => Pι)] := by
          rw [hPκ]
    _ = c ^ 2 * Var[(∑ t, fun ωs : κ → ι => Y (ωs t));
          Measure.pi (fun _ : κ => Pι)] := by
          rw [ProbabilityTheory.variance_const_mul]
    _ = c ^ 2 * ((Fintype.card κ : ℝ) * Var[Y; Pι]) := by
          rw [hvarsum, hsumvar]
    _ = (Fintype.card κ : ℝ)⁻¹ * Var[Y; Pι] := by
          have hcard : (Fintype.card κ : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr Fintype.card_ne_zero
          dsimp [c]
          field_simp [hcard]

/-- Centered second moment of the ordinary finite nonparametric bootstrap
sample mean.

This is Hansen equation (10.13) in the exact second-moment form used by the
bootstrap WLLN proof. -/
theorem integral_sq_resampleMean_sub_empiricalMean_eq_inv_card_mul_variance
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι,
        (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y) ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      (Fintype.card κ : ℝ)⁻¹ *
        Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)] := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : (κ → ι) → ℝ :=
    fun ωs => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs
  have hmean : ∫ ωs, X ωs ∂Pκ = empiricalMean Y := by
    simpa [X, Pκ] using
      integral_empiricalBootstrapResampleMean_uniformOn_fun_eq_empiricalMean
        (κ := κ) (Y := Y)
  have hX_meas : AEMeasurable X Pκ :=
    (measurable_of_finite X).aemeasurable
  calc
    ∫ ωs : κ → ι, (X ωs - empiricalMean Y) ^ 2 ∂Pκ =
        ∫ ωs : κ → ι, (X ωs - ∫ ωs, X ωs ∂Pκ) ^ 2 ∂Pκ := by
          rw [hmean]
    _ = Var[X; Pκ] := (ProbabilityTheory.variance_eq_integral hX_meas).symm
    _ = (Fintype.card κ : ℝ)⁻¹ *
        Var[Y; (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι)] := by
          simpa [X, Pκ] using
            (variance_empiricalBootstrapResampleMean_uniformOn_fun_eq_inv_card_mul
              (κ := κ) (Y := Y))

/-- Scalar second-moment bound for the ordinary finite nonparametric bootstrap
sample mean.

The centered bootstrap sample mean has conditional second moment bounded by
`1 / #κ` times the empirical raw second moment of one draw.  When the resample
size and empirical support have the same cardinality, this is the scalar
`n^{-2} ∑ Y_i^2` bound used in Hansen's proof of Theorem 10.2. -/
theorem integral_sq_resampleMean_sub_empiricalMean_le_inv_card_mul_secondMoment
    {κ : Type*} [Fintype κ] [Nonempty κ] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → ℝ) :
    ∫ ωs : κ → ι,
        (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y) ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) ≤
      (Fintype.card κ : ℝ)⁻¹ *
        (((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, Y i ^ 2) := by
  classical
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  have hvar_le :
      Var[Y; Pι] ≤ ∫ i, Y i ^ 2 ∂Pι :=
    ProbabilityTheory.variance_le_expectation_sq
      (μ := Pι) (X := Y) (AEStronglyMeasurable.of_discrete)
  have hsecond :
      ∫ i, Y i ^ 2 ∂Pι =
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, Y i ^ 2 := by
    simpa [Pι] using
      (integral_uniformOn_univ_eq_card_inv_smul_sum (E := ℝ)
        (fun i => Y i ^ 2))
  have hc_nonneg : 0 ≤ (Fintype.card κ : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  calc
    ∫ ωs : κ → ι,
        (empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y) ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))
        = (Fintype.card κ : ℝ)⁻¹ * Var[Y; Pι] := by
          simpa [Pι] using
            (integral_sq_resampleMean_sub_empiricalMean_eq_inv_card_mul_variance
              (κ := κ) (Y := Y))
    _ ≤ (Fintype.card κ : ℝ)⁻¹ * ∫ i, Y i ^ 2 ∂Pι :=
          mul_le_mul_of_nonneg_left hvar_le hc_nonneg
    _ = (Fintype.card κ : ℝ)⁻¹ *
        (((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, Y i ^ 2) := by
          rw [hsecond]

/-- Finite-dimensional empirical covariance identity for one bootstrap draw.

This is the matrix form of Hansen's exact bootstrap covariance formula
(10.11): under uniform resampling from a finite empirical support, the
covariance matrix is the average outer product of deviations from the empirical
mean. -/
theorem covMat_uniformOn_univ_eq_card_inv_smul_sum_centered
    {k : Type*} (Y : ι → k → ℝ) :
    covMat (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) Y =
      fun a b =>
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal •
          ∑ i, (Y i a -
              ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j a) *
            (Y i b -
              ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j b) := by
  ext a b
  have hmean_a :
      ∫ i, Y i a ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j a :=
    integral_uniformOn_univ_eq_card_inv_smul_sum (fun i => Y i a)
  have hmean_b :
      ∫ i, Y i b ∂(ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) =
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ j, Y j b :=
    integral_uniformOn_univ_eq_card_inv_smul_sum (fun i => Y i b)
  simp [covMat, ProbabilityTheory.covariance, hmean_a, hmean_b,
    integral_uniformOn_univ_eq_card_inv_smul_sum]

omit [Fintype ι] in
/-- Covariance matrix of the ordinary finite nonparametric bootstrap sample mean.

This is the finite-dimensional form of Hansen equation (10.13): the
conditional covariance matrix of the bootstrap sample mean is the empirical
one-draw covariance matrix divided by the number of bootstrap draws. -/
theorem covMat_empiricalBootstrapResampleMean_uniformOn_fun_eq_inv_card_smul
    {κ k : Type*} [Fintype κ] [Nonempty κ] [Fintype k] [Finite ι] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → k → ℝ) :
    covMat
        (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))
        (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a) =
      (Fintype.card κ : ℝ)⁻¹ •
        covMat (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) Y := by
  classical
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  let Pprod : Measure (κ → ι) := Measure.pi (fun _ : κ => Pι)
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let Z : κ → (κ → ι) → k → ℝ := fun t ωs a => Y (ωs t) a
  let c : ℝ := (Fintype.card κ : ℝ)⁻¹
  let j : κ := Classical.choice ‹Nonempty κ›
  have hPκ : Pκ = Pprod := by
    simpa [Pκ, Pprod, Pι] using
      (ProbabilityTheory.uniformOn_pi (Ω := ι) (ι := κ)
        (f := fun _ : κ => (Set.univ : Set ι)))
  have hsample :
      (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a) =
        fun ωs a => c * ∑ t, Z t ωs a := by
    ext ωs a
    simp [empiricalBootstrapResampleMean, Z, c]
  have hZ : ∀ t a, MemLp (fun ωs => Z t ωs a) 2 Pprod := by
    intro t a
    exact ⟨AEStronglyMeasurable.of_discrete, eLpNorm_lt_top_of_finite⟩
  have hiind :
      iIndepFun (fun t (ωs : κ → ι) => ωs t) Pprod := by
    simpa [Pprod] using
      (ProbabilityTheory.iIndepFun_pi
        (μ := fun _ : κ => Pι) (X := fun _ : κ => id)
        (fun _ => aemeasurable_id))
  have hindep :
      ∀ a b, Pairwise (fun t u =>
        (fun ωs => Z t ωs a) ⟂ᵢ[Pprod] (fun ωs => Z u ωs b)) := by
    intro a b t u htu
    exact IndepFun.comp (hiind.indepFun htu)
      (measurable_of_finite (fun i => Y i a))
      (measurable_of_finite (fun i => Y i b))
  have hcov_eval :
      ∀ t, covMat Pprod (Z t) = covMat Pι Y := by
    intro t
    ext a b
    have hmap : Pprod.map (Function.eval t) = Pι :=
      (measurePreserving_eval (μ := fun _ : κ => Pι) t).map_eq
    have hcov :=
      ProbabilityTheory.covariance_map_fun
        (μ := Pprod) (Z := Function.eval t)
        (X := fun i => Y i a) (Y := fun i => Y i b)
        (AEStronglyMeasurable.of_discrete)
        (AEStronglyMeasurable.of_discrete)
        (measurable_pi_apply t).aemeasurable
    calc
      cov[fun ωs => Z t ωs a, fun ωs => Z t ωs b; Pprod]
          = cov[fun i => Y i a, fun i => Y i b; Pprod.map (Function.eval t)] := by
            simpa [Z, Function.comp_def] using hcov.symm
      _ = cov[fun i => Y i a, fun i => Y i b; Pι] := by
            rw [hmap]
  have hcov :
      ∀ t a b,
        cov[fun ωs => Z t ωs a, fun ωs => Z t ωs b; Pprod] =
          cov[fun ωs => Z j ωs a, fun ωs => Z j ωs b; Pprod] := by
    intro t a b
    have ht := congrFun (congrFun (hcov_eval t) a) b
    have hj := congrFun (congrFun (hcov_eval j) a) b
    simpa [covMat] using ht.trans hj.symm
  have hsample_cov :
      covMat Pprod (fun ωs a => c * ∑ t, Z t ωs a) =
        c • covMat Pprod (Z j) := by
    simpa [c] using
      (iidSampleMean_covMat_eq_inv_card_smul
        (μ := Pprod) (Z := Z) j hZ hindep hcov)
  calc
    covMat Pκ
        (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a)
        = covMat Pprod
            (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a) := by
          rw [hPκ]
    _ = covMat Pprod (fun ωs a => c * ∑ t, Z t ωs a) := by
          rw [hsample]
    _ = c • covMat Pprod (Z j) := hsample_cov
    _ = c • covMat Pι Y := by
          rw [hcov_eval j]

omit [Fintype ι] in
/-- Trace of the finite-dimensional nonparametric-bootstrap sample-mean
covariance matrix.

This is the trace form of Hansen equation (10.13). -/
theorem trace_covMat_resampleMean_eq_inv_card_mul
    {κ k : Type*} [Fintype κ] [Nonempty κ] [Fintype k] [Finite ι] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → k → ℝ) :
    Matrix.trace
        (covMat
          (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))
          (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a)) =
      (Fintype.card κ : ℝ)⁻¹ *
        Matrix.trace
          (covMat (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) Y) := by
  rw [covMat_empiricalBootstrapResampleMean_uniformOn_fun_eq_inv_card_smul
    (κ := κ) (Y := Y)]
  simp [Matrix.trace_smul]

/-- The empirical one-draw covariance trace is bounded by the empirical raw
second moment.

This is the finite-dimensional trace inequality used after (10.13) in Hansen's
proof of Theorem 10.2. -/
theorem trace_covMat_uniformOn_univ_le_card_inv_smul_sum_sq
    {k : Type*} [Fintype k] [Nonempty ι] (Y : ι → k → ℝ) :
    Matrix.trace
        (covMat (ProbabilityTheory.uniformOn (Set.univ : Set ι) : Measure ι) Y) ≤
      ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal •
        ∑ i, ∑ a, Y i a ^ 2 := by
  classical
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  have htrace :
      Matrix.trace (covMat Pι Y) = ∑ a, Var[fun i => Y i a; Pι] := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl ?_
    intro a _ha
    exact ProbabilityTheory.covariance_self
      (AEStronglyMeasurable.of_discrete : AEStronglyMeasurable (fun i => Y i a) Pι).aemeasurable
  have hvar_le :
      ∀ a, Var[fun i => Y i a; Pι] ≤ ∫ i, Y i a ^ 2 ∂Pι := by
    intro a
    exact ProbabilityTheory.variance_le_expectation_sq
      (μ := Pι) (X := fun i => Y i a) AEStronglyMeasurable.of_discrete
  have hintegral_sum :
      (∑ a, ∫ i, Y i a ^ 2 ∂Pι) =
        ∫ i, ∑ a, Y i a ^ 2 ∂Pι := by
    rw [integral_finset_sum]
    intro a _ha
    exact Integrable.of_finite
  have hsecond :
      ∫ i, ∑ a, Y i a ^ 2 ∂Pι =
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal •
          ∑ i, ∑ a, Y i a ^ 2 := by
    simpa [Pι] using
      (integral_uniformOn_univ_eq_card_inv_smul_sum (E := ℝ)
        (fun i => ∑ a, Y i a ^ 2))
  calc
    Matrix.trace (covMat Pι Y)
        = ∑ a, Var[fun i => Y i a; Pι] := htrace
    _ ≤ ∑ a, ∫ i, Y i a ^ 2 ∂Pι :=
          Finset.sum_le_sum fun a _ha => hvar_le a
    _ = ∫ i, ∑ a, Y i a ^ 2 ∂Pι := hintegral_sum
    _ = ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal •
          ∑ i, ∑ a, Y i a ^ 2 := hsecond

/-- Trace second-moment bound for the finite-dimensional nonparametric-bootstrap
sample mean.

When the resample size and empirical support have the same cardinality, this is
the vector trace version of Hansen's `n^{-2} ∑ Yᵢ'Yᵢ` bound in the proof of
Theorem 10.2. -/
theorem trace_covMat_resampleMean_le_inv_card_mul_secondMoment
    {κ k : Type*} [Fintype κ] [Nonempty κ] [Fintype k] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → k → ℝ) :
    Matrix.trace
        (covMat
          (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))
          (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a)) ≤
      (Fintype.card κ : ℝ)⁻¹ *
        (((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, ∑ a, Y i a ^ 2) := by
  classical
  let Pι : Measure ι := ProbabilityTheory.uniformOn (Set.univ : Set ι)
  have htrace_eq :
      Matrix.trace
          (covMat
            (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))
            (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a)) =
        (Fintype.card κ : ℝ)⁻¹ * Matrix.trace (covMat Pι Y) := by
    simpa [Pι] using trace_covMat_resampleMean_eq_inv_card_mul (κ := κ) (Y := Y)
  have htrace_le :
      Matrix.trace (covMat Pι Y) ≤
        ((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, ∑ a, Y i a ^ 2 := by
    simpa [Pι] using trace_covMat_uniformOn_univ_le_card_inv_smul_sum_sq (Y := Y)
  have hc_nonneg : 0 ≤ (Fintype.card κ : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  calc
    Matrix.trace
        (covMat
          (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))
          (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a))
        = (Fintype.card κ : ℝ)⁻¹ * Matrix.trace (covMat Pι Y) := htrace_eq
    _ ≤ (Fintype.card κ : ℝ)⁻¹ *
        (((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, ∑ a, Y i a ^ 2) :=
          mul_le_mul_of_nonneg_left htrace_le hc_nonneg

omit [MeasurableSingletonClass ι] in
/-- Expected squared Euclidean norm of the centered nonparametric-bootstrap
sample mean as a covariance trace. -/
theorem integral_norm_sq_resampleMean_sub_empiricalMean_eq_trace_covMat
    {κ k : Type*} [Fintype κ] [Nonempty κ] [Fintype k] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → EuclideanSpace ℝ k) :
    ∫ ωs : κ → ι,
        ‖empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y‖ ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) =
      Matrix.trace
        (covMat
          (ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι))
          (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a)) := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let X : (κ → ι) → EuclideanSpace ℝ k :=
    fun ωs => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs
  have hmean : ∫ ωs, X ωs ∂Pκ = empiricalMean Y := by
    simpa [X, Pκ] using
      integral_empiricalBootstrapResampleMean_uniformOn_fun_eq_empiricalMean
        (κ := κ) (Y := Y)
  calc
    ∫ ωs : κ → ι, ‖X ωs - empiricalMean Y‖ ^ 2 ∂Pκ =
        ∫ ωs : κ → ι, ‖X ωs - ∫ ωs, X ωs ∂Pκ‖ ^ 2 ∂Pκ := by
          rw [hmean]
    _ = Matrix.trace (covMat Pκ (fun ωs a => X ωs a)) := by
          exact integral_norm_sq_sub_mean_eq_trace_covMat_euclidean_of_finite
            (μ := Pκ) X

/-- Finite-dimensional vector second-moment bound for the ordinary
nonparametric-bootstrap sample mean.

When the resample size and empirical support have the same cardinality, this
is Hansen's vector `n^{-2} ∑ Yᵢ'Yᵢ` bound in the proof of Theorem 10.2. -/
theorem integral_norm_sq_resampleMean_sub_empiricalMean_le_secondMoment
    {κ k : Type*} [Fintype κ] [Nonempty κ] [Fintype k] [Nonempty ι]
    [MeasurableSingletonClass (κ → ι)]
    (Y : ι → EuclideanSpace ℝ k) :
    ∫ ωs : κ → ι,
        ‖empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y‖ ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι)) : Measure (κ → ι)) ≤
      (Fintype.card κ : ℝ)⁻¹ *
        (((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, ∑ a, Y i a ^ 2) := by
  classical
  let Pκ : Measure (κ → ι) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (κ → ι))
  let Ycoord : ι → k → ℝ := fun i a => Y i a
  have htrace :
      ∫ ωs : κ → ι,
          ‖empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y‖ ^ 2
          ∂Pκ =
        Matrix.trace (covMat Pκ
          (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a)) := by
    simpa [Pκ] using
      integral_norm_sq_resampleMean_sub_empiricalMean_eq_trace_covMat
        (κ := κ) (Y := Y)
  have htrace_bound :
      Matrix.trace (covMat Pκ
          (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a)) ≤
        (Fintype.card κ : ℝ)⁻¹ *
          (((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, ∑ a, Ycoord i a ^ 2) := by
    simpa [Pκ, Ycoord, empiricalBootstrapResampleMean] using
      trace_covMat_resampleMean_le_inv_card_mul_secondMoment
        (κ := κ) (Y := Ycoord)
  calc
    ∫ ωs : κ → ι,
        ‖empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs - empiricalMean Y‖ ^ 2
        ∂Pκ
        = Matrix.trace (covMat Pκ
            (fun ωs a => empiricalBootstrapResampleMean Y (fun ωs t => ωs t) ωs a)) := htrace
    _ ≤ (Fintype.card κ : ℝ)⁻¹ *
        (((Fintype.card ι : ℝ≥0∞)⁻¹).toReal • ∑ i, ∑ a, Y i a ^ 2) := by
          simpa [Ycoord] using htrace_bound

end EmpiricalDistribution

/-- Hansen Theorem 10.1, chapter-facing name.

Ordinary convergence in probability implies bootstrap convergence in
probability when the sequence is non-random under the bootstrap resampling law. -/
theorem chapter10_bootstrap_convergence_in_probability_of_convergence_in_probability
    [PseudoMetricSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zseq : ℕ → Ω → E} {Z : Ω → E}
    (hZ : TendstoInMeasure μ Zseq atTop Z) :
    TendstoInBootstrapProbability μ Pstar (fun n ω _ => Zseq n ω) Z :=
  tendstoInBootstrapProbability_of_tendstoInMeasure hPstar hZ

/-- Hansen Theorem 10.3, chapter-facing name.

If `Zₙ* ->p* c` and `g` is continuous at `c`, then
`g(Zₙ*) ->p* g(c)`. -/
theorem chapter10_bootstrap_continuous_mapping_probability
    [PseudoMetricSpace E] [PseudoMetricSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zstar : ℕ → Ω → Ωs → E} {c : E} {g : E → F}
    (hZ : TendstoInBootstrapProbability μ Pstar Zstar (fun _ => c))
    (hg : ContinuousAt g c) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) (fun _ => g c) :=
  hZ.continuousAt_const_comp hPstar hg

/-- Chapter 10 bootstrap-probability mapping bridge for globally Lipschitz
transformations.

This is the reusable form needed by theorem wrappers whose statistic is a
linear or otherwise globally controlled transformation of a bootstrap statistic. -/
theorem chapter10_bootstrap_lipschitz_mapping_probability
    [PseudoMetricSpace E] [PseudoMetricSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zstar : ℕ → Ω → Ωs → E} {Z : Ω → E} {g : E → F} {C : ℝ}
    (hC : 0 < C)
    (hg : ∀ x y, dist (g x) (g y) ≤ C * dist x y)
    (hZ : TendstoInBootstrapProbability μ Pstar Zstar Z) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) (fun ω => g (Z ω)) :=
  hZ.lipschitz_comp hPstar hC hg

/-- Hansen Theorem 10.2, centered WLLN from the conditional tail bound.

This is the reusable form of the textbook proof: Markov's inequality and the
conditional variance calculation supply `hle`; the Marcinkiewicz/WLLN argument
supplies `hbound`. -/
theorem chapter10_bootstrap_wlln_centered_of_tail_bound
    [SeminormedAddCommGroup E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {YbarStar : ℕ → Ω → Ωs → E} {Ybar : ℕ → Ω → E}
    {bound : ℝ → ℕ → Ω → ℝ}
    (hbound :
      ∀ η : ℝ, 0 < η →
        TendstoInMeasure μ (fun n ω => bound η n ω) atTop (fun _ => 0))
    (hle :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapTailProb Pstar
          (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0)
          η n ω ≤ bound η n ω) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) :=
  tendstoInBootstrapProbability_of_tail_bound hbound hle

/-- Hansen Theorem 10.2, second conclusion from the centered bootstrap WLLN.

Once the centered bootstrap sample mean satisfies
`Ybar* - Ybar ->p* 0`, and the ordinary sample mean satisfies
`Ybar ->p μY`, the bootstrap sample mean itself satisfies
`Ybar* ->p* μY`.  This is the bootstrap Slutsky/addition step used in the
textbook proof after the centered WLLN is established by the conditional
variance bound. -/
theorem chapter10_bootstrap_wlln_level_from_centered
    [SeminormedAddCommGroup E]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ℕ → Ω → Ωs → E} {Ybar : ℕ → Ω → E} {μY : E}
    (hcenter :
      TendstoInBootstrapProbability μ Pstar
        (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0))
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbability μ Pstar YbarStar (fun _ => μY) := by
  have hYbar_boot :
      TendstoInBootstrapProbability μ Pstar (fun n ω _ => Ybar n ω) (fun _ => μY) :=
    tendstoInBootstrapProbability_of_tendstoInMeasure hPstar hYbar
  have hsum :=
    hcenter.add hPstar hYbar_boot
  exact hsum.congr
    (fun n ω ωs => by simp)
    (fun ω => by simp)

section MarcinkiewiczWLLN

/-- Sample average of absolute values, `n⁻¹ ∑_{i<n} |uᵢ|`.

This is the `Oₚ(1)` factor in Hansen's proof of Theorem 10.20. -/
noncomputable def sampleAbsMean (u : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  (∑ i ∈ Finset.range n, fun ω => |u i ω|) / (n : Ω → ℝ)

/-- Natural-power version of Hansen's Marcinkiewicz WLLN statistic,
`n^{-p} ∑_{i<n} |uᵢ|^p`.

The textbook states the result for every real `r > 1`; this natural-power face
is the one used by the Chapter 10 variance and Lindeberg applications
(`p = 2` and `p = 4`). -/
noncomputable def marcinkiewiczWLLNStatisticNat
    (u : ℕ → Ω → ℝ) (p n : ℕ) (ω : Ω) : ℝ :=
  ((n : ℝ)⁻¹) ^ p * ∑ i ∈ Finset.range n, |u i ω| ^ p

/-- Real-power version of Hansen's Marcinkiewicz WLLN statistic,
`n^{-r} ∑_{i<n} |uᵢ|^r`. -/
noncomputable def marcinkiewiczWLLNStatisticRpow
    (u : ℕ → Ω → ℝ) (r : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((n : ℝ)⁻¹) ^ r * ∑ i ∈ Finset.range n, |u i ω| ^ r

private theorem abs_le_maxNNNorm
    {u : ℕ → Ω → ℝ} {n i : ℕ} {ω : Ω}
    (hi : i ∈ Finset.range n) :
    |u i ω| ≤ (maxNNNorm u n ω : ℝ) := by
  have hle_nn : ‖u i ω‖₊ ≤ maxNNNorm u n ω := by
    dsimp [maxNNNorm]
    exact Finset.le_sup (s := Finset.range n) (f := fun j => ‖u j ω‖₊) hi
  rw [← NNReal.coe_le_coe] at hle_nn
  simpa [Real.norm_eq_abs] using hle_nn

private theorem sampleAbsMean_nonneg
    (u : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ sampleAbsMean u n ω := by
  have hsum : 0 ≤ ∑ i ∈ Finset.range n, |u i ω| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  simpa [sampleAbsMean, div_eq_inv_mul, mul_comm] using
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) hsum

private theorem marcinkiewiczWLLNStatisticNat_nonneg
    (u : ℕ → Ω → ℝ) (p n : ℕ) (ω : Ω) :
    0 ≤ marcinkiewiczWLLNStatisticNat u p n ω := by
  have hscale : 0 ≤ ((n : ℝ)⁻¹) ^ p :=
    pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) p
  have hsum : 0 ≤ ∑ i ∈ Finset.range n, |u i ω| ^ p :=
    Finset.sum_nonneg fun i _ => pow_nonneg (abs_nonneg _) p
  exact mul_nonneg hscale hsum

private theorem marcinkiewiczWLLNStatisticRpow_nonneg
    (u : ℕ → Ω → ℝ) (r : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ marcinkiewiczWLLNStatisticRpow u r n ω := by
  have hscale : 0 ≤ ((n : ℝ)⁻¹) ^ r :=
    Real.rpow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) r
  have hsum : 0 ≤ ∑ i ∈ Finset.range n, |u i ω| ^ r :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) r
  exact mul_nonneg hscale hsum

/-- Deterministic inequality in Hansen's proof of Theorem 10.20.

For natural powers `p ≥ 2`,
`n^{-p} ∑ |uᵢ|^p` is bounded by
`(n^{-1} max |uᵢ|)^{p-1} (n^{-1} ∑ |uᵢ|)`. -/
theorem marcinkiewiczWLLNStatisticNat_le_max_mul_sampleAbsMean
    {u : ℕ → Ω → ℝ} {p n : ℕ} {ω : Ω}
    (hp : 2 ≤ p) :
    marcinkiewiczWLLNStatisticNat u p n ω ≤
      (scaledMaxNNNorm u n ω) ^ (p - 1) * sampleAbsMean u n ω := by
  let a : ℝ := (n : ℝ)⁻¹
  let M : ℝ := (maxNNNorm u n ω : ℝ)
  let S : ℝ := ∑ i ∈ Finset.range n, |u i ω|
  let Sp : ℝ := ∑ i ∈ Finset.range n, |u i ω| ^ p
  have hp1 : 1 ≤ p := (by norm_num : 1 ≤ 2).trans hp
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact inv_nonneg.mpr (Nat.cast_nonneg n)
  have hsum_le : Sp ≤ M ^ (p - 1) * S := by
    calc
      Sp = ∑ i ∈ Finset.range n, |u i ω| ^ p := rfl
      _ ≤ ∑ i ∈ Finset.range n, M ^ (p - 1) * |u i ω| := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have habs_le : |u i ω| ≤ M := by
          simpa [M] using abs_le_maxNNNorm (u := u) (ω := ω) hi
        have hpow_le : |u i ω| ^ (p - 1) ≤ M ^ (p - 1) :=
          pow_le_pow_left₀ (abs_nonneg _) habs_le (p - 1)
        have hpow_eq : |u i ω| ^ p = |u i ω| ^ (p - 1) * |u i ω| := by
          rw [← pow_succ, Nat.sub_add_cancel hp1]
        rw [hpow_eq]
        exact mul_le_mul_of_nonneg_right hpow_le (abs_nonneg _)
      _ = M ^ (p - 1) * S := by
        simp [S, Finset.mul_sum]
  have hscale_le :
      a ^ p * Sp ≤ a ^ p * (M ^ (p - 1) * S) :=
    mul_le_mul_of_nonneg_left hsum_le (pow_nonneg ha_nonneg p)
  have hsample : sampleAbsMean u n ω = a * S := by
    simp [sampleAbsMean, a, S, div_eq_inv_mul]
  have hscaled : scaledMaxNNNorm u n ω = a * M := by
    simp [scaledMaxNNNorm, a, M]
  have hpow_a : a ^ p = a ^ (p - 1) * a := by
    rw [← pow_succ, Nat.sub_add_cancel hp1]
  have hrhs :
      a ^ p * (M ^ (p - 1) * S) =
        (scaledMaxNNNorm u n ω) ^ (p - 1) * sampleAbsMean u n ω := by
    calc
      a ^ p * (M ^ (p - 1) * S)
          = (a ^ (p - 1) * M ^ (p - 1)) * (a * S) := by
            rw [hpow_a]
            ring
      _ = (a * M) ^ (p - 1) * (a * S) := by
            rw [mul_pow]
      _ = (scaledMaxNNNorm u n ω) ^ (p - 1) * sampleAbsMean u n ω := by
            rw [hscaled, hsample]
  change a ^ p * Sp ≤
    (scaledMaxNNNorm u n ω) ^ (p - 1) * sampleAbsMean u n ω
  exact hscale_le.trans_eq hrhs

/-- Deterministic inequality in Hansen's proof of Theorem 10.20 for real
exponents `r > 1`.

This is the textbook display
`n^{-r} ∑ |uᵢ|^r ≤ (n^{-1} max |uᵢ|)^{r-1} (n^{-1} ∑ |uᵢ|)`. -/
theorem marcinkiewiczWLLNStatisticRpow_le_max_mul_sampleAbsMean
    {u : ℕ → Ω → ℝ} {r : ℝ} {n : ℕ} {ω : Ω}
    (hr : 1 < r) :
    marcinkiewiczWLLNStatisticRpow u r n ω ≤
      (scaledMaxNNNorm u n ω) ^ (r - 1) * sampleAbsMean u n ω := by
  let a : ℝ := (n : ℝ)⁻¹
  let M : ℝ := (maxNNNorm u n ω : ℝ)
  let S : ℝ := ∑ i ∈ Finset.range n, |u i ω|
  let Sr : ℝ := ∑ i ∈ Finset.range n, |u i ω| ^ r
  let q : ℝ := r - 1
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact sub_nonneg.mpr hr.le
  have hr_eq : r = q + 1 := by
    dsimp [q]
    ring
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact inv_nonneg.mpr (Nat.cast_nonneg n)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact NNReal.coe_nonneg _
  have hsum_le : Sr ≤ M ^ q * S := by
    calc
      Sr = ∑ i ∈ Finset.range n, |u i ω| ^ r := rfl
      _ ≤ ∑ i ∈ Finset.range n, M ^ q * |u i ω| := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have habs_le : |u i ω| ≤ M := by
          simpa [M] using abs_le_maxNNNorm (u := u) (ω := ω) hi
        have hpow_le : |u i ω| ^ q ≤ M ^ q :=
          Real.rpow_le_rpow (abs_nonneg _) habs_le hq_nonneg
        have hpow_eq : |u i ω| ^ r = |u i ω| ^ q * |u i ω| := by
          rw [hr_eq, Real.rpow_add_of_nonneg (abs_nonneg _) hq_nonneg zero_le_one,
            Real.rpow_one]
        rw [hpow_eq]
        exact mul_le_mul_of_nonneg_right hpow_le (abs_nonneg _)
      _ = M ^ q * S := by
        simp [S, Finset.mul_sum]
  have hscale_le :
      a ^ r * Sr ≤ a ^ r * (M ^ q * S) :=
    mul_le_mul_of_nonneg_left hsum_le (Real.rpow_nonneg ha_nonneg r)
  have hsample : sampleAbsMean u n ω = a * S := by
    simp [sampleAbsMean, a, S, div_eq_inv_mul]
  have hscaled : scaledMaxNNNorm u n ω = a * M := by
    simp [scaledMaxNNNorm, a, M]
  have hpow_a : a ^ r = a ^ q * a := by
    rw [hr_eq, Real.rpow_add_of_nonneg ha_nonneg hq_nonneg zero_le_one, Real.rpow_one]
  have hrhs :
      a ^ r * (M ^ q * S) =
        (scaledMaxNNNorm u n ω) ^ (r - 1) * sampleAbsMean u n ω := by
    calc
      a ^ r * (M ^ q * S)
          = (a ^ q * M ^ q) * (a * S) := by
            rw [hpow_a]
            ring
      _ = (a * M) ^ q * (a * S) := by
            rw [Real.mul_rpow ha_nonneg hM_nonneg]
      _ = (scaledMaxNNNorm u n ω) ^ (r - 1) * sampleAbsMean u n ω := by
            rw [hscaled, hsample]
  change a ^ r * Sr ≤
    (scaledMaxNNNorm u n ω) ^ (r - 1) * sampleAbsMean u n ω
  exact hscale_le.trans_eq hrhs

private theorem tendstoInMeasure_pow_nat_zero_real
    {X : ℕ → Ω → ℝ}
    (hX : TendstoInMeasure μ X atTop (fun _ => 0))
    {q : ℕ} (hq : 0 < q) :
    TendstoInMeasure μ (fun n ω => (X n ω) ^ q) atTop (fun _ => 0) := by
  induction q with
  | zero =>
      exact (Nat.lt_irrefl 0 hq).elim
  | succ q ih =>
      by_cases hq0 : q = 0
      · subst q
        simpa using hX
      · have hq_pos : 0 < q := Nat.pos_of_ne_zero hq0
        have hpow := ih hq_pos
        have hmul := TendstoInMeasure.mul_zero_real hpow hX
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul

private theorem tendstoInMeasure_rpow_pos_zero_real
    {X : ℕ → Ω → ℝ}
    (hX_nonneg : ∀ n ω, 0 ≤ X n ω)
    (hX : TendstoInMeasure μ X atTop (fun _ => 0))
    {q : ℝ} (hq : 0 < q) :
    TendstoInMeasure μ (fun n ω => (X n ω) ^ q) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro ε hε
  let δ : ℝ := ε ^ q⁻¹
  have hδ_pos : 0 < δ := Real.rpow_pos_of_pos hε q⁻¹
  have hδ_nonneg : 0 ≤ δ := hδ_pos.le
  have hδ_pow : δ ^ q = ε := by
    dsimp [δ]
    simpa using Real.rpow_inv_rpow hε.le hq.ne'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hX δ hδ_pos) (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  have hXpow_nonneg : 0 ≤ (X n ω) ^ q :=
    Real.rpow_nonneg (hX_nonneg n ω) q
  have htail_power : ε ≤ (X n ω) ^ q := by
    simpa [Real.dist_eq, abs_of_nonneg hXpow_nonneg] using hω
  have hδ_le_X : δ ≤ X n ω := by
    rw [← Real.rpow_le_rpow_iff hδ_nonneg (hX_nonneg n ω) hq]
    simpa [hδ_pow] using htail_power
  simpa [Real.dist_eq, abs_of_nonneg (hX_nonneg n ω)] using hδ_le_X

/-- Uniform integrability makes `n⁻¹ ∑ |uᵢ|` bounded in probability.

This is the `Oₚ(1)` sample-mean factor used in Hansen's proof of Theorem
10.20. -/
theorem sampleAbsMean_boundedInProbability_of_uniformIntegrable
    [IsFiniteMeasure μ] {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ) :
    BoundedInProbability μ (sampleAbsMean u) := by
  have hAbsUI : UniformIntegrable (fun i ω => |u i ω|) 1 μ :=
    uniformIntegrable_abs hu
  have hAvgUI : UniformIntegrable (sampleAbsMean u) 1 μ := by
    simpa [sampleAbsMean] using
      (uniformIntegrable_average_real (μ := μ) (p := (1 : ℝ≥0∞))
        (f := fun i ω => |u i ω|) le_rfl hAbsUI)
  exact BoundedInProbability.of_uniformIntegrable_one hAvgUI

/-- Hansen Theorem 10.20, natural-power convergence engine.

If the scaled maximum `n⁻¹ max |uᵢ|` is `oₚ(1)` and the absolute sample mean is
`Oₚ(1)`, then `n^{-p} ∑ |uᵢ|^p = oₚ(1)` for every natural `p ≥ 2`. -/
theorem chapter10_marcinkiewicz_wlln_natPower_of_max_and_absMean
    {u : ℕ → Ω → ℝ} {p : ℕ}
    (hp : 2 ≤ p)
    (hmax : TendstoInMeasure μ (scaledMaxNNNorm u) atTop (fun _ => 0))
    (hmean : BoundedInProbability μ (sampleAbsMean u)) :
    TendstoInMeasure μ (marcinkiewiczWLLNStatisticNat u p) atTop (fun _ => 0) := by
  have hp_gt_one : 1 < p := (by norm_num : 1 < 2).trans_le hp
  have hp_sub_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp_gt_one
  have hpow :
      TendstoInMeasure μ
        (fun n ω => (scaledMaxNNNorm u n ω) ^ (p - 1)) atTop (fun _ => 0) :=
    tendstoInMeasure_pow_nat_zero_real hmax hp_sub_pos
  have hprod :
      TendstoInMeasure μ
        (fun n ω => (scaledMaxNNNorm u n ω) ^ (p - 1) * sampleAbsMean u n ω)
        atTop (fun _ => 0) :=
    TendstoInMeasure.mul_boundedInProbability hpow hmean
  exact tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := marcinkiewiczWLLNStatisticNat u p)
    (g := fun n ω => (scaledMaxNNNorm u n ω) ^ (p - 1) * sampleAbsMean u n ω)
    (marcinkiewiczWLLNStatisticNat_nonneg u p)
    (fun n ω =>
      marcinkiewiczWLLNStatisticNat_le_max_mul_sampleAbsMean
        (u := u) (p := p) (n := n) (ω := ω) hp)
    hprod

/-- Hansen Theorem 10.20, natural-power uniformly-integrable wrapper.

For natural `p ≥ 2`, uniform integrability of the real sequence `uᵢ` implies
`n^{-p} ∑ |uᵢ|^p ->p 0`.  The textbook states the same argument for every real
`r > 1`; this wrapper records the integer-power surface needed by the Chapter
10 bootstrap variance and Lindeberg proofs. -/
theorem chapter10_marcinkiewicz_wlln_natPower_of_uniformIntegrable
    [IsFiniteMeasure μ] {u : ℕ → Ω → ℝ} {p : ℕ}
    (hp : 2 ≤ p)
    (hu : UniformIntegrable u 1 μ) :
    TendstoInMeasure μ (marcinkiewiczWLLNStatisticNat u p) atTop (fun _ => 0) :=
  chapter10_marcinkiewicz_wlln_natPower_of_max_and_absMean
    (μ := μ) (u := u) hp
    (max_norm_scaled_tendstoInMeasure_zero_of_uniformIntegrable_norm_r (μ := μ) (Z := u) hu)
    (sampleAbsMean_boundedInProbability_of_uniformIntegrable (μ := μ) hu)

/-- Hansen Theorem 10.20, real-exponent convergence engine.

If the scaled maximum `n⁻¹ max |uᵢ|` is `oₚ(1)` and the absolute sample mean is
`Oₚ(1)`, then `n^{-r} ∑ |uᵢ|^r = oₚ(1)` for every real `r > 1`. -/
theorem chapter10_marcinkiewicz_wlln_rpow_of_max_and_absMean
    {u : ℕ → Ω → ℝ} {r : ℝ}
    (hr : 1 < r)
    (hmax : TendstoInMeasure μ (scaledMaxNNNorm u) atTop (fun _ => 0))
    (hmean : BoundedInProbability μ (sampleAbsMean u)) :
    TendstoInMeasure μ (marcinkiewiczWLLNStatisticRpow u r) atTop (fun _ => 0) := by
  have hq_pos : 0 < r - 1 := sub_pos.mpr hr
  have hscaled_nonneg : ∀ n ω, 0 ≤ scaledMaxNNNorm u n ω := by
    intro n ω
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (NNReal.coe_nonneg _)
  have hpow :
      TendstoInMeasure μ
        (fun n ω => (scaledMaxNNNorm u n ω) ^ (r - 1)) atTop (fun _ => 0) :=
    tendstoInMeasure_rpow_pos_zero_real hscaled_nonneg hmax hq_pos
  have hprod :
      TendstoInMeasure μ
        (fun n ω => (scaledMaxNNNorm u n ω) ^ (r - 1) * sampleAbsMean u n ω)
        atTop (fun _ => 0) :=
    TendstoInMeasure.mul_boundedInProbability hpow hmean
  exact tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := marcinkiewiczWLLNStatisticRpow u r)
    (g := fun n ω => (scaledMaxNNNorm u n ω) ^ (r - 1) * sampleAbsMean u n ω)
    (marcinkiewiczWLLNStatisticRpow_nonneg u r)
    (fun n ω =>
      marcinkiewiczWLLNStatisticRpow_le_max_mul_sampleAbsMean
        (u := u) (r := r) (n := n) (ω := ω) hr)
    hprod

/-- **Hansen Theorem 10.20, Marcinkiewicz WLLN.**

If `uᵢ` is uniformly integrable, then for every real `r > 1`,
`n^{-r} ∑ |uᵢ|^r ->p 0`.  Hansen states the theorem with independence as a
sufficient condition for the ordinary WLLN step; this formulation is slightly
stronger because Mathlib's probability-theory uniform integrability already
provides the `Oₚ(1)` absolute-mean factor, and Chapter 6's maximum theorem
provides the `oₚ(1)` scaled-maximum factor. -/
theorem chapter10_marcinkiewicz_wlln_rpow_of_uniformIntegrable
    [IsFiniteMeasure μ] {u : ℕ → Ω → ℝ} {r : ℝ}
    (hr : 1 < r)
    (hu : UniformIntegrable u 1 μ) :
    TendstoInMeasure μ (marcinkiewiczWLLNStatisticRpow u r) atTop (fun _ => 0) :=
  chapter10_marcinkiewicz_wlln_rpow_of_max_and_absMean
    (μ := μ) (u := u) hr
    (max_norm_scaled_tendstoInMeasure_zero_of_uniformIntegrable_norm_r (μ := μ) (Z := u) hu)
    (sampleAbsMean_boundedInProbability_of_uniformIntegrable (μ := μ) hu)

end MarcinkiewiczWLLN

section BootstrapWLLNSecondMoment

/-- Hansen Theorem 10.2 second-moment bound.

The textbook proof bounds the centered bootstrap sample-mean tail probability
by `η^{-2} n^{-2} ∑ |u_i|^2`; in vector applications `u_i` is the norm of the
original observation. -/
noncomputable def bootstrapWLLNSecondMomentBound
    (u : ℕ → Ω → ℝ) (η : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  η⁻¹ ^ 2 * marcinkiewiczWLLNStatisticNat u 2 n ω

/-- The second-moment bound in Hansen's bootstrap WLLN proof is `oₚ(1)`.

This is exactly the Marcinkiewicz WLLN step in the proof of Theorem 10.2, with
natural power `p = 2`. -/
theorem bootstrapWLLNSecondMomentBound_tendsto_zero
    [IsFiniteMeasure μ] {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ) {η : ℝ} (_hη : 0 < η) :
    TendstoInMeasure μ (fun n ω => bootstrapWLLNSecondMomentBound u η n ω)
      atTop (fun _ => 0) := by
  have hmarc :
      TendstoInMeasure μ (marcinkiewiczWLLNStatisticNat u 2) atTop (fun _ => 0) :=
    chapter10_marcinkiewicz_wlln_natPower_of_uniformIntegrable
      (μ := μ) (u := u) (p := 2) (by norm_num) hu
  change TendstoInMeasure μ
    (fun n ω => η⁻¹ ^ 2 * marcinkiewiczWLLNStatisticNat u 2 n ω)
    atTop (fun _ => 0)
  exact TendstoInMeasure.const_mul_zero_real (μ := μ) (η⁻¹ ^ 2) hmarc

/-- Vector-valued `L²` Markov bound for bootstrap tails.

This is the conditional-probability form of
`P*(‖Z*‖ ≥ η) ≤ η⁻² ‖Z*‖²_{L²(P*)}`.  The right side is written with
Mathlib's `eLpNorm` because this is the reusable layer that applies before a
particular empirical covariance calculation has identified the `L²` seminorm. -/
noncomputable def bootstrapL2ENNTailBound
    [NormedAddCommGroup E]
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → E)
    (η : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (((ENNReal.ofReal η)⁻¹ ^ (2 : ℝ)) *
    eLpNorm (Zstar n ω) 2 (Pstar n ω) ^ (2 : ℝ)).toReal

/-- Conditional Markov inequality for vector-valued bootstrap statistics. -/
theorem bootstrapTailProb_zero_le_l2_eLpNorm_bound
    [NormedAddCommGroup E]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → E}
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {η : ℝ} (hη : 0 < η) (n : ℕ) (ω : Ω) :
    bootstrapTailProb Pstar Zstar (fun _ => 0) η n ω ≤
      bootstrapL2ENNTailBound Pstar Zstar η n ω := by
  have htail :
      (Pstar n ω)
          {ωs : Ωs | ENNReal.ofReal η ≤ ‖Zstar n ω ωs‖ₑ} ≤
        (ENNReal.ofReal η)⁻¹ ^ (2 : ℝ) *
          eLpNorm (Zstar n ω) 2 (Pstar n ω) ^ (2 : ℝ) := by
    simpa using
      (MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm
        (μ := Pstar n ω) (p := (2 : ℝ≥0∞)) (f := Zstar n ω)
        (by norm_num) (by simp) (hZ n ω).1
        (ε := ENNReal.ofReal η) (by simp [hη])
        (by intro htop; exact (ENNReal.ofReal_ne_top htop).elim))
  have hset :
      {ωs : Ωs | η ≤ dist (Zstar n ω ωs) ((fun _ : Ω => (0 : E)) ω)} =
        {ωs : Ωs | ENNReal.ofReal η ≤ ‖Zstar n ω ωs‖ₑ} := by
    ext ωs
    simp only [Set.mem_setOf_eq]
    rw [dist_eq_norm, sub_zero, ← ofReal_norm_eq_enorm]
    exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).symm
  have hmeasure :
      (Pstar n ω)
          {ωs : Ωs | η ≤ dist (Zstar n ω ωs) ((fun _ : Ω => (0 : E)) ω)} ≤
        (ENNReal.ofReal η)⁻¹ ^ (2 : ℝ) *
          eLpNorm (Zstar n ω) 2 (Pstar n ω) ^ (2 : ℝ) := by
    rw [hset]
    exact htail
  have hrhs_ne_top :
      (ENNReal.ofReal η)⁻¹ ^ (2 : ℝ) *
          eLpNorm (Zstar n ω) 2 (Pstar n ω) ^ (2 : ℝ) ≠ ∞ := by
    have hnorm_ne_top : eLpNorm (Zstar n ω) 2 (Pstar n ω) ≠ ∞ :=
      (hZ n ω).eLpNorm_ne_top
    finiteness
  have hreal := ENNReal.toReal_mono hrhs_ne_top hmeasure
  simpa [bootstrapTailProb, bootstrapL2ENNTailBound] using hreal

/-- Conditional Markov inequality for vector bootstrap statistics, written as
a concrete second moment.

This is the textbook-facing form of the `L²` tail bridge:
`P*(‖Z*‖ ≥ η) ≤ E*[‖Z*‖²] / η²`.  It is designed for empirical-bootstrap
specializations where the conditional second moment is then identified by a
finite covariance or norm calculation. -/
theorem bootstrapTailProb_zero_le_integral_norm_sq_div
    [NormedAddCommGroup E]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → E}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {η : ℝ} (hη : 0 < η) (n : ℕ) (ω : Ω) :
    bootstrapTailProb Pstar Zstar (fun _ => 0) η n ω ≤
      (∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω) / η ^ 2 := by
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  let A : Set Ωs :=
    {ωs | η ≤ dist (Zstar n ω ωs) ((fun _ : Ω => (0 : E)) ω)}
  let B : Set Ωs := {ωs | η ^ 2 ≤ ‖Zstar n ω ωs‖ ^ 2}
  have hAB : A ⊆ B := by
    intro ωs hωs
    have hnorm : η ≤ ‖Zstar n ω ωs‖ := by
      simpa [A, dist_eq_norm, sub_zero] using hωs
    exact pow_le_pow_left₀ hη.le hnorm 2
  have hA_le_B : (Pstar n ω).real A ≤ (Pstar n ω).real B :=
    measureReal_mono hAB
  have hInt :
      Integrable (fun ωs => ‖Zstar n ω ωs‖ ^ 2) (Pstar n ω) :=
    (memLp_two_iff_integrable_sq_norm (hZ n ω).1).1 (hZ n ω)
  have hmarkov :
      η ^ 2 * (Pstar n ω).real B ≤
        ∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω := by
    simpa [B] using
      (mul_meas_ge_le_integral_of_nonneg
        (μ := Pstar n ω) (f := fun ωs => ‖Zstar n ω ωs‖ ^ 2)
        (ae_of_all _ fun ωs => pow_nonneg (norm_nonneg (Zstar n ω ωs)) 2)
        hInt (η ^ 2))
  have hB_le :
      (Pstar n ω).real B ≤
        (∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω) / η ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hη)).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmarkov)
  calc
    bootstrapTailProb Pstar Zstar (fun _ => 0) η n ω
        = (Pstar n ω).real A := by
          simp [bootstrapTailProb, A, measureReal_def]
    _ ≤ (Pstar n ω).real B := hA_le_B
    _ ≤ (∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω) / η ^ 2 := hB_le

/-- Conditional Chebyshev inequality for centered scalar bootstrap statistics.

If a scalar bootstrap statistic has conditional mean zero, then its conditional
tail probability is bounded by its conditional variance divided by `η²`. -/
theorem bootstrapTailProb_centered_real_le_variance_div_sq
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hmean : ∀ n ω, (Pstar n ω)[Zstar n ω] = 0)
    {η : ℝ} (hη : 0 < η) (n : ℕ) (ω : Ω) :
    bootstrapTailProb Pstar Zstar (fun _ => 0) η n ω ≤
      Var[Zstar n ω; Pstar n ω] / η ^ 2 := by
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  have hcheb :=
    ProbabilityTheory.meas_ge_le_variance_div_sq
      (μ := Pstar n ω) (X := Zstar n ω) (hZ n ω) hη
  have hset :
      {ωs : Ωs | η ≤ dist (Zstar n ω ωs) ((fun _ : Ω => (0 : ℝ)) ω)} =
        {ωs : Ωs | η ≤ |Zstar n ω ωs - (Pstar n ω)[Zstar n ω]|} := by
    ext ωs
    simp [hmean n ω]
  have hmeasure :
      (Pstar n ω)
          {ωs : Ωs | η ≤ dist (Zstar n ω ωs) ((fun _ : Ω => (0 : ℝ)) ω)} ≤
        ENNReal.ofReal (Var[Zstar n ω; Pstar n ω] / η ^ 2) := by
    rw [hset]
    exact hcheb
  have hnonneg :
      0 ≤ Var[Zstar n ω; Pstar n ω] / η ^ 2 :=
    div_nonneg (ProbabilityTheory.variance_nonneg (Zstar n ω) (Pstar n ω))
      (sq_nonneg η)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  simpa [bootstrapTailProb, ENNReal.toReal_ofReal hnonneg] using hreal

/-- Hansen Theorem 10.2, centered WLLN from the textbook second-moment bound.

Once Chebyshev/Markov and the empirical variance calculation give the
conditional tail bound `hle`, the Marcinkiewicz WLLN proves that bound is
`oₚ(1)`, hence the centered bootstrap sample mean converges in bootstrap
probability to zero. -/
theorem chapter10_bootstrap_wlln_centered_of_second_moment_bound
    [SeminormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {YbarStar : ℕ → Ω → Ωs → E} {Ybar : ℕ → Ω → E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hle :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapTailProb Pstar
          (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0)
          η n ω ≤ bootstrapWLLNSecondMomentBound u η n ω) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) :=
  chapter10_bootstrap_wlln_centered_of_tail_bound
    (bound := fun η n ω => bootstrapWLLNSecondMomentBound u η n ω)
    (fun η hη => bootstrapWLLNSecondMomentBound_tendsto_zero (μ := μ) (η := η) hu hη)
    hle

/-- Hansen Theorem 10.2, scalar centered WLLN from a conditional variance
bound.

This is the Chebyshev/Marcinkiewicz constructor for the scalar case: if the
conditional variance of the centered bootstrap sample mean is bounded by the
textbook `n^{-2} ∑ |u_i|²` term, then the centered bootstrap WLLN follows. -/
theorem chapter10_bootstrap_wlln_centered_real_of_conditional_variance_bound
    [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ℕ → Ω → Ωs → ℝ} {Ybar : ℕ → Ω → ℝ}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hmean :
      ∀ n ω, (Pstar n ω)[fun ωs => YbarStar n ω ωs - Ybar n ω] = 0)
    (hvar :
      ∀ n ω,
        Var[fun ωs => YbarStar n ω ωs - Ybar n ω; Pstar n ω] ≤
          marcinkiewiczWLLNStatisticNat u 2 n ω) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) := by
  refine chapter10_bootstrap_wlln_centered_of_second_moment_bound
    (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
    (u := u) hu ?_
  intro η hη n ω
  calc
    bootstrapTailProb Pstar
        (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) η n ω
        ≤ Var[fun ωs => YbarStar n ω ωs - Ybar n ω; Pstar n ω] / η ^ 2 :=
          bootstrapTailProb_centered_real_le_variance_div_sq
            (Pstar := Pstar)
            (Zstar := fun n ω ωs => YbarStar n ω ωs - Ybar n ω)
            hPstar hZ hmean hη n ω
    _ ≤ marcinkiewiczWLLNStatisticNat u 2 n ω / η ^ 2 :=
          div_le_div_of_nonneg_right (hvar n ω) (sq_nonneg η)
    _ = bootstrapWLLNSecondMomentBound u η n ω := by
          rw [bootstrapWLLNSecondMomentBound]
          field_simp [hη.ne']

/-- Hansen Theorem 10.2, scalar level WLLN from a conditional variance bound.

This packages the scalar conditional-Chebyshev centered result with the
ordinary-sample WLLN for `Ybar`, giving the textbook level conclusion
`Ybar* ->p* μY`. -/
theorem chapter10_bootstrap_wlln_level_real_of_conditional_variance_bound
    [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ℕ → Ω → Ωs → ℝ} {Ybar : ℕ → Ω → ℝ} {μY : ℝ}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hmean :
      ∀ n ω, (Pstar n ω)[fun ωs => YbarStar n ω ωs - Ybar n ω] = 0)
    (hvar :
      ∀ n ω,
        Var[fun ωs => YbarStar n ω ωs - Ybar n ω; Pstar n ω] ≤
          marcinkiewiczWLLNStatisticNat u 2 n ω)
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbability μ Pstar YbarStar (fun _ => μY) :=
  chapter10_bootstrap_wlln_level_from_centered
    (μ := μ) hPstar
    (chapter10_bootstrap_wlln_centered_real_of_conditional_variance_bound
      (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
      (u := u) hPstar hu hZ hmean hvar)
    hYbar

/-- Hansen Theorem 10.2, vector centered WLLN from a bootstrap `L²` seminorm
bound.

This is the vector-valued conditional Markov constructor.  The remaining
empirical-bootstrap specialization identifies the displayed `L²` seminorm
through the finite empirical covariance/norm calculation. -/
theorem chapter10_bootstrap_wlln_centered_of_l2_eLpNorm_bound
    [NormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    {YbarStar : ℕ → Ω → Ωs → E} {Ybar : ℕ → Ω → E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hbound :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapL2ENNTailBound Pstar
          (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) η n ω ≤
            bootstrapWLLNSecondMomentBound u η n ω) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) := by
  refine chapter10_bootstrap_wlln_centered_of_second_moment_bound
    (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
    (u := u) hu ?_
  intro η hη n ω
  exact (bootstrapTailProb_zero_le_l2_eLpNorm_bound
    (Pstar := Pstar)
    (Zstar := fun n ω ωs => YbarStar n ω ωs - Ybar n ω)
    hZ hη n ω).trans (hbound η hη n ω)

/-- Hansen Theorem 10.2, vector centered WLLN from a conditional second-moment
bound.

This is the finite-empirical target form of the vector proof: once the
conditional second moment of the centered bootstrap mean is bounded by
`n^{-2} ∑ ‖uᵢ‖²`, the Marcinkiewicz WLLN gives the centered bootstrap
conclusion. -/
theorem chapter10_bootstrap_wlln_centered_of_integral_norm_sq_bound
    [NormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ℕ → Ω → Ωs → E} {Ybar : ℕ → Ω → E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hbound :
      ∀ n ω,
        (∫ ωs, ‖YbarStar n ω ωs - Ybar n ω‖ ^ 2 ∂Pstar n ω) ≤
          marcinkiewiczWLLNStatisticNat u 2 n ω) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) := by
  refine chapter10_bootstrap_wlln_centered_of_second_moment_bound
    (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
    (u := u) hu ?_
  intro η hη n ω
  calc
    bootstrapTailProb Pstar
        (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) η n ω
        ≤ (∫ ωs, ‖YbarStar n ω ωs - Ybar n ω‖ ^ 2 ∂Pstar n ω) / η ^ 2 :=
          bootstrapTailProb_zero_le_integral_norm_sq_div
            (Pstar := Pstar)
            (Zstar := fun n ω ωs => YbarStar n ω ωs - Ybar n ω)
            hPstar hZ hη n ω
    _ ≤ marcinkiewiczWLLNStatisticNat u 2 n ω / η ^ 2 :=
          div_le_div_of_nonneg_right (hbound n ω) (sq_nonneg η)
    _ = bootstrapWLLNSecondMomentBound u η n ω := by
          rw [bootstrapWLLNSecondMomentBound]
          field_simp [hη.ne']

/-- Hansen Theorem 10.2, vector level WLLN from a bootstrap `L²` seminorm
bound.

This packages the vector conditional-Markov centered result with the
ordinary-sample WLLN for `Ybar`, giving the textbook level conclusion
`Ybar* ->p* μY`. -/
theorem chapter10_bootstrap_wlln_level_of_l2_eLpNorm_bound
    [NormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ℕ → Ω → Ωs → E} {Ybar : ℕ → Ω → E} {μY : E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hbound :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapL2ENNTailBound Pstar
          (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) η n ω ≤
            bootstrapWLLNSecondMomentBound u η n ω)
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbability μ Pstar YbarStar (fun _ => μY) :=
  chapter10_bootstrap_wlln_level_from_centered
    (μ := μ) hPstar
    (chapter10_bootstrap_wlln_centered_of_l2_eLpNorm_bound
      (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
      (u := u) hu hZ hbound)
    hYbar

/-- Hansen Theorem 10.2, vector level WLLN from a conditional second-moment
bound.

This packages the conditional-second-moment centered constructor with the
ordinary-sample WLLN for `Ybar`, giving the textbook level conclusion
`Ybar* ->p* μY`. -/
theorem chapter10_bootstrap_wlln_level_of_integral_norm_sq_bound
    [NormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ℕ → Ω → Ωs → E} {Ybar : ℕ → Ω → E} {μY : E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hbound :
      ∀ n ω,
        (∫ ωs, ‖YbarStar n ω ωs - Ybar n ω‖ ^ 2 ∂Pstar n ω) ≤
          marcinkiewiczWLLNStatisticNat u 2 n ω)
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbability μ Pstar YbarStar (fun _ => μY) :=
  chapter10_bootstrap_wlln_level_from_centered
    (μ := μ) hPstar
    (chapter10_bootstrap_wlln_centered_of_integral_norm_sq_bound
      (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
      (u := u) hPstar hu hZ hbound)
    hYbar

/-- Hansen Theorem 10.2, level WLLN from the textbook second-moment bound.

This packages the centered second-moment/Marcinkiewicz proof with the
ordinary-sample WLLN for `Ybar`, giving the textbook conclusion
`Ybar* ->p* μY`. -/
theorem chapter10_bootstrap_wlln_level_of_second_moment_bound
    [SeminormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ℕ → Ω → Ωs → E} {Ybar : ℕ → Ω → E} {μY : E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hle :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapTailProb Pstar
          (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0)
          η n ω ≤ bootstrapWLLNSecondMomentBound u η n ω)
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbability μ Pstar YbarStar (fun _ => μY) :=
  chapter10_bootstrap_wlln_level_from_centered
    (μ := μ) hPstar
    (chapter10_bootstrap_wlln_centered_of_second_moment_bound
      (μ := μ) (u := u) hu hle)
    hYbar

end BootstrapWLLNSecondMoment

section IndexedBootstrapWLLN

variable {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]

/-- Conditional bootstrap tail probability when the bootstrap sample space may
depend on the sample size. -/
noncomputable def bootstrapTailProbIndexed [PseudoMetricSpace E]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → E) (Z : Ω → E)
    (η : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((Pstar n ω) {ωs | η ≤ dist (Zstar n ω ωs) (Z ω)}).toReal

/-- Indexed-space version of Hansen Definition 10.1.

This is useful for the ordinary finite nonparametric bootstrap, where the
resampling space at sample size `n` is naturally `Fin n -> Fin n`. -/
def TendstoInBootstrapProbabilityIndexed [PseudoMetricSpace E]
    (μ : Measure Ω) (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → E) (Z : Ω → E) : Prop :=
  ∀ η : ℝ, 0 < η →
    TendstoInMeasure μ
      (fun n ω => bootstrapTailProbIndexed Pstar Zstar Z η n ω)
      atTop (fun _ => 0)

/-- Indexed-space bootstrap convergence from a conditional tail-probability
bound. -/
theorem tendstoInBootstrapProbabilityIndexed_of_tail_bound
    [PseudoMetricSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E} {Z : Ω → E}
    {bound : ℝ → ℕ → Ω → ℝ}
    (hbound :
      ∀ η : ℝ, 0 < η →
        TendstoInMeasure μ (fun n ω => bound η n ω) atTop (fun _ => 0))
    (hle :
      ∀ η : ℝ, 0 < η → ∀ n ω,
        bootstrapTailProbIndexed Pstar Zstar Z η n ω ≤ bound η n ω) :
    TendstoInBootstrapProbabilityIndexed μ Pstar Zstar Z := by
  intro η hη
  exact tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω => bootstrapTailProbIndexed Pstar Zstar Z η n ω)
    (g := fun n ω => bound η n ω)
    (fun _ _ => ENNReal.toReal_nonneg)
    (hle η hη)
    (hbound η hη)

/-- Indexed-space version of Hansen Theorem 10.1.

If `Zₙ ->p Z` under the original-sample law, then the same statistic, viewed as
constant under each sample-size-dependent bootstrap law, converges to `Z` in
indexed bootstrap probability. -/
theorem tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure
    [PseudoMetricSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zseq : ℕ → Ω → E} {Z : Ω → E}
    (hZ : TendstoInMeasure μ Zseq atTop Z) :
    TendstoInBootstrapProbabilityIndexed μ Pstar (fun n ω _ => Zseq n ω) Z := by
  classical
  intro η hη
  let A : ℕ → Set Ω := fun n => {ω | η ≤ dist (Zseq n ω) (Z ω)}
  have hA : Tendsto (fun n => μ (A n)) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_dist.mp hZ) η hη
  have hindicator :
      TendstoInMeasure μ (fun n ω => if ω ∈ A n then (1 : ℝ) else 0)
        atTop (fun _ => 0) :=
    tendstoInMeasure_indicator_zero_of_tendsto_measure (μ := μ) hA
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hindicator
  refine Filter.Eventually.of_forall ?_
  intro ω
  by_cases hω : ω ∈ A n
  · have hset :
        {ωs : Ωboot n | η ≤ dist (Zseq n ω) (Z ω)} = Set.univ := by
      have htail : η ≤ dist (Zseq n ω) (Z ω) := by simpa [A] using hω
      ext ωs
      simp [htail]
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    simp [bootstrapTailProbIndexed, A, hω, hset]
  · have hset :
        {ωs : Ωboot n | η ≤ dist (Zseq n ω) (Z ω)} = ∅ := by
      have htail : ¬ η ≤ dist (Zseq n ω) (Z ω) := by simpa [A] using hω
      ext ωs
      simp [htail]
    simp [bootstrapTailProbIndexed, A, hω, hset]

namespace TendstoInBootstrapProbabilityIndexed

/-- Indexed bootstrap convergence is invariant under pointwise equality of the
bootstrap statistic and limit target. -/
theorem congr [PseudoMetricSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E} {Z Z' : Ω → E}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapProbabilityIndexed μ Pstar Zstar Z) :
    TendstoInBootstrapProbabilityIndexed μ Pstar Zstar' Z' := by
  intro η hη
  simpa [bootstrapTailProbIndexed, hstar, hlim] using hZ η hη

/-- Indexed-space Hansen Theorem 10.3, bootstrap continuous-mapping theorem in
probability.

If `Zₙ* ->p* c` on sample-size-dependent bootstrap spaces and `g` is
continuous at `c`, then `g(Zₙ*) ->p* g(c)`. -/
theorem continuousAt_const_comp [PseudoMetricSpace E] [PseudoMetricSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zstar : ∀ n, Ω → Ωboot n → E} {c : E} {g : E → F}
    (hZ : TendstoInBootstrapProbabilityIndexed μ Pstar Zstar (fun _ => c))
    (hg : ContinuousAt g c) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) (fun _ => g c) := by
  intro η hη
  obtain ⟨δ, hδ, hδ_eventually⟩ := (Metric.continuousAt_iff.mp hg) η hη
  refine tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω =>
      bootstrapTailProbIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) (fun _ => g c) η n ω)
    (g := fun n ω => bootstrapTailProbIndexed Pstar Zstar (fun _ => c) δ n ω)
    ?_ ?_ (hZ δ hδ)
  · intro n ω
    exact ENNReal.toReal_nonneg
  · intro n ω
    refine ENNReal.toReal_mono ?_ (measure_mono ?_)
    · haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      exact measure_ne_top (Pstar n ω)
        {ωs | δ ≤ dist (Zstar n ω ωs) c}
    · intro ωs hωs
      by_contra hnot
      have hlt : dist (Zstar n ω ωs) c < δ := lt_of_not_ge hnot
      exact (not_lt_of_ge hωs) (hδ_eventually hlt)

/-- Indexed bootstrap convergence in probability is preserved by globally
Lipschitz maps. -/
theorem lipschitz_comp [PseudoMetricSpace E] [PseudoMetricSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zstar : ∀ n, Ω → Ωboot n → E} {Z : Ω → E} {g : E → F} {C : ℝ}
    (hC : 0 < C)
    (hg : ∀ x y, dist (g x) (g y) ≤ C * dist x y)
    (hZ : TendstoInBootstrapProbabilityIndexed μ Pstar Zstar Z) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) (fun ω => g (Z ω)) := by
  intro η hη
  have hδ : 0 < η / C := div_pos hη hC
  refine tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω =>
      bootstrapTailProbIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) (fun ω => g (Z ω))
        η n ω)
    (g := fun n ω => bootstrapTailProbIndexed Pstar Zstar Z (η / C) n ω)
    ?_ ?_ (hZ (η / C) hδ)
  · intro n ω
    exact ENNReal.toReal_nonneg
  · intro n ω
    refine ENNReal.toReal_mono ?_ (measure_mono ?_)
    · haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      exact measure_ne_top (Pstar n ω)
        {ωs | η / C ≤ dist (Zstar n ω ωs) (Z ω)}
    · intro ωs hωs
      by_contra hnot
      have hlt : dist (Zstar n ω ωs) (Z ω) < η / C := lt_of_not_ge hnot
      have hmap_lt : dist (g (Zstar n ω ωs)) (g (Z ω)) < η := by
        calc
          dist (g (Zstar n ω ωs)) (g (Z ω))
              ≤ C * dist (Zstar n ω ωs) (Z ω) := hg _ _
          _ < C * (η / C) := mul_lt_mul_of_pos_left hlt hC
          _ = η := by
            field_simp [ne_of_gt hC]
      exact (not_lt_of_ge hωs) hmap_lt

/-- Indexed bootstrap convergence in probability is closed under forming
product statistics. -/
theorem prodMk [PseudoMetricSpace E] [PseudoMetricSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Xstar : ∀ n, Ω → Ωboot n → E} {X : Ω → E}
    {Ystar : ∀ n, Ω → Ωboot n → F} {Y : Ω → F}
    (hX : TendstoInBootstrapProbabilityIndexed μ Pstar Xstar X)
    (hY : TendstoInBootstrapProbabilityIndexed μ Pstar Ystar Y) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
      (fun ω => (X ω, Y ω)) := by
  intro η hη
  refine tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω =>
      bootstrapTailProbIndexed Pstar
        (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
        (fun ω => (X ω, Y ω)) η n ω)
    (g := fun n ω =>
      bootstrapTailProbIndexed Pstar Xstar X η n ω +
        bootstrapTailProbIndexed Pstar Ystar Y η n ω)
    ?_ ?_
    (tendstoInMeasure_add_nonneg_zero
      (μ := μ)
      (f := fun n ω => bootstrapTailProbIndexed Pstar Xstar X η n ω)
      (g := fun n ω => bootstrapTailProbIndexed Pstar Ystar Y η n ω)
      (fun _ _ => ENNReal.toReal_nonneg)
      (fun _ _ => ENNReal.toReal_nonneg)
      (hX η hη) (hY η hη))
  · intro n ω
    exact ENNReal.toReal_nonneg
  · intro n ω
    let C : Set (Ωboot n) :=
      {ωs | η ≤ dist (Xstar n ω ωs, Ystar n ω ωs) (X ω, Y ω)}
    let A : Set (Ωboot n) := {ωs | η ≤ dist (Xstar n ω ωs) (X ω)}
    let B : Set (Ωboot n) := {ωs | η ≤ dist (Ystar n ω ωs) (Y ω)}
    have hsubset : C ⊆ A ∪ B := by
      intro ωs hωs
      rcases le_max_iff.mp (by simpa [C, A, B, Prod.dist_eq] using hωs) with h | h
      · exact Or.inl h
      · exact Or.inr h
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    calc
      bootstrapTailProbIndexed Pstar
          (fun n ω ωs => (Xstar n ω ωs, Ystar n ω ωs))
          (fun ω => (X ω, Y ω)) η n ω
          = ((Pstar n ω) C).toReal := rfl
      _ ≤ ((Pstar n ω) (A ∪ B)).toReal :=
          ENNReal.toReal_mono (measure_ne_top (Pstar n ω) (A ∪ B))
            (measure_mono hsubset)
      _ ≤ ((Pstar n ω) A + (Pstar n ω) B).toReal :=
          ENNReal.toReal_mono
            (ENNReal.add_ne_top.2
              ⟨measure_ne_top (Pstar n ω) A, measure_ne_top (Pstar n ω) B⟩)
            (measure_union_le A B)
      _ ≤ ((Pstar n ω) A).toReal + ((Pstar n ω) B).toReal :=
          ENNReal.toReal_add_le
      _ = bootstrapTailProbIndexed Pstar Xstar X η n ω +
          bootstrapTailProbIndexed Pstar Ystar Y η n ω := rfl

/-- Indexed bootstrap convergence in probability is closed under addition. -/
theorem add [SeminormedAddCommGroup E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Xstar Ystar : ∀ n, Ω → Ωboot n → E} {X Y : Ω → E}
    (hX : TendstoInBootstrapProbabilityIndexed μ Pstar Xstar X)
    (hY : TendstoInBootstrapProbabilityIndexed μ Pstar Ystar Y) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => Xstar n ω ωs + Ystar n ω ωs)
      (fun ω => X ω + Y ω) := by
  intro η hη
  have hhalf : 0 < η / 2 := by linarith
  refine tendstoInMeasure_zero_of_nonneg_le
    (μ := μ)
    (f := fun n ω =>
      bootstrapTailProbIndexed Pstar
        (fun n ω ωs => Xstar n ω ωs + Ystar n ω ωs)
        (fun ω => X ω + Y ω) η n ω)
    (g := fun n ω =>
      bootstrapTailProbIndexed Pstar Xstar X (η / 2) n ω +
        bootstrapTailProbIndexed Pstar Ystar Y (η / 2) n ω)
    ?_ ?_
    (tendstoInMeasure_add_nonneg_zero
      (μ := μ)
      (f := fun n ω => bootstrapTailProbIndexed Pstar Xstar X (η / 2) n ω)
      (g := fun n ω => bootstrapTailProbIndexed Pstar Ystar Y (η / 2) n ω)
      (fun _ _ => ENNReal.toReal_nonneg)
      (fun _ _ => ENNReal.toReal_nonneg)
      (hX (η / 2) hhalf) (hY (η / 2) hhalf))
  · intro n ω
    exact ENNReal.toReal_nonneg
  · intro n ω
    let C : Set (Ωboot n) :=
      {ωs | η ≤ dist (Xstar n ω ωs + Ystar n ω ωs) (X ω + Y ω)}
    let A : Set (Ωboot n) := {ωs | η / 2 ≤ dist (Xstar n ω ωs) (X ω)}
    let B : Set (Ωboot n) := {ωs | η / 2 ≤ dist (Ystar n ω ωs) (Y ω)}
    have hsubset : C ⊆ A ∪ B := by
      intro ωs hωs
      by_cases hA : η / 2 ≤ dist (Xstar n ω ωs) (X ω)
      · exact Or.inl hA
      · right
        by_contra hB
        have hX_lt : dist (Xstar n ω ωs) (X ω) < η / 2 := lt_of_not_ge hA
        have hY_lt : dist (Ystar n ω ωs) (Y ω) < η / 2 := lt_of_not_ge hB
        have hdist_le :
            dist (Xstar n ω ωs + Ystar n ω ωs) (X ω + Y ω) ≤
              dist (Xstar n ω ωs) (X ω) + dist (Ystar n ω ωs) (Y ω) :=
          dist_add_add_le _ _ _ _
        have hdist_lt :
            dist (Xstar n ω ωs + Ystar n ω ωs) (X ω + Y ω) < η := by
          linarith
        exact (not_lt_of_ge hωs) hdist_lt
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    calc
      bootstrapTailProbIndexed Pstar
          (fun n ω ωs => Xstar n ω ωs + Ystar n ω ωs)
          (fun ω => X ω + Y ω) η n ω
          = ((Pstar n ω) C).toReal := rfl
      _ ≤ ((Pstar n ω) (A ∪ B)).toReal :=
          ENNReal.toReal_mono (measure_ne_top (Pstar n ω) (A ∪ B))
            (measure_mono hsubset)
      _ ≤ ((Pstar n ω) A + (Pstar n ω) B).toReal :=
          ENNReal.toReal_mono
            (ENNReal.add_ne_top.2
              ⟨measure_ne_top (Pstar n ω) A, measure_ne_top (Pstar n ω) B⟩)
            (measure_union_le A B)
      _ ≤ ((Pstar n ω) A).toReal + ((Pstar n ω) B).toReal :=
          ENNReal.toReal_add_le
      _ = bootstrapTailProbIndexed Pstar Xstar X (η / 2) n ω +
          bootstrapTailProbIndexed Pstar Ystar Y (η / 2) n ω := rfl

/-- Indexed bootstrap convergence in probability is closed under negation. -/
theorem neg [SeminormedAddCommGroup E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E} {Z : Ω → E}
    (hZ : TendstoInBootstrapProbabilityIndexed μ Pstar Zstar Z) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => -Zstar n ω ωs) (fun ω => -Z ω) := by
  intro η hη
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl (hZ η hη)
  refine ae_of_all μ fun ω => ?_
  simp [bootstrapTailProbIndexed]

/-- Indexed bootstrap convergence in probability is closed under subtraction. -/
theorem sub [SeminormedAddCommGroup E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Xstar Ystar : ∀ n, Ω → Ωboot n → E} {X Y : Ω → E}
    (hX : TendstoInBootstrapProbabilityIndexed μ Pstar Xstar X)
    (hY : TendstoInBootstrapProbabilityIndexed μ Pstar Ystar Y) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => Xstar n ω ωs - Ystar n ω ωs)
      (fun ω => X ω - Y ω) := by
  have hsum := hX.add hPstar hY.neg
  exact hsum.congr
    (fun n ω ωs => by simp [sub_eq_add_neg])
    (fun ω => by simp [sub_eq_add_neg])

end TendstoInBootstrapProbabilityIndexed

/-- Indexed-space Hansen Theorem 10.3, chapter-facing name.

If `Zₙ* ->p* c` on sample-size-dependent bootstrap spaces and `g` is
continuous at `c`, then `g(Zₙ*) ->p* g(c)`. -/
theorem chapter10_indexed_bootstrap_continuous_mapping_probability
    [PseudoMetricSpace E] [PseudoMetricSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zstar : ∀ n, Ω → Ωboot n → E} {c : E} {g : E → F}
    (hZ : TendstoInBootstrapProbabilityIndexed μ Pstar Zstar (fun _ => c))
    (hg : ContinuousAt g c) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) (fun _ => g c) :=
  hZ.continuousAt_const_comp hPstar hg

/-- Indexed-space globally Lipschitz mapping bridge for bootstrap convergence
in probability. -/
theorem chapter10_indexed_bootstrap_lipschitz_mapping_probability
    [PseudoMetricSpace E] [PseudoMetricSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Zstar : ∀ n, Ω → Ωboot n → E} {Z : Ω → E} {g : E → F} {C : ℝ}
    (hC : 0 < C)
    (hg : ∀ x y, dist (g x) (g y) ≤ C * dist x y)
    (hZ : TendstoInBootstrapProbabilityIndexed μ Pstar Zstar Z) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) (fun ω => g (Z ω)) :=
  hZ.lipschitz_comp hPstar hC hg

/-- Indexed-space conditional Markov inequality, stated with a concrete
second moment. -/
theorem bootstrapTailProbIndexed_zero_le_integral_norm_sq_div
    [NormedAddCommGroup E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {η : ℝ} (hη : 0 < η) (n : ℕ) (ω : Ω) :
    bootstrapTailProbIndexed Pstar Zstar (fun _ => 0) η n ω ≤
      (∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω) / η ^ 2 := by
  let Pconst : ℕ → Ω → Measure (Ωboot n) := fun _ _ => Pstar n ω
  let Zconst : ℕ → Ω → Ωboot n → E := fun _ _ ωs => Zstar n ω ωs
  have hPconst : ∀ m ω', IsProbabilityMeasure (Pconst m ω') := fun _ _ => hPstar n ω
  have hZconst : ∀ m ω', MemLp (Zconst m ω') 2 (Pconst m ω') := fun _ _ => hZ n ω
  have htail :=
    bootstrapTailProb_zero_le_integral_norm_sq_div
      (Pstar := Pconst) (Zstar := Zconst) hPconst hZconst hη n ω
  simpa [bootstrapTailProbIndexed, bootstrapTailProb, Pconst, Zconst] using htail

/-- Shifted version of Hansen's Theorem 10.2 second-moment bound.

The ordinary `Fin (n+1)` empirical bootstrap avoids the empty sample-size-zero
case while preserving the same `atTop` asymptotics. -/
theorem bootstrapWLLNSecondMomentBound_succ_tendsto_zero
    [IsFiniteMeasure μ] {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ) {η : ℝ} (hη : 0 < η) :
    TendstoInMeasure μ
      (fun n ω => bootstrapWLLNSecondMomentBound u η (n + 1) ω)
      atTop (fun _ => 0) := by
  have h :=
    bootstrapWLLNSecondMomentBound_tendsto_zero
      (μ := μ) (u := u) (η := η) hu hη
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  simpa using (h ε hε).comp (tendsto_add_atTop_nat 1)

/-- Sample-size-indexed finite-resample norm bound in Hansen's Theorem 10.2
scale.

For sample size `n+1`, the expected squared norm of the centered ordinary
nonparametric-bootstrap mean is bounded by
`(n+1)^{-2} sum_{i<n+1} ||Y_i||^2`, the Marcinkiewicz statistic used in the
asymptotic Theorem 10.2 proof. -/
theorem integral_norm_sq_finSucc_resampleMean_sub_empiricalMean_le_marcinkiewicz
    {k : Type*} [Fintype k]
    (Y : ℕ → Ω → EuclideanSpace ℝ k) (n : ℕ) (ω : Ω) :
    ∫ ωs : Fin (n + 1) → Fin (n + 1),
        ‖empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω)‖ ^ 2
        ∂(ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) ≤
      marcinkiewiczWLLNStatisticNat (fun i ω => ‖Y i ω‖) 2 (n + 1) ω := by
  classical
  have hfinite :=
    integral_norm_sq_resampleMean_sub_empiricalMean_le_secondMoment
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω)
  have hsum :
      (∑ i : Fin (n + 1), ∑ a, Y i.val ω a * Y i.val ω a) =
        ∑ i ∈ Finset.range (n + 1), ‖Y i ω‖ * ‖Y i ω‖ := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl ?_
    intro i _
    simpa [pow_two] using (EuclideanSpace.real_norm_sq_eq (Y i.val ω)).symm
  have hscale :
      (Fintype.card (Fin (n + 1)) : ℝ)⁻¹ *
          (((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal •
            ∑ i : Fin (n + 1), ∑ a, Y i.val ω a ^ 2) =
        marcinkiewiczWLLNStatisticNat (fun i ω => ‖Y i ω‖) 2 (n + 1) ω := by
    have hcard_real : (Fintype.card (Fin (n + 1)) : ℝ) = (n + 1 : ℝ) := by
      simp [Fintype.card_fin]
    have hcard_enn_inv :
        (((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal) =
          ((n + 1 : ℝ)⁻¹) := by
      have htoReal :
          ((Fintype.card (Fin (n + 1)) : ℝ≥0∞).toReal) = (n + 1 : ℝ) := by
        rw [Fintype.card_fin]
        simpa using ENNReal.toReal_natCast (n + 1)
      rw [ENNReal.toReal_inv, htoReal]
    rw [show (∑ i : Fin (n + 1), ∑ a, Y i.val ω a ^ 2) =
        ∑ i : Fin (n + 1), ∑ a, Y i.val ω a * Y i.val ω a by
          simp [pow_two], hsum]
    rw [hcard_real, hcard_enn_inv]
    simp [marcinkiewiczWLLNStatisticNat, pow_two, mul_assoc]
  exact hfinite.trans_eq hscale

/-- Scalar sample-size-indexed finite-resample second-moment bound in Hansen's
Theorem 10.2 scale.

For sample size `n+1`, the expected squared centered ordinary
nonparametric-bootstrap mean is bounded by Hansen's
`(n+1)^{-2} sum_{i<n+1} |Y_i|^2` Marcinkiewicz statistic. -/
theorem integral_sq_finSucc_resampleMean_sub_empiricalMean_le_marcinkiewicz
    (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ∫ ωs : Fin (n + 1) → Fin (n + 1),
        (empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω)) ^ 2
        ∂(ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) ≤
      marcinkiewiczWLLNStatisticNat Y 2 (n + 1) ω := by
  classical
  have hfinite :=
    integral_sq_resampleMean_sub_empiricalMean_le_inv_card_mul_secondMoment
      (κ := Fin (n + 1)) (ι := Fin (n + 1))
      (Y := fun i : Fin (n + 1) => Y i.val ω)
  have hsum :
      (∑ i : Fin (n + 1), (Y i.val ω) ^ 2) =
        ∑ i ∈ Finset.range (n + 1), |Y i ω| ^ 2 := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    simp [sq_abs]
  have hscale :
      (Fintype.card (Fin (n + 1)) : ℝ)⁻¹ *
          (((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal •
            ∑ i : Fin (n + 1), (Y i.val ω) ^ 2) =
        marcinkiewiczWLLNStatisticNat Y 2 (n + 1) ω := by
    have hcard_real : (Fintype.card (Fin (n + 1)) : ℝ) = (n + 1 : ℝ) := by
      simp [Fintype.card_fin]
    have hcard_enn_inv :
        (((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal) =
          ((n + 1 : ℝ)⁻¹) := by
      have htoReal :
          ((Fintype.card (Fin (n + 1)) : ℝ≥0∞).toReal) = (n + 1 : ℝ) := by
        rw [Fintype.card_fin]
        simpa using ENNReal.toReal_natCast (n + 1)
      rw [ENNReal.toReal_inv, htoReal]
    rw [hsum, hcard_real, hcard_enn_inv]
    simp [marcinkiewiczWLLNStatisticNat, pow_two, mul_assoc]
  exact hfinite.trans_eq hscale

/-- Indexed-space Hansen Theorem 10.2 centered WLLN from a concrete conditional
second-moment bound. -/
theorem chapter10_indexed_bootstrap_wlln_centered_of_integral_norm_sq_bound
    [NormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ∀ n, Ω → Ωboot n → E} {Ybar : ℕ → Ω → E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hbound :
      ∀ n ω,
        (∫ ωs, ‖YbarStar n ω ωs - Ybar n ω‖ ^ 2 ∂Pstar n ω) ≤
          marcinkiewiczWLLNStatisticNat u 2 n ω) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) := by
  refine tendstoInBootstrapProbabilityIndexed_of_tail_bound
    (bound := fun η n ω => bootstrapWLLNSecondMomentBound u η n ω) ?_ ?_
  · intro η hη
    exact bootstrapWLLNSecondMomentBound_tendsto_zero (μ := μ) (η := η) hu hη
  · intro η hη n ω
    calc
      bootstrapTailProbIndexed Pstar
          (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0) η n ω
          ≤ (∫ ωs, ‖YbarStar n ω ωs - Ybar n ω‖ ^ 2 ∂Pstar n ω) / η ^ 2 :=
            bootstrapTailProbIndexed_zero_le_integral_norm_sq_div
              (Pstar := Pstar)
              (Zstar := fun n ω ωs => YbarStar n ω ωs - Ybar n ω)
              hPstar hZ hη n ω
      _ ≤ marcinkiewiczWLLNStatisticNat u 2 n ω / η ^ 2 :=
            div_le_div_of_nonneg_right (hbound n ω) (sq_nonneg η)
      _ = bootstrapWLLNSecondMomentBound u η n ω := by
            rw [bootstrapWLLNSecondMomentBound]
            field_simp [hη.ne']

/-- Indexed-space Hansen Theorem 10.2 level WLLN from the centered conclusion.

This is the indexed analogue of `chapter10_bootstrap_wlln_level_from_centered`:
centered bootstrap convergence on sample-size-dependent resampling spaces plus
ordinary convergence of the sample mean gives the level bootstrap WLLN. -/
theorem chapter10_indexed_bootstrap_wlln_level_from_centered
    [SeminormedAddCommGroup E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ∀ n, Ω → Ωboot n → E} {Ybar : ℕ → Ω → E} {μY : E}
    (hcenter :
      TendstoInBootstrapProbabilityIndexed μ Pstar
        (fun n ω ωs => YbarStar n ω ωs - Ybar n ω) (fun _ => 0))
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar YbarStar (fun _ => μY) := by
  have hYbar_boot :
      TendstoInBootstrapProbabilityIndexed μ Pstar
        (fun n ω _ => Ybar n ω) (fun _ => μY) :=
    tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure hPstar hYbar
  have hsum :=
    TendstoInBootstrapProbabilityIndexed.add hPstar hcenter hYbar_boot
  exact hsum.congr
    (fun n ω ωs => by simp)
    (fun ω => by simp)

/-- Indexed-space Hansen Theorem 10.2 level WLLN from a conditional
second-moment bound.

This is the sample-size-dependent analogue of
`chapter10_bootstrap_wlln_level_of_integral_norm_sq_bound`: a concrete
conditional bound on `E*[‖Ybar* - Ybar‖²]`, Hansen's Marcinkiewicz convergence
for the bound, and the ordinary WLLN for `Ybar` imply the level indexed
bootstrap WLLN. -/
theorem chapter10_indexed_bootstrap_wlln_level_of_integral_norm_sq_bound
    [NormedAddCommGroup E] [IsFiniteMeasure μ]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {YbarStar : ∀ n, Ω → Ωboot n → E} {Ybar : ℕ → Ω → E} {μY : E}
    {u : ℕ → Ω → ℝ}
    (hu : UniformIntegrable u 1 μ)
    (hZ : ∀ n ω, MemLp (fun ωs => YbarStar n ω ωs - Ybar n ω) 2 (Pstar n ω))
    (hbound :
      ∀ n ω,
        (∫ ωs, ‖YbarStar n ω ωs - Ybar n ω‖ ^ 2 ∂Pstar n ω) ≤
          marcinkiewiczWLLNStatisticNat u 2 n ω)
    (hYbar : TendstoInMeasure μ Ybar atTop (fun _ => μY)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar YbarStar (fun _ => μY) :=
  chapter10_indexed_bootstrap_wlln_level_from_centered
    (μ := μ) hPstar
    (chapter10_indexed_bootstrap_wlln_centered_of_integral_norm_sq_bound
      (μ := μ) (Pstar := Pstar) (YbarStar := YbarStar) (Ybar := Ybar)
      (u := u) hPstar hu hZ hbound)
    hYbar

/-- Ordinary finite nonparametric-bootstrap centered WLLN for `Fin (n+1)`
samples, obtained by feeding the finite squared-norm calculation into Hansen's
Theorem 10.2 Marcinkiewicz bound. -/
theorem chapter10_indexed_bootstrap_wlln_centered_finSucc_resampleMean
    [IsFiniteMeasure μ] {k : Type*} [Fintype k]
    (Y : ℕ → Ω → EuclideanSpace ℝ k)
    (hu : UniformIntegrable (fun i ω => ‖Y i ω‖) 1 μ) :
    TendstoInBootstrapProbabilityIndexed (μ := μ)
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
      (fun _ => 0) := by
  refine tendstoInBootstrapProbabilityIndexed_of_tail_bound
    (bound := fun η n ω =>
      bootstrapWLLNSecondMomentBound (fun i ω => ‖Y i ω‖) η (n + 1) ω) ?_ ?_
  · intro η hη
    exact bootstrapWLLNSecondMomentBound_succ_tendsto_zero
      (μ := μ) (u := fun i ω => ‖Y i ω‖) (η := η) hu hη
  · intro η hη n ω
    have hPstar :
        ∀ m (ω : Ω),
          IsProbabilityMeasure
            (ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (m + 1) → Fin (m + 1)))) := by
      intro m ω
      infer_instance
    have hZ :
        ∀ m (ω : Ω),
          MemLp
            (fun ωs : Fin (m + 1) → Fin (m + 1) =>
              empiricalBootstrapResampleMean
                  (fun i : Fin (m + 1) => Y i.val ω)
                  (fun ωs t => ωs t) ωs -
                empiricalMean (fun i : Fin (m + 1) => Y i.val ω))
            2
            (ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (m + 1) → Fin (m + 1)))) := by
      intro m ω
      exact memLp_two_uniformOn_univ
        (Y := fun ωs : Fin (m + 1) → Fin (m + 1) =>
          empiricalBootstrapResampleMean
              (fun i : Fin (m + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (m + 1) => Y i.val ω))
    calc
      bootstrapTailProbIndexed
          (fun n _ =>
            ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
          (fun n ω ωs =>
            empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
          (fun _ => 0) η n ω
          ≤ (∫ ωs : Fin (n + 1) → Fin (n + 1),
              ‖empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω)‖ ^ 2
              ∂(ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1)))) / η ^ 2 :=
            bootstrapTailProbIndexed_zero_le_integral_norm_sq_div
              (Pstar := fun n _ =>
                ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
              (Zstar := fun n ω ωs =>
                empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
              hPstar hZ hη n ω
      _ ≤ marcinkiewiczWLLNStatisticNat (fun i ω => ‖Y i ω‖) 2 (n + 1) ω /
            η ^ 2 :=
            div_le_div_of_nonneg_right
              (integral_norm_sq_finSucc_resampleMean_sub_empiricalMean_le_marcinkiewicz
                (Y := Y) n ω)
              (sq_nonneg η)
      _ = bootstrapWLLNSecondMomentBound (fun i ω => ‖Y i ω‖) η (n + 1) ω := by
            rw [bootstrapWLLNSecondMomentBound]
            field_simp [hη.ne']

/-- Ordinary finite nonparametric-bootstrap level WLLN for `Fin (n+1)` samples.

This packages the concrete centered finite-resample theorem with an ordinary
sample-mean convergence premise, giving Hansen Theorem 10.2's level conclusion
for the indexed ordinary nonparametric bootstrap. -/
theorem chapter10_indexed_bootstrap_wlln_level_finSucc_resampleMean
    [IsFiniteMeasure μ] {k : Type*} [Fintype k]
    (Y : ℕ → Ω → EuclideanSpace ℝ k) {μY : EuclideanSpace ℝ k}
    (hu : UniformIntegrable (fun i ω => ‖Y i ω‖) 1 μ)
    (hYbar :
      TendstoInMeasure μ
        (fun n ω => empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
        atTop (fun _ => μY)) :
    TendstoInBootstrapProbabilityIndexed (μ := μ)
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        empiricalBootstrapResampleMean
          (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs)
      (fun _ => μY) := by
  have hPstar :
      ∀ n (ω : Ω),
        IsProbabilityMeasure
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1)))) := by
    intro n ω
    infer_instance
  exact chapter10_indexed_bootstrap_wlln_level_from_centered
    (μ := μ)
    (Pstar := fun n _ =>
      ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
    hPstar
    (YbarStar := fun n ω ωs =>
      empiricalBootstrapResampleMean
        (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs)
    (Ybar := fun n ω => empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
    (μY := μY)
    (chapter10_indexed_bootstrap_wlln_centered_finSucc_resampleMean
      (μ := μ) Y hu)
    hYbar

/-- Ordinary scalar finite nonparametric-bootstrap centered WLLN for
`Fin (n+1)` samples.

This is the one-dimensional counterpart of
`chapter10_indexed_bootstrap_wlln_centered_finSucc_resampleMean`, using the
scalar empirical second-moment identity before applying Hansen's
Marcinkiewicz bound. -/
theorem chapter10_indexed_bootstrap_wlln_centered_real_finSucc_resampleMean
    [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (hu : UniformIntegrable Y 1 μ) :
    TendstoInBootstrapProbabilityIndexed (μ := μ)
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
      (fun _ => 0) := by
  have hPstar :
      ∀ n (ω : Ω),
        IsProbabilityMeasure
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1)))) := by
    intro n ω
    infer_instance
  have hZ :
      ∀ n (ω : Ω),
        MemLp
          (fun ωs : Fin (n + 1) → Fin (n + 1) =>
            empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
          2
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1)))) := by
    intro n ω
    exact memLp_two_uniformOn_univ
      (Y := fun ωs : Fin (n + 1) → Fin (n + 1) =>
        empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω)
            (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
  refine tendstoInBootstrapProbabilityIndexed_of_tail_bound
    (bound := fun η n ω => bootstrapWLLNSecondMomentBound Y η (n + 1) ω) ?_ ?_
  · intro η hη
    exact bootstrapWLLNSecondMomentBound_succ_tendsto_zero
      (μ := μ) (u := Y) (η := η) hu hη
  · intro η hη n ω
    calc
      bootstrapTailProbIndexed
          (fun n _ =>
            ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
          (fun n ω ωs =>
            empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
          (fun _ => 0) η n ω
          ≤ (∫ ωs : Fin (n + 1) → Fin (n + 1),
              ‖empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω)‖ ^ 2
              ∂(ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                  Measure (Fin (n + 1) → Fin (n + 1)))) / η ^ 2 :=
            bootstrapTailProbIndexed_zero_le_integral_norm_sq_div
              (Pstar := fun n _ =>
                ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
              (Zstar := fun n ω ωs =>
                empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
              hPstar hZ hη n ω
      _ ≤ marcinkiewiczWLLNStatisticNat Y 2 (n + 1) ω / η ^ 2 :=
            div_le_div_of_nonneg_right ?_ (sq_nonneg η)
      _ = bootstrapWLLNSecondMomentBound Y η (n + 1) ω := by
            rw [bootstrapWLLNSecondMomentBound]
            field_simp [hη.ne']
    simpa [Real.norm_eq_abs, sq_abs] using
      integral_sq_finSucc_resampleMean_sub_empiricalMean_le_marcinkiewicz
        (Y := Y) n ω

/-- Ordinary scalar finite nonparametric-bootstrap level WLLN for `Fin (n+1)`
samples.

This packages the concrete centered scalar finite-resample theorem with an
ordinary sample-mean convergence premise, giving Hansen Theorem 10.2's level
conclusion for the one-dimensional indexed ordinary nonparametric bootstrap. -/
theorem chapter10_indexed_bootstrap_wlln_level_real_finSucc_resampleMean
    [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) {μY : ℝ}
    (hu : UniformIntegrable Y 1 μ)
    (hYbar :
      TendstoInMeasure μ
        (fun n ω => empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
        atTop (fun _ => μY)) :
    TendstoInBootstrapProbabilityIndexed (μ := μ)
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        empiricalBootstrapResampleMean
          (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs)
      (fun _ => μY) := by
  have hPstar :
      ∀ n (ω : Ω),
        IsProbabilityMeasure
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1)))) := by
    intro n ω
    infer_instance
  exact chapter10_indexed_bootstrap_wlln_level_from_centered
    (μ := μ)
    (Pstar := fun n _ =>
      ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
    hPstar
    (YbarStar := fun n ω ωs =>
      empiricalBootstrapResampleMean
        (fun i : Fin (n + 1) => Y i.val ω) (fun ωs t => ωs t) ωs)
    (Ybar := fun n ω => empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
    (μY := μY)
    (chapter10_indexed_bootstrap_wlln_centered_real_finSucc_resampleMean
      (μ := μ) Y hu)
    hYbar

end IndexedBootstrapWLLN

section BootstrapDistribution

/-- Coordinatewise lower-tail relation for finite-dimensional CDFs. -/
def coordinateLE (x y : k → ℝ) : Prop :=
  ∀ i, x i ≤ y i

/-- Conditional bootstrap CDF `Gₙ*(x) = P*[Zₙ* ≤ x]` for a finite-dimensional
random vector. -/
noncomputable def bootstrapVectorCDF
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → k → ℝ)
    (x : k → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((Pstar n ω) {ωs | coordinateLE (Zstar n ω ωs) x}).toReal

/-- Limit CDF `G(x) = P[Z ≤ x]` for a finite-dimensional random vector. -/
noncomputable def vectorCDF
    (ν : Measure Ωlim) (Z : Ωlim → k → ℝ) (x : k → ℝ) : ℝ :=
  (ν {ω | coordinateLE (Z ω) x}).toReal

/-- Hansen Definition 10.2: convergence in bootstrap distribution.

The conditional CDF of `Zstar n` converges in ordinary probability, under the
original-sample law `μ`, to the limit CDF at every continuity point of the
limit CDF. -/
def TendstoInBootstrapDistribution
    (μ : Measure Ω) (Pstar : ℕ → Ω → Measure Ωs)
    (Zstar : ℕ → Ω → Ωs → k → ℝ)
    (ν : Measure Ωlim) (Z : Ωlim → k → ℝ) : Prop :=
  ∀ x : k → ℝ,
    ContinuousAt (fun y => vectorCDF ν Z y) x →
      TendstoInMeasure μ (fun n ω => bootstrapVectorCDF Pstar Zstar x n ω)
        atTop (fun _ => vectorCDF ν Z x)

/-- Constructor for Hansen Definition 10.2 from pointwise conditional-CDF
convergence. -/
theorem TendstoInBootstrapDistribution.of_tendsto_cdf
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hZ :
      ∀ x : k → ℝ,
        ContinuousAt (fun y => vectorCDF ν Z y) x →
          TendstoInMeasure μ (fun n ω => bootstrapVectorCDF Pstar Zstar x n ω)
            atTop (fun _ => vectorCDF ν Z x)) :
    TendstoInBootstrapDistribution μ Pstar Zstar ν Z :=
  hZ

/-- The CDF-convergence projection built into Hansen Definition 10.2. -/
theorem TendstoInBootstrapDistribution.tendsto_cdf
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hZ : TendstoInBootstrapDistribution μ Pstar Zstar ν Z)
    {x : k → ℝ} (hx : ContinuousAt (fun y => vectorCDF ν Z y) x) :
    TendstoInMeasure μ (fun n ω => bootstrapVectorCDF Pstar Zstar x n ω)
      atTop (fun _ => vectorCDF ν Z x) :=
  hZ x hx

/-- Bootstrap-distribution convergence is invariant under pointwise equality of
the bootstrap statistic. -/
theorem TendstoInBootstrapDistribution.congr_bootstrap
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hZ : TendstoInBootstrapDistribution μ Pstar Zstar ν Z) :
    TendstoInBootstrapDistribution μ Pstar Zstar' ν Z := by
  intro x hx
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl (hZ.tendsto_cdf hx)
  refine ae_of_all μ fun ω => ?_
  have hset :
      {ωs : Ωs | coordinateLE (Zstar' n ω ωs) x} =
        {ωs : Ωs | coordinateLE (Zstar n ω ωs) x} := by
    ext ωs
    simp [coordinateLE, hstar n ω ωs]
  simp [bootstrapVectorCDF, hset]

/-- Bootstrap-distribution convergence is invariant under pointwise equality of
the limiting statistic. -/
theorem TendstoInBootstrapDistribution.congr_limit
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z Z' : Ωlim → k → ℝ}
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapDistribution μ Pstar Zstar ν Z) :
    TendstoInBootstrapDistribution μ Pstar Zstar ν Z' := by
  intro x hx
  have hcdf_fun :
      (fun y => vectorCDF ν Z y) = fun y => vectorCDF ν Z' y := by
    funext y
    simp [vectorCDF, hlim]
  have hx_old : ContinuousAt (fun y => vectorCDF ν Z y) x := by
    simpa [hcdf_fun] using hx
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_
    (hZ.tendsto_cdf hx_old)
  refine ae_of_all μ fun _ => ?_
  simp [hcdf_fun]

/-- Pointwise congruence for bootstrap convergence in distribution. -/
theorem TendstoInBootstrapDistribution.congr
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → k → ℝ}
    {Z Z' : Ωlim → k → ℝ}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapDistribution μ Pstar Zstar ν Z) :
    TendstoInBootstrapDistribution μ Pstar Zstar' ν Z' :=
  (hZ.congr_bootstrap hstar).congr_limit hlim

variable {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]

/-- Indexed conditional bootstrap CDF for sample-size-dependent bootstrap
spaces. -/
noncomputable def bootstrapVectorCDFIndexed
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → k → ℝ)
    (x : k → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((Pstar n ω) {ωs | coordinateLE (Zstar n ω ωs) x}).toReal

/-- Indexed-space Hansen Definition 10.2.

This is the distributional counterpart of
`TendstoInBootstrapProbabilityIndexed`; it is needed for ordinary
nonparametric bootstrap constructions whose resampling space varies with
sample size, such as `Fin (n + 1) → Fin (n + 1)`. -/
def TendstoInBootstrapDistributionIndexed
    (μ : Measure Ω) (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → k → ℝ)
    (ν : Measure Ωlim) (Z : Ωlim → k → ℝ) : Prop :=
  ∀ x : k → ℝ,
    ContinuousAt (fun y => vectorCDF ν Z y) x →
      TendstoInMeasure μ
        (fun n ω => bootstrapVectorCDFIndexed Pstar Zstar x n ω)
        atTop (fun _ => vectorCDF ν Z x)

/-- Constructor for indexed Hansen Definition 10.2 from pointwise conditional
CDF convergence. -/
theorem TendstoInBootstrapDistributionIndexed.of_tendsto_cdf
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hZ :
      ∀ x : k → ℝ,
        ContinuousAt (fun y => vectorCDF ν Z y) x →
          TendstoInMeasure μ
            (fun n ω => bootstrapVectorCDFIndexed Pstar Zstar x n ω)
            atTop (fun _ => vectorCDF ν Z x)) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar ν Z :=
  hZ

/-- The CDF-convergence projection built into indexed Hansen Definition 10.2. -/
theorem TendstoInBootstrapDistributionIndexed.tendsto_cdf
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hZ : TendstoInBootstrapDistributionIndexed μ Pstar Zstar ν Z)
    {x : k → ℝ} (hx : ContinuousAt (fun y => vectorCDF ν Z y) x) :
    TendstoInMeasure μ
      (fun n ω => bootstrapVectorCDFIndexed Pstar Zstar x n ω)
      atTop (fun _ => vectorCDF ν Z x) :=
  hZ x hx

/-- Indexed bootstrap-distribution convergence is invariant under pointwise
equality of the bootstrap statistic. -/
theorem TendstoInBootstrapDistributionIndexed.congr_bootstrap
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hZ : TendstoInBootstrapDistributionIndexed μ Pstar Zstar ν Z) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar' ν Z := by
  intro x hx
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl (hZ.tendsto_cdf hx)
  refine ae_of_all μ fun ω => ?_
  have hset :
      {ωs : Ωboot n | coordinateLE (Zstar' n ω ωs) x} =
        {ωs : Ωboot n | coordinateLE (Zstar n ω ωs) x} := by
    ext ωs
    simp [coordinateLE, hstar n ω ωs]
  simp [bootstrapVectorCDFIndexed, hset]

/-- Indexed bootstrap-distribution convergence is invariant under pointwise
equality of the limiting statistic. -/
theorem TendstoInBootstrapDistributionIndexed.congr_limit
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z Z' : Ωlim → k → ℝ}
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapDistributionIndexed μ Pstar Zstar ν Z) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar ν Z' := by
  intro x hx
  have hcdf_fun :
      (fun y => vectorCDF ν Z y) = fun y => vectorCDF ν Z' y := by
    funext y
    simp [vectorCDF, hlim]
  have hx_old : ContinuousAt (fun y => vectorCDF ν Z y) x := by
    simpa [hcdf_fun] using hx
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_
    (hZ.tendsto_cdf hx_old)
  refine ae_of_all μ fun _ => ?_
  simp [hcdf_fun]

/-- Pointwise congruence for indexed bootstrap convergence in distribution. -/
theorem TendstoInBootstrapDistributionIndexed.congr
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z Z' : Ωlim → k → ℝ}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapDistributionIndexed μ Pstar Zstar ν Z) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar' ν Z' :=
  (hZ.congr_bootstrap hstar).congr_limit hlim

/-- Hansen Theorem 10.4, Gaussian bootstrap CLT CDF wrapper.

If the conditional CDFs of a normalized bootstrap statistic converge in
probability to the CDF of `N(0, Σ)` at every continuity point, then the
statistic converges in bootstrap distribution to that Gaussian law. The
remaining empirical-bootstrap CLT work is to derive this CDF premise from
Hansen's iid and second-moment assumptions. -/
theorem chapter10_bootstrap_clt_gaussian_of_tendsto_cdf
    [Fintype k] [DecidableEq k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {S : Matrix k k ℝ}
    (hcdf :
      ∀ x : k → ℝ,
        ContinuousAt
            (fun y =>
              vectorCDF
                (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
                (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
          TendstoInMeasure μ (fun n ω => bootstrapVectorCDF Pstar Zstar x n ω)
            atTop
            (fun _ =>
              vectorCDF
                (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
                (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) x)) :
    TendstoInBootstrapDistribution μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  TendstoInBootstrapDistribution.of_tendsto_cdf hcdf

/-- Indexed-space Hansen Theorem 10.4 Gaussian bootstrap CLT CDF wrapper.

This is the sample-size-dependent counterpart of
`chapter10_bootstrap_clt_gaussian_of_tendsto_cdf`, for ordinary finite
nonparametric bootstrap constructions whose resampling type varies with `n`. -/
theorem chapter10_indexed_bootstrap_clt_gaussian_of_tendsto_cdf
    [Fintype k] [DecidableEq k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {S : Matrix k k ℝ}
    (hcdf :
      ∀ x : k → ℝ,
        ContinuousAt
            (fun y =>
              vectorCDF
                (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
                (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
          TendstoInMeasure μ
            (fun n ω => bootstrapVectorCDFIndexed Pstar Zstar x n ω)
            atTop
            (fun _ =>
              vectorCDF
                (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
                (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) x)) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  TendstoInBootstrapDistributionIndexed.of_tendsto_cdf hcdf

end BootstrapDistribution

section BootstrapWeakDistribution

/-- Conditional bootstrap expectation of a bounded continuous test function.

This is the bounded-continuous-test-function analogue of the conditional CDF
used in `TendstoInBootstrapDistribution`.  It is a convenient weak-convergence
backend for mapping theorems, while the finite-dimensional CDF API remains the
chapter-facing form of Hansen Definition 10.2. -/
noncomputable def bootstrapBoundedContinuousIntegral
    [TopologicalSpace E]
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → E)
    (f : BoundedContinuousFunction E ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ ωs, f (Zstar n ω ωs) ∂Pstar n ω

/-- Conditional bootstrap probability of an event under the transformed
bootstrap statistic.

This real-valued wrapper is the event-probability face used after
bounded-continuous weak convergence has supplied a Portmanteau-style
lower/upper sandwich. -/
noncomputable def bootstrapEventProbability
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → E)
    (A : Set E) (n : ℕ) (ω : Ω) : ℝ :=
  ((Pstar n ω) {ωs | Zstar n ω ωs ∈ A}).toReal

/-- Bootstrap convergence in distribution in bounded-continuous-test-function
form.

For every bounded continuous real test function, the conditional bootstrap
expectation converges in ordinary probability to the corresponding expectation
under the limiting law. -/
def TendstoInBootstrapWeakDistribution
    [TopologicalSpace E]
    (μ : Measure Ω) (Pstar : ℕ → Ω → Measure Ωs)
    (Zstar : ℕ → Ω → Ωs → E)
    (ν : Measure Ωlim) (Z : Ωlim → E) : Prop :=
  ∀ f : BoundedContinuousFunction E ℝ,
    TendstoInMeasure μ
      (fun n ω => bootstrapBoundedContinuousIntegral Pstar Zstar f n ω)
      atTop (fun _ => ∫ ωlim, f (Z ωlim) ∂ν)

/-- Projection from the bounded-continuous-test-function bootstrap convergence
definition. -/
theorem TendstoInBootstrapWeakDistribution.tendsto_integral
    [TopologicalSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (f : BoundedContinuousFunction E ℝ) :
    TendstoInMeasure μ
      (fun n ω => bootstrapBoundedContinuousIntegral Pstar Zstar f n ω)
      atTop (fun _ => ∫ ωlim, f (Z ωlim) ∂ν) :=
  hZ f

/-- Bootstrap weak convergence is invariant under pointwise equality of the
bootstrap statistic. -/
theorem TendstoInBootstrapWeakDistribution.congr_bootstrap
    [TopologicalSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z) :
    TendstoInBootstrapWeakDistribution μ Pstar Zstar' ν Z := by
  intro f
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl (hZ.tendsto_integral f)
  refine ae_of_all μ fun ω => ?_
  simp [bootstrapBoundedContinuousIntegral, hstar]

/-- Bootstrap weak convergence is invariant under pointwise equality of the
limiting statistic. -/
theorem TendstoInBootstrapWeakDistribution.congr_limit
    [TopologicalSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {Z Z' : Ωlim → E}
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z) :
    TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z' := by
  intro f
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ (hZ.tendsto_integral f)
  refine ae_of_all μ fun _ => ?_
  simp [hlim]

/-- Pointwise congruence for bootstrap weak convergence. -/
theorem TendstoInBootstrapWeakDistribution.congr
    [TopologicalSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → E}
    {Z Z' : Ωlim → E}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z) :
    TendstoInBootstrapWeakDistribution μ Pstar Zstar' ν Z' :=
  (hZ.congr_bootstrap hstar).congr_limit hlim

/-- Transfer bootstrap weak convergence across an `oₚ(1)` difference in every
bounded-continuous test-function integral.

This is the reusable linearization bridge behind nonlinear bootstrap Delta
method wrappers: once the linearized statistic has a bootstrap weak limit, it
is enough to show that applying any bounded continuous test function and
taking the conditional bootstrap expectation differs from the nonlinear
statistic by `oₚ(1)`. -/
theorem TendstoInBootstrapWeakDistribution.of_integral_difference_zero
    [TopologicalSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hdiff :
      ∀ f : BoundedContinuousFunction E ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegral Pstar Zstar' f n ω -
              bootstrapBoundedContinuousIntegral Pstar Zstar f n ω)
          atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistribution μ Pstar Zstar' ν Z := by
  intro f
  have hlin := hZ.tendsto_integral f
  have hlin0 := TendstoInMeasure.sub_limit_zero_real hlin
  have hsum := TendstoInMeasure.add_zero_real (hdiff f) hlin0
  have htarget0 :
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapBoundedContinuousIntegral Pstar Zstar' f n ω -
            ∫ ωlim, f (Z ωlim) ∂ν)
        atTop (fun _ => 0) := by
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hsum
    exact ae_of_all μ fun ω => by ring
  exact TendstoInMeasure.of_sub_limit_zero_real htarget0

variable {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]

/-- Indexed conditional bootstrap expectation of a bounded continuous test
function, for sample-size-dependent bootstrap spaces. -/
noncomputable def bootstrapBoundedContinuousIntegralIndexed
    [TopologicalSpace E]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → E)
    (f : BoundedContinuousFunction E ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ ωs, f (Zstar n ω ωs) ∂Pstar n ω

/-- Indexed conditional bootstrap probability of a transformed event. -/
noncomputable def bootstrapEventProbabilityIndexed
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → E)
    (A : Set E) (n : ℕ) (ω : Ω) : ℝ :=
  ((Pstar n ω) {ωs | Zstar n ω ωs ∈ A}).toReal

/-- Indexed bootstrap convergence in distribution in
bounded-continuous-test-function form.

This is the sample-size-dependent counterpart of
`TendstoInBootstrapWeakDistribution`, used when the ordinary nonparametric
bootstrap resampling space varies with `n`. -/
def TendstoInBootstrapWeakDistributionIndexed
    [TopologicalSpace E]
    (μ : Measure Ω) (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → E)
    (ν : Measure Ωlim) (Z : Ωlim → E) : Prop :=
  ∀ f : BoundedContinuousFunction E ℝ,
    TendstoInMeasure μ
      (fun n ω => bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
      atTop (fun _ => ∫ ωlim, f (Z ωlim) ∂ν)

/-- Projection from indexed bounded-continuous-test-function bootstrap
convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.tendsto_integral
    [TopologicalSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (f : BoundedContinuousFunction E ℝ) :
    TendstoInMeasure μ
      (fun n ω => bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
      atTop (fun _ => ∫ ωlim, f (Z ωlim) ∂ν) :=
  hZ f

/-- Indexed bootstrap weak convergence is invariant under pointwise equality of
the bootstrap statistic. -/
theorem TendstoInBootstrapWeakDistributionIndexed.congr_bootstrap
    [TopologicalSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' ν Z := by
  intro f
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl (hZ.tendsto_integral f)
  refine ae_of_all μ fun ω => ?_
  simp [bootstrapBoundedContinuousIntegralIndexed, hstar]

/-- Indexed bootstrap weak convergence is invariant under pointwise equality of
the limiting statistic. -/
theorem TendstoInBootstrapWeakDistributionIndexed.congr_limit
    [TopologicalSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z Z' : Ωlim → E}
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z' := by
  intro f
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ (hZ.tendsto_integral f)
  refine ae_of_all μ fun _ => ?_
  simp [hlim]

/-- Pointwise congruence for indexed bootstrap weak convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.congr
    [TopologicalSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {Z Z' : Ωlim → E}
    (hstar : ∀ n ω ωs, Zstar n ω ωs = Zstar' n ω ωs)
    (hlim : ∀ ω, Z ω = Z' ω)
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' ν Z' :=
  (hZ.congr_bootstrap hstar).congr_limit hlim

/-- Transfer indexed bootstrap weak convergence across an `oₚ(1)` difference in
every bounded-continuous test-function integral. -/
theorem TendstoInBootstrapWeakDistributionIndexed.of_integral_difference_zero
    [TopologicalSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hdiff :
      ∀ f : BoundedContinuousFunction E ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
          atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar' ν Z := by
  intro f
  have hlin := hZ.tendsto_integral f
  have hlin0 := TendstoInMeasure.sub_limit_zero_real hlin
  have hsum := TendstoInMeasure.add_zero_real (hdiff f) hlin0
  have htarget0 :
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
            ∫ ωlim, f (Z ωlim) ∂ν)
        atTop (fun _ => 0) := by
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hsum
    exact ae_of_all μ fun ω => by ring
  exact TendstoInMeasure.of_sub_limit_zero_real htarget0

private theorem tendstoInMeasure_of_squeeze_approx_real
    {X : ℕ → Ω → ℝ} {c : ℝ}
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ L U : ℕ → Ω → ℝ, ∃ l u : ℝ,
          l ≤ c ∧ c ≤ u ∧ u - l ≤ ε ∧
            (∀ n ω, L n ω ≤ X n ω) ∧
            (∀ n ω, X n ω ≤ U n ω) ∧
            TendstoInMeasure μ L atTop (fun _ => l) ∧
            TendstoInMeasure μ U atTop (fun _ => u)) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨L, U, l, u, hlc, hcu, hgap, hLX, hXU, hL, hU⟩ :=
    happrox (ε / 3) hε3
  rw [tendstoInMeasure_iff_dist] at hL hU
  have hLtail := hL (ε / 3) hε3
  have hUtail := hU (ε / 3) hε3
  have hsum :
      Tendsto
        (fun n =>
          μ {ω | ε / 3 ≤ dist (L n ω) l} +
            μ {ω | ε / 3 ≤ dist (U n ω) u})
        atTop (𝓝 0) := by
    simpa using hLtail.add hUtail
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le _) ?_
  intro n
  calc
    μ {ω | ε ≤ dist (X n ω) c}
        ≤ μ ({ω | ε / 3 ≤ dist (L n ω) l} ∪
            {ω | ε / 3 ≤ dist (U n ω) u}) := by
          refine measure_mono ?_
          intro ω hω
          simp only [Set.mem_union, Set.mem_setOf_eq]
          by_cases hLbig : ε / 3 ≤ dist (L n ω) l
          · exact Or.inl hLbig
          · right
            by_contra hUnot
            have hLsmall : dist (L n ω) l < ε / 3 := not_le.mp hLbig
            have hUsmall : dist (U n ω) u < ε / 3 := not_le.mp hUnot
            have hLabs : |L n ω - l| < ε / 3 := by
              simpa [Real.dist_eq] using hLsmall
            have hUabs : |U n ω - u| < ε / 3 := by
              simpa [Real.dist_eq] using hUsmall
            have hLgt : l - ε / 3 < L n ω := by
              linarith [(abs_lt.mp hLabs).1]
            have hUlt : U n ω < u + ε / 3 := by
              linarith [(abs_lt.mp hUabs).2]
            have hx_lower : c - ε < X n ω := by
              have hcl : c - l ≤ ε / 3 := by linarith
              linarith [hLgt, hLX n ω]
            have hx_upper : X n ω < c + ε := by
              have huc : u - c ≤ ε / 3 := by linarith
              linarith [hUlt, hXU n ω]
            have hdist_lt : dist (X n ω) c < ε := by
              rw [Real.dist_eq]
              exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
            exact (not_le_of_gt hdist_lt) hω
    _ ≤ μ {ω | ε / 3 ≤ dist (L n ω) l} +
        μ {ω | ε / 3 ≤ dist (U n ω) u} :=
          measure_union_le _ _

/-- Bootstrap weak convergence gives event-probability convergence whenever
the event indicator can be squeezed by bounded continuous test functions.

This is the reusable Portmanteau-style bridge for Hansen Theorem 10.5's
event-probability face.  The topological/null-frontier argument that constructs
the lower and upper bounded continuous functions is kept as an explicit premise,
so the theorem works for any event class where that approximation is available. -/
theorem TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_boundedContinuous_sandwich
    [TopologicalSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E} {A : Set E} {c : ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ lower upper : BoundedContinuousFunction E ℝ,
        (∫ ωlim, lower (Z ωlim) ∂ν) ≤ c ∧
          c ≤ (∫ ωlim, upper (Z ωlim) ∂ν) ∧
          (∫ ωlim, upper (Z ωlim) ∂ν) -
              (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
          (∀ n ω,
            bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤
              bootstrapEventProbability Pstar Zstar A n ω) ∧
          (∀ n ω,
            bootstrapEventProbability Pstar Zstar A n ω ≤
              bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω)) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar Zstar A)
      atTop (fun _ => c) := by
  refine tendstoInMeasure_of_squeeze_approx_real (μ := μ) ?_
  intro ε hε
  obtain ⟨lower, upper, hlc, hcu, hgap, hlower, hupper⟩ := happrox ε hε
  refine ⟨bootstrapBoundedContinuousIntegral Pstar Zstar lower,
    bootstrapBoundedContinuousIntegral Pstar Zstar upper,
    ∫ ωlim, lower (Z ωlim) ∂ν,
    ∫ ωlim, upper (Z ωlim) ∂ν, hlc, hcu, hgap, hlower, hupper, ?_, ?_⟩
  · exact hZ.tendsto_integral lower
  · exact hZ.tendsto_integral upper

/-- Indexed bootstrap weak convergence gives event-probability convergence
whenever the event indicator can be squeezed by bounded continuous test
functions. -/
theorem TendstoInBootstrapWeakDistributionIndexed.event_probability_tendsto_of_sandwich
    [TopologicalSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E} {A : Set E} {c : ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ lower upper : BoundedContinuousFunction E ℝ,
        (∫ ωlim, lower (Z ωlim) ∂ν) ≤ c ∧
          c ≤ (∫ ωlim, upper (Z ωlim) ∂ν) ∧
          (∫ ωlim, upper (Z ωlim) ∂ν) -
              (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
          (∀ n ω,
            bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤
              bootstrapEventProbabilityIndexed Pstar Zstar A n ω) ∧
          (∀ n ω,
            bootstrapEventProbabilityIndexed Pstar Zstar A n ω ≤
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω)) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar Zstar A)
      atTop (fun _ => c) := by
  refine tendstoInMeasure_of_squeeze_approx_real (μ := μ) ?_
  intro ε hε
  obtain ⟨lower, upper, hlc, hcu, hgap, hlower, hupper⟩ := happrox ε hε
  refine ⟨bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower,
    bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper,
    ∫ ωlim, lower (Z ωlim) ∂ν,
    ∫ ωlim, upper (Z ωlim) ∂ν, hlc, hcu, hgap, hlower, hupper, ?_, ?_⟩
  · exact hZ.tendsto_integral lower
  · exact hZ.tendsto_integral upper

/-- Bootstrap weak convergence transfers any real conditional functional that
can be squeezed by bounded continuous test-function integrals.

This is the general bounded-continuous sandwich step behind the
Portmanteau/event-probability bridge and the a.e.-continuous mapping route:
once the target conditional functional lies between lower and upper bounded
continuous test integrals whose limit-law integrals have arbitrarily small
gap, convergence in probability follows. -/
theorem TendstoInBootstrapWeakDistribution.integral_tendsto_of_boundedContinuous_sandwich
    [TopologicalSpace E]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E} {X : ℕ → Ω → ℝ} {c : ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ lower upper : BoundedContinuousFunction E ℝ,
        (∫ ωlim, lower (Z ωlim) ∂ν) ≤ c ∧
          c ≤ (∫ ωlim, upper (Z ωlim) ∂ν) ∧
          (∫ ωlim, upper (Z ωlim) ∂ν) -
              (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
          (∀ n ω,
            bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤ X n ω) ∧
          (∀ n ω,
            X n ω ≤
              bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω)) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  refine tendstoInMeasure_of_squeeze_approx_real (μ := μ) ?_
  intro ε hε
  obtain ⟨lower, upper, hlc, hcu, hgap, hlower, hupper⟩ := happrox ε hε
  refine ⟨bootstrapBoundedContinuousIntegral Pstar Zstar lower,
    bootstrapBoundedContinuousIntegral Pstar Zstar upper,
    ∫ ωlim, lower (Z ωlim) ∂ν,
    ∫ ωlim, upper (Z ωlim) ∂ν, hlc, hcu, hgap, hlower, hupper, ?_, ?_⟩
  · exact hZ.tendsto_integral lower
  · exact hZ.tendsto_integral upper

/-- Indexed bootstrap weak convergence transfers real conditional functionals
that are squeezed by bounded continuous test-function integrals. -/
theorem TendstoInBootstrapWeakDistributionIndexed.integral_tendsto_of_sandwich
    [TopologicalSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E} {X : ℕ → Ω → ℝ} {c : ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ lower upper : BoundedContinuousFunction E ℝ,
        (∫ ωlim, lower (Z ωlim) ∂ν) ≤ c ∧
          c ≤ (∫ ωlim, upper (Z ωlim) ∂ν) ∧
          (∫ ωlim, upper (Z ωlim) ∂ν) -
              (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
          (∀ n ω,
            bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤ X n ω) ∧
          (∀ n ω,
            X n ω ≤
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω)) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  refine tendstoInMeasure_of_squeeze_approx_real (μ := μ) ?_
  intro ε hε
  obtain ⟨lower, upper, hlc, hcu, hgap, hlower, hupper⟩ := happrox ε hε
  refine ⟨bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower,
    bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper,
    ∫ ωlim, lower (Z ωlim) ∂ν,
    ∫ ωlim, upper (Z ωlim) ∂ν, hlc, hcu, hgap, hlower, hupper, ?_, ?_⟩
  · exact hZ.tendsto_integral lower
  · exact hZ.tendsto_integral upper

/-- Bootstrap weak convergence mapped through a possibly discontinuous
transformation, assuming bounded-continuous sandwich approximations for every
bounded continuous test function after transformation.

This is the reusable approximation-facing form of Hansen Theorem 10.5.  The
separate topological step for an a.e.-continuous `g` is to construct the
sandwich premise for each transformed test function. -/
theorem TendstoInBootstrapWeakDistribution.map_of_boundedContinuous_sandwich
    [TopologicalSpace E] [TopologicalSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E} {g : E → F}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction F ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  intro f
  exact hZ.integral_tendsto_of_boundedContinuous_sandwich
    (X := fun n ω =>
      bootstrapBoundedContinuousIntegral Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) f n ω)
    (c := ∫ ωlim, f (g (Z ωlim)) ∂ν)
    (happrox f)

/-- Indexed version of
`TendstoInBootstrapWeakDistribution.map_of_boundedContinuous_sandwich`. -/
theorem TendstoInBootstrapWeakDistributionIndexed.map_of_boundedContinuous_sandwich
    [TopologicalSpace E] [TopologicalSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E} {g : E → F}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction F ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  intro f
  exact hZ.integral_tendsto_of_sandwich
    (X := fun n ω =>
      bootstrapBoundedContinuousIntegralIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) f n ω)
    (c := ∫ ωlim, f (g (Z ωlim)) ∂ν)
    (happrox f)

private noncomputable def nnrealBoundedContinuousFunctionToReal
    [TopologicalSpace E] (f : BoundedContinuousFunction E NNReal) :
    BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.comp ((↑) : NNReal → ℝ)
    NNReal.isometry_coe.lipschitz f

private theorem nnrealBoundedContinuousFunctionToReal_apply
    [TopologicalSpace E] (f : BoundedContinuousFunction E NNReal) (x : E) :
    nnrealBoundedContinuousFunctionToReal f x = (f x : ℝ) :=
  rfl

/-- Bounded-continuous lower/upper sandwiches for events with null frontier.

For a probability law on a pseudo-emetric space, if the event boundary carries
zero mass, then for every tolerance there are bounded continuous functions
below and above the event indicator whose integrals differ by at most that
tolerance.  This is the topological approximation input needed by the
bootstrap event-probability Portmanteau bridge. -/
theorem boundedContinuous_event_sandwich_of_null_frontier
    [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {law : Measure E} [IsProbabilityMeasure law] {A : Set E}
    {ε : ℝ} (hε : 0 < ε) (hfrontier : law (frontier A) = 0) :
    ∃ lower upper : BoundedContinuousFunction E ℝ,
      (∀ x, x ∈ A → lower x ≤ 1) ∧
        (∀ x, x ∉ A → lower x ≤ 0) ∧
        (∀ x, x ∈ A → 1 ≤ upper x) ∧
        (∀ x, 0 ≤ upper x) ∧
        (∫ x, lower x ∂law) ≤ law.real A ∧
        law.real A ≤ (∫ x, upper x ∂law) ∧
        (∫ x, upper x ∂law) - (∫ x, lower x ∂law) ≤ ε := by
  classical
  let δs : ℕ → ℝ := fun n => (1 : ℝ) / (n + 1)
  have hδs_pos : ∀ n, 0 < δs n := fun n => by positivity
  have hδs_lim : Tendsto δs atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let upperSeq : ℕ → BoundedContinuousFunction E ℝ := fun n =>
    nnrealBoundedContinuousFunctionToReal (thickenedIndicator (hδs_pos n) (closure A))
  let complSeq : ℕ → BoundedContinuousFunction E ℝ := fun n =>
    nnrealBoundedContinuousFunctionToReal (thickenedIndicator (hδs_pos n) (interior A)ᶜ)
  have hupper_tendsto :
      Tendsto (fun n => ∫ x, upperSeq n x ∂law)
        atTop (𝓝 (law.real (closure A))) := by
    change Tendsto
      (fun n => ∫ x, (thickenedIndicator (hδs_pos n) (closure A) x : ℝ) ∂law)
        atTop (𝓝 (law.real (closure A)))
    exact tendsto_integral_thickenedIndicator_of_isClosed law isClosed_closure
      (δs_pos := hδs_pos) hδs_lim
  have hcompl_tendsto :
      Tendsto (fun n => ∫ x, complSeq n x ∂law)
        atTop (𝓝 (law.real ((interior A)ᶜ))) := by
    change Tendsto
      (fun n => ∫ x, (thickenedIndicator (hδs_pos n) (interior A)ᶜ x : ℝ) ∂law)
        atTop (𝓝 (law.real ((interior A)ᶜ)))
    exact tendsto_integral_thickenedIndicator_of_isClosed law
      isOpen_interior.isClosed_compl
      (δs_pos := hδs_pos) hδs_lim
  have hε4 : 0 < ε / 4 := by positivity
  have hupper_room : law.real (closure A) < law.real (closure A) + ε / 4 := by
    linarith
  have hcompl_room : law.real ((interior A)ᶜ) < law.real ((interior A)ᶜ) + ε / 4 := by
    linarith
  obtain ⟨Nu, hNu⟩ :=
    eventually_atTop.mp (hupper_tendsto.eventually_lt_const hupper_room)
  obtain ⟨Nl, hNl⟩ :=
    eventually_atTop.mp (hcompl_tendsto.eventually_lt_const hcompl_room)
  let upper : BoundedContinuousFunction E ℝ := upperSeq Nu
  let lower : BoundedContinuousFunction E ℝ :=
    BoundedContinuousFunction.const E (1 : ℝ) - complSeq Nl
  have hupper_lt :
      ∫ x, upper x ∂law < law.real (closure A) + ε / 4 := by
    exact hNu Nu le_rfl
  have hcompl_lt :
      ∫ x, complSeq Nl x ∂law < law.real ((interior A)ᶜ) + ε / 4 := by
    exact hNl Nl le_rfl
  have hclosure_real : law.real (closure A) = law.real A := by
    simp [Measure.real_def, measure_closure_of_null_frontier hfrontier]
  have hinterior_real : law.real (interior A) = law.real A := by
    simp [Measure.real_def, measure_interior_of_null_frontier hfrontier]
  have hclosure_interior : law.real (closure A) = law.real (interior A) := by
    rw [hclosure_real, hinterior_real]
  have hcompl_real : law.real ((interior A)ᶜ) = 1 - law.real (interior A) := by
    rw [measureReal_compl isOpen_interior.measurableSet]
    simp
  have hlower_eq :
      ∫ x, lower x ∂law = 1 - ∫ x, complSeq Nl x ∂law := by
    calc
      ∫ x, lower x ∂law =
          law.real Set.univ • (1 : ℝ) - ∫ x, complSeq Nl x ∂law := by
            simpa [lower] using
              (BoundedContinuousFunction.integral_const_sub
                (μ := law) (complSeq Nl) (1 : ℝ))
      _ = 1 - ∫ x, complSeq Nl x ∂law := by simp
  have hlower_gt :
      law.real (interior A) - ε / 4 < ∫ x, lower x ∂law := by
    rw [hlower_eq]
    rw [hcompl_real] at hcompl_lt
    linarith
  refine ⟨lower, upper, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hnonneg : 0 ≤ complSeq Nl x := by
      simp [complSeq, nnrealBoundedContinuousFunctionToReal_apply]
    change 1 - complSeq Nl x ≤ (1 : ℝ)
    linarith
  · intro x hx
    have hxcomp : x ∈ (interior A)ᶜ := by
      exact fun hxi => hx (interior_subset hxi)
    have hone :
        thickenedIndicator (hδs_pos Nl) (interior A)ᶜ x = (1 : NNReal) :=
      thickenedIndicator_one_of_mem_closure (hδs_pos Nl) (interior A)ᶜ
        (subset_closure hxcomp)
    have hcompl_one : complSeq Nl x = (1 : ℝ) := by
      simp [complSeq, nnrealBoundedContinuousFunctionToReal_apply, hone]
    change 1 - complSeq Nl x ≤ (0 : ℝ)
    linarith
  · intro x hx
    have hxcl : x ∈ closure A := subset_closure hx
    have hone :
        thickenedIndicator (hδs_pos Nu) (closure A) x = (1 : NNReal) :=
      thickenedIndicator_one_of_mem_closure (hδs_pos Nu) (closure A)
        (by simpa [closure_closure] using hxcl)
    have hupper_one : upper x = (1 : ℝ) := by
      simp [upper, upperSeq, nnrealBoundedContinuousFunctionToReal_apply, hone]
    linarith
  · intro x
    simp [upper, upperSeq, nnrealBoundedContinuousFunctionToReal_apply]
  · have hlower_le_interior_indicator :
        (fun x => lower x) ≤ fun x => if x ∈ interior A then (1 : ℝ) else 0 := by
      intro x
      by_cases hx : x ∈ interior A
      · have hnonneg : 0 ≤ complSeq Nl x := by
          simp [complSeq, nnrealBoundedContinuousFunctionToReal_apply]
        simp [lower, hx, hnonneg]
      · have hxcomp : x ∈ (interior A)ᶜ := by
          exact hx
        have hone :
            thickenedIndicator (hδs_pos Nl) (interior A)ᶜ x = (1 : NNReal) :=
          thickenedIndicator_one_of_mem_closure (hδs_pos Nl) (interior A)ᶜ
            (subset_closure hxcomp)
        simp [lower, complSeq, nnrealBoundedContinuousFunctionToReal_apply, hx, hone]
    calc
      ∫ x, lower x ∂law
          ≤ ∫ x, (if x ∈ interior A then (1 : ℝ) else 0) ∂law := by
            refine integral_mono (lower.integrable law)
              ((integrable_indicator_iff isOpen_interior.measurableSet).mpr
                (integrable_const (1 : ℝ)).integrableOn) ?_
            exact hlower_le_interior_indicator
      _ = law.real (interior A) := by
            rw [← integral_indicator_one isOpen_interior.measurableSet]
            rfl
      _ = law.real A := hinterior_real
  · have hclosure_indicator_le_upper :
        (fun x => if x ∈ closure A then (1 : ℝ) else 0) ≤ fun x => upper x := by
      intro x
      by_cases hx : x ∈ closure A
      · have hone :
            thickenedIndicator (hδs_pos Nu) (closure A) x = (1 : NNReal) :=
          thickenedIndicator_one_of_mem_closure (hδs_pos Nu) (closure A)
            (by simpa [closure_closure] using hx)
        simp [upper, upperSeq, nnrealBoundedContinuousFunctionToReal_apply, hx, hone]
      · have hnonneg : 0 ≤ upper x := by
          simp [upper, upperSeq, nnrealBoundedContinuousFunctionToReal_apply]
        simp [hx, hnonneg]
    calc
      law.real A = law.real (closure A) := hclosure_real.symm
      _ = ∫ x, (if x ∈ closure A then (1 : ℝ) else 0) ∂law := by
            rw [← integral_indicator_one isClosed_closure.measurableSet]
            rfl
      _ ≤ ∫ x, upper x ∂law := by
            refine integral_mono
              ((integrable_indicator_iff isClosed_closure.measurableSet).mpr
                (integrable_const (1 : ℝ)).integrableOn)
              (upper.integrable law) ?_
            exact hclosure_indicator_le_upper
  · have hgap_lt :
        (∫ x, upper x ∂law) - (∫ x, lower x ∂law) < ε := by
      have hupper_lt' : ∫ x, upper x ∂law <
          law.real (interior A) + ε / 4 := by
        simpa [hclosure_interior] using hupper_lt
      linarith
    exact le_of_lt hgap_lt

private theorem integrable_boundedContinuous_comp_measurable
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {P : Measure Ωs} [IsFiniteMeasure P] {Z : Ωs → E}
    (hZ : Measurable Z) (f : BoundedContinuousFunction E ℝ) :
    Integrable (fun ωs => f (Z ωs)) P := by
  refine Integrable.of_bound
    ((f.continuous.measurable.comp hZ).aestronglyMeasurable) ‖f‖ ?_
  exact ae_of_all P fun ωs => f.norm_coe_le_norm (Z ωs)

/-- Pointwise bounded-continuous event sandwiches integrate to probability
sandwiches after composing with a measurable statistic.

This is the measure-theoretic bridge from an event-indicator approximation
`lower <= 1_A <= upper` to the integral inequalities used by the bootstrap
Portmanteau wrapper. -/
theorem boundedContinuous_event_integral_sandwich
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {P : Measure Ωs} [IsFiniteMeasure P] {Z : Ωs → E} {A : Set E}
    (hZ : Measurable Z) (hA : MeasurableSet A)
    {lower upper : BoundedContinuousFunction E ℝ}
    (hl_mem : ∀ x, x ∈ A → lower x ≤ 1)
    (hl_notMem : ∀ x, x ∉ A → lower x ≤ 0)
    (hu_mem : ∀ x, x ∈ A → 1 ≤ upper x)
    (hu_nonneg : ∀ x, 0 ≤ upper x) :
    (∫ ωs, lower (Z ωs) ∂P) ≤ P.real {ωs | Z ωs ∈ A} ∧
      P.real {ωs | Z ωs ∈ A} ≤ (∫ ωs, upper (Z ωs) ∂P) := by
  classical
  let S : Set Ωs := {ωs | Z ωs ∈ A}
  have hS : MeasurableSet S := hA.preimage hZ
  have hlower_int : Integrable (fun ωs => lower (Z ωs)) P :=
    integrable_boundedContinuous_comp_measurable (P := P) hZ lower
  have hupper_int : Integrable (fun ωs => upper (Z ωs)) P :=
    integrable_boundedContinuous_comp_measurable (P := P) hZ upper
  have hindicator_int : Integrable (fun ωs => if ωs ∈ S then (1 : ℝ) else 0) P := by
    simpa [S] using
      ((integrable_indicator_iff hS).mpr
        (integrable_const (1 : ℝ)).integrableOn)
  constructor
  · have hlower_le_indicator :
        (fun ωs => lower (Z ωs)) ≤
          fun ωs => if ωs ∈ S then (1 : ℝ) else 0 := by
      intro ωs
      by_cases hωs : Z ωs ∈ A
      · simpa [S, hωs] using hl_mem (Z ωs) hωs
      · simpa [S, hωs] using hl_notMem (Z ωs) hωs
    calc
      ∫ ωs, lower (Z ωs) ∂P
          ≤ ∫ ωs, (if ωs ∈ S then (1 : ℝ) else 0) ∂P :=
            integral_mono hlower_int hindicator_int hlower_le_indicator
      _ = P.real S := by
            rw [← integral_indicator_one hS]
            rfl
      _ = P.real {ωs | Z ωs ∈ A} := rfl
  · have hindicator_le_upper :
        (fun ωs => if ωs ∈ S then (1 : ℝ) else 0) ≤
          fun ωs => upper (Z ωs) := by
      intro ωs
      by_cases hωs : Z ωs ∈ A
      · simpa [S, hωs] using hu_mem (Z ωs) hωs
      · simpa [S, hωs] using hu_nonneg (Z ωs)
    calc
      P.real {ωs | Z ωs ∈ A} = P.real S := rfl
      _ = ∫ ωs, (if ωs ∈ S then (1 : ℝ) else 0) ∂P := by
            rw [← integral_indicator_one hS]
            rfl
      _ ≤ ∫ ωs, upper (Z ωs) ∂P :=
            integral_mono hindicator_int hupper_int hindicator_le_upper

/-- Conditional-bootstrap event probability sandwich from pointwise
bounded-continuous lower and upper functions.

This packages `boundedContinuous_event_integral_sandwich` in the `n, ω`
conditional-bootstrap notation required by
`TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_boundedContinuous_sandwich`. -/
theorem bootstrapEventProbability_sandwich_of_boundedContinuous_event_sandwich
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → E} {A : Set E}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hA : MeasurableSet A)
    {lower upper : BoundedContinuousFunction E ℝ}
    (hl_mem : ∀ x, x ∈ A → lower x ≤ 1)
    (hl_notMem : ∀ x, x ∉ A → lower x ≤ 0)
    (hu_mem : ∀ x, x ∈ A → 1 ≤ upper x)
    (hu_nonneg : ∀ x, 0 ≤ upper x) :
    (∀ n ω,
      bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤
        bootstrapEventProbability Pstar Zstar A n ω) ∧
      (∀ n ω,
        bootstrapEventProbability Pstar Zstar A n ω ≤
          bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω) := by
  constructor
  · intro n ω
    letI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    simpa [bootstrapBoundedContinuousIntegral, bootstrapEventProbability,
      Measure.real_def] using
      (boundedContinuous_event_integral_sandwich
        (P := Pstar n ω) (Z := Zstar n ω) (A := A)
        (hZstar n ω) hA hl_mem hl_notMem hu_mem hu_nonneg).1
  · intro n ω
    letI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    simpa [bootstrapBoundedContinuousIntegral, bootstrapEventProbability,
      Measure.real_def] using
        (boundedContinuous_event_integral_sandwich
          (P := Pstar n ω) (Z := Zstar n ω) (A := A)
          (hZstar n ω) hA hl_mem hl_notMem hu_mem hu_nonneg).2

/-- Indexed conditional-bootstrap event probability sandwich from pointwise
bounded-continuous lower and upper functions. -/
theorem bootstrapEventProbabilityIndexed_sandwich_of_boundedContinuous_event_sandwich
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E} {A : Set E}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hA : MeasurableSet A)
    {lower upper : BoundedContinuousFunction E ℝ}
    (hl_mem : ∀ x, x ∈ A → lower x ≤ 1)
    (hl_notMem : ∀ x, x ∉ A → lower x ≤ 0)
    (hu_mem : ∀ x, x ∈ A → 1 ≤ upper x)
    (hu_nonneg : ∀ x, 0 ≤ upper x) :
    (∀ n ω,
      bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤
        bootstrapEventProbabilityIndexed Pstar Zstar A n ω) ∧
      (∀ n ω,
        bootstrapEventProbabilityIndexed Pstar Zstar A n ω ≤
          bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω) := by
  constructor
  · intro n ω
    letI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    simpa [bootstrapBoundedContinuousIntegralIndexed,
      bootstrapEventProbabilityIndexed, Measure.real_def] using
      (boundedContinuous_event_integral_sandwich
        (P := Pstar n ω) (Z := Zstar n ω) (A := A)
        (hZstar n ω) hA hl_mem hl_notMem hu_mem hu_nonneg).1
  · intro n ω
    letI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    simpa [bootstrapBoundedContinuousIntegralIndexed,
      bootstrapEventProbabilityIndexed, Measure.real_def] using
      (boundedContinuous_event_integral_sandwich
        (P := Pstar n ω) (Z := Zstar n ω) (A := A)
        (hZstar n ω) hA hl_mem hl_notMem hu_mem hu_nonneg).2

/-- Bootstrap weak convergence gives event-probability convergence for events
whose limit-law frontier has zero mass.

This combines the bounded-continuous-test-function bootstrap convergence
definition, the null-frontier event-sandwich constructor, and the conditional
bootstrap integral sandwich. -/
theorem TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_null_frontier
    [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → E} {A : Set E}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZ : AEMeasurable Z ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map Z) (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar Zstar A)
      atTop (fun _ => (ν.map Z).real A) := by
  letI : IsProbabilityMeasure (ν.map Z) := Measure.isProbabilityMeasure_map hZ
  refine hweak.event_probability_tendsto_of_boundedContinuous_sandwich ?_
  intro ε hε
  obtain ⟨lower, upper, hl_mem, hl_notMem, hu_mem, hu_nonneg,
      hlower_law, hupper_law, hgap_law⟩ :=
    boundedContinuous_event_sandwich_of_null_frontier
      (law := ν.map Z) (A := A) hε hfrontier
  have hlower_map :
      ∫ x, lower x ∂(ν.map Z) = ∫ ωlim, lower (Z ωlim) ∂ν :=
    integral_map hZ lower.continuous.measurable.aestronglyMeasurable
  have hupper_map :
      ∫ x, upper x ∂(ν.map Z) = ∫ ωlim, upper (Z ωlim) ∂ν :=
    integral_map hZ upper.continuous.measurable.aestronglyMeasurable
  obtain ⟨hlower_boot, hupper_boot⟩ :=
    bootstrapEventProbability_sandwich_of_boundedContinuous_event_sandwich
      (Pstar := Pstar) (Zstar := Zstar) (A := A)
      hPstar hZstar hA hl_mem hl_notMem hu_mem hu_nonneg
  refine ⟨lower, upper, ?_, ?_, ?_, hlower_boot, hupper_boot⟩
  · simpa [hlower_map] using hlower_law
  · simpa [hupper_map] using hupper_law
  · simpa [hlower_map, hupper_map] using hgap_law

/-- Indexed bootstrap weak convergence gives event-probability convergence for
events whose limit-law frontier has zero mass. -/
theorem TendstoInBootstrapWeakDistributionIndexed.event_probability_tendsto_of_null_frontier
    [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → E} {A : Set E}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZ : AEMeasurable Z ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map Z) (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar Zstar A)
      atTop (fun _ => (ν.map Z).real A) := by
  letI : IsProbabilityMeasure (ν.map Z) := Measure.isProbabilityMeasure_map hZ
  refine hweak.event_probability_tendsto_of_sandwich ?_
  intro ε hε
  obtain ⟨lower, upper, hl_mem, hl_notMem, hu_mem, hu_nonneg,
      hlower_law, hupper_law, hgap_law⟩ :=
    boundedContinuous_event_sandwich_of_null_frontier
      (law := ν.map Z) (A := A) hε hfrontier
  have hlower_map :
      ∫ x, lower x ∂(ν.map Z) = ∫ ωlim, lower (Z ωlim) ∂ν :=
    integral_map hZ lower.continuous.measurable.aestronglyMeasurable
  have hupper_map :
      ∫ x, upper x ∂(ν.map Z) = ∫ ωlim, upper (Z ωlim) ∂ν :=
    integral_map hZ upper.continuous.measurable.aestronglyMeasurable
  obtain ⟨hlower_boot, hupper_boot⟩ :=
    bootstrapEventProbabilityIndexed_sandwich_of_boundedContinuous_event_sandwich
      (Pstar := Pstar) (Zstar := Zstar) (A := A)
      hPstar hZstar hA hl_mem hl_notMem hu_mem hu_nonneg
  refine ⟨lower, upper, ?_, ?_, ?_, hlower_boot, hupper_boot⟩
  · simpa [hlower_map] using hlower_law
  · simpa [hupper_map] using hupper_law
  · simpa [hlower_map, hupper_map] using hgap_law

/-- Bootstrap weak convergence plus a bounded-continuous integral
linearization gives event-probability convergence for null-frontier events.

This is the event-probability face of the nonlinear Delta-method transfer:
one first proves a weak limit for the linearized statistic, then checks that
the nonlinear statistic has the same conditional bounded-continuous integrals
up to `oₚ(1)`. -/
theorem TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_integral_diff
    [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar Zstar' : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → E} {A : Set E}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hdiff :
      ∀ f : BoundedContinuousFunction E ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegral Pstar Zstar' f n ω -
              bootstrapBoundedContinuousIntegral Pstar Zstar f n ω)
          atTop (fun _ => 0))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZ : AEMeasurable Z ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map Z) (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar Zstar' A)
      atTop (fun _ => (ν.map Z).real A) := by
  exact (hweak.of_integral_difference_zero hdiff).event_probability_tendsto_of_null_frontier
    hPstar hZstar' hZ hA hfrontier

/-- Indexed bootstrap weak convergence plus a bounded-continuous integral
linearization gives event-probability convergence for null-frontier events. -/
theorem TendstoInBootstrapWeakDistributionIndexed.event_probability_tendsto_of_integral_diff
    [PseudoEMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → E} {A : Set E}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hdiff :
      ∀ f : BoundedContinuousFunction E ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
          atTop (fun _ => 0))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZ : AEMeasurable Z ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map Z) (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar Zstar' A)
      atTop (fun _ => (ν.map Z).real A) := by
  exact (hweak.of_integral_difference_zero hdiff).event_probability_tendsto_of_null_frontier
    hPstar hZstar' hZ hA hfrontier

/-- Coordinate lower orthants are closed in product space. -/
theorem isClosed_coordinateLE (x : k → ℝ) :
    IsClosed {z : k → ℝ | coordinateLE z x} := by
  rw [show {z : k → ℝ | coordinateLE z x} =
      ⋂ i : k, {z : k → ℝ | z i ≤ x i} by
    ext z
    simp [coordinateLE]]
  exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const

/-- Coordinate lower orthants are measurable. -/
theorem measurableSet_coordinateLE
    [MeasurableSpace (k → ℝ)] [OpensMeasurableSpace (k → ℝ)] (x : k → ℝ) :
    MeasurableSet {z : k → ℝ | coordinateLE z x} :=
  (isClosed_coordinateLE x).measurableSet

/-- The frontier of a finite-dimensional coordinate lower orthant is contained
in the finite union of its coordinate hyperplanes. -/
theorem frontier_coordinateLE_subset_iUnion_coord_eq [Finite k] (x : k → ℝ) :
    frontier {z : k → ℝ | coordinateLE z x} ⊆
      ⋃ i : k, {z : k → ℝ | z i = x i} := by
  intro z hz
  have hz_lower : z ∈ {z : k → ℝ | coordinateLE z x} :=
    (isClosed_coordinateLE x).frontier_subset hz
  by_contra hnot
  have hstrict : ∀ i : k, z i < x i := by
    intro i
    have hne : z i ≠ x i := by
      intro hi
      exact hnot (Set.mem_iUnion.mpr ⟨i, by simp [hi]⟩)
    exact lt_of_le_of_ne (hz_lower i) hne
  have hopen :
      IsOpen {z : k → ℝ | ∀ i : k, z i < x i} := by
    rw [show {z : k → ℝ | ∀ i : k, z i < x i} =
        ⋂ i : k, {z : k → ℝ | z i < x i} by
      ext y
      simp]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (continuous_apply i) continuous_const
  have hsubset :
      {z : k → ℝ | ∀ i : k, z i < x i} ⊆
        {z : k → ℝ | coordinateLE z x} := by
    intro y hy i
    exact (hy i).le
  have hz_interior : z ∈ interior {z : k → ℝ | coordinateLE z x} :=
    interior_maximal hsubset hopen hstrict
  exact ((mem_frontier_iff_notMem_interior hz_lower).mp hz) hz_interior

/-- A coordinate lower-orthant frontier is null when every coordinate
hyperplane at the cutoff is null. -/
theorem measure_frontier_coordinateLE_eq_zero_of_coord_singletons [Finite k]
    {law : Measure (k → ℝ)} (x : k → ℝ)
    (hcoord : ∀ i : k, law {z : k → ℝ | z i = x i} = 0) :
    law (frontier {z : k → ℝ | coordinateLE z x}) = 0 := by
  refine measure_mono_null (frontier_coordinateLE_subset_iUnion_coord_eq x) ?_
  exact measure_iUnion_null hcoord

/-- Mapped lower-orthant frontiers are null when each transformed coordinate
has zero mass at the cutoff. -/
theorem map_measure_frontier_coordinateLE_eq_zero_of_coord_singletons [Finite k]
    {ν : Measure Ωlim} {Z : Ωlim → k → ℝ} (hZ : AEMeasurable Z ν)
    (x : k → ℝ) (hcoord : ∀ i : k, ν {ωlim | Z ωlim i = x i} = 0) :
    (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0 := by
  refine measure_frontier_coordinateLE_eq_zero_of_coord_singletons x ?_
  intro i
  have hhyperplane :
      MeasurableSet {z : k → ℝ | z i = x i} :=
    (isClosed_eq (continuous_apply i) continuous_const).measurableSet
  rw [Measure.map_apply_of_aemeasurable hZ hhyperplane]
  simpa using hcoord i

/-- Positive definite multivariate Gaussian laws assign zero mass to coordinate
lower-orthant frontiers.

This discharges the null-frontier premise in the Gaussian finite-dimensional
faces of Hansen Theorems 10.4, 10.6, and 10.7 when the covariance matrix is
positive definite. -/
theorem multivariateGaussian_coordinateLE_frontier_null_of_posDef
    [Fintype k] [DecidableEq k] {S : Matrix k k ℝ}
    (hS : S.PosDef) (x : k → ℝ) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
      (frontier {z : k → ℝ | coordinateLE z x}) = 0 := by
  have hcoord_aemeas :
      AEMeasurable (fun z : EuclideanSpace ℝ k => (z : k → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S) :=
    (PiLp.continuous_ofLp 2 (fun _ : k => ℝ)).aemeasurable
  refine map_measure_frontier_coordinateLE_eq_zero_of_coord_singletons
    (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) S)
    (Z := fun z : EuclideanSpace ℝ k => (z : k → ℝ))
    hcoord_aemeas x ?_
  intro i
  have hvar_pos : 0 < S i i := hS.diag_pos
  have hvar_ne : (S i i).toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hvar_pos)
  haveI : NoAtoms (gaussianReal 0 (S i i).toNNReal) :=
    noAtoms_gaussianReal hvar_ne
  have hLaw :
      HasLaw (fun z : EuclideanSpace ℝ k => z.ofLp i)
        (gaussianReal 0 (S i i).toNNReal)
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S) := by
    simpa using
      (multivariateGaussian_eval_hasLaw
        (μ := (0 : EuclideanSpace ℝ k)) (S := S) hS.posSemidef (i := i))
  have hpre :=
    HasLaw.preimage_eq (μ := multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      hLaw (measurableSet_singleton (x i))
  calc
    (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
        {z : EuclideanSpace ℝ k | (z : k → ℝ) i = x i}
        =
          (gaussianReal 0 (S i i).toNNReal) {x i} := by
            simpa using hpre
    _ = 0 := measure_singleton (x i)

/-- Weak bootstrap convergence gives conditional-CDF convergence at a
lower-orthant null-frontier point.

This is the bridge from the bounded-continuous-test-function API back to
Hansen Definition 10.2's coordinate-CDF surface. -/
theorem TendstoInBootstrapWeakDistribution.bootstrapVectorCDF_tendsto_of_null_frontier
    [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZ : AEMeasurable Z ν) {x : k → ℝ}
    (hfrontier : (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInMeasure μ (fun n ω => bootstrapVectorCDF Pstar Zstar x n ω)
      atTop (fun _ => vectorCDF ν Z x) := by
  letI : Fintype k := Fintype.ofFinite k
  let A : Set (k → ℝ) := {z | coordinateLE z x}
  have hA : MeasurableSet A := measurableSet_coordinateLE x
  have hevent :
      TendstoInMeasure μ (bootstrapEventProbability Pstar Zstar A)
        atTop (fun _ => (ν.map Z).real A) :=
    hweak.event_probability_tendsto_of_null_frontier hPstar hZstar hZ hA hfrontier
  simpa [bootstrapVectorCDF, bootstrapEventProbability, vectorCDF, A, Measure.real_def,
    Measure.map_apply_of_aemeasurable hZ hA] using hevent

/-- Indexed weak bootstrap convergence gives conditional-CDF convergence at a
lower-orthant null-frontier point. -/
theorem TendstoInBootstrapWeakDistributionIndexed.bootstrapVectorCDF_tendsto_of_null_frontier
    [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZ : AEMeasurable Z ν) {x : k → ℝ}
    (hfrontier : (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInMeasure μ (fun n ω => bootstrapVectorCDFIndexed Pstar Zstar x n ω)
      atTop (fun _ => vectorCDF ν Z x) := by
  letI : Fintype k := Fintype.ofFinite k
  let A : Set (k → ℝ) := {z | coordinateLE z x}
  have hA : MeasurableSet A := measurableSet_coordinateLE x
  have hevent :
      TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar Zstar A)
        atTop (fun _ => (ν.map Z).real A) :=
    hweak.event_probability_tendsto_of_null_frontier hPstar hZstar hZ hA hfrontier
  simpa [bootstrapVectorCDFIndexed, bootstrapEventProbabilityIndexed, vectorCDF, A,
    Measure.real_def, Measure.map_apply_of_aemeasurable hZ hA] using hevent

/-- Bootstrap weak convergence plus a bounded-continuous integral
linearization gives Hansen coordinate-CDF convergence at lower-orthant
null-frontier points. -/
theorem TendstoInBootstrapWeakDistribution.bootstrapVectorCDF_tendsto_of_integral_diff
    [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hdiff :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegral Pstar Zstar' f n ω -
              bootstrapBoundedContinuousIntegral Pstar Zstar f n ω)
          atTop (fun _ => 0))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZ : AEMeasurable Z ν) {x : k → ℝ}
    (hfrontier : (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInMeasure μ (fun n ω => bootstrapVectorCDF Pstar Zstar' x n ω)
      atTop (fun _ => vectorCDF ν Z x) := by
  exact (hweak.of_integral_difference_zero hdiff).bootstrapVectorCDF_tendsto_of_null_frontier
    hPstar hZstar' hZ hfrontier

/-- Indexed bootstrap weak convergence plus a bounded-continuous integral
linearization gives Hansen coordinate-CDF convergence at lower-orthant
null-frontier points. -/
theorem TendstoInBootstrapWeakDistributionIndexed.bootstrapVectorCDF_tendsto_of_integral_diff
    [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hdiff :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
          atTop (fun _ => 0))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZ : AEMeasurable Z ν) {x : k → ℝ}
    (hfrontier : (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInMeasure μ (fun n ω => bootstrapVectorCDFIndexed Pstar Zstar' x n ω)
      atTop (fun _ => vectorCDF ν Z x) := by
  exact (hweak.of_integral_difference_zero hdiff).bootstrapVectorCDF_tendsto_of_null_frontier
    hPstar hZstar' hZ hfrontier

/-- Weak bootstrap convergence implies Hansen's coordinate-CDF bootstrap
distribution convergence when every relevant lower orthant has null frontier
under the limiting law.

The null-frontier premise is stated only at continuity points of the limiting
CDF, matching Hansen Definition 10.2. -/
theorem TendstoInBootstrapDistribution.of_weakDistribution_null_frontiers
    [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZ : AEMeasurable Z ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y => vectorCDF ν Z y) x →
        (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar Zstar ν Z := by
  letI : Fintype k := Fintype.ofFinite k
  intro x hx
  exact hweak.bootstrapVectorCDF_tendsto_of_null_frontier
    hPstar hZstar hZ (hfrontier x hx)

/-- Indexed weak bootstrap convergence implies indexed Hansen coordinate-CDF
bootstrap distribution convergence when every relevant lower orthant has null
frontier under the limiting law. -/
theorem TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers
    [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZ : AEMeasurable Z ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y => vectorCDF ν Z y) x →
        (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar ν Z := by
  letI : Fintype k := Fintype.ofFinite k
  intro x hx
  exact hweak.bootstrapVectorCDF_tendsto_of_null_frontier
    hPstar hZstar hZ (hfrontier x hx)

/-- Hansen Theorem 10.4, Gaussian bootstrap CLT from weak bootstrap
convergence.

If a normalized bootstrap statistic converges weakly, in the
bounded-continuous-test-function bootstrap sense, to `N(0, S)`, then the
coordinate-CDF version of Hansen Definition 10.2 follows at all continuity
points whose lower-orthant frontiers are null under that Gaussian law. -/
theorem chapter10_bootstrap_clt_gaussian_of_weakDistribution
    [Fintype k] [DecidableEq k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {S : Matrix k k ℝ}
    (hweak :
      TendstoInBootstrapWeakDistribution μ Pstar Zstar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  have hZlim :
      AEMeasurable (fun z : EuclideanSpace ℝ k => (z : k → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S) :=
    (PiLp.continuous_ofLp 2 (fun _ : k => ℝ)).aemeasurable
  exact
    TendstoInBootstrapDistribution.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (Z := fun z : EuclideanSpace ℝ k => (z : k → ℝ))
      hweak hPstar hZstar hZlim hfrontier

/-- Hansen Theorem 10.4 Gaussian bootstrap CLT from weak bootstrap convergence
with positive definite covariance.

This is the theorem-facing finite-dimensional route: positive definiteness of
`Σ` makes every Gaussian lower-orthant frontier null, so a bounded-continuous
bootstrap weak limit to `N(0,Σ)` directly yields Hansen Definition 10.2. -/
theorem chapter10_bootstrap_clt_gaussian_of_weakDistribution_posDef
    [Fintype k] [DecidableEq k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hweak :
      TendstoInBootstrapWeakDistribution μ Pstar Zstar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω)) :
    TendstoInBootstrapDistribution μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_bootstrap_clt_gaussian_of_weakDistribution
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (S := S)
    hweak hPstar hZstar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Indexed-space Hansen Theorem 10.4 Gaussian bootstrap CLT from weak
bootstrap convergence. -/
theorem chapter10_indexed_bootstrap_clt_gaussian_of_weakDistribution
    [Fintype k] [DecidableEq k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {S : Matrix k k ℝ}
    (hweak :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ k) S).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  have hZlim :
      AEMeasurable (fun z : EuclideanSpace ℝ k => (z : k → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S) :=
    (PiLp.continuous_ofLp 2 (fun _ : k => ℝ)).aemeasurable
  exact
    TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (Z := fun z : EuclideanSpace ℝ k => (z : k → ℝ))
      hweak hPstar hZstar hZlim hfrontier

/-- Indexed-space Hansen Theorem 10.4 Gaussian bootstrap CLT from weak bootstrap
convergence with positive definite covariance. -/
theorem chapter10_indexed_bootstrap_clt_gaussian_of_weakDistribution_posDef
    [Fintype k] [DecidableEq k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {S : Matrix k k ℝ}
    (hS : S.PosDef)
    (hweak :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
        (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω)) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_of_weakDistribution
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (S := S)
    hweak hPstar hZstar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Weak bootstrap convergence plus bounded-continuous integral
linearization implies Hansen's coordinate-CDF bootstrap distribution
convergence when the limiting lower orthants have null frontiers. -/
theorem TendstoInBootstrapDistribution.of_weakDistribution_integral_diff
    [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar Zstar' : ℕ → Ω → Ωs → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hdiff :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegral Pstar Zstar' f n ω -
              bootstrapBoundedContinuousIntegral Pstar Zstar f n ω)
          atTop (fun _ => 0))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZ : AEMeasurable Z ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y => vectorCDF ν Z y) x →
        (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar Zstar' ν Z := by
  letI : Fintype k := Fintype.ofFinite k
  intro x hx
  exact hweak.bootstrapVectorCDF_tendsto_of_integral_diff
    hdiff hPstar hZstar' hZ (hfrontier x hx)

/-- Indexed weak bootstrap convergence plus bounded-continuous integral
linearization implies indexed Hansen coordinate-CDF bootstrap distribution
convergence when the limiting lower orthants have null frontiers. -/
theorem TendstoInBootstrapDistributionIndexed.of_weakDistribution_integral_diff
    [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar Zstar' : ∀ n, Ω → Ωboot n → k → ℝ}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν] {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hdiff :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegralIndexed Pstar Zstar' f n ω -
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω)
          atTop (fun _ => 0))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar' : ∀ n ω, Measurable (Zstar' n ω))
    (hZ : AEMeasurable Z ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y => vectorCDF ν Z y) x →
        (ν.map Z) (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar Zstar' ν Z := by
  letI : Fintype k := Fintype.ofFinite k
  intro x hx
  exact hweak.bootstrapVectorCDF_tendsto_of_integral_diff
    hdiff hPstar hZstar' hZ (hfrontier x hx)

/-- Clipped first moments converge under bootstrap weak convergence.

This is the bounded-continuous core of the Theorem 10.9
distribution-to-moment argument; the remaining UI/tail step removes the
clipping. -/
theorem TendstoInBootstrapWeakDistribution.integral_realClip_tendsto
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    {R : ℝ} (hR : 0 ≤ R) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
      atTop
      (fun _ => ∫ ωlim, realClip R (Z ωlim) ∂ν) := by
  simpa [bootstrapBoundedContinuousIntegral, realClipBoundedContinuousFunction_apply]
    using hZ (realClipBoundedContinuousFunction R hR)

/-- Indexed clipped first moments converge under indexed bootstrap weak
convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.integral_realClip_tendsto
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    {R : ℝ} (hR : 0 ≤ R) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
      atTop
      (fun _ => ∫ ωlim, realClip R (Z ωlim) ∂ν) := by
  simpa [bootstrapBoundedContinuousIntegralIndexed, realClipBoundedContinuousFunction_apply]
    using hZ (realClipBoundedContinuousFunction R hR)

/-- Clipped second moments converge under bootstrap weak convergence.

This is the bounded-continuous core used before the UI/tail argument upgrades
clipped second moments to the full conditional second moments in Hansen
Theorem 10.9. -/
theorem TendstoInBootstrapWeakDistribution.integral_realClip_sq_tendsto
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    {R : ℝ} (hR : 0 ≤ R) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
      atTop
      (fun _ => ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν) := by
  simpa [bootstrapBoundedContinuousIntegral, realClipBoundedContinuousFunction_apply]
    using hZ ((realClipBoundedContinuousFunction R hR) ^ (2 : ℕ))

/-- Indexed clipped second moments converge under indexed bootstrap weak
convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.integral_realClip_sq_tendsto
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    {R : ℝ} (hR : 0 ≤ R) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
      atTop
      (fun _ => ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν) := by
  simpa [bootstrapBoundedContinuousIntegralIndexed, realClipBoundedContinuousFunction_apply]
    using hZ ((realClipBoundedContinuousFunction R hR) ^ (2 : ℕ))

private theorem tendstoInMeasure_of_approx_limits_real
    {X : ℕ → Ω → ℝ} {c : ℝ}
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ cε : ℝ, dist cε c ≤ ε ∧
          TendstoInMeasure μ X atTop (fun _ => cε)) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  obtain ⟨cε, hcε, hX⟩ := happrox (ε / 2) (by positivity)
  rw [tendstoInMeasure_iff_dist] at hX
  have htail := hX (ε / 2) (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => zero_le _) ?_
  intro n
  refine measure_mono ?_
  intro ω hω
  have hωdist : ε ≤ dist (X n ω) c := hω
  have hdist : dist (X n ω) c ≤ dist (X n ω) cε + dist cε c :=
    dist_triangle (X n ω) cε c
  have : ε / 2 ≤ dist (X n ω) cε := by
    linarith
  exact this

private theorem tendstoInMeasure_of_approx_limits_real_tailProb
    {X : ℕ → Ω → ℝ} {c : ℝ}
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ Y : ℕ → Ω → ℝ, ∃ y : ℝ,
          dist y c ≤ ε ∧
            TendstoInMeasure μ Y atTop (fun _ => y) ∧
            Tendsto (fun n => μ {ω | ε ≤ dist (X n ω - Y n ω) 0})
              atTop (𝓝 0)) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  obtain ⟨Y, y, hyc, hY, herr⟩ := happrox (ε / 3) (by positivity)
  rw [tendstoInMeasure_iff_dist] at hY
  have hYtail := hY (ε / 3) (by positivity)
  have hsum := herr.add hYtail
  have hsum0 :
      Tendsto
        (fun n =>
          μ {ω | ε / 3 ≤ dist (X n ω - Y n ω) 0} +
            μ {ω | ε / 3 ≤ dist (Y n ω) y})
        atTop (𝓝 0) := by
    simpa using hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum0
    (fun _ => zero_le _) ?_
  intro n
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_cases herr_big : ε / 3 ≤ dist (X n ω - Y n ω) 0
  · exact Or.inl herr_big
  · right
    by_contra hY_not
    have herr_small : dist (X n ω - Y n ω) 0 < ε / 3 := not_le.mp herr_big
    have hY_small : dist (Y n ω) y < ε / 3 := not_le.mp hY_not
    have htri :
        dist (X n ω) c ≤
          dist (X n ω - Y n ω) 0 + dist (Y n ω) y + dist y c := by
      have h1 := dist_triangle (X n ω) y c
      have h2 := dist_triangle (X n ω) (Y n ω) y
      have hxy : dist (X n ω) (Y n ω) = dist (X n ω - Y n ω) 0 := by
        simp [Real.dist_eq]
      linarith
    have hlt : dist (X n ω) c < ε := by linarith
    exact (not_le.mpr hlt) hω

/-- Bootstrap weak convergence plus clipping-tail control gives full first
moment convergence.

This is the UI/tail assembly step for Hansen Theorem 10.9's conditional first
moment premise. -/
theorem TendstoInBootstrapWeakDistribution.integral_tendsto_of_realClip_tails
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω)[Zstar n ω] -
            (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[Zstar n ω])
      atTop (fun _ => ∫ ωlim, Z ωlim ∂ν) := by
  refine tendstoInMeasure_of_approx_limits_real (μ := μ) ?_
  intro ε hε
  obtain ⟨R, hR, hlim, htail⟩ := hTail ε hε
  let clipMean : ℕ → Ω → ℝ :=
    fun n ω => (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]
  let clipLimit : ℝ := ∫ ωlim, realClip R (Z ωlim) ∂ν
  have hclip :
      TendstoInMeasure μ clipMean atTop (fun _ => clipLimit) := by
    simpa [clipMean, clipLimit] using
      hZ.integral_realClip_tendsto hR
  have hclip0 :
      TendstoInMeasure μ (fun n ω => clipMean n ω - clipLimit)
        atTop (fun _ => 0) :=
    TendstoInMeasure.sub_limit_zero_real hclip
  have hsum := TendstoInMeasure.add_zero_real htail hclip0
  have hmean0 :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω)[Zstar n ω] - clipLimit)
        atTop (fun _ => 0) := by
    refine hsum.congr_left (fun n => ae_of_all μ fun ω => ?_)
    dsimp [clipMean]
    ring
  have hmean :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[Zstar n ω])
        atTop (fun _ => clipLimit) :=
    TendstoInMeasure.of_sub_limit_zero_real hmean0
  exact ⟨clipLimit, by simpa [clipLimit, Real.dist_eq, abs_sub_comm] using hlim, hmean⟩

/-- Indexed bootstrap weak convergence plus clipping-tail control gives full
first moment convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.integral_tendsto_of_realClip_tails
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω)[Zstar n ω] -
            (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[Zstar n ω])
      atTop (fun _ => ∫ ωlim, Z ωlim ∂ν) := by
  refine tendstoInMeasure_of_approx_limits_real (μ := μ) ?_
  intro ε hε
  obtain ⟨R, hR, hlim, htail⟩ := hTail ε hε
  let clipMean : ℕ → Ω → ℝ :=
    fun n ω => (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]
  let clipLimit : ℝ := ∫ ωlim, realClip R (Z ωlim) ∂ν
  have hclip :
      TendstoInMeasure μ clipMean atTop (fun _ => clipLimit) := by
    simpa [clipMean, clipLimit] using
      hZ.integral_realClip_tendsto hR
  have hclip0 :
      TendstoInMeasure μ (fun n ω => clipMean n ω - clipLimit)
        atTop (fun _ => 0) :=
    TendstoInMeasure.sub_limit_zero_real hclip
  have hsum := TendstoInMeasure.add_zero_real htail hclip0
  have hmean0 :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω)[Zstar n ω] - clipLimit)
        atTop (fun _ => 0) := by
    refine hsum.congr_left (fun n => ae_of_all μ fun ω => ?_)
    dsimp [clipMean]
    ring
  have hmean :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[Zstar n ω])
        atTop (fun _ => clipLimit) :=
    TendstoInMeasure.of_sub_limit_zero_real hmean0
  exact ⟨clipLimit, by simpa [clipLimit, Real.dist_eq, abs_sub_comm] using hlim, hmean⟩

/-- Bootstrap weak convergence plus tail-small-in-probability control gives
full first moment convergence.

This is the probability-mode version of the UI/tail assembly used in Hansen
Theorem 10.9: the chosen clipping error only needs to be small in probability
at the approximation tolerance. -/
theorem TendstoInBootstrapWeakDistribution.integral_tendsto_of_realClip_tailProb
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              ((Pstar n ω)[Zstar n ω] -
                (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[Zstar n ω])
      atTop (fun _ => ∫ ωlim, Z ωlim ∂ν) := by
  refine tendstoInMeasure_of_approx_limits_real_tailProb (μ := μ) ?_
  intro ε hε
  obtain ⟨R, hR, hlim, htail⟩ := hTail ε hε
  let clipMean : ℕ → Ω → ℝ :=
    fun n ω => (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]
  let clipLimit : ℝ := ∫ ωlim, realClip R (Z ωlim) ∂ν
  refine ⟨clipMean, clipLimit, ?_, ?_, ?_⟩
  · simpa [clipLimit, Real.dist_eq, abs_sub_comm] using hlim
  · simpa [clipMean, clipLimit] using hZ.integral_realClip_tendsto hR
  · simpa [clipMean] using htail

/-- Indexed bootstrap weak convergence plus tail-small-in-probability control
gives full first moment convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.integral_tendsto_of_realClip_tailProb
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              ((Pstar n ω)[Zstar n ω] -
                (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[Zstar n ω])
      atTop (fun _ => ∫ ωlim, Z ωlim ∂ν) := by
  refine tendstoInMeasure_of_approx_limits_real_tailProb (μ := μ) ?_
  intro ε hε
  obtain ⟨R, hR, hlim, htail⟩ := hTail ε hε
  let clipMean : ℕ → Ω → ℝ :=
    fun n ω => (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]
  let clipLimit : ℝ := ∫ ωlim, realClip R (Z ωlim) ∂ν
  refine ⟨clipMean, clipLimit, ?_, ?_, ?_⟩
  · simpa [clipLimit, Real.dist_eq, abs_sub_comm] using hlim
  · simpa [clipMean, clipLimit] using hZ.integral_realClip_tendsto hR
  · simpa [clipMean] using htail

/-- Bootstrap weak convergence plus clipping-tail control gives full second
moment convergence.

This is the UI/tail assembly step for Hansen Theorem 10.9's conditional second
moment premise. -/
theorem TendstoInBootstrapWeakDistribution.integral_sq_tendsto_of_realClip_tails
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω)[(Zstar n ω) ^ 2] -
            (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[(Zstar n ω) ^ 2])
      atTop (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) := by
  refine tendstoInMeasure_of_approx_limits_real (μ := μ) ?_
  intro ε hε
  obtain ⟨R, hR, hlim, htail⟩ := hTail ε hε
  let clipSecond : ℕ → Ω → ℝ :=
    fun n ω => (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]
  let clipLimit : ℝ := ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν
  have hclip :
      TendstoInMeasure μ clipSecond atTop (fun _ => clipLimit) := by
    simpa [clipSecond, clipLimit] using
      hZ.integral_realClip_sq_tendsto hR
  have hclip0 :
      TendstoInMeasure μ (fun n ω => clipSecond n ω - clipLimit)
        atTop (fun _ => 0) :=
    TendstoInMeasure.sub_limit_zero_real hclip
  have hsum := TendstoInMeasure.add_zero_real htail hclip0
  have hsecond0 :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω)[(Zstar n ω) ^ 2] - clipLimit)
        atTop (fun _ => 0) := by
    refine hsum.congr_left (fun n => ae_of_all μ fun ω => ?_)
    dsimp [clipSecond]
    ring
  have hsecond :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[(Zstar n ω) ^ 2])
        atTop (fun _ => clipLimit) :=
    TendstoInMeasure.of_sub_limit_zero_real hsecond0
  exact ⟨clipLimit, by simpa [clipLimit, Real.dist_eq, abs_sub_comm] using hlim, hsecond⟩

/-- Indexed bootstrap weak convergence plus clipping-tail control gives full
second moment convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.integral_sq_tendsto_of_realClip_tails
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω)[(Zstar n ω) ^ 2] -
            (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[(Zstar n ω) ^ 2])
      atTop (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) := by
  refine tendstoInMeasure_of_approx_limits_real (μ := μ) ?_
  intro ε hε
  obtain ⟨R, hR, hlim, htail⟩ := hTail ε hε
  let clipSecond : ℕ → Ω → ℝ :=
    fun n ω => (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]
  let clipLimit : ℝ := ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν
  have hclip :
      TendstoInMeasure μ clipSecond atTop (fun _ => clipLimit) := by
    simpa [clipSecond, clipLimit] using
      hZ.integral_realClip_sq_tendsto hR
  have hclip0 :
      TendstoInMeasure μ (fun n ω => clipSecond n ω - clipLimit)
        atTop (fun _ => 0) :=
    TendstoInMeasure.sub_limit_zero_real hclip
  have hsum := TendstoInMeasure.add_zero_real htail hclip0
  have hsecond0 :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω)[(Zstar n ω) ^ 2] - clipLimit)
        atTop (fun _ => 0) := by
    refine hsum.congr_left (fun n => ae_of_all μ fun ω => ?_)
    dsimp [clipSecond]
    ring
  have hsecond :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[(Zstar n ω) ^ 2])
        atTop (fun _ => clipLimit) :=
    TendstoInMeasure.of_sub_limit_zero_real hsecond0
  exact ⟨clipLimit, by simpa [clipLimit, Real.dist_eq, abs_sub_comm] using hlim, hsecond⟩

/-- Bootstrap weak convergence plus tail-small-in-probability control gives
full second moment convergence.

This is the probability-mode version of the UI/tail assembly used in Hansen
Theorem 10.9: the chosen squared clipping error only needs to be small in
probability at the approximation tolerance. -/
theorem TendstoInBootstrapWeakDistribution.integral_sq_tendsto_of_realClip_tailProb
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              ((Pstar n ω)[(Zstar n ω) ^ 2] -
                (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[(Zstar n ω) ^ 2])
      atTop (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) := by
  refine tendstoInMeasure_of_approx_limits_real_tailProb (μ := μ) ?_
  intro ε hε
  obtain ⟨R, hR, hlim, htail⟩ := hTail ε hε
  let clipSecond : ℕ → Ω → ℝ :=
    fun n ω => (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]
  let clipLimit : ℝ := ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν
  refine ⟨clipSecond, clipLimit, ?_, ?_, ?_⟩
  · simpa [clipLimit, Real.dist_eq, abs_sub_comm] using hlim
  · simpa [clipSecond, clipLimit] using hZ.integral_realClip_sq_tendsto hR
  · simpa [clipSecond] using htail

/-- Indexed bootstrap weak convergence plus tail-small-in-probability control
gives full second moment convergence. -/
theorem TendstoInBootstrapWeakDistributionIndexed.integral_sq_tendsto_of_realClip_tailProb
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              ((Pstar n ω)[(Zstar n ω) ^ 2] -
                (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ
      (fun n ω => (Pstar n ω)[(Zstar n ω) ^ 2])
      atTop (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) := by
  refine tendstoInMeasure_of_approx_limits_real_tailProb (μ := μ) ?_
  intro ε hε
  obtain ⟨R, hR, hlim, htail⟩ := hTail ε hε
  let clipSecond : ℕ → Ω → ℝ :=
    fun n ω => (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]
  let clipLimit : ℝ := ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν
  refine ⟨clipSecond, clipLimit, ?_, ?_, ?_⟩
  · simpa [clipLimit, Real.dist_eq, abs_sub_comm] using hlim
  · simpa [clipSecond, clipLimit] using hZ.integral_realClip_sq_tendsto hR
  · simpa [clipSecond] using htail

/-- Hansen Theorem 10.5, globally continuous weak-convergence face.

If `Zₙ* ->d* Z` in bounded-continuous-test-function form and `g` is continuous,
then `g(Zₙ*) ->d* g(Z)`.  The more general textbook discontinuity-set-null
form is obtained by replacing the global-continuity premise with the
Portmanteau/ae-continuity bridge. -/
theorem chapter10_bootstrap_continuous_mapping_distribution
    [TopologicalSpace E] [TopologicalSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E} {g : E → F}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hg : Continuous g) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ω => g (Z ω)) := by
  intro f
  let gc : C(E, F) := ⟨g, hg⟩
  simpa [bootstrapBoundedContinuousIntegral, Function.comp_def] using
    hZ (f.compContinuous gc)

/-- Indexed Hansen Theorem 10.5, globally continuous weak-convergence face.

This is the sample-size-dependent counterpart of
`chapter10_bootstrap_continuous_mapping_distribution`. -/
theorem chapter10_indexed_bootstrap_continuous_mapping_distribution
    [TopologicalSpace E] [TopologicalSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E} {g : E → F}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hg : Continuous g) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ω => g (Z ω)) := by
  intro f
  let gc : C(E, F) := ⟨g, hg⟩
  simpa [bootstrapBoundedContinuousIntegralIndexed, Function.comp_def] using
    hZ (f.compContinuous gc)

/-- Hansen Theorem 10.5, globally continuous finite-dimensional CDF face.

After a continuous transformation into `k → ℝ`, the bounded-continuous
bootstrap CMT implies Hansen Definition 10.2 whenever the transformed limiting
lower orthants have null frontier at the relevant continuity points.  The
measurability premises are stated for the transformed statistics so this wrapper
can also be used when measurability is supplied by a model-specific layer. -/
theorem chapter10_bootstrap_continuous_mapping_distribution_of_null_frontiers
    [TopologicalSpace E] [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstarMapped : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZMapped : AEMeasurable (fun ωlim => g (Z ωlim)) ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  exact
    TendstoInBootstrapDistribution.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim))
        (chapter10_bootstrap_continuous_mapping_distribution
          (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
          (g := g) hZ hg)
        hPstar hZstarMapped hZMapped hfrontier

/-- Indexed Hansen Theorem 10.5, globally continuous finite-dimensional CDF
face. -/
theorem chapter10_indexed_bootstrap_continuous_mapping_distribution_of_null_frontiers
    [TopologicalSpace E] [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstarMapped : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZMapped : AEMeasurable (fun ωlim => g (Z ωlim)) ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  exact
    TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim))
      (chapter10_indexed_bootstrap_continuous_mapping_distribution
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
        (g := g) hZ hg)
      hPstar hZstarMapped hZMapped hfrontier

/-- Hansen Theorem 10.5, globally continuous finite-dimensional CDF face with
measurability derived from the underlying statistic.

This is a convenience wrapper around
`chapter10_bootstrap_continuous_mapping_distribution_of_null_frontiers` for the
common case where `g` is globally continuous and the original bootstrap and
limit statistics are measurable. -/
theorem chapter10_bootstrap_continuous_mapping_distribution_of_null_frontiers_measurable
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZlim : AEMeasurable Z ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  refine
    chapter10_bootstrap_continuous_mapping_distribution_of_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) hZ hg hPstar ?_ ?_ hfrontier
  · intro n ω
    exact hg.measurable.comp (hZstar n ω)
  · have hg_ae : AEMeasurable g (ν.map Z) := hg.measurable.aemeasurable
    simpa [Function.comp_def] using hg_ae.comp_aemeasurable hZlim

/-- Indexed Hansen Theorem 10.5, globally continuous finite-dimensional CDF face
with measurability derived from the underlying statistic. -/
theorem chapter10_indexed_bootstrap_continuous_mapping_distribution_of_null_frontiers_measurable
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZlim : AEMeasurable Z ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  refine
    chapter10_indexed_bootstrap_continuous_mapping_distribution_of_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) hZ hg hPstar ?_ ?_ hfrontier
  · intro n ω
    exact hg.measurable.comp (hZstar n ω)
  · have hg_ae : AEMeasurable g (ν.map Z) := hg.measurable.aemeasurable
    simpa [Function.comp_def] using hg_ae.comp_aemeasurable hZlim

/-- Hansen Theorem 10.5, globally continuous event-probability face.

After a continuous transformation `g`, bounded-continuous lower/upper
sandwiches for an event `A` imply convergence in probability of the conditional
bootstrap event probabilities.  The remaining textbook discontinuity-set-null
case supplies these sandwiches from the null-boundary hypothesis. -/
theorem chapter10_bootstrap_continuous_mapping_event_probability
    [TopologicalSpace E] [TopologicalSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {Z : Ωlim → E} {g : E → F} {A : Set F} {c : ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ lower upper : BoundedContinuousFunction F ℝ,
        (∫ ωlim, lower (g (Z ωlim)) ∂ν) ≤ c ∧
          c ≤ (∫ ωlim, upper (g (Z ωlim)) ∂ν) ∧
          (∫ ωlim, upper (g (Z ωlim)) ∂ν) -
              (∫ ωlim, lower (g (Z ωlim)) ∂ν) ≤ ε ∧
          (∀ n ω,
            bootstrapBoundedContinuousIntegral Pstar
                (fun n ω ωs => g (Zstar n ω ωs)) lower n ω ≤
              bootstrapEventProbability Pstar
                (fun n ω ωs => g (Zstar n ω ωs)) A n ω) ∧
          (∀ n ω,
            bootstrapEventProbability Pstar
                (fun n ω ωs => g (Zstar n ω ωs)) A n ω ≤
              bootstrapBoundedContinuousIntegral Pstar
                (fun n ω ωs => g (Zstar n ω ωs)) upper n ω)) :
    TendstoInMeasure μ
      (bootstrapEventProbability Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => c) := by
  exact
    (chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) hZ hg).event_probability_tendsto_of_boundedContinuous_sandwich
        happrox

/-- Indexed Hansen Theorem 10.5, globally continuous event-probability face. -/
theorem chapter10_indexed_bootstrap_continuous_mapping_event_probability
    [TopologicalSpace E] [TopologicalSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {Z : Ωlim → E} {g : E → F} {A : Set F} {c : ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ lower upper : BoundedContinuousFunction F ℝ,
        (∫ ωlim, lower (g (Z ωlim)) ∂ν) ≤ c ∧
          c ≤ (∫ ωlim, upper (g (Z ωlim)) ∂ν) ∧
          (∫ ωlim, upper (g (Z ωlim)) ∂ν) -
              (∫ ωlim, lower (g (Z ωlim)) ∂ν) ≤ ε ∧
          (∀ n ω,
            bootstrapBoundedContinuousIntegralIndexed Pstar
                (fun n ω ωs => g (Zstar n ω ωs)) lower n ω ≤
              bootstrapEventProbabilityIndexed Pstar
                (fun n ω ωs => g (Zstar n ω ωs)) A n ω) ∧
          (∀ n ω,
            bootstrapEventProbabilityIndexed Pstar
                (fun n ω ωs => g (Zstar n ω ωs)) A n ω ≤
              bootstrapBoundedContinuousIntegralIndexed Pstar
                (fun n ω ωs => g (Zstar n ω ωs)) upper n ω)) :
    TendstoInMeasure μ
      (bootstrapEventProbabilityIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => c) := by
  exact
    (chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := g) hZ hg).event_probability_tendsto_of_sandwich happrox

/-- Hansen Theorem 10.5, globally continuous event-probability face with a
null-frontier event.

If `Zₙ* ->d* Z`, `g` is continuous, the conditional bootstrap laws are finite,
and the transformed limit law gives zero mass to the frontier of `A`, then
the conditional probabilities `P*[g(Zₙ*) ∈ A]` converge in probability to
`P[g(Z) ∈ A]`. -/
theorem chapter10_bootstrap_continuous_mapping_event_probability_of_null_frontier
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZlim : AEMeasurable Z ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbability Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  refine
    TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_null_frontier
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim)) (A := A)
      ?_ hPstar ?_ ?_ hA hfrontier
  · exact
      chapter10_bootstrap_continuous_mapping_distribution
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
        (g := g) hZ hg
  · intro n ω
    exact hg.measurable.comp (hZstar n ω)
  · have hg_ae : AEMeasurable g (ν.map Z) := hg.measurable.aemeasurable
    simpa [Function.comp_def] using hg_ae.comp_aemeasurable hZlim

/-- Indexed Hansen Theorem 10.5, globally continuous event-probability face
with a null-frontier event. -/
theorem chapter10_indexed_bootstrap_continuous_mapping_event_probability_of_null_frontier
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hg : Continuous g)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (Zstar n ω))
    (hZlim : AEMeasurable Z ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbabilityIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  refine
    TendstoInBootstrapWeakDistributionIndexed.event_probability_tendsto_of_null_frontier
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim)) (A := A)
      ?_ hPstar ?_ ?_ hA hfrontier
  · exact
      chapter10_indexed_bootstrap_continuous_mapping_distribution
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
        (g := g) hZ hg
  · intro n ω
    exact hg.measurable.comp (hZstar n ω)
  · have hg_ae : AEMeasurable g (ν.map Z) := hg.measurable.aemeasurable
    simpa [Function.comp_def] using hg_ae.comp_aemeasurable hZlim

/-- Hansen Theorem 10.5, sandwich-mapped event-probability face with a
null-frontier event.

This is the theorem-facing composition of
`TendstoInBootstrapWeakDistribution.map_of_boundedContinuous_sandwich` with
the null-frontier event bridge.  It is useful when `g` is not globally
continuous but transformed bounded-continuous test functions have
lower/upper bounded-continuous approximations on the original space. -/
theorem chapter10_bootstrap_mapping_event_probability_of_sandwich_null_frontier
    [TopologicalSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction F ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZlim : AEMeasurable (fun ωlim => g (Z ωlim)) ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbability Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  refine
    TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_null_frontier
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim)) (A := A)
      ?_ hPstar hZstar hZlim hA hfrontier
  exact hZ.map_of_boundedContinuous_sandwich happrox

/-- Indexed Hansen Theorem 10.5, sandwich-mapped event-probability face with a
null-frontier event. -/
theorem chapter10_indexed_bootstrap_mapping_event_probability_of_sandwich_null_frontier
    [TopologicalSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction F ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZlim : AEMeasurable (fun ωlim => g (Z ωlim)) ν)
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbabilityIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  refine
    TendstoInBootstrapWeakDistributionIndexed.event_probability_tendsto_of_null_frontier
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim)) (A := A)
      ?_ hPstar hZstar hZlim hA hfrontier
  exact hZ.map_of_boundedContinuous_sandwich happrox

/-- Hansen Theorem 10.5, sandwich-mapped finite-dimensional CDF face.

Bounded-continuous sandwich approximations give mapped weak convergence; null
frontiers for transformed lower orthants then recover Hansen Definition 10.2. -/
theorem chapter10_bootstrap_mapping_distribution_of_sandwich_null_frontiers
    [TopologicalSpace E] [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZ : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegral Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegral Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZlim : AEMeasurable (fun ωlim => g (Z ωlim)) ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  refine
    TendstoInBootstrapDistribution.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim))
      ?_ hPstar hZstar hZlim hfrontier
  exact hZ.map_of_boundedContinuous_sandwich happrox

/-- Indexed Hansen Theorem 10.5, sandwich-mapped finite-dimensional CDF face. -/
theorem chapter10_indexed_bootstrap_mapping_distribution_of_sandwich_null_frontiers
    [TopologicalSpace E] [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hZ : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (happrox :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ ε : ℝ, 0 < ε →
        ∃ lower upper : BoundedContinuousFunction E ℝ,
          (∫ ωlim, lower (Z ωlim) ∂ν) ≤
              (∫ ωlim, f (g (Z ωlim)) ∂ν) ∧
            (∫ ωlim, f (g (Z ωlim)) ∂ν) ≤
              (∫ ωlim, upper (Z ωlim) ∂ν) ∧
            (∫ ωlim, upper (Z ωlim) ∂ν) -
                (∫ ωlim, lower (Z ωlim) ∂ν) ≤ ε ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar Zstar lower n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω) ∧
            (∀ n ω,
              bootstrapBoundedContinuousIntegralIndexed Pstar
                  (fun n ω ωs => g (Zstar n ω ωs)) f n ω ≤
                bootstrapBoundedContinuousIntegralIndexed Pstar Zstar upper n ω))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hZlim : AEMeasurable (fun ωlim => g (Z ωlim)) ν)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  refine
    TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim))
      ?_ hPstar hZstar hZlim hfrontier
  exact hZ.map_of_boundedContinuous_sandwich happrox

/-- The textbook a.e.-continuity premise in Hansen Theorem 10.5.

This condition package is intentionally limit-law-facing: it records that the
transformed limit statistic is measurable and that the transformation is
continuous at `Z` outside a `ν`-null set.  The Portmanteau step deriving
transformed weak convergence from this premise is kept separate from the
event-probability wrappers below. -/
structure BootstrapAEMappingPremise
    [TopologicalSpace E] [TopologicalSpace F] [MeasurableSpace F]
    (ν : Measure Ωlim) (Z : Ωlim → E) (g : E → F) : Prop where
  aemeasurable : AEMeasurable (fun ωlim => g (Z ωlim)) ν
  ae_continuous : ∀ᵐ ωlim ∂ν, ContinuousAt g (Z ωlim)

/-- Global continuity supplies Hansen's a.e.-continuity mapping premise. -/
theorem BootstrapAEMappingPremise.of_continuous
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    {ν : Measure Ωlim} {Z : Ωlim → E} {g : E → F}
    (hZ : AEMeasurable Z ν) (hg : Continuous g) :
    BootstrapAEMappingPremise ν Z g := by
  exact
    { aemeasurable := hg.measurable.aemeasurable.comp_aemeasurable hZ
      ae_continuous := ae_of_all ν fun _ => hg.continuousAt }

/-- Hansen Theorem 10.5, a.e.-continuous transformed-event face.

The a.e.-continuity package records the textbook mapping premise, while the
transformed weak-convergence hypothesis is explicit.  This gives the
null-frontier event-probability conclusion without assuming that `g` is
globally continuous. -/
theorem chapter10_bootstrap_ae_continuous_mapping_event_probability_of_null_frontier
    [TopologicalSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hmap : BootstrapAEMappingPremise ν Z g)
    (hweakMapped :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbability Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  exact
    TendstoInBootstrapWeakDistribution.event_probability_tendsto_of_null_frontier
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim)) (A := A)
      hweakMapped hPstar hZstar hmap.aemeasurable hA hfrontier

/-- Indexed Hansen Theorem 10.5, a.e.-continuous transformed-event face. -/
theorem chapter10_indexed_bootstrap_ae_continuous_mapping_event_probability_of_null_frontier
    [TopologicalSpace E]
    [PseudoEMetricSpace F] [MeasurableSpace F] [BorelSpace F] [OpensMeasurableSpace F]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → F} {A : Set F}
    (hmap : BootstrapAEMappingPremise ν Z g)
    (hweakMapped :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hA : MeasurableSet A)
    (hfrontier : (ν.map (fun ωlim => g (Z ωlim))) (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbabilityIndexed Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) A)
      atTop (fun _ => (ν.map (fun ωlim => g (Z ωlim))).real A) := by
  exact
    TendstoInBootstrapWeakDistributionIndexed.event_probability_tendsto_of_null_frontier
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim)) (A := A)
      hweakMapped hPstar hZstar hmap.aemeasurable hA hfrontier

/-- Hansen Theorem 10.5, a.e.-continuous finite-dimensional CDF face.

This is the Definition 10.2 counterpart of
`chapter10_bootstrap_ae_continuous_mapping_event_probability_of_null_frontier`.
The a.e.-continuity package records Hansen's mapping premise, while the
transformed weak-convergence hypothesis is explicit; null frontiers for
transformed lower orthants then give conditional-CDF convergence. -/
theorem chapter10_bootstrap_ae_continuous_mapping_distribution_of_null_frontiers
    [TopologicalSpace E] [Finite k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hmap : BootstrapAEMappingPremise ν Z g)
    (hweakMapped :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  exact
    TendstoInBootstrapDistribution.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim))
      hweakMapped hPstar hZstar hmap.aemeasurable hfrontier

/-- Indexed Hansen Theorem 10.5, a.e.-continuous finite-dimensional CDF face. -/
theorem chapter10_indexed_bootstrap_ae_continuous_mapping_distribution_of_null_frontiers
    [TopologicalSpace E] [Finite k]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : Ωlim → E} {g : E → k → ℝ}
    (hmap : BootstrapAEMappingPremise ν Z g)
    (hweakMapped :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZstar : ∀ n ω, Measurable (fun ωs => g (Zstar n ω ωs)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt (fun y =>
        vectorCDF ν (fun ωlim => g (Z ωlim)) y) x →
        (ν.map (fun ωlim => g (Z ωlim)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => g (Zstar n ω ωs)) ν (fun ωlim => g (Z ωlim)) := by
  exact
    TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => g (Zstar n ω ωs))
      (ν := ν) (Z := fun ωlim => g (Z ωlim))
      hweakMapped hPstar hZstar hmap.aemeasurable hfrontier

end BootstrapWeakDistribution

section BootstrapDeltaMethod

/-- Hansen Theorem 10.6, linearized bootstrap Delta-method bridge.

Once the nonlinear estimator has been reduced to its derivative-linearized
statistic, bootstrap weak convergence is preserved by the continuous linear
derivative map.  The deterministic differentiability remainder supplies the
separate `oₚ*` step in the full Delta-method proof. -/
theorem chapter10_bootstrap_delta_method_linear
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → E}
    {ξ : Ωlim → E} (G : E →L[ℝ] F)
    (hT : TendstoInBootstrapWeakDistribution μ Pstar Tstar ν ξ) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => G (Tstar n ω ωs)) ν (fun ω => G (ξ ω)) :=
  chapter10_bootstrap_continuous_mapping_distribution hT G.continuous

/-- Matrix-linear form of the bootstrap Delta-method bridge. -/
theorem chapter10_bootstrap_delta_method_matrix_linear
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {ξ : Ωlim → EuclideanSpace ℝ d} (G : Matrix r d ℝ)
    (hT : TendstoInBootstrapWeakDistribution μ Pstar Tstar ν ξ) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      ν (fun ω => matrixContinuousLinearMap G (ξ ω)) :=
  chapter10_bootstrap_delta_method_linear (matrixContinuousLinearMap G) hT

/-- Hansen Theorem 10.6, Gaussian covariance specialization.

If the bootstrap linearized statistic converges weakly to `N(0, V)`, then its
matrix-derivative image converges weakly to `N(0, G V G')`, matching the
textbook covariance formula. -/
theorem chapter10_bootstrap_delta_method_gaussian
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) := by
  intro f
  have hlinear :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => matrixContinuousLinearMap G z) :=
    chapter10_bootstrap_delta_method_matrix_linear (G := G) hT
  have hmap :
      (multivariateGaussian (0 : EuclideanSpace ℝ d) V).map
          (matrixContinuousLinearMap G) =
        multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (map_matrix_multivariateGaussian
        (μ := (0 : EuclideanSpace ℝ d)) hV G)
  have htarget :
      ∫ z, f z ∂(multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) =
        ∫ z, f (matrixContinuousLinearMap G z)
          ∂(multivariateGaussian (0 : EuclideanSpace ℝ d) V) := by
    rw [← hmap]
    exact integral_map (matrixContinuousLinearMap G).continuous.aemeasurable
      f.continuous.aestronglyMeasurable
  simpa [htarget] using hlinear.tendsto_integral f

/-- Hansen Theorem 10.6, Gaussian CDF specialization.

This is the Hansen Definition 10.2 face of the matrix-linear bootstrap Delta
method.  A Gaussian bootstrap weak limit for the input statistic transfers
through the derivative matrix, then the weak-to-CDF bridge gives coordinate CDF
convergence at transformed Gaussian continuity points with null lower-orthant
frontiers. -/
theorem chapter10_bootstrap_delta_method_gaussian_distribution
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hfrontier : ∀ x : r → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
              (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
            (fun z : EuclideanSpace ℝ r => (z : r → ℝ)))
          (frontier {z : r → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs =>
        ((matrixContinuousLinearMap G (Tstar n ω ωs) :
          EuclideanSpace ℝ r) : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) := by
  let coord : EuclideanSpace ℝ r → r → ℝ := fun z => (z : r → ℝ)
  have hcoord : Continuous coord :=
    PiLp.continuous_ofLp 2 (fun _ : r => ℝ)
  have hthetaWeak :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_bootstrap_delta_method_gaussian
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (V := V) G hV hT
  have hcoordWeak :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => coord (matrixContinuousLinearMap G (Tstar n ω ωs)))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => coord z) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := coord) hthetaWeak hcoord
  have hZstar :
      ∀ n ω,
        Measurable
          (fun ωs =>
            coord (matrixContinuousLinearMap G (Tstar n ω ωs))) := by
    intro n ω
    exact hcoord.measurable.comp
      ((matrixContinuousLinearMap G).continuous.measurable.comp (hTstar n ω))
  have hZlim :
      AEMeasurable (fun z : EuclideanSpace ℝ r => coord z)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) :=
    hcoord.aemeasurable
  exact
    TendstoInBootstrapDistribution.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => coord (matrixContinuousLinearMap G (Tstar n ω ωs)))
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => coord z)
      hcoordWeak hPstar hZstar hZlim hfrontier

/-- Hansen Theorem 10.6, Gaussian CDF specialization with positive definite
transformed covariance.

When `G V G'` is positive definite, the Gaussian lower-orthant null-frontier
premise in `chapter10_bootstrap_delta_method_gaussian_distribution` is
automatic. -/
theorem chapter10_bootstrap_delta_method_gaussian_distribution_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs =>
        ((matrixContinuousLinearMap G (Tstar n ω ωs) :
          EuclideanSpace ℝ r) : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (V := V) G
    hV hT hPstar hTstar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hGVG x)

/-- Indexed Hansen Theorem 10.6, linearized bootstrap Delta-method bridge for
sample-size-dependent bootstrap spaces. -/
theorem chapter10_indexed_bootstrap_delta_method_linear
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → E}
    {ξ : Ωlim → E} (G : E →L[ℝ] F)
    (hT : TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar ν ξ) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => G (Tstar n ω ωs)) ν (fun ω => G (ξ ω)) :=
  chapter10_indexed_bootstrap_continuous_mapping_distribution hT G.continuous

/-- Indexed matrix-linear form of the bootstrap Delta-method bridge. -/
theorem chapter10_indexed_bootstrap_delta_method_matrix_linear
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {ξ : Ωlim → EuclideanSpace ℝ d} (G : Matrix r d ℝ)
    (hT : TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar ν ξ) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      ν (fun ω => matrixContinuousLinearMap G (ξ ω)) :=
  chapter10_indexed_bootstrap_delta_method_linear
    (matrixContinuousLinearMap G) hT

/-- Indexed Hansen Theorem 10.6, Gaussian covariance specialization for
sample-size-dependent bootstrap spaces. -/
theorem chapter10_indexed_bootstrap_delta_method_gaussian
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) := by
  intro f
  have hlinear :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => matrixContinuousLinearMap G z) :=
    chapter10_indexed_bootstrap_delta_method_matrix_linear (G := G) hT
  have hmap :
      (multivariateGaussian (0 : EuclideanSpace ℝ d) V).map
          (matrixContinuousLinearMap G) =
        multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (map_matrix_multivariateGaussian
        (μ := (0 : EuclideanSpace ℝ d)) hV G)
  have htarget :
      ∫ z, f z ∂(multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) =
        ∫ z, f (matrixContinuousLinearMap G z)
          ∂(multivariateGaussian (0 : EuclideanSpace ℝ d) V) := by
    rw [← hmap]
    exact integral_map (matrixContinuousLinearMap G).continuous.aemeasurable
      f.continuous.aestronglyMeasurable
  simpa [htarget] using hlinear.tendsto_integral f

/-- Indexed Hansen Theorem 10.6, Gaussian CDF specialization. -/
theorem chapter10_indexed_bootstrap_delta_method_gaussian_distribution
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hfrontier : ∀ x : r → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
              (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
            (fun z : EuclideanSpace ℝ r => (z : r → ℝ)))
          (frontier {z : r → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs =>
        ((matrixContinuousLinearMap G (Tstar n ω ωs) :
          EuclideanSpace ℝ r) : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) := by
  let coord : EuclideanSpace ℝ r → r → ℝ := fun z => (z : r → ℝ)
  have hcoord : Continuous coord :=
    PiLp.continuous_ofLp 2 (fun _ : r => ℝ)
  have hthetaWeak :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_indexed_bootstrap_delta_method_gaussian
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (V := V) G hV hT
  have hcoordWeak :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => coord (matrixContinuousLinearMap G (Tstar n ω ωs)))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => coord z) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := coord) hthetaWeak hcoord
  have hZstar :
      ∀ n ω,
        Measurable
          (fun ωs =>
            coord (matrixContinuousLinearMap G (Tstar n ω ωs))) := by
    intro n ω
    exact hcoord.measurable.comp
      ((matrixContinuousLinearMap G).continuous.measurable.comp (hTstar n ω))
  have hZlim :
      AEMeasurable (fun z : EuclideanSpace ℝ r => coord z)
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) :=
    hcoord.aemeasurable
  exact
    TendstoInBootstrapDistributionIndexed.of_weakDistribution_null_frontiers
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => coord (matrixContinuousLinearMap G (Tstar n ω ωs)))
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => coord z)
      hcoordWeak hPstar hZstar hZlim hfrontier

/-- Indexed Hansen Theorem 10.6, Gaussian CDF specialization with positive
definite transformed covariance. -/
theorem chapter10_indexed_bootstrap_delta_method_gaussian_distribution_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs =>
        ((matrixContinuousLinearMap G (Tstar n ω ωs) :
          EuclideanSpace ℝ r) : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (V := V) G
    hV hT hPstar hTstar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hGVG x)

/-- Hansen Theorem 10.7, smooth-function Gaussian bootstrap wrapper.

If the bootstrap moment/statistic has Gaussian bootstrap limit `N(0,V)` and
the centered bootstrap smooth-function estimator has already been reduced to
the derivative-linearized statistic `G T*`, then it has bootstrap limit
`N(0, G V G')`. The remaining theorem-specific work is the nonlinear
differentiability/`oₚ*` constructor that supplies this linearization for
Hansen's smooth-function estimator. -/
theorem chapter10_bootstrap_smooth_function_gaussian_of_linearization
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs)) :
    TendstoInBootstrapWeakDistribution μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  (chapter10_bootstrap_delta_method_gaussian (μ := μ) (Pstar := Pstar)
    (Tstar := Tstar) (V := V) G hV hT).congr_bootstrap
      (fun n ω ωs => (hlinearization n ω ωs).symm)

/-- Hansen Theorem 10.7, smooth-function Gaussian CDF wrapper from exact
linearization.

This is the Hansen Definition 10.2 face of
`chapter10_bootstrap_smooth_function_gaussian_of_linearization`: the
matrix-linear Gaussian Delta-method CDF theorem supplies the coordinate-CDF
conclusion, and the supplied pointwise linearization identifies the
smooth-function bootstrap statistic with the derivative-linearized statistic. -/
theorem chapter10_bootstrap_smooth_function_gaussian_distribution_of_linearization
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hfrontier : ∀ x : r → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
              (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
            (fun z : EuclideanSpace ℝ r => (z : r → ℝ)))
          (frontier {z : r → ℝ | coordinateLE z x}) = 0)
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) := by
  have hdelta :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs =>
          ((matrixContinuousLinearMap G (Tstar n ω ωs) :
            EuclideanSpace ℝ r) : r → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
    chapter10_bootstrap_delta_method_gaussian_distribution
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (V := V) G
      hV hT hPstar hTstar hfrontier
  exact hdelta.congr_bootstrap fun n ω ωs =>
    congrArg (fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      (hlinearization n ω ωs).symm

/-- Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from exact
linearization with positive definite transformed covariance.

This is the positive-definite covariance specialization of
`chapter10_bootstrap_smooth_function_gaussian_distribution_of_linearization`;
the Gaussian lower-orthant null-frontier premise is discharged automatically. -/
theorem chapter10_bootstrap_smooth_function_gaussian_distribution_of_linearization_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_smooth_function_gaussian_distribution_of_linearization
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hGVG x)
    hlinearization

/-- Hansen Theorem 10.7 smooth-function Gaussian wrapper from
bounded-continuous test-function linearization.

This is the weak-distribution transfer form used when differentiability gives
an `oₚ*` nonlinear remainder strong enough to make every bounded-continuous
test-function conditional expectation agree asymptotically with the
derivative-linearized statistic. -/
theorem chapter10_bootstrap_smooth_function_gaussian_of_integral_linearization
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hlinearization :
      ∀ f : BoundedContinuousFunction (EuclideanSpace ℝ r) ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegral Pstar thetaStar f n ω -
              bootstrapBoundedContinuousIntegral Pstar
                (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
                f n ω)
          atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistribution μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  TendstoInBootstrapWeakDistribution.of_integral_difference_zero
    (μ := μ) (Pstar := Pstar)
    (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
    (Zstar' := thetaStar)
    (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
    (Z := fun z : EuclideanSpace ℝ r => z)
    (chapter10_bootstrap_delta_method_gaussian (μ := μ) (Pstar := Pstar)
      (Tstar := Tstar) (V := V) G hV hT)
    hlinearization

/-- Hansen Theorem 10.7, smooth-function Gaussian CDF wrapper from
bounded-continuous test-function linearization.

If the nonlinear smooth-function statistic has the same conditional
bounded-continuous test-function integrals as its derivative-linearized version
up to `oₚ(1)`, then the Gaussian weak wrapper plus the weak-to-CDF bridge give
Hansen Definition 10.2 convergence at transformed Gaussian lower orthants with
null frontier. -/
theorem chapter10_bootstrap_smooth_function_gaussian_distribution_of_integral_linearization
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hlinearization :
      ∀ f : BoundedContinuousFunction (EuclideanSpace ℝ r) ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegral Pstar thetaStar f n ω -
              bootstrapBoundedContinuousIntegral Pstar
                (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
                f n ω)
          atTop (fun _ => 0))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hfrontier : ∀ x : r → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
              (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
            (fun z : EuclideanSpace ℝ r => (z : r → ℝ)))
          (frontier {z : r → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) := by
  let coord : EuclideanSpace ℝ r → r → ℝ := fun z => (z : r → ℝ)
  have hcoord : Continuous coord :=
    PiLp.continuous_ofLp 2 (fun _ : r => ℝ)
  have hweak :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_bootstrap_smooth_function_gaussian_of_integral_linearization
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  have hZstar :
      ∀ n ω, Measurable (fun ωs => coord (thetaStar n ω ωs)) := by
    intro n ω
    exact hcoord.measurable.comp (hthetaStar n ω)
  exact
    chapter10_bootstrap_continuous_mapping_distribution_of_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := coord) hweak hcoord hPstar hZstar hcoord.aemeasurable hfrontier

/-- Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from
bounded-continuous test-function linearization with positive definite
transformed covariance. -/
theorem chapter10_bootstrap_smooth_function_gaussian_distribution_of_integral_linearization_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hlinearization :
      ∀ f : BoundedContinuousFunction (EuclideanSpace ℝ r) ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegral Pstar thetaStar f n ω -
              bootstrapBoundedContinuousIntegral Pstar
                (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
                f n ω)
          atTop (fun _ => 0))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_smooth_function_gaussian_distribution_of_integral_linearization
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hlinearization
    hPstar hthetaStar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hGVG x)

/-- Indexed Hansen Theorem 10.7, smooth-function Gaussian bootstrap wrapper
from exact linearization. -/
theorem chapter10_indexed_bootstrap_smooth_function_gaussian_of_linearization
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  (chapter10_indexed_bootstrap_delta_method_gaussian
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (V := V) G hV hT).congr_bootstrap
      (fun n ω ωs => (hlinearization n ω ωs).symm)

/-- Indexed Hansen Theorem 10.7, smooth-function Gaussian CDF wrapper from
exact linearization. -/
theorem
    chapter10_indexed_bootstrap_smooth_function_gaussian_distribution_of_linearization
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hfrontier : ∀ x : r → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
              (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
            (fun z : EuclideanSpace ℝ r => (z : r → ℝ)))
          (frontier {z : r → ℝ | coordinateLE z x}) = 0)
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) := by
  have hdelta :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs =>
          ((matrixContinuousLinearMap G (Tstar n ω ωs) :
            EuclideanSpace ℝ r) : r → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
    chapter10_indexed_bootstrap_delta_method_gaussian_distribution
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (V := V) G
      hV hT hPstar hTstar hfrontier
  exact hdelta.congr_bootstrap fun n ω ωs =>
    congrArg (fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      (hlinearization n ω ωs).symm

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from
exact linearization with positive definite transformed covariance. -/
theorem
    chapter10_indexed_bootstrap_smooth_function_gaussian_distribution_of_linearization_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_smooth_function_gaussian_distribution_of_linearization
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hGVG x)
    hlinearization

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian wrapper from
bounded-continuous test-function linearization. -/
theorem chapter10_indexed_bootstrap_smooth_function_gaussian_of_integral_linearization
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hlinearization :
      ∀ f : BoundedContinuousFunction (EuclideanSpace ℝ r) ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegralIndexed Pstar thetaStar f n ω -
              bootstrapBoundedContinuousIntegralIndexed Pstar
                (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
                f n ω)
          atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  TendstoInBootstrapWeakDistributionIndexed.of_integral_difference_zero
    (μ := μ) (Pstar := Pstar)
    (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
    (Zstar' := thetaStar)
    (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
    (Z := fun z : EuclideanSpace ℝ r => z)
    (chapter10_indexed_bootstrap_delta_method_gaussian
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (V := V) G hV hT)
    hlinearization

/-- Indexed Hansen Theorem 10.7, smooth-function Gaussian CDF wrapper from
bounded-continuous test-function linearization. -/
theorem
    chapter10_indexed_bootstrap_smooth_function_gaussian_distribution_of_integral_linearization
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hlinearization :
      ∀ f : BoundedContinuousFunction (EuclideanSpace ℝ r) ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegralIndexed Pstar thetaStar f n ω -
              bootstrapBoundedContinuousIntegralIndexed Pstar
                (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
                f n ω)
          atTop (fun _ => 0))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hfrontier : ∀ x : r → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
              (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
            (fun z : EuclideanSpace ℝ r => (z : r → ℝ)))
          (frontier {z : r → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) := by
  let coord : EuclideanSpace ℝ r → r → ℝ := fun z => (z : r → ℝ)
  have hcoord : Continuous coord :=
    PiLp.continuous_ofLp 2 (fun _ : r => ℝ)
  have hweak :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_indexed_bootstrap_smooth_function_gaussian_of_integral_linearization
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  have hZstar :
      ∀ n ω, Measurable (fun ωs => coord (thetaStar n ω ωs)) := by
    intro n ω
    exact hcoord.measurable.comp (hthetaStar n ω)
  exact
    chapter10_indexed_bootstrap_continuous_mapping_distribution_of_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := coord) hweak hcoord hPstar hZstar hcoord.aemeasurable hfrontier

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from
bounded-continuous test-function linearization with positive definite
transformed covariance. -/
theorem
    chapter10_indexed_bootstrap_smooth_function_gaussian_distribution_of_integral_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hlinearization :
      ∀ f : BoundedContinuousFunction (EuclideanSpace ℝ r) ℝ,
        TendstoInMeasure μ
          (fun n ω =>
            bootstrapBoundedContinuousIntegralIndexed Pstar thetaStar f n ω -
              bootstrapBoundedContinuousIntegralIndexed Pstar
                (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
                f n ω)
          atTop (fun _ => 0))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_smooth_function_gaussian_distribution_of_integral_linearization
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hlinearization
    hPstar hthetaStar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hGVG x)

end BootstrapDeltaMethod

section SmoothFunctionBootstrapVariance

/-- Smooth-function plug-in covariance functional `Gᵀ V G`.

This is the covariance map in Hansen's smooth-function bootstrap delta-method
results, with `G` the Jacobian and `V` the covariance matrix of the underlying
moment/statistic. -/
noncomputable def smoothFunctionVarianceFunctional
    {d r : Type*} [Fintype d] [Fintype r]
    (G : Matrix d r ℝ) (V : Matrix d d ℝ) : Matrix r r ℝ :=
  Gᵀ * V * G

/-- The smooth-function plug-in covariance map is continuous in its Jacobian
and covariance inputs. -/
theorem smoothFunctionVarianceFunctional_continuous
    {d r : Type*} [Fintype d] [Fintype r] :
    Continuous (fun p : Matrix d r ℝ × Matrix d d ℝ =>
      smoothFunctionVarianceFunctional p.1 p.2) := by
  unfold smoothFunctionVarianceFunctional
  exact ((continuous_fst.matrix_transpose).matrix_mul continuous_snd).matrix_mul
    continuous_fst

/-- Hansen Theorem 10.8, plug-in covariance continuous-mapping bridge.

If the bootstrap Jacobian/covariance pair converges in bootstrap probability to
the population pair, then the smooth-function covariance plug-in
`Gstarᵀ Vstar Gstar` converges in bootstrap probability to `Gᵀ V G`.  The
concrete Theorem 10.8 constructors provide the joint bootstrap-probability
premise from the smooth-function model and the bootstrap WLLN/CLT layer. -/
theorem chapter10_bootstrap_smooth_variance_consistency
    {d r : Type*} [Fintype d] [Fintype r]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Gstar : ℕ → Ω → Ωs → Matrix d r ℝ}
    {Vstar : ℕ → Ω → Ωs → Matrix d d ℝ}
    {G : Matrix d r ℝ} {V : Matrix d d ℝ}
    (hGV :
      TendstoInBootstrapProbability μ Pstar
        (fun n ω ωs => (Gstar n ω ωs, Vstar n ω ωs))
        (fun _ => (G, V))) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gstar n ω ωs) (Vstar n ω ωs))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  TendstoInBootstrapProbability.continuousAt_const_comp
    (E := Matrix d r ℝ × Matrix d d ℝ)
    (F := Matrix r r ℝ)
    (Pstar := Pstar)
    (Zstar := fun n ω ωs => (Gstar n ω ωs, Vstar n ω ωs))
    (c := (G, V))
    (g := fun p => smoothFunctionVarianceFunctional p.1 p.2)
    hPstar hGV smoothFunctionVarianceFunctional_continuous.continuousAt

/-- Hansen Theorem 10.8, componentwise plug-in covariance bridge.

This wrapper packages the usual proof shape: establish separate bootstrap
convergence of the plug-in Jacobian and covariance inputs, combine them into a
joint convergence statement, then apply the smooth covariance CMT. -/
theorem chapter10_bootstrap_smooth_variance_consistency_of_components
    {d r : Type*} [Fintype d] [Fintype r]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Gstar : ℕ → Ω → Ωs → Matrix d r ℝ}
    {Vstar : ℕ → Ω → Ωs → Matrix d d ℝ}
    {G : Matrix d r ℝ} {V : Matrix d d ℝ}
    (hG :
      TendstoInBootstrapProbability μ Pstar Gstar (fun _ => G))
    (hV :
      TendstoInBootstrapProbability μ Pstar Vstar (fun _ => V)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gstar n ω ωs) (Vstar n ω ωs))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_bootstrap_smooth_variance_consistency hPstar
    (TendstoInBootstrapProbability.prodMk hPstar hG hV)

/-- Hansen Theorem 10.8, plug-in covariance bridge from ordinary component
convergence.

This wrapper covers the common plug-in case where the bootstrap component
statistics are deterministic under the resampling law.  Ordinary convergence in
probability of `G_n` and `V_n` is lifted to bootstrap-probability convergence by
Theorem 10.1, then fed through the smooth covariance continuous-mapping bridge. -/
theorem chapter10_bootstrap_smooth_variance_consistency_of_tendstoInMeasure_components
    {d r : Type*} [Fintype d] [Fintype r]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Gseq : ℕ → Ω → Matrix d r ℝ}
    {Vseq : ℕ → Ω → Matrix d d ℝ}
    {G : Matrix d r ℝ} {V : Matrix d d ℝ}
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hV : TendstoInMeasure μ Vseq atTop (fun _ => V)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ => smoothFunctionVarianceFunctional (Gseq n ω) (Vseq n ω))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_bootstrap_smooth_variance_consistency_of_components hPstar
    (chapter10_bootstrap_convergence_in_probability_of_convergence_in_probability
      (μ := μ) (Pstar := Pstar) hPstar hG)
    (chapter10_bootstrap_convergence_in_probability_of_convergence_in_probability
      (μ := μ) (Pstar := Pstar) hPstar hV)

/-- Hansen Theorem 10.8, plug-in covariance bridge from continuous stochastic
component maps.

This is the CMT-shaped constructor for stochastic plug-in Jacobian/covariance
inputs: if a bootstrap statistic `Ustar` converges to a constant `u` and the
Jacobian and covariance plug-ins are continuous at `u`, then
`G(Ustar)ᵀ V(Ustar) G(Ustar)` converges to `G(u)ᵀ V(u) G(u)`. -/
theorem chapter10_bootstrap_smooth_variance_consistency_of_continuous_plugins
    {d r A : Type*} [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Pstar : ℕ → Ω → Measure Ωs}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Ustar : ℕ → Ω → Ωs → A} {u : A}
    {Gfun : A → Matrix d r ℝ} {Vfun : A → Matrix d d ℝ}
    (hU : TendstoInBootstrapProbability μ Pstar Ustar (fun _ => u))
    (hG : ContinuousAt Gfun u) (hV : ContinuousAt Vfun u) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gfun (Ustar n ω ωs))
          (Vfun (Ustar n ω ωs)))
      (fun _ => smoothFunctionVarianceFunctional (Gfun u) (Vfun u)) :=
  chapter10_bootstrap_smooth_variance_consistency_of_components hPstar
    (TendstoInBootstrapProbability.continuousAt_const_comp
      (Pstar := Pstar) (Zstar := Ustar) (c := u) hPstar hU hG)
    (TendstoInBootstrapProbability.continuousAt_const_comp
      (Pstar := Pstar) (Zstar := Ustar) (c := u) hPstar hU hV)

/-- Indexed Hansen Theorem 10.8, plug-in covariance continuous-mapping bridge
for sample-size-dependent bootstrap spaces. -/
theorem chapter10_indexed_bootstrap_smooth_variance_consistency
    {d r : Type*} [Fintype d] [Fintype r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Gstar : ∀ n, Ω → Ωboot n → Matrix d r ℝ}
    {Vstar : ∀ n, Ω → Ωboot n → Matrix d d ℝ}
    {G : Matrix d r ℝ} {V : Matrix d d ℝ}
    (hGV :
      TendstoInBootstrapProbabilityIndexed μ Pstar
        (fun n ω ωs => (Gstar n ω ωs, Vstar n ω ωs))
        (fun _ => (G, V))) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gstar n ω ωs) (Vstar n ω ωs))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  TendstoInBootstrapProbabilityIndexed.continuousAt_const_comp
    (E := Matrix d r ℝ × Matrix d d ℝ)
    (F := Matrix r r ℝ)
    (Pstar := Pstar)
    (Zstar := fun n ω ωs => (Gstar n ω ωs, Vstar n ω ωs))
    (c := (G, V))
    (g := fun p => smoothFunctionVarianceFunctional p.1 p.2)
    hPstar hGV smoothFunctionVarianceFunctional_continuous.continuousAt

/-- Indexed Hansen Theorem 10.8, componentwise plug-in covariance bridge. -/
theorem chapter10_indexed_bootstrap_smooth_variance_consistency_of_components
    {d r : Type*} [Fintype d] [Fintype r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Gstar : ∀ n, Ω → Ωboot n → Matrix d r ℝ}
    {Vstar : ∀ n, Ω → Ωboot n → Matrix d d ℝ}
    {G : Matrix d r ℝ} {V : Matrix d d ℝ}
    (hG :
      TendstoInBootstrapProbabilityIndexed μ Pstar Gstar (fun _ => G))
    (hV :
      TendstoInBootstrapProbabilityIndexed μ Pstar Vstar (fun _ => V)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gstar n ω ωs) (Vstar n ω ωs))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_indexed_bootstrap_smooth_variance_consistency hPstar
    (TendstoInBootstrapProbabilityIndexed.prodMk hPstar hG hV)

/-- Indexed Hansen Theorem 10.8, plug-in covariance bridge from ordinary
component convergence. -/
theorem
    chapter10_indexed_bootstrap_smooth_variance_consistency_of_tendstoInMeasure_components
    {d r : Type*} [Fintype d] [Fintype r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Gseq : ℕ → Ω → Matrix d r ℝ}
    {Vseq : ℕ → Ω → Matrix d d ℝ}
    {G : Matrix d r ℝ} {V : Matrix d d ℝ}
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hV : TendstoInMeasure μ Vseq atTop (fun _ => V)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ => smoothFunctionVarianceFunctional (Gseq n ω) (Vseq n ω))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_indexed_bootstrap_smooth_variance_consistency_of_components hPstar
    (tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure
      (μ := μ) (Pstar := Pstar) hPstar hG)
    (tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure
      (μ := μ) (Pstar := Pstar) hPstar hV)

/-- Indexed Hansen Theorem 10.8, plug-in covariance bridge from continuous
stochastic component maps. -/
theorem
    chapter10_indexed_bootstrap_smooth_variance_consistency_of_continuous_plugins
    {d r A : Type*} [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    {Ustar : ∀ n, Ω → Ωboot n → A} {u : A}
    {Gfun : A → Matrix d r ℝ} {Vfun : A → Matrix d d ℝ}
    (hU : TendstoInBootstrapProbabilityIndexed μ Pstar Ustar (fun _ => u))
    (hG : ContinuousAt Gfun u) (hV : ContinuousAt Vfun u) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gfun (Ustar n ω ωs))
          (Vfun (Ustar n ω ωs)))
      (fun _ => smoothFunctionVarianceFunctional (Gfun u) (Vfun u)) :=
  chapter10_indexed_bootstrap_smooth_variance_consistency_of_components hPstar
    (TendstoInBootstrapProbabilityIndexed.continuousAt_const_comp
      (Pstar := Pstar) (Zstar := Ustar) (c := u) hPstar hU hG)
    (TendstoInBootstrapProbabilityIndexed.continuousAt_const_comp
      (Pstar := Pstar) (Zstar := Ustar) (c := u) hPstar hU hV)

end SmoothFunctionBootstrapVariance

section BootstrapVariance

/-- Conditional bootstrap mean of a real statistic. -/
noncomputable def bootstrapMeanReal
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  (Pstar n ω)[Zstar n ω]

/-- Conditional bootstrap second moment of a real statistic. -/
noncomputable def bootstrapSecondMomentReal
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  (Pstar n ω)[(Zstar n ω) ^ 2]

/-- Conditional bootstrap variance of a real statistic. -/
noncomputable def bootstrapVarianceReal
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  Var[Zstar n ω; Pstar n ω]

/-- Indexed conditional bootstrap mean of a real statistic. -/
noncomputable def bootstrapMeanRealIndexed
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Pstar n ω)[Zstar n ω]

/-- Indexed conditional bootstrap second moment of a real statistic. -/
noncomputable def bootstrapSecondMomentRealIndexed
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Pstar n ω)[(Zstar n ω) ^ 2]

/-- Indexed conditional bootstrap variance of a real statistic. -/
noncomputable def bootstrapVarianceRealIndexed
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Var[Zstar n ω; Pstar n ω]

/-- Pointwise bootstrap mean clipping error bound by an absolute-tail integral. -/
theorem bootstrapMeanReal_abs_sub_realClip_le_two_mul_integral_tail_abs
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZ : ∀ n ω, Integrable (Zstar n ω) (Pstar n ω))
    {R : ℝ} (hR : 0 ≤ R) (n : ℕ) (ω : Ω) :
    |bootstrapMeanReal Pstar Zstar n ω -
      (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]| ≤
      2 * ∫ ωs,
        Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
          (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω := by
  haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
  simpa [bootstrapMeanReal] using
    abs_integral_sub_realClip_le_two_mul_integral_tail_abs
      (μ := Pstar n ω) (Y := Zstar n ω) (hZ n ω) hR

/-- Bootstrap mean clipping errors vanish in probability when their
absolute-tail integrals vanish in probability. -/
theorem bootstrapMeanReal_sub_realClip_tendsto_zero_of_tail_integral
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZ : ∀ n ω, Integrable (Zstar n ω) (Pstar n ω))
    {R : ℝ} (hR : 0 ≤ R)
    (hTail :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        bootstrapMeanReal Pstar Zstar n ω -
          (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
      atTop (fun _ => 0) := by
  have hTail2 := TendstoInMeasure.const_mul_zero_real (μ := μ) 2 hTail
  refine TendstoInMeasure.of_abs_le_zero_real hTail2 ?_
  intro n ω
  have hbound :=
    bootstrapMeanReal_abs_sub_realClip_le_two_mul_integral_tail_abs
      hPstar hZ hR n ω
  have htail_nonneg :
      0 ≤ ∫ ωs,
        Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
          (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω := by
    exact integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun ωs _ => abs_nonneg (Zstar n ω ωs)) ωs
  calc
    |bootstrapMeanReal Pstar Zstar n ω -
      (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]| ≤
        2 * ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω := hbound
    _ = |2 * ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω| := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) htail_nonneg)]

/-- Pointwise bootstrap second-moment clipping error bound by a squared-tail
integral. -/
theorem bootstrapSecondMomentReal_abs_sub_realClip_sq_le_two_mul_integral_tail_sq
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {R : ℝ} (hR : 0 ≤ R) (n : ℕ) (ω : Ω) :
    |bootstrapSecondMomentReal Pstar Zstar n ω -
      (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]| ≤
      2 * ∫ ωs,
        Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
          (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω := by
  haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
  simpa [bootstrapSecondMomentReal] using
    abs_integral_sq_sub_realClip_sq_le_two_mul_integral_tail_sq
      (μ := Pstar n ω) (Y := Zstar n ω) (hZ n ω) hR

/-- Bootstrap second-moment clipping errors vanish in probability when their
squared-tail integrals vanish in probability. -/
theorem bootstrapSecondMomentReal_sub_realClip_sq_tendsto_zero_of_tail_integral
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {R : ℝ} (hR : 0 ≤ R)
    (hTail :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        bootstrapSecondMomentReal Pstar Zstar n ω -
          (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
      atTop (fun _ => 0) := by
  have hTail2 := TendstoInMeasure.const_mul_zero_real (μ := μ) 2 hTail
  refine TendstoInMeasure.of_abs_le_zero_real hTail2 ?_
  intro n ω
  have hbound :=
    bootstrapSecondMomentReal_abs_sub_realClip_sq_le_two_mul_integral_tail_sq
      hPstar hZ hR n ω
  have htail_nonneg :
      0 ≤ ∫ ωs,
        Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
          (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω := by
    exact integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun ωs _ => sq_nonneg (Zstar n ω ωs)) ωs
  calc
    |bootstrapSecondMomentReal Pstar Zstar n ω -
      (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]| ≤
        2 * ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω := hbound
    _ = |2 * ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω| := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) htail_nonneg)]

/-- Tail-integral constructor for the first-moment clipping premise used in
Hansen Theorem 10.9. -/
theorem bootstrapMeanReal_realClip_tails_of_tail_integrals
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZlim : Integrable Z ν)
    (hZstar : ∀ n ω, Integrable (Zstar n ω) (Pstar n ω))
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => |Z ωlim|) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapMeanReal Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
        atTop (fun _ => 0) := by
  intro ε hε
  obtain ⟨R, hR, hlimTail, hsourceTail⟩ := hTail (ε / 2) (by positivity)
  refine ⟨R, hR, ?_, ?_⟩
  · have hclip :=
      abs_integral_sub_realClip_le_two_mul_integral_tail_abs
        (μ := ν) (Y := Z) hZlim hR
    calc
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤
          2 * ∫ ωlim,
            Set.indicator {ωlim | R ≤ |Z ωlim|}
              (fun ωlim => |Z ωlim|) ωlim ∂ν := hclip
      _ ≤ 2 * (ε / 2) := by nlinarith
      _ = ε := by ring
  · exact bootstrapMeanReal_sub_realClip_tendsto_zero_of_tail_integral
      (μ := μ) hPstar hZstar hR hsourceTail

/-- Tail-integral constructor for the second-moment clipping premise used in
Hansen Theorem 10.9. -/
theorem bootstrapSecondMomentReal_realClip_tails_of_tail_integrals
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hZstar : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapSecondMomentReal Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
        atTop (fun _ => 0) := by
  intro ε hε
  obtain ⟨R, hR, hlimTail, hsourceTail⟩ := hTail (ε / 2) (by positivity)
  refine ⟨R, hR, ?_, ?_⟩
  · have hclip :=
      abs_integral_sq_sub_realClip_sq_le_two_mul_integral_tail_sq
        (μ := ν) (Y := Z) hZlim hR
    calc
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤
          2 * ∫ ωlim,
            Set.indicator {ωlim | R ≤ |Z ωlim|}
              (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν := hclip
      _ ≤ 2 * (ε / 2) := by nlinarith
      _ = ε := by ring
  · exact bootstrapSecondMomentReal_sub_realClip_sq_tendsto_zero_of_tail_integral
      (μ := μ) hPstar hZstar hR hsourceTail

/-- Conditional absolute-tail integrals vanish in probability when dominated
by squared-tail integrals at a threshold at least one. -/
theorem bootstrapTailAbsIntegral_tendsto_zero_of_tailSqIntegral
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {R : ℝ} (hR : 1 ≤ R)
    (hTailSq :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ
      (fun n ω =>
        ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω)
      atTop (fun _ => 0) := by
  refine tendstoInMeasure_zero_of_nonneg_le (μ := μ) ?_ ?_ hTailSq
  · intro n ω
    exact integral_nonneg fun ωs =>
      Set.indicator_nonneg (fun ωs _ => abs_nonneg (Zstar n ω ωs)) ωs
  · intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact integral_tail_abs_le_integral_tail_sq_of_one_le
      (μ := Pstar n ω) (Y := Zstar n ω) (hZ n ω) hR

/-- Conditional variance equals second moment minus squared conditional mean. -/
theorem bootstrapVarianceReal_eq_secondMoment_sub_mean_sq
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (n : ℕ) (ω : Ω) :
    bootstrapVarianceReal Pstar Zstar n ω =
      bootstrapSecondMomentReal Pstar Zstar n ω -
        (bootstrapMeanReal Pstar Zstar n ω) ^ 2 := by
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  simpa [bootstrapVarianceReal, bootstrapSecondMomentReal, bootstrapMeanReal]
    using (ProbabilityTheory.variance_eq_sub (μ := Pstar n ω) (X := Zstar n ω)
      (hZ n ω))

/-- Indexed conditional variance equals second moment minus squared conditional
mean. -/
theorem bootstrapVarianceRealIndexed_eq_secondMoment_sub_mean_sq
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (n : ℕ) (ω : Ω) :
    bootstrapVarianceRealIndexed Pstar Zstar n ω =
      bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
        (bootstrapMeanRealIndexed Pstar Zstar n ω) ^ 2 := by
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  simpa [bootstrapVarianceRealIndexed, bootstrapSecondMomentRealIndexed,
    bootstrapMeanRealIndexed] using
      (ProbabilityTheory.variance_eq_sub (μ := Pstar n ω) (X := Zstar n ω)
        (hZ n ω))

/-- Hansen Theorem 10.9, variance-consistency moment bridge.

If the conditional bootstrap first and second moments of a real statistic
converge in ordinary probability to the corresponding limit moments, then the
conditional bootstrap variance converges in probability to the variance
functional `m₂ - m²`.  The remaining Theorem 10.9 constructors show how
bootstrap distribution plus uniform square integrability imply these moment
premises, and how finite bootstrap replications estimate this conditional
variance. -/
theorem chapter10_bootstrap_variance_consistency_of_moment_convergence
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {m m₂ : ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanReal Pstar Zstar) atTop (fun _ => m))
    (hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentReal Pstar Zstar) atTop
        (fun _ => m₂)) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
      (fun _ => m₂ - m ^ 2) := by
  have hmean_sq :
      TendstoInMeasure μ
        (fun n ω => bootstrapMeanReal Pstar Zstar n ω *
          bootstrapMeanReal Pstar Zstar n ω)
        atTop (fun _ => m * m) :=
    TendstoInMeasure.mul_limits_real hmean hmean
  have hsecond0 := TendstoInMeasure.sub_limit_zero_real hsecond
  have hmean_sq0 := TendstoInMeasure.sub_limit_zero_real hmean_sq
  have hdiff0 :
      TendstoInMeasure μ
        (fun n ω =>
          (bootstrapSecondMomentReal Pstar Zstar n ω -
            bootstrapMeanReal Pstar Zstar n ω *
              bootstrapMeanReal Pstar Zstar n ω) -
            (m₂ - m * m))
        atTop (fun _ => 0) := by
    have hsub := TendstoInMeasure.sub_zero_real hsecond0 hmean_sq0
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hsub
    refine ae_of_all μ fun ω => ?_
    ring
  have hdiff :
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapSecondMomentReal Pstar Zstar n ω -
            bootstrapMeanReal Pstar Zstar n ω *
              bootstrapMeanReal Pstar Zstar n ω)
        atTop (fun _ => m₂ - m * m) :=
    TendstoInMeasure.of_sub_limit_zero_real hdiff0
  have hvar :
      TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
        (fun _ => m₂ - m * m) := by
    refine TendstoInMeasure.congr
      (f := fun n ω =>
        bootstrapSecondMomentReal Pstar Zstar n ω -
          bootstrapMeanReal Pstar Zstar n ω *
            bootstrapMeanReal Pstar Zstar n ω)
      (f' := bootstrapVarianceReal Pstar Zstar)
      (g := fun _ : Ω => m₂ - m * m)
      (g' := fun _ : Ω => m₂ - m * m)
      (fun n => ?_) EventuallyEq.rfl hdiff
    refine ae_of_all μ fun ω => ?_
    rw [bootstrapVarianceReal_eq_secondMoment_sub_mean_sq hPstar hZ]
    ring
  simpa [pow_two] using hvar

/-- Indexed Hansen Theorem 10.9, variance-consistency moment bridge. -/
theorem chapter10_indexed_bootstrap_variance_consistency_of_moment_convergence
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    {m m₂ : ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanRealIndexed Pstar Zstar) atTop
        (fun _ => m))
    (hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentRealIndexed Pstar Zstar) atTop
        (fun _ => m₂)) :
    TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
      (fun _ => m₂ - m ^ 2) := by
  have hmean_sq :
      TendstoInMeasure μ
        (fun n ω => bootstrapMeanRealIndexed Pstar Zstar n ω *
          bootstrapMeanRealIndexed Pstar Zstar n ω)
        atTop (fun _ => m * m) :=
    TendstoInMeasure.mul_limits_real hmean hmean
  have hsecond0 := TendstoInMeasure.sub_limit_zero_real hsecond
  have hmean_sq0 := TendstoInMeasure.sub_limit_zero_real hmean_sq
  have hdiff0 :
      TendstoInMeasure μ
        (fun n ω =>
          (bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
            bootstrapMeanRealIndexed Pstar Zstar n ω *
              bootstrapMeanRealIndexed Pstar Zstar n ω) -
            (m₂ - m * m))
        atTop (fun _ => 0) := by
    have hsub := TendstoInMeasure.sub_zero_real hsecond0 hmean_sq0
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hsub
    refine ae_of_all μ fun ω => ?_
    ring
  have hdiff :
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
            bootstrapMeanRealIndexed Pstar Zstar n ω *
              bootstrapMeanRealIndexed Pstar Zstar n ω)
        atTop (fun _ => m₂ - m * m) :=
    TendstoInMeasure.of_sub_limit_zero_real hdiff0
  have hvar :
      TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
        (fun _ => m₂ - m * m) := by
    refine TendstoInMeasure.congr
      (f := fun n ω =>
        bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
          bootstrapMeanRealIndexed Pstar Zstar n ω *
            bootstrapMeanRealIndexed Pstar Zstar n ω)
      (f' := bootstrapVarianceRealIndexed Pstar Zstar)
      (g := fun _ : Ω => m₂ - m * m)
      (g' := fun _ : Ω => m₂ - m * m)
      (fun n => ?_) EventuallyEq.rfl hdiff
    refine ae_of_all μ fun ω => ?_
    rw [bootstrapVarianceRealIndexed_eq_secondMoment_sub_mean_sq hPstar hZ]
    ring
  simpa [pow_two] using hvar

/-- Hansen Theorem 10.10, smooth-function variance-consistency wrapper.

In the smooth-function model, Hansen's bounded-derivative argument is used to
prove uniform square integrability and hence the conditional first/second
moment convergence premises. Once those moment premises are available, the
untrimmed bootstrap variance consistency conclusion is exactly the Theorem
10.9 moment bridge. -/
theorem chapter10_smooth_bootstrap_variance_consistency_of_moment_convergence
    {Pstar : ℕ → Ω → Measure Ωs} {ZthetaStar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (ZthetaStar n ω) 2 (Pstar n ω))
    {m m₂ : ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanReal Pstar ZthetaStar) atTop
        (fun _ => m))
    (hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentReal Pstar ZthetaStar) atTop
        (fun _ => m₂)) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar ZthetaStar) atTop
      (fun _ => m₂ - m ^ 2) :=
  chapter10_bootstrap_variance_consistency_of_moment_convergence
    hPstar hZ hmean hsecond

/-- Hansen Theorem 10.9, weak-distribution plus UI/tail variance bridge.

Bootstrap weak convergence gives clipped first and second moment convergence.
If the supplied clipping-tail controls remove the clipping, the conditional
bootstrap variance converges to the variance functional of the limit law. -/
theorem chapter10_bootstrap_variance_consistency_of_weak_distribution_realClip_tails
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailMean : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapMeanReal Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
        atTop (fun _ => 0))
    (hTailSecond : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapSecondMomentReal Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) := by
  have hmean :
      TendstoInMeasure μ (bootstrapMeanReal Pstar Zstar) atTop
        (fun _ => ∫ ωlim, Z ωlim ∂ν) := by
    simpa [bootstrapMeanReal] using
      hweak.integral_tendsto_of_realClip_tails hTailMean
  have hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentReal Pstar Zstar) atTop
        (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) := by
    simpa [bootstrapSecondMomentReal] using
      hweak.integral_sq_tendsto_of_realClip_tails hTailSecond
  exact chapter10_bootstrap_variance_consistency_of_moment_convergence
    hPstar hZmem hmean hsecond

/-- Indexed Hansen Theorem 10.9, weak-distribution plus UI/tail variance
bridge. -/
theorem chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_realClip_tails
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailMean : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapMeanRealIndexed Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
        atTop (fun _ => 0))
    (hTailSecond : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) := by
  have hmean :
      TendstoInMeasure μ (bootstrapMeanRealIndexed Pstar Zstar) atTop
        (fun _ => ∫ ωlim, Z ωlim ∂ν) := by
    simpa [bootstrapMeanRealIndexed] using
      hweak.integral_tendsto_of_realClip_tails hTailMean
  have hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentRealIndexed Pstar Zstar) atTop
        (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) := by
    simpa [bootstrapSecondMomentRealIndexed] using
      hweak.integral_sq_tendsto_of_realClip_tails hTailSecond
  exact chapter10_indexed_bootstrap_variance_consistency_of_moment_convergence
    hPstar hZmem hmean hsecond

/-- Hansen Theorem 10.9, weak-distribution plus concrete tail-integral
variance bridge.

This packages the clipping-tail premises of
`chapter10_bootstrap_variance_consistency_of_weak_distribution_realClip_tails`
from conditional first- and second-tail integral controls.  Uniform square
integrability supplies those tail-integral controls in the textbook proof. -/
theorem chapter10_bootstrap_variance_consistency_of_weak_distribution_tail_integrals
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailMean : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => |Z ωlim|) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω)
        atTop (fun _ => 0))
    (hTailSecond : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstarInt : ∀ n ω, Integrable (Zstar n ω) (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    exact memLp_one_iff_integrable.mp ((hZmem n ω).mono_exponent one_le_two)
  have hZlimInt : Integrable Z ν :=
    memLp_one_iff_integrable.mp (hZlim.mono_exponent one_le_two)
  exact chapter10_bootstrap_variance_consistency_of_weak_distribution_realClip_tails
    (μ := μ) (ν := ν) hPstar hZmem hweak
    (bootstrapMeanReal_realClip_tails_of_tail_integrals
      (μ := μ) (ν := ν) hPstarFinite hZlimInt hZstarInt hTailMean)
    (bootstrapSecondMomentReal_realClip_tails_of_tail_integrals
      (μ := μ) (ν := ν) hPstarFinite hZlim hZmem hTailSecond)

/-- Hansen Theorem 10.9, weak-distribution plus squared-tail-integral
variance bridge.

For thresholds at least one, squared tails dominate absolute tails.  Thus a
single uniform-square-tail control supplies both the first- and second-tail
integral premises needed for conditional bootstrap variance consistency. -/
theorem chapter10_bootstrap_variance_consistency_of_weak_distribution_square_tail_integrals
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailSq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hTailMean : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => |Z ωlim|) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω)
        atTop (fun _ => 0) := by
    intro ε hε
    obtain ⟨R, hR_one, hlimSq, hsourceSq⟩ := hTailSq ε hε
    have hR_nonneg : 0 ≤ R := zero_le_one.trans hR_one
    refine ⟨R, hR_nonneg, ?_, ?_⟩
    · have hlimAbsLe :=
        integral_tail_abs_le_integral_tail_sq_of_one_le
          (μ := ν) (Y := Z) hZlim hR_one
      exact hlimAbsLe.trans hlimSq
    · exact bootstrapTailAbsIntegral_tendsto_zero_of_tailSqIntegral
        (μ := μ) hPstarFinite hZmem hR_one hsourceSq
  have hTailSecond : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
        atTop (fun _ => 0) := by
    intro ε hε
    obtain ⟨R, hR_one, hlimSq, hsourceSq⟩ := hTailSq ε hε
    exact ⟨R, zero_le_one.trans hR_one, hlimSq, hsourceSq⟩
  exact chapter10_bootstrap_variance_consistency_of_weak_distribution_tail_integrals
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailMean hTailSecond

/-- Textbook-style uniform square-tail condition for Hansen Theorem 10.9.

For every tolerance, a threshold can be chosen so that the limit squared tail is
small and the corresponding conditional bootstrap squared tail is small in
probability.  This is the conditional two-probability-space form of uniform
square integrability used by the theorem-facing Chapter 10 variance wrapper. -/
def BootstrapUniformSquareTail
    (μ : Measure Ω) (Pstar : ℕ → Ω → Measure Ωs)
    (Zstar : ℕ → Ω → Ωs → ℝ) (ν : Measure Ωlim) (Z : Ωlim → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
    (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
      (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
    Tendsto
      (fun n =>
        μ {ω |
          ε ≤ dist
            (∫ ωs,
              Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
            0})
      atTop (𝓝 0)

/-- Hansen Theorem 10.9 conditional mean convergence from weak convergence and
uniform square-tail control.

This is one of the two conditional moment conclusions used by the variance
consistency bridge.  Squared-tail control supplies the first-moment clipping
error because thresholds are chosen at least one. -/
theorem chapter10_bootstrap_mean_tendsto_of_weak_distribution_uniform_square_tail
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailSq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (∫ ωs,
                Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                  (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ (bootstrapMeanReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, Z ωlim ∂ν) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstarInt : ∀ n ω, Integrable (Zstar n ω) (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    exact memLp_one_iff_integrable.mp ((hZmem n ω).mono_exponent one_le_two)
  have hZlimInt : Integrable Z ν :=
    memLp_one_iff_integrable.mp (hZlim.mono_exponent one_le_two)
  have hTailMeanProb : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (bootstrapMeanReal Pstar Zstar n ω -
                (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
              0})
        atTop (𝓝 0) := by
    intro ε hε
    obtain ⟨R, hR_one, hlimSq, hsourceSq⟩ := hTailSq (ε / 2) (by positivity)
    have hR_nonneg : 0 ≤ R := zero_le_one.trans hR_one
    refine ⟨R, hR_nonneg, ?_, ?_⟩
    · have hlimAbsLe :=
        integral_tail_abs_le_integral_tail_sq_of_one_le
          (μ := ν) (Y := Z) hZlim hR_one
      have hclip :=
        abs_integral_sub_realClip_le_two_mul_integral_tail_abs
          (μ := ν) (Y := Z) hZlimInt hR_nonneg
      calc
        |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤
            2 * ∫ ωlim,
              Set.indicator {ωlim | R ≤ |Z ωlim|}
                (fun ωlim => |Z ωlim|) ωlim ∂ν := hclip
        _ ≤ 2 * ∫ ωlim,
              Set.indicator {ωlim | R ≤ |Z ωlim|}
                (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν := by nlinarith
        _ ≤ 2 * (ε / 2) := by nlinarith
        _ = ε := by ring
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        hsourceSq (fun _ => zero_le _) ?_
      intro n
      refine measure_mono ?_
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      let tailSq : ℝ :=
        ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω
      have htailSq_nonneg : 0 ≤ tailSq := by
        dsimp [tailSq]
        exact integral_nonneg fun ωs =>
          Set.indicator_nonneg (fun ωs _ => sq_nonneg (Zstar n ω ωs)) ωs
      have hboundMean :=
        bootstrapMeanReal_abs_sub_realClip_le_two_mul_integral_tail_abs
          hPstarFinite hZstarInt hR_nonneg n ω
      have htailAbsLe :
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω ≤ tailSq := by
        haveI : IsFiniteMeasure (Pstar n ω) := hPstarFinite n ω
        exact integral_tail_abs_le_integral_tail_sq_of_one_le
          (μ := Pstar n ω) (Y := Zstar n ω) (hZmem n ω) hR_one
      have hdist_mean :
          ε ≤
            |bootstrapMeanReal Pstar Zstar n ω -
              (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]| := by
        simpa [Real.dist_eq] using hω
      have htail_ge : ε / 2 ≤ tailSq := by nlinarith
      simpa [tailSq, Real.dist_eq, abs_of_nonneg htailSq_nonneg] using htail_ge
  simpa [bootstrapMeanReal] using
    hweak.integral_tendsto_of_realClip_tailProb hTailMeanProb

/-- Hansen Theorem 10.9 conditional second-moment convergence from weak
convergence and uniform square-tail control.

This is the second conditional moment conclusion used by the variance
consistency bridge. -/
theorem chapter10_bootstrap_secondMoment_tendsto_of_weak_distribution_uniform_square_tail
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailSq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (∫ ωs,
                Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                  (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ (bootstrapSecondMomentReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hTailSecondProb : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (bootstrapSecondMomentReal Pstar Zstar n ω -
                (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
              0})
        atTop (𝓝 0) := by
    intro ε hε
    obtain ⟨R, hR_one, hlimSq, hsourceSq⟩ := hTailSq (ε / 2) (by positivity)
    have hR_nonneg : 0 ≤ R := zero_le_one.trans hR_one
    refine ⟨R, hR_nonneg, ?_, ?_⟩
    · have hclip :=
        abs_integral_sq_sub_realClip_sq_le_two_mul_integral_tail_sq
          (μ := ν) (Y := Z) hZlim hR_nonneg
      calc
        |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
            ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤
            2 * ∫ ωlim,
              Set.indicator {ωlim | R ≤ |Z ωlim|}
                (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν := hclip
        _ ≤ 2 * (ε / 2) := by nlinarith
        _ = ε := by ring
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        hsourceSq (fun _ => zero_le _) ?_
      intro n
      refine measure_mono ?_
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      let tailSq : ℝ :=
        ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω
      have htailSq_nonneg : 0 ≤ tailSq := by
        dsimp [tailSq]
        exact integral_nonneg fun ωs =>
          Set.indicator_nonneg (fun ωs _ => sq_nonneg (Zstar n ω ωs)) ωs
      have hboundSecond :=
        bootstrapSecondMomentReal_abs_sub_realClip_sq_le_two_mul_integral_tail_sq
          hPstarFinite hZmem hR_nonneg n ω
      have hdist_second :
          ε ≤
            |bootstrapSecondMomentReal Pstar Zstar n ω -
              (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]| := by
        simpa [Real.dist_eq] using hω
      have htail_ge : ε / 2 ≤ tailSq := by nlinarith
      simpa [tailSq, Real.dist_eq, abs_of_nonneg htailSq_nonneg] using htail_ge
  simpa [bootstrapSecondMomentReal] using
    hweak.integral_sq_tendsto_of_realClip_tailProb hTailSecondProb

/-- Hansen Theorem 10.9 conditional mean convergence from the named
uniform-square-tail condition package. -/
theorem chapter10_bootstrap_mean_tendsto_of_weak_distribution_of_uniformSquareTail
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTail μ Pstar Zstar ν Z) :
    TendstoInMeasure μ (bootstrapMeanReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, Z ωlim ∂ν) :=
  chapter10_bootstrap_mean_tendsto_of_weak_distribution_uniform_square_tail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail

/-- Hansen Theorem 10.9 conditional second-moment convergence from the named
uniform-square-tail condition package. -/
theorem chapter10_bootstrap_secondMoment_tendsto_of_weak_distribution_of_uniformSquareTail
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTail μ Pstar Zstar ν Z) :
    TendstoInMeasure μ (bootstrapSecondMomentReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) :=
  chapter10_bootstrap_secondMoment_tendsto_of_weak_distribution_uniform_square_tail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail

/-- Hansen Theorem 10.9, weak-distribution plus uniform-square-tail variance
bridge.

This is the theorem-facing uniform-integrability assembly: for every tolerance
one chooses a large threshold whose squared tail is small for the limit law and
small in probability for the conditional bootstrap law. -/
theorem chapter10_bootstrap_variance_consistency_of_weak_distribution_uniform_square_tail
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailSq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (∫ ωs,
                Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                  (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) := by
  have hmean :
      TendstoInMeasure μ (bootstrapMeanReal Pstar Zstar) atTop
        (fun _ => ∫ ωlim, Z ωlim ∂ν) :=
    chapter10_bootstrap_mean_tendsto_of_weak_distribution_uniform_square_tail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailSq
  have hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentReal Pstar Zstar) atTop
        (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) :=
    chapter10_bootstrap_secondMoment_tendsto_of_weak_distribution_uniform_square_tail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailSq
  exact chapter10_bootstrap_variance_consistency_of_moment_convergence
    hPstar hZmem hmean hsecond

/-- Hansen Theorem 10.9 from a named uniform-square-tail condition.

This is the public theorem-facing wrapper: bootstrap weak convergence plus
`BootstrapUniformSquareTail` gives conditional bootstrap variance consistency. -/
theorem chapter10_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
    [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTail μ Pstar Zstar ν Z) :
    TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_bootstrap_variance_consistency_of_weak_distribution_uniform_square_tail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail

/-- Indexed textbook-style uniform square-tail condition for Hansen Theorem
10.9.

This is the sample-size-dependent bootstrap-space version of
`BootstrapUniformSquareTail`: for every tolerance, one threshold makes the
limit squared tail small and makes the corresponding indexed conditional
bootstrap squared tail small in probability. -/
def BootstrapUniformSquareTailIndexed
    (μ : Measure Ω) {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → ℝ) (ν : Measure Ωlim)
    (Z : Ωlim → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
    (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
      (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
    Tendsto
      (fun n =>
        μ {ω |
          ε ≤ dist
            (∫ ωs,
              Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
            0})
      atTop (𝓝 0)

/-- Indexed Hansen Theorem 10.9 conditional mean convergence from weak
convergence and uniform square-tail control. -/
theorem chapter10_indexed_bootstrap_mean_tendsto_of_weak_distribution_uniform_square_tail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailSq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (∫ ωs,
                Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                  (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ (bootstrapMeanRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, Z ωlim ∂ν) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstarInt : ∀ n ω, Integrable (Zstar n ω) (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    exact memLp_one_iff_integrable.mp ((hZmem n ω).mono_exponent one_le_two)
  have hZlimInt : Integrable Z ν :=
    memLp_one_iff_integrable.mp (hZlim.mono_exponent one_le_two)
  have hTailMeanProb : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (bootstrapMeanRealIndexed Pstar Zstar n ω -
                (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)])
              0})
        atTop (𝓝 0) := by
    intro ε hε
    obtain ⟨R, hR_one, hlimSq, hsourceSq⟩ := hTailSq (ε / 2) (by positivity)
    have hR_nonneg : 0 ≤ R := zero_le_one.trans hR_one
    refine ⟨R, hR_nonneg, ?_, ?_⟩
    · have hlimAbsLe :=
        integral_tail_abs_le_integral_tail_sq_of_one_le
          (μ := ν) (Y := Z) hZlim hR_one
      have hclip :=
        abs_integral_sub_realClip_le_two_mul_integral_tail_abs
          (μ := ν) (Y := Z) hZlimInt hR_nonneg
      calc
        |(∫ ωlim, Z ωlim ∂ν) - ∫ ωlim, realClip R (Z ωlim) ∂ν| ≤
            2 * ∫ ωlim,
              Set.indicator {ωlim | R ≤ |Z ωlim|}
                (fun ωlim => |Z ωlim|) ωlim ∂ν := hclip
        _ ≤ 2 * ∫ ωlim,
              Set.indicator {ωlim | R ≤ |Z ωlim|}
                (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν := by nlinarith
        _ ≤ 2 * (ε / 2) := by nlinarith
        _ = ε := by ring
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        hsourceSq (fun _ => zero_le _) ?_
      intro n
      refine measure_mono ?_
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      let tailSq : ℝ :=
        ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω
      have htailSq_nonneg : 0 ≤ tailSq := by
        dsimp [tailSq]
        exact integral_nonneg fun ωs =>
          Set.indicator_nonneg (fun ωs _ => sq_nonneg (Zstar n ω ωs)) ωs
      have hboundMean :
          |bootstrapMeanRealIndexed Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]| ≤
            2 * ∫ ωs,
              Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω := by
        haveI : IsFiniteMeasure (Pstar n ω) := hPstarFinite n ω
        simpa [bootstrapMeanRealIndexed] using
          abs_integral_sub_realClip_le_two_mul_integral_tail_abs
            (μ := Pstar n ω) (Y := Zstar n ω) (hZstarInt n ω) hR_nonneg
      have htailAbsLe :
          ∫ ωs,
            Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
              (fun ωs => |Zstar n ω ωs|) ωs ∂Pstar n ω ≤ tailSq := by
        haveI : IsFiniteMeasure (Pstar n ω) := hPstarFinite n ω
        exact integral_tail_abs_le_integral_tail_sq_of_one_le
          (μ := Pstar n ω) (Y := Zstar n ω) (hZmem n ω) hR_one
      have hdist_mean :
          ε ≤
            |bootstrapMeanRealIndexed Pstar Zstar n ω -
              (Pstar n ω)[fun ωs => realClip R (Zstar n ω ωs)]| := by
        simpa [Real.dist_eq] using hω
      have htail_ge : ε / 2 ≤ tailSq := by nlinarith
      simpa [tailSq, Real.dist_eq, abs_of_nonneg htailSq_nonneg] using htail_ge
  simpa [bootstrapMeanRealIndexed] using
    hweak.integral_tendsto_of_realClip_tailProb hTailMeanProb

/-- Indexed Hansen Theorem 10.9 conditional second-moment convergence from
weak convergence and uniform square-tail control. -/
theorem chapter10_indexed_bootstrap_secondMoment_tendsto_of_weak_distribution_uniform_square_tail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailSq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (∫ ωs,
                Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                  (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ (bootstrapSecondMomentRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hTailSecondProb : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 ≤ R ∧
      |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
          ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
                (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2])
              0})
        atTop (𝓝 0) := by
    intro ε hε
    obtain ⟨R, hR_one, hlimSq, hsourceSq⟩ := hTailSq (ε / 2) (by positivity)
    have hR_nonneg : 0 ≤ R := zero_le_one.trans hR_one
    refine ⟨R, hR_nonneg, ?_, ?_⟩
    · have hclip :=
        abs_integral_sq_sub_realClip_sq_le_two_mul_integral_tail_sq
          (μ := ν) (Y := Z) hZlim hR_nonneg
      calc
        |(∫ ωlim, (Z ωlim) ^ 2 ∂ν) -
            ∫ ωlim, (realClip R (Z ωlim)) ^ 2 ∂ν| ≤
            2 * ∫ ωlim,
              Set.indicator {ωlim | R ≤ |Z ωlim|}
                (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν := hclip
        _ ≤ 2 * (ε / 2) := by nlinarith
        _ = ε := by ring
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        hsourceSq (fun _ => zero_le _) ?_
      intro n
      refine measure_mono ?_
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      let tailSq : ℝ :=
        ∫ ωs,
          Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
            (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω
      have htailSq_nonneg : 0 ≤ tailSq := by
        dsimp [tailSq]
        exact integral_nonneg fun ωs =>
          Set.indicator_nonneg (fun ωs _ => sq_nonneg (Zstar n ω ωs)) ωs
      have hboundSecond :
          |bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
            (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]| ≤
            2 * ∫ ωs,
              Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω := by
        haveI : IsFiniteMeasure (Pstar n ω) := hPstarFinite n ω
        simpa [bootstrapSecondMomentRealIndexed] using
          abs_integral_sq_sub_realClip_sq_le_two_mul_integral_tail_sq
            (μ := Pstar n ω) (Y := Zstar n ω) (hZmem n ω) hR_nonneg
      have hdist_second :
          ε ≤
            |bootstrapSecondMomentRealIndexed Pstar Zstar n ω -
              (Pstar n ω)[fun ωs => (realClip R (Zstar n ω ωs)) ^ 2]| := by
        simpa [Real.dist_eq] using hω
      have htail_ge : ε / 2 ≤ tailSq := by nlinarith
      simpa [tailSq, Real.dist_eq, abs_of_nonneg htailSq_nonneg] using htail_ge
  simpa [bootstrapSecondMomentRealIndexed] using
    hweak.integral_sq_tendsto_of_realClip_tailProb hTailSecondProb

/-- Indexed Hansen Theorem 10.9 conditional mean convergence from the named
uniform-square-tail condition package. -/
theorem chapter10_indexed_bootstrap_mean_tendsto_of_weak_distribution_of_uniformSquareTail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z) :
    TendstoInMeasure μ (bootstrapMeanRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, Z ωlim ∂ν) :=
  chapter10_indexed_bootstrap_mean_tendsto_of_weak_distribution_uniform_square_tail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail

/-- Indexed Hansen Theorem 10.9 conditional second-moment convergence from the
named uniform-square-tail condition package. -/
theorem chapter10_indexed_bootstrap_secondMoment_tendsto_of_weak_distribution_of_uniformSquareTail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z) :
    TendstoInMeasure μ (bootstrapSecondMomentRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) :=
  chapter10_indexed_bootstrap_secondMoment_tendsto_of_weak_distribution_uniform_square_tail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail

/-- Indexed Hansen Theorem 10.9, weak-distribution plus uniform-square-tail
variance bridge. -/
theorem chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_uniform_square_tail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailSq : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
        (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε ∧
      Tendsto
        (fun n =>
          μ {ω |
            ε ≤ dist
              (∫ ωs,
                Set.indicator {ωs | R ≤ |Zstar n ω ωs|}
                  (fun ωs => (Zstar n ω ωs) ^ 2) ωs ∂Pstar n ω)
              0})
        atTop (𝓝 0)) :
    TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) := by
  have hmean :
      TendstoInMeasure μ (bootstrapMeanRealIndexed Pstar Zstar) atTop
        (fun _ => ∫ ωlim, Z ωlim ∂ν) :=
    chapter10_indexed_bootstrap_mean_tendsto_of_weak_distribution_uniform_square_tail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailSq
  have hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentRealIndexed Pstar Zstar) atTop
        (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν) :=
    chapter10_indexed_bootstrap_secondMoment_tendsto_of_weak_distribution_uniform_square_tail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailSq
  exact chapter10_indexed_bootstrap_variance_consistency_of_moment_convergence
    hPstar hZmem hmean hsecond

/-- Indexed Hansen Theorem 10.9 from a named uniform-square-tail condition. -/
theorem chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ} {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z) :
    TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_uniform_square_tail
    (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail

end BootstrapVariance

section BootstrapCovariance

/-- Conditional bootstrap mean vector of a finite-dimensional statistic. -/
noncomputable def bootstrapMeanVec
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → k → ℝ)
    (n : ℕ) (ω : Ω) : k → ℝ :=
  fun a => (Pstar n ω)[fun ωs => Zstar n ω ωs a]

/-- Conditional bootstrap cross-moment matrix of a finite-dimensional statistic. -/
noncomputable def bootstrapCrossMomentMat
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → k → ℝ)
    (n : ℕ) (ω : Ω) : Matrix k k ℝ :=
  fun a c => (Pstar n ω)[fun ωs => Zstar n ω ωs a * Zstar n ω ωs c]

/-- Moment-form conditional bootstrap covariance matrix. -/
noncomputable def bootstrapCovarianceMomentMat
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → k → ℝ)
    (n : ℕ) (ω : Ω) : Matrix k k ℝ :=
  fun a c =>
    bootstrapCrossMomentMat Pstar Zstar n ω a c -
      bootstrapMeanVec Pstar Zstar n ω a * bootstrapMeanVec Pstar Zstar n ω c

/-- Conditional bootstrap covariance matrix, stated directly with `cov`. -/
noncomputable def bootstrapCovarianceMat
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → k → ℝ)
    (n : ℕ) (ω : Ω) : Matrix k k ℝ :=
  fun a c => cov[fun ωs => Zstar n ω ωs a,
    fun ωs => Zstar n ω ωs c; Pstar n ω]

/-- Conditional covariance equals the moment-form covariance matrix. -/
theorem bootstrapCovarianceMat_eq_momentMat
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (n : ℕ) (ω : Ω) :
    bootstrapCovarianceMat Pstar Zstar n ω =
      bootstrapCovarianceMomentMat Pstar Zstar n ω := by
  ext a c
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  simpa [bootstrapCovarianceMat, bootstrapCovarianceMomentMat, bootstrapCrossMomentMat,
    bootstrapMeanVec, Pi.mul_apply] using
    (ProbabilityTheory.covariance_eq_sub (hZ n ω a) (hZ n ω c))

/-- Indexed conditional bootstrap mean vector of a finite-dimensional statistic. -/
noncomputable def bootstrapMeanVecIndexed
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → k → ℝ)
    (n : ℕ) (ω : Ω) : k → ℝ :=
  fun a => (Pstar n ω)[fun ωs => Zstar n ω ωs a]

/-- Indexed conditional bootstrap cross-moment matrix of a finite-dimensional
statistic. -/
noncomputable def bootstrapCrossMomentMatIndexed
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → k → ℝ)
    (n : ℕ) (ω : Ω) : Matrix k k ℝ :=
  fun a c => (Pstar n ω)[fun ωs => Zstar n ω ωs a * Zstar n ω ωs c]

/-- Indexed moment-form conditional bootstrap covariance matrix. -/
noncomputable def bootstrapCovarianceMomentMatIndexed
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → k → ℝ)
    (n : ℕ) (ω : Ω) : Matrix k k ℝ :=
  fun a c =>
    bootstrapCrossMomentMatIndexed Pstar Zstar n ω a c -
      bootstrapMeanVecIndexed Pstar Zstar n ω a *
        bootstrapMeanVecIndexed Pstar Zstar n ω c

/-- Indexed conditional bootstrap covariance matrix, stated directly with
`cov`. -/
noncomputable def bootstrapCovarianceMatIndexed
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → k → ℝ)
    (n : ℕ) (ω : Ω) : Matrix k k ℝ :=
  fun a c => cov[fun ωs => Zstar n ω ωs a,
    fun ωs => Zstar n ω ωs c; Pstar n ω]

/-- Indexed conditional covariance equals the moment-form covariance matrix. -/
theorem bootstrapCovarianceMatIndexed_eq_momentMat
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (n : ℕ) (ω : Ω) :
    bootstrapCovarianceMatIndexed Pstar Zstar n ω =
      bootstrapCovarianceMomentMatIndexed Pstar Zstar n ω := by
  ext a c
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  simpa [bootstrapCovarianceMatIndexed, bootstrapCovarianceMomentMatIndexed,
    bootstrapCrossMomentMatIndexed, bootstrapMeanVecIndexed, Pi.mul_apply] using
      (ProbabilityTheory.covariance_eq_sub (hZ n ω a) (hZ n ω c))

/-- Hansen Theorem 10.9 finite-dimensional mean-vector wrapper.

Bootstrap weak convergence of the vector statistic plus the named
uniform-square-tail condition on each coordinate implies convergence in
probability of the conditional bootstrap mean vector.  This is the
coordinatewise vector surface used by the covariance and trimmed-variance
layers, where the textbook proofs first establish scalar uniform
square-integrability for every coordinate. -/
theorem chapter10_bootstrap_meanVec_tendsto_of_weak_distribution_of_uniformSquareTail
    [Fintype k] [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail :
      ∀ a,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs => Zstar n ω ωs a) ν
          (fun ωlim => Z ωlim a)) :
    TendstoInMeasure μ (bootstrapMeanVec Pstar Zstar) atTop
      (fun _ => fun a => ∫ ωlim, Z ωlim a ∂ν) := by
  refine tendstoInMeasure_pi (fun a => ?_)
  have hweak_a :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => Zstar n ω ωs a) ν
        (fun ωlim => Z ωlim a) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := fun z : k → ℝ => z a) hweak (continuous_apply a)
  simpa [bootstrapMeanVec, bootstrapMeanReal] using
    chapter10_bootstrap_mean_tendsto_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) (Pstar := Pstar)
      (Zstar := fun n ω ωs => Zstar n ω ωs a)
      (Z := fun ωlim => Z ωlim a)
      hPstar (fun n ω => hZmem n ω a) (hZlim a) hweak_a (hTail a)

private theorem integral_mul_eq_half_integral_add_sq_sub_sq
    {P : Measure Ωs} {X Y : Ωs → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    ∫ ωs, X ωs * Y ωs ∂P =
      ((∫ ωs, (X ωs + Y ωs) ^ 2 ∂P) -
        (∫ ωs, (X ωs) ^ 2 ∂P) -
        (∫ ωs, (Y ωs) ^ 2 ∂P)) / 2 := by
  let S : Ωs → ℝ := fun ωs => (X ωs + Y ωs) ^ 2
  let A : Ωs → ℝ := fun ωs => (X ωs) ^ 2
  let C : Ωs → ℝ := fun ωs => (Y ωs) ^ 2
  have hA : Integrable A P := by
    dsimp [A]
    exact hX.integrable_sq
  have hC : Integrable C P := by
    dsimp [C]
    exact hY.integrable_sq
  have hS : Integrable S P := by
    dsimp [S]
    exact (hX.add hY).integrable_sq
  calc
    ∫ ωs, X ωs * Y ωs ∂P =
        ∫ ωs, (S ωs - A ωs - C ωs) / 2 ∂P := by
          refine integral_congr_ae ?_
          exact ae_of_all P fun ωs => by
            dsimp [S, A, C]
            ring
    _ = (∫ ωs, (S - A - C) ωs ∂P) / 2 := by
          rw [integral_div]
          have hInt :
              ∫ ωs, S ωs - A ωs - C ωs ∂P =
                ∫ ωs, (S - A - C) ωs ∂P := by
            refine integral_congr_ae ?_
            exact ae_of_all P fun ωs => by simp [Pi.sub_apply]
          exact congrArg (fun t : ℝ => t / 2) hInt
    _ = ((∫ ωs, S ωs ∂P) - (∫ ωs, A ωs ∂P) - (∫ ωs, C ωs ∂P)) / 2 := by
          have hintegral :
              ∫ ωs, (S - A - C) ωs ∂P =
                (∫ ωs, S ωs ∂P) - (∫ ωs, A ωs ∂P) -
                  (∫ ωs, C ωs ∂P) := by
            calc
              ∫ ωs, (S - A - C) ωs ∂P =
                  ∫ ωs, ((S - A) - C) ωs ∂P := by
                    refine integral_congr_ae ?_
                    exact ae_of_all P fun ωs => by simp [Pi.sub_apply]
              _ = (∫ ωs, (S - A) ωs ∂P) - (∫ ωs, C ωs ∂P) :=
                    integral_sub (hS.sub hA) hC
              _ =
                  ((∫ ωs, S ωs ∂P) - (∫ ωs, A ωs ∂P)) -
                    (∫ ωs, C ωs ∂P) := by
                    have hSA :
                        ∫ ωs, (S - A) ωs ∂P =
                          (∫ ωs, S ωs ∂P) - (∫ ωs, A ωs ∂P) := by
                      simpa [Pi.sub_apply] using integral_sub hS hA
                    exact congrArg (fun t => t - ∫ ωs, C ωs ∂P) hSA
              _ =
                  (∫ ωs, S ωs ∂P) - (∫ ωs, A ωs ∂P) -
                    (∫ ωs, C ωs ∂P) := by ring
          rw [hintegral]
    _ =
        ((∫ ωs, (X ωs + Y ωs) ^ 2 ∂P) -
          (∫ ωs, (X ωs) ^ 2 ∂P) -
          (∫ ωs, (Y ωs) ^ 2 ∂P)) / 2 := by
          rfl

/-- Hansen Theorem 10.9 finite-dimensional cross-moment wrapper.

Bootstrap weak convergence plus named uniform-square-tail conditions for each
coordinate and each coordinate sum imply convergence in probability of the
conditional bootstrap cross-moment matrix. The proof uses
`xy = ((x + y)^2 - x^2 - y^2) / 2`, so model-specific layers can verify scalar
square-tail conditions rather than developing a separate product-tail API. -/
theorem chapter10_bootstrap_crossMomentMat_tendsto_of_weak_distribution_of_uniformSquareTail
    [Fintype k] [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailCoord :
      ∀ a,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs => Zstar n ω ωs a) ν
          (fun ωlim => Z ωlim a))
    (hTailSum :
      ∀ a c,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) ν
          (fun ωlim => Z ωlim a + Z ωlim c)) :
    TendstoInMeasure μ (bootstrapCrossMomentMat Pstar Zstar) atTop
      (fun _ => fun a c => ∫ ωlim, Z ωlim a * Z ωlim c ∂ν) := by
  refine tendstoInMeasure_pi (fun a => ?_)
  refine tendstoInMeasure_pi (fun c => ?_)
  have hweak_a :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => Zstar n ω ωs a) ν
        (fun ωlim => Z ωlim a) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := fun z : k → ℝ => z a) hweak (continuous_apply a)
  have hweak_c :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => Zstar n ω ωs c) ν
        (fun ωlim => Z ωlim c) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := fun z : k → ℝ => z c) hweak (continuous_apply c)
  have hweak_sum :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) ν
        (fun ωlim => Z ωlim a + Z ωlim c) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := fun z : k → ℝ => z a + z c) hweak
      ((continuous_apply a).add (continuous_apply c))
  have hsecond_a :
      TendstoInMeasure μ
        (bootstrapSecondMomentReal Pstar
          (fun n ω ωs => Zstar n ω ωs a))
        atTop (fun _ => ∫ ωlim, (Z ωlim a) ^ 2 ∂ν) :=
    chapter10_bootstrap_secondMoment_tendsto_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) (Pstar := Pstar)
      (Zstar := fun n ω ωs => Zstar n ω ωs a)
      (Z := fun ωlim => Z ωlim a)
      hPstar (fun n ω => hZmem n ω a) (hZlim a) hweak_a (hTailCoord a)
  have hsecond_c :
      TendstoInMeasure μ
        (bootstrapSecondMomentReal Pstar
          (fun n ω ωs => Zstar n ω ωs c))
        atTop (fun _ => ∫ ωlim, (Z ωlim c) ^ 2 ∂ν) :=
    chapter10_bootstrap_secondMoment_tendsto_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) (Pstar := Pstar)
      (Zstar := fun n ω ωs => Zstar n ω ωs c)
      (Z := fun ωlim => Z ωlim c)
      hPstar (fun n ω => hZmem n ω c) (hZlim c) hweak_c (hTailCoord c)
  have hsecond_sum :
      TendstoInMeasure μ
        (bootstrapSecondMomentReal Pstar
          (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c))
        atTop
          (fun _ => ∫ ωlim, (Z ωlim a + Z ωlim c) ^ 2 ∂ν) :=
    chapter10_bootstrap_secondMoment_tendsto_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) (Pstar := Pstar)
      (Zstar := fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c)
      (Z := fun ωlim => Z ωlim a + Z ωlim c)
      hPstar
      (fun n ω => (hZmem n ω a).add (hZmem n ω c))
      ((hZlim a).add (hZlim c)) hweak_sum (hTailSum a c)
  have hcenter0 :
      TendstoInMeasure μ
        (fun n ω =>
          ((bootstrapSecondMomentReal Pstar
              (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) n ω -
              ∫ ωlim, (Z ωlim a + Z ωlim c) ^ 2 ∂ν) -
            (bootstrapSecondMomentReal Pstar
              (fun n ω ωs => Zstar n ω ωs a) n ω -
              ∫ ωlim, (Z ωlim a) ^ 2 ∂ν)) -
            (bootstrapSecondMomentReal Pstar
              (fun n ω ωs => Zstar n ω ωs c) n ω -
              ∫ ωlim, (Z ωlim c) ^ 2 ∂ν))
        atTop (fun _ => 0) :=
    TendstoInMeasure.sub_zero_real
      (TendstoInMeasure.sub_zero_real
        (TendstoInMeasure.sub_limit_zero_real hsecond_sum)
        (TendstoInMeasure.sub_limit_zero_real hsecond_a))
      (TendstoInMeasure.sub_limit_zero_real hsecond_c)
  have hhalf0 :
      TendstoInMeasure μ
        (fun n ω =>
          (1 / 2 : ℝ) *
            (((bootstrapSecondMomentReal Pstar
                (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) n ω -
                ∫ ωlim, (Z ωlim a + Z ωlim c) ^ 2 ∂ν) -
              (bootstrapSecondMomentReal Pstar
                (fun n ω ωs => Zstar n ω ωs a) n ω -
                ∫ ωlim, (Z ωlim a) ^ 2 ∂ν)) -
              (bootstrapSecondMomentReal Pstar
                (fun n ω ωs => Zstar n ω ωs c) n ω -
                ∫ ωlim, (Z ωlim c) ^ 2 ∂ν)))
        atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real (μ := μ) (1 / 2 : ℝ) hcenter0
  have hcross0 :
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapCrossMomentMat Pstar Zstar n ω a c -
            ∫ ωlim, Z ωlim a * Z ωlim c ∂ν)
        atTop (fun _ => 0) := by
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hhalf0
    refine ae_of_all μ fun ω => ?_
    have hboot :
        bootstrapCrossMomentMat Pstar Zstar n ω a c =
          ((bootstrapSecondMomentReal Pstar
              (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) n ω) -
            (bootstrapSecondMomentReal Pstar
              (fun n ω ωs => Zstar n ω ωs a) n ω) -
            (bootstrapSecondMomentReal Pstar
              (fun n ω ωs => Zstar n ω ωs c) n ω)) / 2 := by
      simpa [bootstrapCrossMomentMat, bootstrapSecondMomentReal] using
        integral_mul_eq_half_integral_add_sq_sub_sq
          (P := Pstar n ω)
          (X := fun ωs => Zstar n ω ωs a)
          (Y := fun ωs => Zstar n ω ωs c)
          (hZmem n ω a) (hZmem n ω c)
    have hlim :
        ∫ ωlim, Z ωlim a * Z ωlim c ∂ν =
          ((∫ ωlim, (Z ωlim a + Z ωlim c) ^ 2 ∂ν) -
            (∫ ωlim, (Z ωlim a) ^ 2 ∂ν) -
            (∫ ωlim, (Z ωlim c) ^ 2 ∂ν)) / 2 := by
      simpa using
        integral_mul_eq_half_integral_add_sq_sub_sq
          (P := ν)
          (X := fun ωlim => Z ωlim a)
          (Y := fun ωlim => Z ωlim c)
          (hZlim a) (hZlim c)
    change
      (1 / 2 : ℝ) *
        ((bootstrapSecondMomentReal Pstar
              (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) n ω -
            ∫ ωlim, (Z ωlim a + Z ωlim c) ^ 2 ∂ν -
          (bootstrapSecondMomentReal Pstar
              (fun n ω ωs => Zstar n ω ωs a) n ω -
            ∫ ωlim, (Z ωlim a) ^ 2 ∂ν)) -
          (bootstrapSecondMomentReal Pstar
              (fun n ω ωs => Zstar n ω ωs c) n ω -
            ∫ ωlim, (Z ωlim c) ^ 2 ∂ν)) =
        bootstrapCrossMomentMat Pstar Zstar n ω a c -
          ∫ ωlim, Z ωlim a * Z ωlim c ∂ν
    rw [hboot, hlim]
    ring
  simpa [bootstrapCrossMomentMat] using
    TendstoInMeasure.of_sub_limit_zero_real hcross0

/-- Conditional bootstrap covariance moment bridge for two real coordinates. -/
theorem chapter10_bootstrap_covarianceReal_tendsto_of_moments
    {Pstar : ℕ → Ω → Measure Ωs} {Xstar Ystar : ℕ → Ω → Ωs → ℝ}
    {mX mY mXY : ℝ}
    (hmeanX :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[Xstar n ω])
        atTop (fun _ => mX))
    (hmeanY :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[Ystar n ω])
        atTop (fun _ => mY))
    (hcross :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs])
        atTop (fun _ => mXY)) :
    TendstoInMeasure μ
      (fun n ω =>
        (Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs] -
          (Pstar n ω)[Xstar n ω] * (Pstar n ω)[Ystar n ω])
      atTop (fun _ => mXY - mX * mY) := by
  have hmean_prod :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω)[Xstar n ω] * (Pstar n ω)[Ystar n ω])
        atTop (fun _ => mX * mY) :=
    TendstoInMeasure.mul_limits_real hmeanX hmeanY
  have hcross0 := TendstoInMeasure.sub_limit_zero_real hcross
  have hmean_prod0 := TendstoInMeasure.sub_limit_zero_real hmean_prod
  have hdiff0 :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs] -
            (Pstar n ω)[Xstar n ω] * (Pstar n ω)[Ystar n ω]) -
            (mXY - mX * mY))
        atTop (fun _ => 0) := by
    have hsub := TendstoInMeasure.sub_zero_real hcross0 hmean_prod0
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hsub
    exact ae_of_all μ fun ω => by ring
  exact TendstoInMeasure.of_sub_limit_zero_real hdiff0

/-- Indexed conditional bootstrap covariance moment bridge for two real
coordinates. -/
theorem chapter10_indexed_bootstrap_covarianceReal_tendsto_of_moments
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ}
    {mX mY mXY : ℝ}
    (hmeanX :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[Xstar n ω])
        atTop (fun _ => mX))
    (hmeanY :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[Ystar n ω])
        atTop (fun _ => mY))
    (hcross :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs])
        atTop (fun _ => mXY)) :
    TendstoInMeasure μ
      (fun n ω =>
        (Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs] -
          (Pstar n ω)[Xstar n ω] * (Pstar n ω)[Ystar n ω])
      atTop (fun _ => mXY - mX * mY) := by
  have hmean_prod :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω)[Xstar n ω] * (Pstar n ω)[Ystar n ω])
        atTop (fun _ => mX * mY) :=
    TendstoInMeasure.mul_limits_real hmeanX hmeanY
  have hcross0 := TendstoInMeasure.sub_limit_zero_real hcross
  have hmean_prod0 := TendstoInMeasure.sub_limit_zero_real hmean_prod
  have hdiff0 :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs] -
            (Pstar n ω)[Xstar n ω] * (Pstar n ω)[Ystar n ω]) -
            (mXY - mX * mY))
        atTop (fun _ => 0) := by
    have hsub := TendstoInMeasure.sub_zero_real hcross0 hmean_prod0
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hsub
    exact ae_of_all μ fun ω => by ring
  exact TendstoInMeasure.of_sub_limit_zero_real hdiff0

/-- Conditional bootstrap covariance-matrix bridge from mean-vector and
cross-moment convergence. -/
theorem chapter10_bootstrap_covarianceMomentMat_tendsto_of_moments
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanVec Pstar Zstar) atTop (fun _ => m))
    (hcross :
      TendstoInMeasure μ (bootstrapCrossMomentMat Pstar Zstar) atTop
        (fun _ => M₂)) :
    TendstoInMeasure μ (bootstrapCovarianceMomentMat Pstar Zstar) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) := by
  refine tendstoInMeasure_pi (fun a => ?_)
  refine tendstoInMeasure_pi (fun c => ?_)
  have hentry :=
    chapter10_bootstrap_covarianceReal_tendsto_of_moments
      (μ := μ)
      (Pstar := Pstar)
      (Xstar := fun n ω ωs => Zstar n ω ωs a)
      (Ystar := fun n ω ωs => Zstar n ω ωs c)
      (mX := m a) (mY := m c) (mXY := M₂ a c)
      (by
        simpa [bootstrapMeanVec] using
          TendstoInMeasure.pi_apply hmean a)
      (by
        simpa [bootstrapMeanVec] using
          TendstoInMeasure.pi_apply hmean c)
      (by
        simpa [bootstrapCrossMomentMat] using
          TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hcross a) c)
  simpa [bootstrapCovarianceMomentMat, bootstrapMeanVec, bootstrapCrossMomentMat]
    using hentry

/-- Indexed conditional bootstrap covariance-matrix bridge from mean-vector and
cross-moment convergence. -/
theorem chapter10_indexed_bootstrap_covarianceMomentMat_tendsto_of_moments
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanVecIndexed Pstar Zstar) atTop
        (fun _ => m))
    (hcross :
      TendstoInMeasure μ (bootstrapCrossMomentMatIndexed Pstar Zstar) atTop
        (fun _ => M₂)) :
    TendstoInMeasure μ (bootstrapCovarianceMomentMatIndexed Pstar Zstar)
      atTop (fun _ => fun a c => M₂ a c - m a * m c) := by
  refine tendstoInMeasure_pi (fun a => ?_)
  refine tendstoInMeasure_pi (fun c => ?_)
  have hentry :=
    chapter10_indexed_bootstrap_covarianceReal_tendsto_of_moments
      (μ := μ)
      (Pstar := Pstar)
      (Xstar := fun n ω ωs => Zstar n ω ωs a)
      (Ystar := fun n ω ωs => Zstar n ω ωs c)
      (mX := m a) (mY := m c) (mXY := M₂ a c)
      (by
        simpa [bootstrapMeanVecIndexed] using
          TendstoInMeasure.pi_apply hmean a)
      (by
        simpa [bootstrapMeanVecIndexed] using
          TendstoInMeasure.pi_apply hmean c)
      (by
        simpa [bootstrapCrossMomentMatIndexed] using
          TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hcross a) c)
  simpa [bootstrapCovarianceMomentMatIndexed, bootstrapMeanVecIndexed,
    bootstrapCrossMomentMatIndexed] using hentry

/-- Zero-mean conditional bootstrap covariance-moment matrix bridge.

When the conditional bootstrap mean vector converges to zero, convergence of
the conditional cross-moment matrix targets the covariance matrix directly. -/
theorem chapter10_bootstrap_covarianceMomentMat_tendsto_of_zero_mean_moments
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {V : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanVec Pstar Zstar)
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ (bootstrapCrossMomentMat Pstar Zstar)
        atTop (fun _ => V)) :
    TendstoInMeasure μ (bootstrapCovarianceMomentMat Pstar Zstar)
      atTop (fun _ => V) := by
  simpa using
    (chapter10_bootstrap_covarianceMomentMat_tendsto_of_moments
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
      (m := fun _ : k => 0) (M₂ := V) hmean hcross)

/-- Indexed zero-mean conditional bootstrap covariance-moment matrix bridge. -/
theorem chapter10_indexed_bootstrap_covarianceMomentMat_tendsto_of_zero_mean_moments
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {V : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanVecIndexed Pstar Zstar)
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ (bootstrapCrossMomentMatIndexed Pstar Zstar)
        atTop (fun _ => V)) :
    TendstoInMeasure μ (bootstrapCovarianceMomentMatIndexed Pstar Zstar)
      atTop (fun _ => V) := by
  simpa using
    (chapter10_indexed_bootstrap_covarianceMomentMat_tendsto_of_moments
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
      (m := fun _ : k => 0) (M₂ := V) hmean hcross)

/-- Conditional bootstrap covariance matrix bridge, stated for `cov`. -/
theorem chapter10_bootstrap_covarianceMat_tendsto_of_moments
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanVec Pstar Zstar) atTop (fun _ => m))
    (hcross :
      TendstoInMeasure μ (bootstrapCrossMomentMat Pstar Zstar) atTop
        (fun _ => M₂)) :
    TendstoInMeasure μ (bootstrapCovarianceMat Pstar Zstar) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) := by
  have hmoment :=
    chapter10_bootstrap_covarianceMomentMat_tendsto_of_moments
      (μ := μ) hmean hcross
  refine TendstoInMeasure.congr
    (f := bootstrapCovarianceMomentMat Pstar Zstar)
    (f' := bootstrapCovarianceMat Pstar Zstar)
    (g := fun _ : Ω => fun a c => M₂ a c - m a * m c)
    (g' := fun _ : Ω => fun a c => M₂ a c - m a * m c)
    (fun n => ?_) EventuallyEq.rfl hmoment
  exact ae_of_all μ fun ω =>
    (bootstrapCovarianceMat_eq_momentMat
      (Pstar := Pstar) (Zstar := Zstar) hPstar hZ n ω).symm

/-- Indexed conditional bootstrap covariance matrix bridge, stated for `cov`. -/
theorem chapter10_indexed_bootstrap_covarianceMat_tendsto_of_moments
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanVecIndexed Pstar Zstar) atTop
        (fun _ => m))
    (hcross :
      TendstoInMeasure μ (bootstrapCrossMomentMatIndexed Pstar Zstar) atTop
        (fun _ => M₂)) :
    TendstoInMeasure μ (bootstrapCovarianceMatIndexed Pstar Zstar) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) := by
  have hmoment :=
    chapter10_indexed_bootstrap_covarianceMomentMat_tendsto_of_moments
      (μ := μ) hmean hcross
  refine TendstoInMeasure.congr
    (f := bootstrapCovarianceMomentMatIndexed Pstar Zstar)
    (f' := bootstrapCovarianceMatIndexed Pstar Zstar)
    (g := fun _ : Ω => fun a c => M₂ a c - m a * m c)
    (g' := fun _ : Ω => fun a c => M₂ a c - m a * m c)
    (fun n => ?_) EventuallyEq.rfl hmoment
  exact ae_of_all μ fun ω =>
    (bootstrapCovarianceMatIndexed_eq_momentMat
      (Pstar := Pstar) (Zstar := Zstar) hPstar hZ n ω).symm

/-- Zero-mean conditional bootstrap covariance-matrix bridge, stated for
`cov`.

This is the Theorem 10.12/10.19 covariance target in the asymptotically
centered case: zero conditional means plus cross-moment convergence imply
conditional bootstrap covariance convergence to `V`. -/
theorem chapter10_bootstrap_covarianceMat_tendsto_of_zero_mean_moments
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    {V : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanVec Pstar Zstar)
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ (bootstrapCrossMomentMat Pstar Zstar)
        atTop (fun _ => V)) :
    TendstoInMeasure μ (bootstrapCovarianceMat Pstar Zstar)
      atTop (fun _ => V) := by
  simpa using
    (chapter10_bootstrap_covarianceMat_tendsto_of_moments
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
      hPstar hZ (m := fun _ : k => 0) (M₂ := V) hmean hcross)

/-- Indexed zero-mean conditional bootstrap covariance-matrix bridge, stated
for `cov`. -/
theorem chapter10_indexed_bootstrap_covarianceMat_tendsto_of_zero_mean_moments
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    {V : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ (bootstrapMeanVecIndexed Pstar Zstar)
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ (bootstrapCrossMomentMatIndexed Pstar Zstar)
        atTop (fun _ => V)) :
    TendstoInMeasure μ (bootstrapCovarianceMatIndexed Pstar Zstar)
      atTop (fun _ => V) := by
  simpa using
    (chapter10_indexed_bootstrap_covarianceMat_tendsto_of_moments
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
      hPstar hZ (m := fun _ : k => 0) (M₂ := V) hmean hcross)

/-- Hansen Theorem 10.9/10.12 covariance matrix from bootstrap weak
convergence and scalar uniform-square-tail controls.

Coordinatewise named uniform-square-tail assumptions give the conditional mean
vector, while named uniform-square-tail assumptions for each coordinate sum
give the cross-moment matrix through the polarization identity. The covariance
target is therefore the limit cross moment minus the outer product of the limit
mean vector. -/
theorem chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
    [Fintype k] [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailCoord :
      ∀ a,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs => Zstar n ω ωs a) ν
          (fun ωlim => Z ωlim a))
    (hTailSum :
      ∀ a c,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) ν
          (fun ωlim => Z ωlim a + Z ωlim c)) :
    TendstoInMeasure μ (bootstrapCovarianceMat Pstar Zstar) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_bootstrap_covarianceMat_tendsto_of_moments
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
    hPstar hZmem
    (chapter10_bootstrap_meanVec_tendsto_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailCoord)
    (chapter10_bootstrap_crossMomentMat_tendsto_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailCoord hTailSum)

/-- Indexed Hansen Theorem 10.9 finite-dimensional mean-vector wrapper.

This is the sample-size-dependent counterpart of
`chapter10_bootstrap_meanVec_tendsto_of_weak_distribution_of_uniformSquareTail`. -/
theorem chapter10_indexed_bootstrap_meanVec_tendsto_of_weak_distribution_of_uniformSquareTail
    [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail :
      ∀ a,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs => Zstar n ω ωs a) ν
          (fun ωlim => Z ωlim a)) :
    TendstoInMeasure μ (bootstrapMeanVecIndexed Pstar Zstar) atTop
      (fun _ => fun a => ∫ ωlim, Z ωlim a ∂ν) := by
  refine tendstoInMeasure_pi (fun a => ?_)
  have hweak_a :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => Zstar n ω ωs a) ν
        (fun ωlim => Z ωlim a) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := fun z : k → ℝ => z a) hweak (continuous_apply a)
  simpa [bootstrapMeanVecIndexed, bootstrapMeanRealIndexed] using
    chapter10_indexed_bootstrap_mean_tendsto_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) (Pstar := Pstar)
      (Zstar := fun n ω ωs => Zstar n ω ωs a)
      (Z := fun ωlim => Z ωlim a)
      hPstar (fun n ω => hZmem n ω a) (hZlim a) hweak_a (hTail a)

/-- Indexed Hansen Theorem 10.9 finite-dimensional cross-moment wrapper.

Coordinate and coordinate-sum indexed uniform-square-tail conditions identify
the conditional cross moments by the same polarization identity as the
fixed-space theorem. -/
theorem
    chapter10_indexed_bootstrap_crossMomentMat_tendsto_of_weak_distribution_of_uniformSquareTail
    [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailCoord :
      ∀ a,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs => Zstar n ω ωs a) ν
          (fun ωlim => Z ωlim a))
    (hTailSum :
      ∀ a c,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) ν
          (fun ωlim => Z ωlim a + Z ωlim c)) :
    TendstoInMeasure μ (bootstrapCrossMomentMatIndexed Pstar Zstar) atTop
      (fun _ => fun a c => ∫ ωlim, Z ωlim a * Z ωlim c ∂ν) := by
  refine tendstoInMeasure_pi (fun a => ?_)
  refine tendstoInMeasure_pi (fun c => ?_)
  have hweak_a :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => Zstar n ω ωs a) ν
        (fun ωlim => Z ωlim a) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := fun z : k → ℝ => z a) hweak (continuous_apply a)
  have hweak_c :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => Zstar n ω ωs c) ν
        (fun ωlim => Z ωlim c) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := fun z : k → ℝ => z c) hweak (continuous_apply c)
  have hweak_sum :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) ν
        (fun ωlim => Z ωlim a + Z ωlim c) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      (g := fun z : k → ℝ => z a + z c) hweak
      ((continuous_apply a).add (continuous_apply c))
  have hsecond_a :
      TendstoInMeasure μ
        (bootstrapSecondMomentRealIndexed Pstar
          (fun n ω ωs => Zstar n ω ωs a))
        atTop (fun _ => ∫ ωlim, (Z ωlim a) ^ 2 ∂ν) :=
    chapter10_indexed_bootstrap_secondMoment_tendsto_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) (Pstar := Pstar)
      (Zstar := fun n ω ωs => Zstar n ω ωs a)
      (Z := fun ωlim => Z ωlim a)
      hPstar (fun n ω => hZmem n ω a) (hZlim a) hweak_a (hTailCoord a)
  have hsecond_c :
      TendstoInMeasure μ
        (bootstrapSecondMomentRealIndexed Pstar
          (fun n ω ωs => Zstar n ω ωs c))
        atTop (fun _ => ∫ ωlim, (Z ωlim c) ^ 2 ∂ν) :=
    chapter10_indexed_bootstrap_secondMoment_tendsto_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) (Pstar := Pstar)
      (Zstar := fun n ω ωs => Zstar n ω ωs c)
      (Z := fun ωlim => Z ωlim c)
      hPstar (fun n ω => hZmem n ω c) (hZlim c) hweak_c (hTailCoord c)
  have hsecond_sum :
      TendstoInMeasure μ
        (bootstrapSecondMomentRealIndexed Pstar
          (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c))
        atTop
          (fun _ => ∫ ωlim, (Z ωlim a + Z ωlim c) ^ 2 ∂ν) :=
    chapter10_indexed_bootstrap_secondMoment_tendsto_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) (Pstar := Pstar)
      (Zstar := fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c)
      (Z := fun ωlim => Z ωlim a + Z ωlim c)
      hPstar
      (fun n ω => (hZmem n ω a).add (hZmem n ω c))
      ((hZlim a).add (hZlim c)) hweak_sum (hTailSum a c)
  have hcenter0 :
      TendstoInMeasure μ
        (fun n ω =>
          ((bootstrapSecondMomentRealIndexed Pstar
              (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) n ω -
              ∫ ωlim, (Z ωlim a + Z ωlim c) ^ 2 ∂ν) -
            (bootstrapSecondMomentRealIndexed Pstar
              (fun n ω ωs => Zstar n ω ωs a) n ω -
              ∫ ωlim, (Z ωlim a) ^ 2 ∂ν)) -
            (bootstrapSecondMomentRealIndexed Pstar
              (fun n ω ωs => Zstar n ω ωs c) n ω -
              ∫ ωlim, (Z ωlim c) ^ 2 ∂ν))
        atTop (fun _ => 0) :=
    TendstoInMeasure.sub_zero_real
      (TendstoInMeasure.sub_zero_real
        (TendstoInMeasure.sub_limit_zero_real hsecond_sum)
        (TendstoInMeasure.sub_limit_zero_real hsecond_a))
      (TendstoInMeasure.sub_limit_zero_real hsecond_c)
  have hhalf0 :
      TendstoInMeasure μ
        (fun n ω =>
          (1 / 2 : ℝ) *
            (((bootstrapSecondMomentRealIndexed Pstar
                (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) n ω -
                ∫ ωlim, (Z ωlim a + Z ωlim c) ^ 2 ∂ν) -
              (bootstrapSecondMomentRealIndexed Pstar
                (fun n ω ωs => Zstar n ω ωs a) n ω -
                ∫ ωlim, (Z ωlim a) ^ 2 ∂ν)) -
              (bootstrapSecondMomentRealIndexed Pstar
                (fun n ω ωs => Zstar n ω ωs c) n ω -
                ∫ ωlim, (Z ωlim c) ^ 2 ∂ν)))
        atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real (μ := μ) (1 / 2 : ℝ) hcenter0
  have hcross0 :
      TendstoInMeasure μ
        (fun n ω =>
          bootstrapCrossMomentMatIndexed Pstar Zstar n ω a c -
            ∫ ωlim, Z ωlim a * Z ωlim c ∂ν)
        atTop (fun _ => 0) := by
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hhalf0
    refine ae_of_all μ fun ω => ?_
    have hboot :
        bootstrapCrossMomentMatIndexed Pstar Zstar n ω a c =
          ((bootstrapSecondMomentRealIndexed Pstar
              (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) n ω) -
            (bootstrapSecondMomentRealIndexed Pstar
              (fun n ω ωs => Zstar n ω ωs a) n ω) -
            (bootstrapSecondMomentRealIndexed Pstar
              (fun n ω ωs => Zstar n ω ωs c) n ω)) / 2 := by
      simpa [bootstrapCrossMomentMatIndexed, bootstrapSecondMomentRealIndexed] using
        integral_mul_eq_half_integral_add_sq_sub_sq
          (P := Pstar n ω)
          (X := fun ωs => Zstar n ω ωs a)
          (Y := fun ωs => Zstar n ω ωs c)
          (hZmem n ω a) (hZmem n ω c)
    have hlim :
        ∫ ωlim, Z ωlim a * Z ωlim c ∂ν =
          ((∫ ωlim, (Z ωlim a + Z ωlim c) ^ 2 ∂ν) -
            (∫ ωlim, (Z ωlim a) ^ 2 ∂ν) -
            (∫ ωlim, (Z ωlim c) ^ 2 ∂ν)) / 2 := by
      simpa using
        integral_mul_eq_half_integral_add_sq_sub_sq
          (P := ν)
          (X := fun ωlim => Z ωlim a)
          (Y := fun ωlim => Z ωlim c)
          (hZlim a) (hZlim c)
    change
      (1 / 2 : ℝ) *
        ((bootstrapSecondMomentRealIndexed Pstar
              (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) n ω -
            ∫ ωlim, (Z ωlim a + Z ωlim c) ^ 2 ∂ν -
          (bootstrapSecondMomentRealIndexed Pstar
              (fun n ω ωs => Zstar n ω ωs a) n ω -
            ∫ ωlim, (Z ωlim a) ^ 2 ∂ν)) -
          (bootstrapSecondMomentRealIndexed Pstar
              (fun n ω ωs => Zstar n ω ωs c) n ω -
            ∫ ωlim, (Z ωlim c) ^ 2 ∂ν)) =
        bootstrapCrossMomentMatIndexed Pstar Zstar n ω a c -
          ∫ ωlim, Z ωlim a * Z ωlim c ∂ν
    rw [hboot, hlim]
    ring
  simpa [bootstrapCrossMomentMatIndexed] using
    TendstoInMeasure.of_sub_limit_zero_real hcross0

/-- Indexed Hansen Theorem 10.9/10.12 covariance matrix from bootstrap weak
convergence and scalar indexed uniform-square-tail controls. -/
theorem chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
    [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailCoord :
      ∀ a,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs => Zstar n ω ωs a) ν
          (fun ωlim => Z ωlim a))
    (hTailSum :
      ∀ a c,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) ν
          (fun ωlim => Z ωlim a + Z ωlim c)) :
    TendstoInMeasure μ (bootstrapCovarianceMatIndexed Pstar Zstar) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_bootstrap_covarianceMat_tendsto_of_moments
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
    hPstar hZmem
    (chapter10_indexed_bootstrap_meanVec_tendsto_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailCoord)
    (chapter10_indexed_bootstrap_crossMomentMat_tendsto_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailCoord hTailSum)

/-- Hansen's trimmed bootstrap statistic `Z** = Z* 1{‖Z*‖ ≤ τ}`. -/
noncomputable def trimmedBootstrapStatistic
    {k : Type*} [Fintype k]
    (Zstar : ℕ → Ω → Ωs → k → ℝ) (τ : ℕ → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Ωs) : k → ℝ :=
  if ‖Zstar n ω ωs‖ ≤ τ n then Zstar n ω ωs else 0

/-- Conditional covariance matrix of Hansen's trimmed bootstrap statistic. -/
noncomputable def trimmedBootstrapCovarianceMat
    {k : Type*} [Fintype k]
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → k → ℝ)
    (τ : ℕ → ℝ) (n : ℕ) (ω : Ω) : Matrix k k ℝ :=
  bootstrapCovarianceMat Pstar (trimmedBootstrapStatistic Zstar τ) n ω

/-- Indexed Hansen trimmed bootstrap statistic `Z** = Z* 1{‖Z*‖ ≤ τ}` for
sample-size-dependent bootstrap spaces. -/
noncomputable def trimmedBootstrapStatisticIndexed
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*}
    (Zstar : ∀ n, Ω → Ωboot n → k → ℝ) (τ : ℕ → ℝ)
    (n : ℕ) (ω : Ω) (ωs : Ωboot n) : k → ℝ :=
  if ‖Zstar n ω ωs‖ ≤ τ n then Zstar n ω ωs else 0

/-- The norm of Hansen's trimmed bootstrap statistic is bounded by
`max (τ n) 0` pointwise. -/
theorem norm_trimmedBootstrapStatistic_le_max
    {k : Type*} [Fintype k]
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω) (ωs : Ωs) :
    ‖trimmedBootstrapStatistic Zstar τ n ω ωs‖ ≤ max (τ n) 0 := by
  by_cases htrim : ‖Zstar n ω ωs‖ ≤ τ n
  · have hle : ‖Zstar n ω ωs‖ ≤ max (τ n) 0 :=
      htrim.trans (le_max_left _ _)
    simp [trimmedBootstrapStatistic, htrim, hle]
  · simp [trimmedBootstrapStatistic, htrim]

/-- If the trimming threshold is nonnegative, Hansen's trimmed bootstrap
statistic has norm bounded by that threshold pointwise. -/
theorem norm_trimmedBootstrapStatistic_le_of_nonneg
    {k : Type*} [Fintype k]
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) (ω : Ω) (ωs : Ωs) :
    ‖trimmedBootstrapStatistic Zstar τ n ω ωs‖ ≤ τ n :=
  (norm_trimmedBootstrapStatistic_le_max (Zstar := Zstar) (τ := τ) n ω ωs).trans
    (max_le le_rfl hτ)

/-- Coordinate bound for Hansen's trimmed bootstrap statistic. -/
theorem abs_trimmedBootstrapStatistic_apply_le_of_nonneg
    {k : Type*} [Fintype k]
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) (ω : Ω) (ωs : Ωs) (a : k) :
    |trimmedBootstrapStatistic Zstar τ n ω ωs a| ≤ τ n := by
  simpa [Real.norm_eq_abs] using
    (norm_le_pi_norm (trimmedBootstrapStatistic Zstar τ n ω ωs) a).trans
      (norm_trimmedBootstrapStatistic_le_of_nonneg
        (Zstar := Zstar) (τ := τ) hτ ω ωs)

/-- Squared coordinate bound for Hansen's trimmed bootstrap statistic. -/
theorem sq_trimmedBootstrapStatistic_apply_le_sq_of_nonneg
    {k : Type*} [Fintype k]
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) (ω : Ω) (ωs : Ωs) (a : k) :
    (trimmedBootstrapStatistic Zstar τ n ω ωs a) ^ 2 ≤ (τ n) ^ 2 :=
  sq_le_sq.mpr (by
    simpa [abs_of_nonneg hτ] using
      abs_trimmedBootstrapStatistic_apply_le_of_nonneg
        (Zstar := Zstar) (τ := τ) hτ ω ωs a)

/-- Coordinate-sum bound for Hansen's trimmed bootstrap statistic. -/
theorem abs_add_trimmedBootstrapStatistic_apply_le_two_mul_of_nonneg
    {k : Type*} [Fintype k]
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) (ω : Ω) (ωs : Ωs) (a c : k) :
    |trimmedBootstrapStatistic Zstar τ n ω ωs a +
      trimmedBootstrapStatistic Zstar τ n ω ωs c| ≤ 2 * τ n := by
  have ha :=
    abs_trimmedBootstrapStatistic_apply_le_of_nonneg
      (Zstar := Zstar) (τ := τ) hτ ω ωs a
  have hc :=
    abs_trimmedBootstrapStatistic_apply_le_of_nonneg
      (Zstar := Zstar) (τ := τ) hτ ω ωs c
  calc
    |trimmedBootstrapStatistic Zstar τ n ω ωs a +
        trimmedBootstrapStatistic Zstar τ n ω ωs c| ≤
        |trimmedBootstrapStatistic Zstar τ n ω ωs a| +
          |trimmedBootstrapStatistic Zstar τ n ω ωs c| :=
      abs_add_le _ _
    _ ≤ τ n + τ n := add_le_add ha hc
    _ = 2 * τ n := by ring

/-- Squared coordinate-sum bound for Hansen's trimmed bootstrap statistic. -/
theorem sq_add_trimmedBootstrapStatistic_apply_le_sq_two_mul_of_nonneg
    {k : Type*} [Fintype k]
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) (ω : Ω) (ωs : Ωs) (a c : k) :
    (trimmedBootstrapStatistic Zstar τ n ω ωs a +
      trimmedBootstrapStatistic Zstar τ n ω ωs c) ^ 2 ≤ (2 * τ n) ^ 2 :=
  sq_le_sq.mpr (by
    have h2τ : 0 ≤ 2 * τ n := mul_nonneg (by norm_num) hτ
    simpa [abs_of_nonneg h2τ] using
      abs_add_trimmedBootstrapStatistic_apply_le_two_mul_of_nonneg
        (Zstar := Zstar) (τ := τ) hτ ω ωs a c)

/-- Coordinate-product bound for Hansen's trimmed bootstrap statistic. -/
theorem abs_mul_trimmedBootstrapStatistic_apply_le_sq_of_nonneg
    {k : Type*} [Fintype k]
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) (ω : Ω) (ωs : Ωs) (a c : k) :
    |trimmedBootstrapStatistic Zstar τ n ω ωs a *
      trimmedBootstrapStatistic Zstar τ n ω ωs c| ≤ (τ n) ^ 2 := by
  have ha :=
    abs_trimmedBootstrapStatistic_apply_le_of_nonneg
      (Zstar := Zstar) (τ := τ) hτ ω ωs a
  have hc :=
    abs_trimmedBootstrapStatistic_apply_le_of_nonneg
      (Zstar := Zstar) (τ := τ) hτ ω ωs c
  calc
    |trimmedBootstrapStatistic Zstar τ n ω ωs a *
        trimmedBootstrapStatistic Zstar τ n ω ωs c| =
        |trimmedBootstrapStatistic Zstar τ n ω ωs a| *
          |trimmedBootstrapStatistic Zstar τ n ω ωs c| := abs_mul _ _
    _ ≤ τ n * τ n := mul_le_mul ha hc (abs_nonneg _) hτ
    _ = (τ n) ^ 2 := by ring

/-- The coordinate squared tail of a trimmed statistic is zero above the trim
threshold. -/
theorem integral_tail_sq_trimmedBootstrapStatistic_apply_eq_zero_of_lt
    {k : Type*} [Fintype k]
    {P : Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) {R : ℝ} (hR : τ n < R)
    (ω : Ω) (a : k) :
    (∫ ωs, Set.indicator
      {ωs | R ≤ |trimmedBootstrapStatistic Zstar τ n ω ωs a|}
      (fun ωs => (trimmedBootstrapStatistic Zstar τ n ω ωs a) ^ 2)
      ωs ∂P) = 0 := by
  refine integral_eq_zero_of_ae ?_
  exact ae_of_all P fun ωs => by
    have hcoord :=
      abs_trimmedBootstrapStatistic_apply_le_of_nonneg
        (Zstar := Zstar) (τ := τ) hτ ω ωs a
    have hnotmem :
        ωs ∉
          {x | R ≤ |trimmedBootstrapStatistic Zstar τ n ω x a|} :=
      not_le.mpr (lt_of_le_of_lt hcoord hR)
    rw [Set.indicator_of_notMem hnotmem]
    simp

/-- The coordinate-sum squared tail of a trimmed statistic is zero above twice
the trim threshold. -/
theorem integral_tail_sq_add_trimmedBootstrapStatistic_apply_eq_zero_of_lt
    {k : Type*} [Fintype k]
    {P : Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) {R : ℝ} (hR : 2 * τ n < R)
    (ω : Ω) (a c : k) :
    (∫ ωs, Set.indicator
      {ωs |
        R ≤ |trimmedBootstrapStatistic Zstar τ n ω ωs a +
          trimmedBootstrapStatistic Zstar τ n ω ωs c|}
      (fun ωs =>
        (trimmedBootstrapStatistic Zstar τ n ω ωs a +
          trimmedBootstrapStatistic Zstar τ n ω ωs c) ^ 2)
      ωs ∂P) = 0 := by
  refine integral_eq_zero_of_ae ?_
  exact ae_of_all P fun ωs => by
    have hsum :=
      abs_add_trimmedBootstrapStatistic_apply_le_two_mul_of_nonneg
        (Zstar := Zstar) (τ := τ) hτ ω ωs a c
    have hnotmem :
        ωs ∉
          {x |
            R ≤ |trimmedBootstrapStatistic Zstar τ n ω x a +
              trimmedBootstrapStatistic Zstar τ n ω x c|} :=
      not_le.mpr (lt_of_le_of_lt hsum hR)
    rw [Set.indicator_of_notMem hnotmem]
    simp

/-- A bounded measurable coordinate of Hansen's trimmed bootstrap statistic is
in every finite-measure `Lᵖ` space. -/
theorem memLp_trimmedBootstrapStatistic_apply_of_aestronglyMeasurable_of_nonneg
    {k : Type*} [Fintype k]
    {P : Measure Ωs} [IsFiniteMeasure P]
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) (ω : Ω) (a : k) {p : ℝ≥0∞}
    (hmeas :
      AEStronglyMeasurable
        (fun ωs => trimmedBootstrapStatistic Zstar τ n ω ωs a) P) :
    MemLp (fun ωs => trimmedBootstrapStatistic Zstar τ n ω ωs a) p P :=
  MemLp.of_bound hmeas (τ n) <|
    ae_of_all P fun ωs => by
      simpa [Real.norm_eq_abs] using
        abs_trimmedBootstrapStatistic_apply_le_of_nonneg
          (Zstar := Zstar) (τ := τ) hτ ω ωs a

/-- Indexed version of `norm_trimmedBootstrapStatistic_le_max`. -/
theorem norm_trimmedBootstrapStatisticIndexed_le_max
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω) (ωs : Ωboot n) :
    ‖trimmedBootstrapStatisticIndexed Zstar τ n ω ωs‖ ≤ max (τ n) 0 := by
  by_cases htrim : ‖Zstar n ω ωs‖ ≤ τ n
  · have hle : ‖Zstar n ω ωs‖ ≤ max (τ n) 0 :=
      htrim.trans (le_max_left _ _)
    simp [trimmedBootstrapStatisticIndexed, htrim, hle]
  · simp [trimmedBootstrapStatisticIndexed, htrim]

/-- Indexed pointwise threshold bound for Hansen's trimmed bootstrap statistic. -/
theorem norm_trimmedBootstrapStatisticIndexed_le_of_nonneg
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) (ω : Ω) (ωs : Ωboot n) :
    ‖trimmedBootstrapStatisticIndexed Zstar τ n ω ωs‖ ≤ τ n :=
  (norm_trimmedBootstrapStatisticIndexed_le_max
    (Zstar := Zstar) (τ := τ) n ω ωs).trans
    (max_le le_rfl hτ)

/-- Indexed coordinate bound for Hansen's trimmed bootstrap statistic. -/
theorem abs_trimmedBootstrapStatisticIndexed_apply_le_of_nonneg
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) (ω : Ω) (ωs : Ωboot n) (a : k) :
    |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a| ≤ τ n := by
  simpa [Real.norm_eq_abs] using
    (norm_le_pi_norm (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs) a).trans
      (norm_trimmedBootstrapStatisticIndexed_le_of_nonneg
        (Zstar := Zstar) (τ := τ) hτ ω ωs)

/-- Indexed squared coordinate bound for Hansen's trimmed bootstrap statistic. -/
theorem sq_trimmedBootstrapStatisticIndexed_apply_le_sq_of_nonneg
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) (ω : Ω) (ωs : Ωboot n) (a : k) :
    (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a) ^ 2 ≤ (τ n) ^ 2 :=
  sq_le_sq.mpr (by
    simpa [abs_of_nonneg hτ] using
      abs_trimmedBootstrapStatisticIndexed_apply_le_of_nonneg
        (Zstar := Zstar) (τ := τ) hτ ω ωs a)

/-- Indexed coordinate-sum bound for Hansen's trimmed bootstrap statistic. -/
theorem abs_add_trimmedBootstrapStatisticIndexed_apply_le_two_mul_of_nonneg
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) (ω : Ω) (ωs : Ωboot n) (a c : k) :
    |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a +
      trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c| ≤ 2 * τ n := by
  have ha :=
    abs_trimmedBootstrapStatisticIndexed_apply_le_of_nonneg
      (Zstar := Zstar) (τ := τ) hτ ω ωs a
  have hc :=
    abs_trimmedBootstrapStatisticIndexed_apply_le_of_nonneg
      (Zstar := Zstar) (τ := τ) hτ ω ωs c
  calc
    |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a +
        trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c| ≤
        |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a| +
          |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c| :=
      abs_add_le _ _
    _ ≤ τ n + τ n := add_le_add ha hc
    _ = 2 * τ n := by ring

/-- Indexed squared coordinate-sum bound for Hansen's trimmed bootstrap statistic. -/
theorem sq_add_trimmedBootstrapStatisticIndexed_apply_le_sq_two_mul_of_nonneg
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) (ω : Ω) (ωs : Ωboot n) (a c : k) :
    (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a +
      trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c) ^ 2 ≤
      (2 * τ n) ^ 2 :=
  sq_le_sq.mpr (by
    have h2τ : 0 ≤ 2 * τ n := mul_nonneg (by norm_num) hτ
    simpa [abs_of_nonneg h2τ] using
      abs_add_trimmedBootstrapStatisticIndexed_apply_le_two_mul_of_nonneg
        (Zstar := Zstar) (τ := τ) hτ ω ωs a c)

/-- Indexed coordinate-product bound for Hansen's trimmed bootstrap statistic. -/
theorem abs_mul_trimmedBootstrapStatisticIndexed_apply_le_sq_of_nonneg
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) (ω : Ω) (ωs : Ωboot n) (a c : k) :
    |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a *
      trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c| ≤ (τ n) ^ 2 := by
  have ha :=
    abs_trimmedBootstrapStatisticIndexed_apply_le_of_nonneg
      (Zstar := Zstar) (τ := τ) hτ ω ωs a
  have hc :=
    abs_trimmedBootstrapStatisticIndexed_apply_le_of_nonneg
      (Zstar := Zstar) (τ := τ) hτ ω ωs c
  calc
    |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a *
        trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c| =
        |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a| *
          |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c| := abs_mul _ _
    _ ≤ τ n * τ n := mul_le_mul ha hc (abs_nonneg _) hτ
    _ = (τ n) ^ 2 := by ring

/-- Indexed coordinate squared tail of a trimmed statistic is zero above the
trim threshold. -/
theorem integral_tail_sq_trimmedBootstrapStatisticIndexed_apply_eq_zero_of_lt
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} {P : Measure (Ωboot n)}
    (hτ : 0 ≤ τ n) {R : ℝ} (hR : τ n < R)
    (ω : Ω) (a : k) :
    (∫ ωs, Set.indicator
      {ωs | R ≤ |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a|}
      (fun ωs => (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a) ^ 2)
      ωs ∂P) = 0 := by
  refine integral_eq_zero_of_ae ?_
  exact ae_of_all P fun ωs => by
    have hcoord :=
      abs_trimmedBootstrapStatisticIndexed_apply_le_of_nonneg
        (Zstar := Zstar) (τ := τ) hτ ω ωs a
    have hnotmem :
        ωs ∉
          {x | R ≤ |trimmedBootstrapStatisticIndexed Zstar τ n ω x a|} :=
      not_le.mpr (lt_of_le_of_lt hcoord hR)
    rw [Set.indicator_of_notMem hnotmem]
    simp

/-- Indexed coordinate-sum squared tail of a trimmed statistic is zero above
twice the trim threshold. -/
theorem integral_tail_sq_add_trimmedBootstrapStatisticIndexed_apply_eq_zero_of_lt
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} {P : Measure (Ωboot n)}
    (hτ : 0 ≤ τ n) {R : ℝ} (hR : 2 * τ n < R)
    (ω : Ω) (a c : k) :
    (∫ ωs, Set.indicator
      {ωs |
        R ≤ |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a +
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c|}
      (fun ωs =>
        (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a +
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c) ^ 2)
      ωs ∂P) = 0 := by
  refine integral_eq_zero_of_ae ?_
  exact ae_of_all P fun ωs => by
    have hsum :=
      abs_add_trimmedBootstrapStatisticIndexed_apply_le_two_mul_of_nonneg
        (Zstar := Zstar) (τ := τ) hτ ω ωs a c
    have hnotmem :
        ωs ∉
          {x |
            R ≤ |trimmedBootstrapStatisticIndexed Zstar τ n ω x a +
              trimmedBootstrapStatisticIndexed Zstar τ n ω x c|} :=
      not_le.mpr (lt_of_le_of_lt hsum hR)
    rw [Set.indicator_of_notMem hnotmem]
    simp

/-- Indexed bounded measurable coordinates of Hansen's trimmed bootstrap
statistic are in every finite-measure `Lᵖ` space. -/
theorem
    memLp_trimmedBootstrapStatisticIndexed_apply_of_aestronglyMeasurable_of_nonneg
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} {P : Measure (Ωboot n)} [IsFiniteMeasure P]
    (hτ : 0 ≤ τ n) (ω : Ω) (a : k) {p : ℝ≥0∞}
    (hmeas :
      AEStronglyMeasurable
        (fun ωs => trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a) P) :
    MemLp (fun ωs => trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a) p P :=
  MemLp.of_bound hmeas (τ n) <|
    ae_of_all P fun ωs => by
      simpa [Real.norm_eq_abs] using
        abs_trimmedBootstrapStatisticIndexed_apply_le_of_nonneg
          (Zstar := Zstar) (τ := τ) hτ ω ωs a

/-- Indexed conditional covariance matrix of Hansen's trimmed bootstrap
statistic. -/
noncomputable def trimmedBootstrapCovarianceMatIndexed
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → k → ℝ)
    (τ : ℕ → ℝ) (n : ℕ) (ω : Ω) : Matrix k k ℝ :=
  bootstrapCovarianceMatIndexed Pstar (trimmedBootstrapStatisticIndexed Zstar τ)
    n ω

/-- Hansen Theorem 10.12, trimmed conditional covariance moment bridge.

For the trimmed statistic `Z** = Z* 1{‖Z*‖ ≤ τ}`, convergence of its conditional
mean vector and cross-moment matrix implies convergence of its conditional
covariance matrix.  The smooth-model proof of Theorem 10.12 supplies these
moment premises by showing the trimming is asymptotically negligible and the
trimmed sequence is uniformly square integrable. -/
theorem chapter10_trimmedBootstrapVariance_tendsto_of_moments
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {τ : ℕ → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ :
      ∀ n ω a,
        MemLp (fun ωs => trimmedBootstrapStatistic Zstar τ n ω ωs a) 2
          (Pstar n ω))
    {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ
        (bootstrapMeanVec Pstar (trimmedBootstrapStatistic Zstar τ))
        atTop (fun _ => m))
    (hcross :
      TendstoInMeasure μ
        (bootstrapCrossMomentMat Pstar (trimmedBootstrapStatistic Zstar τ))
        atTop (fun _ => M₂)) :
    TendstoInMeasure μ (trimmedBootstrapCovarianceMat Pstar Zstar τ) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) := by
  simpa [trimmedBootstrapCovarianceMat] using
    chapter10_bootstrap_covarianceMat_tendsto_of_moments
      (μ := μ) (Pstar := Pstar)
      (Zstar := trimmedBootstrapStatistic Zstar τ)
      hPstar hZ hmean hcross

/-- Theorem 10.12 zero-mean covariance specialization.

In the asymptotically centered case, if the trimmed conditional mean converges
to zero and the trimmed conditional cross moment converges to `V`, then the
trimmed conditional covariance converges to `V`. -/
theorem chapter10_trimmedBootstrapVariance_tendsto
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {τ : ℕ → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ :
      ∀ n ω a,
        MemLp (fun ωs => trimmedBootstrapStatistic Zstar τ n ω ωs a) 2
          (Pstar n ω))
    {V : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ
        (bootstrapMeanVec Pstar (trimmedBootstrapStatistic Zstar τ))
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ
        (bootstrapCrossMomentMat Pstar (trimmedBootstrapStatistic Zstar τ))
        atTop (fun _ => V)) :
    TendstoInMeasure μ (trimmedBootstrapCovarianceMat Pstar Zstar τ) atTop
      (fun _ => V) := by
  have h :=
    chapter10_trimmedBootstrapVariance_tendsto_of_moments
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
      hPstar hZ hmean hcross
  simpa using h

/-- Indexed Hansen Theorem 10.12, trimmed conditional covariance moment
bridge. -/
theorem chapter10_indexed_trimmedBootstrapVariance_tendsto_of_moments
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {τ : ℕ → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ :
      ∀ n ω a,
        MemLp
          (fun ωs => trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a) 2
          (Pstar n ω))
    {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ
        (bootstrapMeanVecIndexed Pstar
          (trimmedBootstrapStatisticIndexed Zstar τ))
        atTop (fun _ => m))
    (hcross :
      TendstoInMeasure μ
        (bootstrapCrossMomentMatIndexed Pstar
          (trimmedBootstrapStatisticIndexed Zstar τ))
        atTop (fun _ => M₂)) :
    TendstoInMeasure μ (trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ)
      atTop (fun _ => fun a c => M₂ a c - m a * m c) := by
  simpa [trimmedBootstrapCovarianceMatIndexed] using
    chapter10_indexed_bootstrap_covarianceMat_tendsto_of_moments
      (μ := μ) (Pstar := Pstar)
      (Zstar := trimmedBootstrapStatisticIndexed Zstar τ)
      hPstar hZ hmean hcross

/-- Indexed Theorem 10.12 zero-mean covariance specialization. -/
theorem chapter10_indexed_trimmedBootstrapVariance_tendsto
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {τ : ℕ → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ :
      ∀ n ω a,
        MemLp
          (fun ωs => trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a) 2
          (Pstar n ω))
    {V : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ
        (bootstrapMeanVecIndexed Pstar
          (trimmedBootstrapStatisticIndexed Zstar τ))
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ
        (bootstrapCrossMomentMatIndexed Pstar
          (trimmedBootstrapStatisticIndexed Zstar τ))
        atTop (fun _ => V)) :
    TendstoInMeasure μ (trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ)
      atTop (fun _ => V) := by
  have h :=
    chapter10_indexed_trimmedBootstrapVariance_tendsto_of_moments
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
      hPstar hZ hmean hcross
  simpa using h

end BootstrapCovariance

section BootstrapRegression

/-- Hansen Theorem 10.18, nonlinear-regression delta-method Gaussian wrapper.

If the bootstrap regression coefficient statistic converges weakly to
`N(0,Vβ)`, then the derivative-linearized statistic for a smooth transformation
with Jacobian `R` converges weakly to `N(0,R' Vβ R)`.  This is the regression
surface of the bootstrap Delta method; the concrete OLS bootstrap constructor
supplies the coefficient-level bootstrap CLT premise. -/
theorem chapter10_bootstrap_regression_theta_gaussian
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    (hVβ : Vβ.PosSemidef)
    (hβ :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (fun n ω ωs => matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs))
      (multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R))
      (fun z : EuclideanSpace ℝ q => z) := by
  simpa [Matrix.transpose_transpose] using
    chapter10_bootstrap_delta_method_gaussian (μ := μ) (Pstar := Pstar)
      (Tstar := TbetaStar) (V := Vβ) (G := Rᵀ) hVβ hβ

/-- Hansen Theorem 10.18, regression Gaussian CDF wrapper.

This is the Hansen Definition 10.2 face of
`chapter10_bootstrap_regression_theta_gaussian`: after the coefficient-level
bootstrap CLT and the delta-method linear map, coordinate CDF convergence
follows at transformed Gaussian continuity points whose lower-orthant
frontiers are null. -/
theorem chapter10_bootstrap_regression_theta_gaussian_distribution
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    (hVβ : Vβ.PosSemidef)
    (hβ :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) := by
  simpa [Matrix.transpose_transpose] using
    chapter10_bootstrap_delta_method_gaussian_distribution
      (μ := μ) (Pstar := Pstar) (Tstar := TbetaStar) (V := Vβ)
      (G := Rᵀ) hVβ hβ hPstar hTbetaStar
      (by simpa [Matrix.transpose_transpose] using hfrontier)

/-- Hansen Theorem 10.18, regression Gaussian CDF wrapper with positive
definite transformed covariance.

When `R' Vβ R` is positive definite, the transformed Gaussian lower-orthant
null-frontier premise in `chapter10_bootstrap_regression_theta_gaussian_distribution`
is automatic. -/
theorem chapter10_bootstrap_regression_theta_gaussian_distribution_posDef
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    (hVβ : Vβ.PosSemidef)
    (hRVR : (Rᵀ * Vβ * R).PosDef)
    (hβ :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_bootstrap_regression_theta_gaussian_distribution
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar) (Vβ := Vβ)
    R hVβ hβ hPstar hTbetaStar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hRVR x)

/-- Indexed Hansen Theorem 10.18, nonlinear-regression delta-method Gaussian
wrapper for sample-size-dependent bootstrap spaces. -/
theorem chapter10_indexed_bootstrap_regression_theta_gaussian
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    (hVβ : Vβ.PosSemidef)
    (hβ :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (fun n ω ωs => matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs))
      (multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R))
      (fun z : EuclideanSpace ℝ q => z) := by
  simpa [Matrix.transpose_transpose] using
    chapter10_indexed_bootstrap_delta_method_gaussian
      (μ := μ) (Pstar := Pstar) (Tstar := TbetaStar) (V := Vβ)
      (G := Rᵀ) hVβ hβ

/-- Indexed Hansen Theorem 10.18, regression Gaussian CDF wrapper. -/
theorem chapter10_indexed_bootstrap_regression_theta_gaussian_distribution
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    (hVβ : Vβ.PosSemidef)
    (hβ :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω))
    (hfrontier : ∀ x : q → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R))
              (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) y) x →
        ((multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R)).map
            (fun z : EuclideanSpace ℝ q => (z : q → ℝ)))
          (frontier {z : q → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) := by
  simpa [Matrix.transpose_transpose] using
    chapter10_indexed_bootstrap_delta_method_gaussian_distribution
      (μ := μ) (Pstar := Pstar) (Tstar := TbetaStar) (V := Vβ)
      (G := Rᵀ) hVβ hβ hPstar hTbetaStar
      (by simpa [Matrix.transpose_transpose] using hfrontier)

/-- Indexed Hansen Theorem 10.18, regression Gaussian CDF wrapper with
positive definite transformed covariance. -/
theorem chapter10_indexed_bootstrap_regression_theta_gaussian_distribution_posDef
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    (hVβ : Vβ.PosSemidef)
    (hRVR : (Rᵀ * Vβ * R).PosDef)
    (hβ :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTbetaStar : ∀ n ω, Measurable (TbetaStar n ω)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ q) (Rᵀ * Vβ * R))
      (fun z : EuclideanSpace ℝ q => (z : q → ℝ)) :=
  chapter10_indexed_bootstrap_regression_theta_gaussian_distribution
    (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar) (Vβ := Vβ)
    R hVβ hβ hPstar hTbetaStar
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hRVR x)

/-- Hansen Theorem 10.19, regression-facing trimmed bootstrap variance bridge.

For the transformed regression statistic, if the trimmed conditional mean
converges to zero and the trimmed conditional cross moment converges to the
delta-method covariance `R' Vβ R`, then the trimmed bootstrap covariance
estimator converges to `R' Vβ R`.  The concrete regression proof supplies these
moment premises from Theorems 10.11 and 10.12. -/
theorem chapter10_bootstrap_regression_trimmedVariance_tendsto
    {k q : Type*} [Fintype k] [Fintype q]
    {Pstar : ℕ → Ω → Measure Ωs}
    {ZthetaStar : ℕ → Ω → Ωs → q → ℝ}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ :
      ∀ n ω a,
        MemLp (fun ωs => trimmedBootstrapStatistic ZthetaStar τ n ω ωs a) 2
          (Pstar n ω))
    (hmean :
      TendstoInMeasure μ
        (bootstrapMeanVec Pstar (trimmedBootstrapStatistic ZthetaStar τ))
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ
        (bootstrapCrossMomentMat Pstar (trimmedBootstrapStatistic ZthetaStar τ))
        atTop (fun _ => smoothFunctionVarianceFunctional R Vβ)) :
    TendstoInMeasure μ (trimmedBootstrapCovarianceMat Pstar ZthetaStar τ) atTop
      (fun _ => smoothFunctionVarianceFunctional R Vβ) :=
  chapter10_trimmedBootstrapVariance_tendsto
    (μ := μ) (Pstar := Pstar) (Zstar := ZthetaStar) (τ := τ)
    hPstar hZ hmean hcross

/-- Indexed Hansen Theorem 10.19, regression-facing trimmed bootstrap variance
bridge for sample-size-dependent bootstrap spaces. -/
theorem chapter10_indexed_bootstrap_regression_trimmedVariance_tendsto
    {k q : Type*} [Fintype k] [Fintype q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {ZthetaStar : ∀ n, Ω → Ωboot n → q → ℝ}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            trimmedBootstrapStatisticIndexed ZthetaStar τ n ω ωs a) 2
          (Pstar n ω))
    (hmean :
      TendstoInMeasure μ
        (bootstrapMeanVecIndexed Pstar
          (trimmedBootstrapStatisticIndexed ZthetaStar τ))
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ
        (bootstrapCrossMomentMatIndexed Pstar
          (trimmedBootstrapStatisticIndexed ZthetaStar τ))
        atTop (fun _ => smoothFunctionVarianceFunctional R Vβ)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMatIndexed Pstar ZthetaStar τ)
      atTop (fun _ => smoothFunctionVarianceFunctional R Vβ) :=
  chapter10_indexed_trimmedBootstrapVariance_tendsto
    (μ := μ) (Pstar := Pstar) (Zstar := ZthetaStar) (τ := τ)
    hPstar hZ hmean hcross

end BootstrapRegression

section FiniteReplicationVariance

/-- Mean across `B` finite bootstrap replications of a real statistic. -/
noncomputable def finiteReplicationMeanReal
    (Z : ℕ → ℕ → Ω → ℝ) (B : ℕ) (ω : Ω) : ℝ :=
  (B : ℝ)⁻¹ * ∑ b ∈ Finset.range B, Z B b ω

/-- Second moment across `B` finite bootstrap replications of a real statistic. -/
noncomputable def finiteReplicationSecondMomentReal
    (Z : ℕ → ℕ → Ω → ℝ) (B : ℕ) (ω : Ω) : ℝ :=
  (B : ℝ)⁻¹ * ∑ b ∈ Finset.range B, (Z B b ω) ^ 2

/-- Cross moment across `B` finite bootstrap replications of two real statistics. -/
noncomputable def finiteReplicationCrossMomentReal
    (X Y : ℕ → ℕ → Ω → ℝ) (B : ℕ) (ω : Ω) : ℝ :=
  (B : ℝ)⁻¹ * ∑ b ∈ Finset.range B, X B b ω * Y B b ω

/-- Finite-sample degrees-of-freedom correction `B / (B - 1)`. -/
noncomputable def finiteReplicationVarianceCorrection (B : ℕ) : ℝ :=
  (B : ℝ) / ((B : ℝ) - 1)

/-- Moment-form finite-replication variance estimator for a real statistic. -/
noncomputable def finiteReplicationVarianceMomentReal
    (Z : ℕ → ℕ → Ω → ℝ) (B : ℕ) (ω : Ω) : ℝ :=
  finiteReplicationVarianceCorrection B *
    (finiteReplicationSecondMomentReal Z B ω -
      (finiteReplicationMeanReal Z B ω) ^ 2)

/-- Moment-form finite-replication covariance estimator for two real statistics. -/
noncomputable def finiteReplicationCovarianceMomentReal
    (X Y : ℕ → ℕ → Ω → ℝ) (B : ℕ) (ω : Ω) : ℝ :=
  finiteReplicationVarianceCorrection B *
    (finiteReplicationCrossMomentReal X Y B ω -
      finiteReplicationMeanReal X B ω * finiteReplicationMeanReal Y B ω)

/-- Centered finite-replication covariance estimator for two real statistics. -/
noncomputable def finiteReplicationCovarianceCenteredReal
    (X Y : ℕ → ℕ → Ω → ℝ) (B : ℕ) (ω : Ω) : ℝ :=
  (((B : ℝ) - 1)⁻¹) *
    ∑ b ∈ Finset.range B,
      (X B b ω - finiteReplicationMeanReal X B ω) *
        (Y B b ω - finiteReplicationMeanReal Y B ω)

/-- Centered finite-replication variance estimator for a real statistic.

This is the scalar `X = Y` notation for Hansen's centered finite-replication
covariance estimator. -/
noncomputable def finiteReplicationVarianceCenteredReal
    (Z : ℕ → ℕ → Ω → ℝ) (B : ℕ) (ω : Ω) : ℝ :=
  finiteReplicationCovarianceCenteredReal Z Z B ω

/-- Mean vector across `B` finite bootstrap replications. -/
noncomputable def finiteReplicationMeanVec
    (Z : ℕ → ℕ → Ω → k → ℝ) (B : ℕ) (ω : Ω) : k → ℝ :=
  fun a => (B : ℝ)⁻¹ * ∑ b ∈ Finset.range B, Z B b ω a

/-- Cross-moment matrix across `B` finite bootstrap replications. -/
noncomputable def finiteReplicationCrossMomentMat
    (Z : ℕ → ℕ → Ω → k → ℝ) (B : ℕ) (ω : Ω) : Matrix k k ℝ :=
  fun a c => (B : ℝ)⁻¹ * ∑ b ∈ Finset.range B, Z B b ω a * Z B b ω c

/-- Moment-form finite-replication covariance matrix estimator. -/
noncomputable def finiteReplicationCovarianceMomentMat
    (Z : ℕ → ℕ → Ω → k → ℝ) (B : ℕ) (ω : Ω) : Matrix k k ℝ :=
  fun a c =>
    finiteReplicationVarianceCorrection B *
      (finiteReplicationCrossMomentMat Z B ω a c -
        finiteReplicationMeanVec Z B ω a * finiteReplicationMeanVec Z B ω c)

/-- Centered finite-replication covariance matrix estimator. -/
noncomputable def finiteReplicationCovarianceCenteredMat
    (Z : ℕ → ℕ → Ω → k → ℝ) (B : ℕ) (ω : Ω) : Matrix k k ℝ :=
  fun a c =>
    (((B : ℝ) - 1)⁻¹) *
      ∑ b ∈ Finset.range B,
        (Z B b ω a - finiteReplicationMeanVec Z B ω a) *
          (Z B b ω c - finiteReplicationMeanVec Z B ω c)

private theorem tendstoInMeasure_of_integral_norm_sq_le_inv
    [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ} {x C : ℝ}
    (hInt : ∀ n, Integrable (fun ω => ‖X n ω - x‖ ^ (2 : ℝ)) μ)
    (hbound :
      ∀ᶠ n in atTop,
        (∫ ω, ‖X n ω - x‖ ^ (2 : ℝ) ∂μ) ≤ C / (n : ℝ)) :
    TendstoInMeasure μ X atTop (fun _ => x) := by
  have hupper : Tendsto (fun n : ℕ => C / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop C
  have hnonneg :
      ∀ᶠ n in atTop,
        (0 : ℝ) ≤ ∫ ω, ‖X n ω - x‖ ^ (2 : ℝ) ∂μ :=
    Eventually.of_forall fun n =>
      integral_nonneg fun ω =>
        Real.rpow_nonneg (norm_nonneg (X n ω - x)) _
  have hscaled :
      Tendsto (fun n => ∫ ω, ‖X n ω - x‖ ^ (2 : ℝ) ∂μ)
        atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hupper hnonneg hbound
  have hscaled' :
      Tendsto
        (fun n => (∫ ω, ‖X n ω - x‖ ^ (2 : ℝ) ∂μ) /
          (fun _ : ℕ => (1 : ℝ)) n ^ (2 : ℝ))
        atTop (𝓝 0) := by
    simpa using hscaled
  have hsub_scaled :
      TendstoInMeasure μ
        (fun n ω => ((fun _ : ℕ => (1 : ℝ)) n)⁻¹ * (X n ω - x))
        atTop (fun _ => 0) :=
    TendstoInMeasure.of_integral_norm_rpow_scaled_tendsto_zero
      (μ := μ) (X := fun n ω => X n ω - x)
      (a := fun _ : ℕ => (1 : ℝ)) (p := (2 : ℝ))
      (by norm_num)
      (Eventually.of_forall fun _ => by norm_num)
      hInt hscaled'
  have hsub :
      TendstoInMeasure μ (fun n ω => X n ω - x) atTop (fun _ => 0) := by
    simpa using hsub_scaled
  exact TendstoInMeasure.of_sub_limit_zero_real hsub

/-- Finite-replication WLLN for real means from an `L²` error bound.

This is the bounded-trimmed WLLN constructor used by Hansen Theorem 10.11:
an `O(B⁻¹)` mean-square error for the finite simulation average implies
convergence in probability of the finite-replication mean. -/
theorem finiteReplicationMeanReal_tendsto_of_integral_sq_error_le_inv
    [IsFiniteMeasure μ]
    {Z : ℕ → ℕ → Ω → ℝ} {m C : ℝ}
    (hInt :
      ∀ B, Integrable
        (fun ω => ‖finiteReplicationMeanReal Z B ω - m‖ ^ (2 : ℝ)) μ)
    (hbound :
      ∀ᶠ B in atTop,
        (∫ ω, ‖finiteReplicationMeanReal Z B ω - m‖ ^ (2 : ℝ) ∂μ) ≤
          C / (B : ℝ)) :
    TendstoInMeasure μ (finiteReplicationMeanReal Z) atTop (fun _ => m) :=
  tendstoInMeasure_of_integral_norm_sq_le_inv (μ := μ)
    (X := finiteReplicationMeanReal Z) hInt hbound

/-- Finite-replication WLLN for real second moments from an `L²` error bound. -/
theorem finiteReplicationSecondMomentReal_tendsto_of_integral_sq_error_le_inv
    [IsFiniteMeasure μ]
    {Z : ℕ → ℕ → Ω → ℝ} {m₂ C : ℝ}
    (hInt :
      ∀ B, Integrable
        (fun ω => ‖finiteReplicationSecondMomentReal Z B ω - m₂‖ ^ (2 : ℝ)) μ)
    (hbound :
      ∀ᶠ B in atTop,
        (∫ ω, ‖finiteReplicationSecondMomentReal Z B ω - m₂‖ ^ (2 : ℝ) ∂μ) ≤
          C / (B : ℝ)) :
    TendstoInMeasure μ (finiteReplicationSecondMomentReal Z) atTop
      (fun _ => m₂) :=
  tendstoInMeasure_of_integral_norm_sq_le_inv (μ := μ)
    (X := finiteReplicationSecondMomentReal Z) hInt hbound

/-- Finite-replication WLLN for real cross moments from an `L²` error bound. -/
theorem finiteReplicationCrossMomentReal_tendsto_of_integral_sq_error_le_inv
    [IsFiniteMeasure μ]
    {X Y : ℕ → ℕ → Ω → ℝ} {mXY C : ℝ}
    (hInt :
      ∀ B, Integrable
        (fun ω => ‖finiteReplicationCrossMomentReal X Y B ω - mXY‖ ^ (2 : ℝ)) μ)
    (hbound :
      ∀ᶠ B in atTop,
        (∫ ω, ‖finiteReplicationCrossMomentReal X Y B ω - mXY‖ ^ (2 : ℝ) ∂μ) ≤
          C / (B : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCrossMomentReal X Y) atTop
      (fun _ => mXY) :=
  tendstoInMeasure_of_integral_norm_sq_le_inv (μ := μ)
    (X := finiteReplicationCrossMomentReal X Y) hInt hbound

/-- Coordinatewise finite-replication WLLN for mean vectors from `L²` error
bounds. -/
theorem finiteReplicationMeanVec_tendsto_of_integral_sq_error_le_inv
    [IsFiniteMeasure μ] {k : Type*} [Fintype k]
    {Z : ℕ → ℕ → Ω → k → ℝ} {m : k → ℝ} {C : k → ℝ}
    (hInt :
      ∀ a B, Integrable
        (fun ω => ‖finiteReplicationMeanVec Z B ω a - m a‖ ^ (2 : ℝ)) μ)
    (hbound :
      ∀ a,
        ∀ᶠ B in atTop,
          (∫ ω, ‖finiteReplicationMeanVec Z B ω a - m a‖ ^ (2 : ℝ) ∂μ) ≤
            C a / (B : ℝ)) :
    TendstoInMeasure μ (finiteReplicationMeanVec Z) atTop (fun _ => m) := by
  refine tendstoInMeasure_pi (fun a => ?_)
  simpa [finiteReplicationMeanVec, finiteReplicationMeanReal] using
    finiteReplicationMeanReal_tendsto_of_integral_sq_error_le_inv
      (μ := μ) (Z := fun B b ω => Z B b ω a) (m := m a) (C := C a)
      (by simpa [finiteReplicationMeanVec, finiteReplicationMeanReal] using hInt a)
      (by simpa [finiteReplicationMeanVec, finiteReplicationMeanReal] using hbound a)

/-- Coordinatewise finite-replication WLLN for cross-moment matrices from
`L²` error bounds. -/
theorem finiteReplicationCrossMomentMat_tendsto_of_integral_sq_error_le_inv
    [IsFiniteMeasure μ] {k : Type*} [Fintype k]
    {Z : ℕ → ℕ → Ω → k → ℝ} {M₂ : Matrix k k ℝ} {C : k → k → ℝ}
    (hInt :
      ∀ a c B, Integrable
        (fun ω => ‖finiteReplicationCrossMomentMat Z B ω a c - M₂ a c‖ ^
          (2 : ℝ)) μ)
    (hbound :
      ∀ a c,
        ∀ᶠ B in atTop,
          (∫ ω, ‖finiteReplicationCrossMomentMat Z B ω a c - M₂ a c‖ ^
              (2 : ℝ) ∂μ) ≤
            C a c / (B : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCrossMomentMat Z) atTop
      (fun _ => M₂) := by
  refine tendstoInMeasure_pi (fun a => ?_)
  refine tendstoInMeasure_pi (fun c => ?_)
  simpa [finiteReplicationCrossMomentMat, finiteReplicationCrossMomentReal] using
    finiteReplicationCrossMomentReal_tendsto_of_integral_sq_error_le_inv
      (μ := μ)
      (X := fun B b ω => Z B b ω a)
      (Y := fun B b ω => Z B b ω c)
      (mXY := M₂ a c) (C := C a c)
      (by
        simpa [finiteReplicationCrossMomentMat, finiteReplicationCrossMomentReal]
          using hInt a c)
      (by
        simpa [finiteReplicationCrossMomentMat, finiteReplicationCrossMomentReal]
          using hbound a c)

/-- The finite-replication degrees-of-freedom correction `B / (B - 1)`
tends to `1`. -/
theorem finiteReplicationVarianceCorrection_tendsto_one :
    Tendsto finiteReplicationVarianceCorrection atTop (𝓝 1) := by
  let r : ℕ → ℝ := finiteReplicationVarianceCorrection
  have hB : Tendsto (fun B : ℕ => (B : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun B : ℕ => (B : ℝ) - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-(1 : ℝ)) hB
  have hrSub : Tendsto (fun B => r B - 1) atTop (𝓝 0) := by
    have hsmall : Tendsto (fun B : ℕ => (1 : ℝ) / ((B : ℝ) - 1))
        atTop (𝓝 0) :=
      hden.const_div_atTop (1 : ℝ)
    have heq : (fun B => r B - 1) =ᶠ[atTop]
        (fun B : ℕ => (1 : ℝ) / ((B : ℝ) - 1)) := by
      filter_upwards [eventually_gt_atTop 1] with B hB_gt
      have hden_ne : (B : ℝ) - 1 ≠ 0 := by
        have hgt : (1 : ℝ) < (B : ℝ) := by
          exact_mod_cast hB_gt
        linarith
      dsimp [r, finiteReplicationVarianceCorrection]
      field_simp [hden_ne]
      ring
    rw [tendsto_congr' heq]
    exact hsmall
  have hadd := hrSub.add_const 1
  simpa [r, finiteReplicationVarianceCorrection, sub_eq_add_neg, add_assoc,
    add_comm, add_left_comm] using hadd

/-- The centered finite-replication covariance formula equals its moment form
whenever the number of replications is greater than one. -/
theorem finiteReplicationCovarianceCenteredReal_eq_momentReal
    {X Y : ℕ → ℕ → Ω → ℝ} {B : ℕ} (hB : 1 < B) (ω : Ω) :
    finiteReplicationCovarianceCenteredReal X Y B ω =
      finiteReplicationCovarianceMomentReal X Y B ω := by
  have hB0_nat : B ≠ 0 := Nat.ne_of_gt (lt_trans zero_lt_one hB)
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB0_nat
  have hden_ne : (B : ℝ) - 1 ≠ 0 := by
    have hgt : (1 : ℝ) < (B : ℝ) := by exact_mod_cast hB
    linarith
  have hsumX :
      ∑ b ∈ Finset.range B, X B b ω =
        (B : ℝ) * finiteReplicationMeanReal X B ω := by
    unfold finiteReplicationMeanReal
    field_simp [hB0]
  have hsumY :
      ∑ b ∈ Finset.range B, Y B b ω =
        (B : ℝ) * finiteReplicationMeanReal Y B ω := by
    unfold finiteReplicationMeanReal
    field_simp [hB0]
  have hcenter_sum :
      ∑ b ∈ Finset.range B,
          (X B b ω - finiteReplicationMeanReal X B ω) *
            (Y B b ω - finiteReplicationMeanReal Y B ω) =
        ∑ b ∈ Finset.range B, X B b ω * Y B b ω -
          (B : ℝ) * finiteReplicationMeanReal X B ω *
            finiteReplicationMeanReal Y B ω := by
    calc
      ∑ b ∈ Finset.range B,
          (X B b ω - finiteReplicationMeanReal X B ω) *
            (Y B b ω - finiteReplicationMeanReal Y B ω)
          =
        ∑ b ∈ Finset.range B,
          (X B b ω * Y B b ω -
            X B b ω * finiteReplicationMeanReal Y B ω -
            finiteReplicationMeanReal X B ω * Y B b ω +
            finiteReplicationMeanReal X B ω *
              finiteReplicationMeanReal Y B ω) := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          ring
      _ =
        ∑ b ∈ Finset.range B, X B b ω * Y B b ω -
          (∑ b ∈ Finset.range B, X B b ω) *
            finiteReplicationMeanReal Y B ω -
          finiteReplicationMeanReal X B ω *
            (∑ b ∈ Finset.range B, Y B b ω) +
          (B : ℝ) * finiteReplicationMeanReal X B ω *
            finiteReplicationMeanReal Y B ω := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_mul, Finset.mul_sum, mul_assoc]
      _ =
        ∑ b ∈ Finset.range B, X B b ω * Y B b ω -
          (B : ℝ) * finiteReplicationMeanReal X B ω *
            finiteReplicationMeanReal Y B ω := by
          rw [hsumX, hsumY]
          ring
  unfold finiteReplicationCovarianceCenteredReal
  unfold finiteReplicationCovarianceMomentReal
  unfold finiteReplicationCrossMomentReal
  unfold finiteReplicationVarianceCorrection
  rw [hcenter_sum]
  field_simp [hB0, hden_ne]

/-- The centered finite-replication variance formula equals its moment form
whenever the number of replications is greater than one. -/
theorem finiteReplicationVarianceCenteredReal_eq_momentReal
    {Z : ℕ → ℕ → Ω → ℝ} {B : ℕ} (hB : 1 < B) (ω : Ω) :
    finiteReplicationVarianceCenteredReal Z B ω =
      finiteReplicationVarianceMomentReal Z B ω := by
  simpa [finiteReplicationVarianceCenteredReal,
    finiteReplicationVarianceMomentReal, finiteReplicationCovarianceMomentReal,
    finiteReplicationCrossMomentReal, finiteReplicationSecondMomentReal, pow_two]
    using finiteReplicationCovarianceCenteredReal_eq_momentReal
      (X := Z) (Y := Z) hB ω

/-- Matrix form of `finiteReplicationCovarianceCenteredReal_eq_momentReal`. -/
theorem finiteReplicationCovarianceCenteredMat_eq_momentMat
    {k : Type*} {Z : ℕ → ℕ → Ω → k → ℝ} {B : ℕ}
    (hB : 1 < B) (ω : Ω) :
    finiteReplicationCovarianceCenteredMat Z B ω =
      finiteReplicationCovarianceMomentMat Z B ω := by
  ext a c
  simpa [finiteReplicationCovarianceCenteredMat, finiteReplicationCovarianceMomentMat,
    finiteReplicationMeanVec, finiteReplicationCrossMomentMat,
    finiteReplicationMeanReal, finiteReplicationCrossMomentReal] using
    finiteReplicationCovarianceCenteredReal_eq_momentReal
      (X := fun B b ω => Z B b ω a)
      (Y := fun B b ω => Z B b ω c) hB ω

/-- Hansen Theorem 10.11, finite-replication variance moment bridge.

If the finite-`B` replication mean and second moment converge in probability to
their conditional limits, then the moment-form finite-replication variance
converges in probability to `m₂ - m²`.  In applications, the moment premises are
the bootstrap WLLN for bounded trimmed replications. -/
theorem chapter10_finiteReplicationVariance_tendsto_of_moments
    {Z : ℕ → ℕ → Ω → ℝ} {m m₂ : ℝ}
    (hmean :
      TendstoInMeasure μ (finiteReplicationMeanReal Z) atTop (fun _ => m))
    (hsecond :
      TendstoInMeasure μ (finiteReplicationSecondMomentReal Z) atTop
        (fun _ => m₂)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Z) atTop
      (fun _ => m₂ - m ^ 2) := by
  have hmean_sq :
      TendstoInMeasure μ
        (fun B ω => finiteReplicationMeanReal Z B ω *
          finiteReplicationMeanReal Z B ω)
        atTop (fun _ => m * m) :=
    TendstoInMeasure.mul_limits_real hmean hmean
  have hsecond0 := TendstoInMeasure.sub_limit_zero_real hsecond
  have hmean_sq0 := TendstoInMeasure.sub_limit_zero_real hmean_sq
  have hdiff0 :
      TendstoInMeasure μ
        (fun B ω =>
          (finiteReplicationSecondMomentReal Z B ω -
            finiteReplicationMeanReal Z B ω *
              finiteReplicationMeanReal Z B ω) -
            (m₂ - m * m))
        atTop (fun _ => 0) := by
    have hsub := TendstoInMeasure.sub_zero_real hsecond0 hmean_sq0
    refine TendstoInMeasure.congr (fun B => ?_) EventuallyEq.rfl hsub
    refine ae_of_all μ fun ω => ?_
    ring
  have hdiff :
      TendstoInMeasure μ
        (fun B ω =>
          finiteReplicationSecondMomentReal Z B ω -
            finiteReplicationMeanReal Z B ω *
              finiteReplicationMeanReal Z B ω)
        atTop (fun _ => m₂ - m * m) :=
    TendstoInMeasure.of_sub_limit_zero_real hdiff0
  have hfactor :
      TendstoInMeasure μ
        (fun B (_ : Ω) => finiteReplicationVarianceCorrection B)
        atTop (fun _ => 1) :=
    tendstoInMeasure_const_real (μ := μ)
      finiteReplicationVarianceCorrection_tendsto_one
  have hprod :
      TendstoInMeasure μ
        (fun B ω =>
          finiteReplicationVarianceCorrection B *
            (finiteReplicationSecondMomentReal Z B ω -
              (finiteReplicationMeanReal Z B ω) ^ 2))
        atTop (fun _ => 1 * (m₂ - m * m)) := by
    simpa [pow_two] using TendstoInMeasure.mul_limits_real hfactor hdiff
  refine TendstoInMeasure.congr
    (f := fun B ω =>
      finiteReplicationVarianceCorrection B *
        (finiteReplicationSecondMomentReal Z B ω -
          (finiteReplicationMeanReal Z B ω) ^ 2))
    (f' := finiteReplicationVarianceMomentReal Z)
    (g := fun _ : Ω => 1 * (m₂ - m * m))
    (g' := fun _ : Ω => m₂ - m ^ 2)
    (fun B => ?_) ?_ hprod
  · exact ae_of_all μ fun ω => by
      simp [finiteReplicationVarianceMomentReal]
  · exact ae_of_all μ fun _ => by ring

/-- Hansen Theorem 10.11, finite-replication variance from bounded-trimmed
`L²` WLLN bounds.

The displayed `C / B` mean-square bounds are the probability-theory premises
supplied by the bounded trimmed bootstrap WLLN.  This wrapper turns those
bounds into the mean and second-moment convergence premises needed by
`chapter10_finiteReplicationVariance_tendsto_of_moments`. -/
theorem chapter10_finiteReplicationVariance_tendsto_of_l2_error_bounds
    [IsFiniteMeasure μ]
    {Z : ℕ → ℕ → Ω → ℝ} {m m₂ Cmean Csecond : ℝ}
    (hmeanInt :
      ∀ B, Integrable
        (fun ω => ‖finiteReplicationMeanReal Z B ω - m‖ ^ (2 : ℝ)) μ)
    (hmeanBound :
      ∀ᶠ B in atTop,
        (∫ ω, ‖finiteReplicationMeanReal Z B ω - m‖ ^ (2 : ℝ) ∂μ) ≤
          Cmean / (B : ℝ))
    (hsecondInt :
      ∀ B, Integrable
        (fun ω => ‖finiteReplicationSecondMomentReal Z B ω - m₂‖ ^ (2 : ℝ)) μ)
    (hsecondBound :
      ∀ᶠ B in atTop,
        (∫ ω, ‖finiteReplicationSecondMomentReal Z B ω - m₂‖ ^ (2 : ℝ) ∂μ) ≤
          Csecond / (B : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Z) atTop
      (fun _ => m₂ - m ^ 2) :=
  chapter10_finiteReplicationVariance_tendsto_of_moments
    (μ := μ)
    (finiteReplicationMeanReal_tendsto_of_integral_sq_error_le_inv
      (μ := μ) (Z := Z) (m := m) (C := Cmean) hmeanInt hmeanBound)
    (finiteReplicationSecondMomentReal_tendsto_of_integral_sq_error_le_inv
      (μ := μ) (Z := Z) (m₂ := m₂) (C := Csecond)
      hsecondInt hsecondBound)

/-- Hansen Theorem 10.11, centered finite-replication variance moment bridge.

This is the textbook-centered version of
`chapter10_finiteReplicationVariance_tendsto_of_moments`, obtained from the
exact centered/moment-form identity for `B > 1`. -/
theorem chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_moments
    {Z : ℕ → ℕ → Ω → ℝ} {m m₂ : ℝ}
    (hmean :
      TendstoInMeasure μ (finiteReplicationMeanReal Z) atTop (fun _ => m))
    (hsecond :
      TendstoInMeasure μ (finiteReplicationSecondMomentReal Z) atTop
        (fun _ => m₂)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Z) atTop
      (fun _ => m₂ - m ^ 2) := by
  have hmoment :=
    chapter10_finiteReplicationVariance_tendsto_of_moments
      (μ := μ) hmean hsecond
  refine TendstoInMeasure.congr'
    (f := finiteReplicationVarianceMomentReal Z)
    (f' := finiteReplicationVarianceCenteredReal Z)
    (g := fun _ : Ω => m₂ - m ^ 2)
    (g' := fun _ : Ω => m₂ - m ^ 2)
    ?_ EventuallyEq.rfl hmoment
  filter_upwards [eventually_gt_atTop 1] with B hB
  exact ae_of_all μ fun ω =>
    (finiteReplicationVarianceCenteredReal_eq_momentReal
      (Z := Z) hB ω).symm

/-- Hansen Theorem 10.11, centered finite-replication variance from
bounded-trimmed `L²` WLLN bounds. -/
theorem chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_l2_error_bounds
    [IsFiniteMeasure μ]
    {Z : ℕ → ℕ → Ω → ℝ} {m m₂ Cmean Csecond : ℝ}
    (hmeanInt :
      ∀ B, Integrable
        (fun ω => ‖finiteReplicationMeanReal Z B ω - m‖ ^ (2 : ℝ)) μ)
    (hmeanBound :
      ∀ᶠ B in atTop,
        (∫ ω, ‖finiteReplicationMeanReal Z B ω - m‖ ^ (2 : ℝ) ∂μ) ≤
          Cmean / (B : ℝ))
    (hsecondInt :
      ∀ B, Integrable
        (fun ω => ‖finiteReplicationSecondMomentReal Z B ω - m₂‖ ^ (2 : ℝ)) μ)
    (hsecondBound :
      ∀ᶠ B in atTop,
        (∫ ω, ‖finiteReplicationSecondMomentReal Z B ω - m₂‖ ^ (2 : ℝ) ∂μ) ≤
          Csecond / (B : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Z) atTop
      (fun _ => m₂ - m ^ 2) :=
  chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_moments
    (μ := μ)
    (finiteReplicationMeanReal_tendsto_of_integral_sq_error_le_inv
      (μ := μ) (Z := Z) (m := m) (C := Cmean) hmeanInt hmeanBound)
    (finiteReplicationSecondMomentReal_tendsto_of_integral_sq_error_le_inv
      (μ := μ) (Z := Z) (m₂ := m₂) (C := Csecond)
      hsecondInt hsecondBound)

/-- Hansen Theorem 10.9/10.11 bridge from finite-replication simulation error.

If the finite-replication variance estimator differs from the conditional
bootstrap variance by `oₚ(1)`, and the conditional bootstrap variance converges
to the asymptotic variance, then the finite-replication variance estimator has
the same asymptotic target. -/
theorem chapter10_finiteReplicationVariance_tendsto_of_bootstrap_variance
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {σ2 : ℝ}
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω)
        atTop (fun _ => 0))
    (hboot :
      TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
        (fun _ => σ2)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => σ2) :=
  TendstoInMeasure.of_sub_tendsto_zero_real hfinite hboot

/-- Hansen Theorem 10.9/10.11 finite-replication variance from conditional
bootstrap moment convergence.

This combines the finite-replication simulation-error bridge with the
conditional bootstrap variance moment theorem: convergence of the conditional
bootstrap mean and second moment supplies the conditional variance target. -/
theorem chapter10_finiteReplicationVariance_tendsto_of_bootstrap_moments
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {m m₂ : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hmean :
      TendstoInMeasure μ (bootstrapMeanReal Pstar Zstar) atTop
        (fun _ => m))
    (hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentReal Pstar Zstar) atTop
        (fun _ => m₂))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => m₂ - m ^ 2) :=
  chapter10_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ) hfinite
    (chapter10_bootstrap_variance_consistency_of_moment_convergence
      (μ := μ) hPstar hZ hmean hsecond)

/-- Zero-mean finite-replication variance wrapper for Hansen Theorem 10.11.

When the conditional bootstrap mean converges to zero, the moment-premise
finite-replication bridge targets the limiting second moment directly. -/
theorem chapter10_finiteReplicationVariance_tendsto_of_bootstrap_zero_mean_moments
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {σ2 : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hmean :
      TendstoInMeasure μ (bootstrapMeanReal Pstar Zstar) atTop
        (fun _ => 0))
    (hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentReal Pstar Zstar) atTop
        (fun _ => σ2))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => σ2) := by
  simpa using
    (chapter10_finiteReplicationVariance_tendsto_of_bootstrap_moments
      (μ := μ) (m := 0) (m₂ := σ2)
      hPstar hZ hmean hsecond hfinite)

/-- Hansen Theorem 10.9/10.11 centered finite-replication variance from
conditional bootstrap variance consistency.

This is the scalar textbook-centered analogue of
`chapter10_finiteReplicationVariance_tendsto_of_bootstrap_variance`. -/
theorem chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {σ2 : ℝ}
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω)
        atTop (fun _ => 0))
    (hboot :
      TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
        (fun _ => σ2)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => σ2) :=
  TendstoInMeasure.of_sub_tendsto_zero_real hfinite hboot

/-- Hansen Theorem 10.9/10.11 centered finite-replication variance from
conditional bootstrap moment convergence. -/
theorem chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_moments
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {m m₂ : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hmean :
      TendstoInMeasure μ (bootstrapMeanReal Pstar Zstar) atTop
        (fun _ => m))
    (hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentReal Pstar Zstar) atTop
        (fun _ => m₂))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => m₂ - m ^ 2) :=
  chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ) hfinite
    (chapter10_bootstrap_variance_consistency_of_moment_convergence
      (μ := μ) hPstar hZ hmean hsecond)

/-- Hansen Theorem 10.9/10.11 finite-replication variance from bootstrap weak
convergence and a uniform-square-tail condition.

This packages the two variance layers used in the theorem: a finite-replication
simulation-error premise estimates the conditional bootstrap variance, while
bootstrap weak convergence plus the named uniform-square-tail condition sends
that conditional variance to the limiting variance functional. -/
theorem chapter10_finiteReplicationVariance_tendsto_of_weak_distribution_uniformSquareTail
    [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTail μ Pstar Zstar ν Z)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) hfinite
    (chapter10_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail)

/-- Hansen Theorem 10.9/10.11 centered finite-replication variance from
bootstrap weak convergence and a named uniform-square-tail condition.

This is the textbook-centered scalar counterpart of
`chapter10_finiteReplicationVariance_tendsto_of_weak_distribution_uniformSquareTail`:
simulation error against the conditional bootstrap variance plus the Theorem
10.9 uniform-square-tail variance bridge yields consistency of Hansen's
centered finite-replication variance estimator. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_weak_distribution_uniformSquareTail
    [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTail μ Pstar Zstar ν Z)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) hfinite
    (chapter10_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail)

/-- Indexed Hansen Theorem 10.9/10.11 bridge from finite-replication
simulation error.

This is the sample-size-dependent bootstrap-space analogue of
`chapter10_finiteReplicationVariance_tendsto_of_bootstrap_variance`. -/
theorem chapter10_indexed_finiteReplicationVariance_tendsto_of_bootstrap_variance
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {σ2 : ℝ}
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω)
        atTop (fun _ => 0))
    (hboot :
      TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
        (fun _ => σ2)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => σ2) :=
  TendstoInMeasure.of_sub_tendsto_zero_real hfinite hboot

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication variance from
conditional bootstrap moment convergence. -/
theorem chapter10_indexed_finiteReplicationVariance_tendsto_of_bootstrap_moments
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {m m₂ : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hmean :
      TendstoInMeasure μ (bootstrapMeanRealIndexed Pstar Zstar) atTop
        (fun _ => m))
    (hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentRealIndexed Pstar Zstar) atTop
        (fun _ => m₂))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => m₂ - m ^ 2) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ) hfinite
    (chapter10_indexed_bootstrap_variance_consistency_of_moment_convergence
      (μ := μ) hPstar hZ hmean hsecond)

/-- Indexed zero-mean finite-replication variance wrapper for Hansen Theorem
10.11. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_of_bootstrap_zero_mean_moments
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {σ2 : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hmean :
      TendstoInMeasure μ (bootstrapMeanRealIndexed Pstar Zstar) atTop
        (fun _ => 0))
    (hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentRealIndexed Pstar Zstar) atTop
        (fun _ => σ2))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => σ2) := by
  simpa using
    (chapter10_indexed_finiteReplicationVariance_tendsto_of_bootstrap_moments
      (μ := μ) (m := 0) (m₂ := σ2)
      hPstar hZ hmean hsecond hfinite)

/-- Indexed Hansen Theorem 10.9/10.11 centered finite-replication variance
from conditional bootstrap variance consistency. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {σ2 : ℝ}
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω)
        atTop (fun _ => 0))
    (hboot :
      TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
        (fun _ => σ2)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => σ2) :=
  TendstoInMeasure.of_sub_tendsto_zero_real hfinite hboot

/-- Indexed Hansen Theorem 10.9/10.11 centered finite-replication variance
from conditional bootstrap moment convergence. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_moments
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {m m₂ : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hmean :
      TendstoInMeasure μ (bootstrapMeanRealIndexed Pstar Zstar) atTop
        (fun _ => m))
    (hsecond :
      TendstoInMeasure μ (bootstrapSecondMomentRealIndexed Pstar Zstar) atTop
        (fun _ => m₂))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => m₂ - m ^ 2) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ) hfinite
    (chapter10_indexed_bootstrap_variance_consistency_of_moment_convergence
      (μ := μ) hPstar hZ hmean hsecond)

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication variance from
bootstrap weak convergence and a named uniform-square-tail condition. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_of_weak_distribution_uniformSquareTail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) hfinite
    (chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail)

/-- Indexed Hansen Theorem 10.9/10.11 centered finite-replication variance
from bootstrap weak convergence and a named uniform-square-tail condition. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_uniformSquareTail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) hfinite
    (chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail)

/-- Finite-replication covariance moment bridge for two real statistics.

If the finite-`B` replication means of `X` and `Y` and their cross moment
converge in probability, then the moment-form finite-replication covariance
converges in probability to `mXY - mX * mY`. -/
theorem chapter10_finiteReplicationCovarianceReal_tendsto_of_moments
    {X Y : ℕ → ℕ → Ω → ℝ} {mX mY mXY : ℝ}
    (hmeanX :
      TendstoInMeasure μ (finiteReplicationMeanReal X) atTop (fun _ => mX))
    (hmeanY :
      TendstoInMeasure μ (finiteReplicationMeanReal Y) atTop (fun _ => mY))
    (hcross :
      TendstoInMeasure μ (finiteReplicationCrossMomentReal X Y) atTop
        (fun _ => mXY)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentReal X Y) atTop
      (fun _ => mXY - mX * mY) := by
  have hmean_prod :
      TendstoInMeasure μ
        (fun B ω => finiteReplicationMeanReal X B ω *
          finiteReplicationMeanReal Y B ω)
        atTop (fun _ => mX * mY) :=
    TendstoInMeasure.mul_limits_real hmeanX hmeanY
  have hcross0 := TendstoInMeasure.sub_limit_zero_real hcross
  have hmean_prod0 := TendstoInMeasure.sub_limit_zero_real hmean_prod
  have hdiff0 :
      TendstoInMeasure μ
        (fun B ω =>
          (finiteReplicationCrossMomentReal X Y B ω -
            finiteReplicationMeanReal X B ω *
              finiteReplicationMeanReal Y B ω) -
            (mXY - mX * mY))
        atTop (fun _ => 0) := by
    have hsub := TendstoInMeasure.sub_zero_real hcross0 hmean_prod0
    refine TendstoInMeasure.congr (fun B => ?_) EventuallyEq.rfl hsub
    exact ae_of_all μ fun ω => by ring
  have hdiff :
      TendstoInMeasure μ
        (fun B ω =>
          finiteReplicationCrossMomentReal X Y B ω -
            finiteReplicationMeanReal X B ω *
              finiteReplicationMeanReal Y B ω)
        atTop (fun _ => mXY - mX * mY) :=
    TendstoInMeasure.of_sub_limit_zero_real hdiff0
  have hfactor :
      TendstoInMeasure μ
        (fun B (_ : Ω) => finiteReplicationVarianceCorrection B)
        atTop (fun _ => 1) :=
    tendstoInMeasure_const_real (μ := μ)
      finiteReplicationVarianceCorrection_tendsto_one
  have hprod :
      TendstoInMeasure μ
        (fun B ω =>
          finiteReplicationVarianceCorrection B *
            (finiteReplicationCrossMomentReal X Y B ω -
              finiteReplicationMeanReal X B ω *
                finiteReplicationMeanReal Y B ω))
        atTop (fun _ => 1 * (mXY - mX * mY)) :=
    TendstoInMeasure.mul_limits_real hfactor hdiff
  simpa [finiteReplicationCovarianceMomentReal] using hprod

/-- Hansen Theorem 10.11, finite-dimensional covariance-matrix moment bridge.

If the finite-`B` replication mean vector and cross-moment matrix converge in
probability, then the moment-form finite-replication covariance matrix
converges in probability to the corresponding covariance matrix `M₂ - mm'`.
The bounded-trimmed bootstrap WLLN supplies these moment premises in the
textbook application. -/
theorem chapter10_finiteReplicationCovarianceMat_tendsto_of_moments
    {k : Type*} [Fintype k]
    {Z : ℕ → ℕ → Ω → k → ℝ} {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ (finiteReplicationMeanVec Z) atTop (fun _ => m))
    (hcross :
      TendstoInMeasure μ (finiteReplicationCrossMomentMat Z) atTop
        (fun _ => M₂)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Z) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) := by
  refine tendstoInMeasure_pi (fun a => ?_)
  refine tendstoInMeasure_pi (fun c => ?_)
  have hentry :=
    chapter10_finiteReplicationCovarianceReal_tendsto_of_moments
      (μ := μ)
      (X := fun B b ω => Z B b ω a)
      (Y := fun B b ω => Z B b ω c)
      (mX := m a) (mY := m c) (mXY := M₂ a c)
      (by
        simpa [finiteReplicationMeanVec, finiteReplicationMeanReal] using
          TendstoInMeasure.pi_apply hmean a)
      (by
        simpa [finiteReplicationMeanVec, finiteReplicationMeanReal] using
          TendstoInMeasure.pi_apply hmean c)
      (by
        simpa [finiteReplicationCrossMomentMat,
          finiteReplicationCrossMomentReal] using
          TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hcross a) c)
  simpa [finiteReplicationCovarianceMomentMat, finiteReplicationMeanVec,
    finiteReplicationCrossMomentMat, finiteReplicationCovarianceMomentReal,
    finiteReplicationMeanReal, finiteReplicationCrossMomentReal] using hentry

/-- Textbook-centered finite-replication covariance bridge for two real
statistics.

This is the same convergence result as
`chapter10_finiteReplicationCovarianceReal_tendsto_of_moments`, but stated for
the centered `1 / (B - 1) ∑ (X_b - Xbar)(Y_b - Ybar)` estimator. -/
theorem chapter10_finiteReplicationCovarianceCenteredReal_tendsto_of_moments
    {X Y : ℕ → ℕ → Ω → ℝ} {mX mY mXY : ℝ}
    (hmeanX :
      TendstoInMeasure μ (finiteReplicationMeanReal X) atTop (fun _ => mX))
    (hmeanY :
      TendstoInMeasure μ (finiteReplicationMeanReal Y) atTop (fun _ => mY))
    (hcross :
      TendstoInMeasure μ (finiteReplicationCrossMomentReal X Y) atTop
        (fun _ => mXY)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredReal X Y) atTop
      (fun _ => mXY - mX * mY) := by
  have hmoment :=
    chapter10_finiteReplicationCovarianceReal_tendsto_of_moments
      (μ := μ) hmeanX hmeanY hcross
  refine TendstoInMeasure.congr'
    (f := finiteReplicationCovarianceMomentReal X Y)
    (f' := finiteReplicationCovarianceCenteredReal X Y)
    (g := fun _ : Ω => mXY - mX * mY)
    (g' := fun _ : Ω => mXY - mX * mY)
    ?_ EventuallyEq.rfl hmoment
  filter_upwards [eventually_gt_atTop 1] with B hB
  exact ae_of_all μ fun ω =>
    (finiteReplicationCovarianceCenteredReal_eq_momentReal
      (X := X) (Y := Y) hB ω).symm

/-- Hansen Theorem 10.11, centered real finite-replication covariance from
bounded-trimmed `L²` WLLN bounds. -/
theorem chapter10_finiteReplicationCovarianceCenteredReal_tendsto_of_l2_error_bounds
    [IsFiniteMeasure μ]
    {X Y : ℕ → ℕ → Ω → ℝ} {mX mY mXY CX CY CXY : ℝ}
    (hmeanXInt :
      ∀ B, Integrable
        (fun ω => ‖finiteReplicationMeanReal X B ω - mX‖ ^ (2 : ℝ)) μ)
    (hmeanXBound :
      ∀ᶠ B in atTop,
        (∫ ω, ‖finiteReplicationMeanReal X B ω - mX‖ ^ (2 : ℝ) ∂μ) ≤
          CX / (B : ℝ))
    (hmeanYInt :
      ∀ B, Integrable
        (fun ω => ‖finiteReplicationMeanReal Y B ω - mY‖ ^ (2 : ℝ)) μ)
    (hmeanYBound :
      ∀ᶠ B in atTop,
        (∫ ω, ‖finiteReplicationMeanReal Y B ω - mY‖ ^ (2 : ℝ) ∂μ) ≤
          CY / (B : ℝ))
    (hcrossInt :
      ∀ B, Integrable
        (fun ω => ‖finiteReplicationCrossMomentReal X Y B ω - mXY‖ ^ (2 : ℝ)) μ)
    (hcrossBound :
      ∀ᶠ B in atTop,
        (∫ ω, ‖finiteReplicationCrossMomentReal X Y B ω - mXY‖ ^ (2 : ℝ) ∂μ) ≤
          CXY / (B : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredReal X Y) atTop
      (fun _ => mXY - mX * mY) :=
  chapter10_finiteReplicationCovarianceCenteredReal_tendsto_of_moments
    (μ := μ)
    (finiteReplicationMeanReal_tendsto_of_integral_sq_error_le_inv
      (μ := μ) (Z := X) (m := mX) (C := CX) hmeanXInt hmeanXBound)
    (finiteReplicationMeanReal_tendsto_of_integral_sq_error_le_inv
      (μ := μ) (Z := Y) (m := mY) (C := CY) hmeanYInt hmeanYBound)
    (finiteReplicationCrossMomentReal_tendsto_of_integral_sq_error_le_inv
      (μ := μ) (X := X) (Y := Y) (mXY := mXY) (C := CXY)
      hcrossInt hcrossBound)

/-- Hansen Theorem 10.11, textbook-centered finite-dimensional covariance
bridge.

This wrapper states the finite-replication covariance convergence for Hansen's
centered estimator `1 / (B - 1) ∑ (Z_b - Zbar)(Z_b - Zbar)'`, using the exact
centered/moment-form identity and the finite-dimensional moment bridge. -/
theorem chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_moments
    {k : Type*} [Fintype k]
    {Z : ℕ → ℕ → Ω → k → ℝ} {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hmean :
      TendstoInMeasure μ (finiteReplicationMeanVec Z) atTop (fun _ => m))
    (hcross :
      TendstoInMeasure μ (finiteReplicationCrossMomentMat Z) atTop
        (fun _ => M₂)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Z) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) := by
  have hmoment :=
    chapter10_finiteReplicationCovarianceMat_tendsto_of_moments
      (μ := μ) hmean hcross
  refine TendstoInMeasure.congr'
    (f := finiteReplicationCovarianceMomentMat Z)
    (f' := finiteReplicationCovarianceCenteredMat Z)
    (g := fun _ : Ω => fun a c => M₂ a c - m a * m c)
    (g' := fun _ : Ω => fun a c => M₂ a c - m a * m c)
    ?_ EventuallyEq.rfl hmoment
  filter_upwards [eventually_gt_atTop 1] with B hB
  exact ae_of_all μ fun ω =>
    (finiteReplicationCovarianceCenteredMat_eq_momentMat
      (Z := Z) hB ω).symm

/-- Hansen Theorem 10.11, centered finite-dimensional covariance from
bounded-trimmed coordinatewise `L²` WLLN bounds.

This is the theorem-facing constructor for the finite-replication trimmed
bootstrap covariance estimator: once bounded trimmed replications supply
`O(B⁻¹)` mean-square errors for coordinate means and cross moments, the
centered finite-replication covariance matrix converges to `M₂ - m m'`. -/
theorem chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_error_bounds
    [IsFiniteMeasure μ] {k : Type*} [Fintype k]
    {Z : ℕ → ℕ → Ω → k → ℝ} {m : k → ℝ} {M₂ : Matrix k k ℝ}
    {Cmean : k → ℝ} {Ccross : k → k → ℝ}
    (hmeanInt :
      ∀ a B, Integrable
        (fun ω => ‖finiteReplicationMeanVec Z B ω a - m a‖ ^ (2 : ℝ)) μ)
    (hmeanBound :
      ∀ a,
        ∀ᶠ B in atTop,
          (∫ ω, ‖finiteReplicationMeanVec Z B ω a - m a‖ ^ (2 : ℝ) ∂μ) ≤
            Cmean a / (B : ℝ))
    (hcrossInt :
      ∀ a c B, Integrable
        (fun ω => ‖finiteReplicationCrossMomentMat Z B ω a c - M₂ a c‖ ^
          (2 : ℝ)) μ)
    (hcrossBound :
      ∀ a c,
        ∀ᶠ B in atTop,
          (∫ ω, ‖finiteReplicationCrossMomentMat Z B ω a c - M₂ a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Ccross a c / (B : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Z) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_moments
    (μ := μ)
    (finiteReplicationMeanVec_tendsto_of_integral_sq_error_le_inv
      (μ := μ) (Z := Z) (m := m) (C := Cmean) hmeanInt hmeanBound)
    (finiteReplicationCrossMomentMat_tendsto_of_integral_sq_error_le_inv
      (μ := μ) (Z := Z) (M₂ := M₂) (C := Ccross)
      hcrossInt hcrossBound)

/-- Hansen Theorem 10.9/10.11 finite-replication covariance matrix from
conditional bootstrap covariance consistency.

If the moment-form finite-replication covariance estimator differs from the
conditional bootstrap covariance matrix by `oₚ(1)`, and the conditional
bootstrap covariance converges to `V`, then the finite-replication covariance
estimator has the same asymptotic target. -/
theorem chapter10_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    {k : Type*} [Fintype k]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {V : Matrix k k ℝ}
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMat Pstar Zstar n ω)
        atTop (fun _ => 0))
    (hboot :
      TendstoInMeasure μ (bootstrapCovarianceMat Pstar Zstar) atTop
        (fun _ => V)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => V) :=
  TendstoInMeasure.of_sub_tendsto_zero_matrix hfinite hboot

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication covariance matrix
from conditional bootstrap covariance consistency. -/
theorem chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {V : Matrix k k ℝ}
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar Zstar n ω)
        atTop (fun _ => 0))
    (hboot :
      TendstoInMeasure μ (bootstrapCovarianceMatIndexed Pstar Zstar) atTop
        (fun _ => V)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => V) :=
  TendstoInMeasure.of_sub_tendsto_zero_matrix hfinite hboot

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication covariance matrix
from conditional bootstrap moment convergence. -/
theorem chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_bootstrap_moments
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hmean :
      TendstoInMeasure μ (bootstrapMeanVecIndexed Pstar Zstar) atTop
        (fun _ => m))
    (hcross :
      TendstoInMeasure μ (bootstrapCrossMomentMatIndexed Pstar Zstar) atTop
        (fun _ => M₂))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) :=
  chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ) hfinite
    (chapter10_indexed_bootstrap_covarianceMat_tendsto_of_moments
      (μ := μ) hPstar hZ hmean hcross)

/-- Indexed zero-mean finite-replication covariance-matrix wrapper for Hansen
Theorem 10.11. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_zero_mean_moments
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {V : Matrix k k ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hmean :
      TendstoInMeasure μ (bootstrapMeanVecIndexed Pstar Zstar)
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ (bootstrapCrossMomentMatIndexed Pstar Zstar)
        atTop (fun _ => V))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => V) := by
  simpa using
    (chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_bootstrap_moments
      (μ := μ) (m := fun _ : k => 0) (M₂ := V)
      hPstar hZ hmean hcross hfinite)

/-- Hansen Theorem 10.9/10.11 finite-replication covariance matrix from
bootstrap weak convergence and uniform-square-tail controls.

This is the moment-form covariance counterpart of
`chapter10_finiteReplicationVariance_tendsto_of_weak_distribution_uniformSquareTail`.
The finite-replication simulation error estimates the conditional bootstrap
covariance, and the Theorem 10.9 weak/uniform-square-tail covariance bridge
identifies its limit. -/
theorem chapter10_finiteReplicationCovarianceMat_tendsto_of_weak_distribution_uniformSquareTail
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailCoord :
      ∀ a,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs => Zstar n ω ωs a) ν
          (fun ωlim => Z ωlim a))
    (hTailSum :
      ∀ a c,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) ν
          (fun ωlim => Z ωlim a + Z ωlim c))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMat Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ) hfinite
    (chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailCoord hTailSum)

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication covariance matrix
from bootstrap weak convergence and indexed uniform-square-tail controls. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_weak_distribution_uniformSquareTail
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailCoord :
      ∀ a,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs => Zstar n ω ωs a) ν
          (fun ωlim => Z ωlim a))
    (hTailSum :
      ∀ a c,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) ν
          (fun ωlim => Z ωlim a + Z ωlim c))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ) hfinite
    (chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailCoord hTailSum)

/-- Hansen Theorem 10.9/10.11 bridge for the textbook-centered finite
replication covariance matrix.

This is the covariance-matrix analogue of
`chapter10_finiteReplicationVariance_tendsto_of_bootstrap_variance`: an
`oₚ(1)` simulation-error premise against the conditional bootstrap covariance,
together with conditional covariance consistency, yields asymptotic consistency
of Hansen's centered finite-replication estimator. -/
theorem chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    {k : Type*} [Fintype k]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {V : Matrix k k ℝ}
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMat Pstar Zstar n ω)
        atTop (fun _ => 0))
    (hboot :
      TendstoInMeasure μ (bootstrapCovarianceMat Pstar Zstar) atTop
        (fun _ => V)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => V) :=
  TendstoInMeasure.of_sub_tendsto_zero_matrix hfinite hboot

/-- Indexed Hansen Theorem 10.9/10.11 bridge for the textbook-centered finite
replication covariance matrix. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {V : Matrix k k ℝ}
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar Zstar n ω)
        atTop (fun _ => 0))
    (hboot :
      TendstoInMeasure μ (bootstrapCovarianceMatIndexed Pstar Zstar) atTop
        (fun _ => V)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => V) :=
  TendstoInMeasure.of_sub_tendsto_zero_matrix hfinite hboot

/-- Hansen Theorem 10.9/10.11 centered finite-replication covariance from
bootstrap weak convergence and uniform-square-tail controls.

This composes the Theorem 10.9 conditional covariance consistency wrapper with
the finite-replication simulation-error transfer for Hansen's centered
covariance estimator. Coordinate and coordinate-sum uniform square tails supply
the conditional covariance target by polarization. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_weak_distribution_uniformSquareTail
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailCoord :
      ∀ a,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs => Zstar n ω ωs a) ν
          (fun ωlim => Z ωlim a))
    (hTailSum :
      ∀ a c,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) ν
          (fun ωlim => Z ωlim a + Z ωlim c))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMat Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ) hfinite
    (chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailCoord hTailSum)

/-- Indexed Hansen Theorem 10.9/10.11 centered finite-replication covariance
from bootstrap weak convergence and indexed uniform-square-tail controls. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_weak_tail
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailCoord :
      ∀ a,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs => Zstar n ω ωs a) ν
          (fun ωlim => Z ωlim a))
    (hTailSum :
      ∀ a c,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) ν
          (fun ωlim => Z ωlim a + Z ωlim c))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ) hfinite
    (chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailCoord hTailSum)

/-- Hansen Theorem 10.9/10.11 scalar centered finite-replication covariance
from conditional bootstrap covariance consistency.

This is the real-coordinate counterpart of
`chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance`:
an `oₚ(1)` simulation-error premise against the conditional bootstrap
covariance transfers conditional covariance consistency to Hansen's centered
finite-replication covariance estimator. -/
theorem chapter10_finiteReplicationCovarianceCenteredReal_tendsto_of_bootstrap_covariance
    {Xsim Ysim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Xstar Ystar : ℕ → Ω → Ωs → ℝ}
    {v : ℝ}
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredReal Xsim Ysim n ω -
            ((Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs] -
              (Pstar n ω)[Xstar n ω] * (Pstar n ω)[Ystar n ω]))
        atTop (fun _ => 0))
    (hboot :
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs] -
            (Pstar n ω)[Xstar n ω] * (Pstar n ω)[Ystar n ω])
        atTop (fun _ => v)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredReal Xsim Ysim)
      atTop (fun _ => v) :=
  TendstoInMeasure.of_sub_tendsto_zero_real hfinite hboot

/-- Hansen Theorem 10.9/10.11 scalar centered finite-replication covariance
from conditional bootstrap moment convergence.

This packages the simulation-error bridge with the conditional bootstrap
covariance moment theorem: convergence of the conditional bootstrap means and
cross moment supplies the conditional covariance target. -/
theorem chapter10_finiteReplicationCovarianceCenteredReal_tendsto_of_bootstrap_moments
    {Xsim Ysim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Xstar Ystar : ℕ → Ω → Ωs → ℝ}
    {mX mY mXY : ℝ}
    (hmeanX :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[Xstar n ω])
        atTop (fun _ => mX))
    (hmeanY :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[Ystar n ω])
        atTop (fun _ => mY))
    (hcross :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs])
        atTop (fun _ => mXY))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredReal Xsim Ysim n ω -
            ((Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs] -
              (Pstar n ω)[Xstar n ω] * (Pstar n ω)[Ystar n ω]))
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredReal Xsim Ysim)
      atTop (fun _ => mXY - mX * mY) :=
  chapter10_finiteReplicationCovarianceCenteredReal_tendsto_of_bootstrap_covariance
    (μ := μ) hfinite
    (chapter10_bootstrap_covarianceReal_tendsto_of_moments
      (μ := μ) hmeanX hmeanY hcross)

/-- Zero-mean scalar finite-replication covariance wrapper for Hansen Theorem
10.11. -/
theorem chapter10_finiteReplicationCovarianceCenteredReal_tendsto_of_bootstrap_zero_mean_moments
    {Xsim Ysim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Xstar Ystar : ℕ → Ω → Ωs → ℝ}
    {v : ℝ}
    (hmeanX :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[Xstar n ω])
        atTop (fun _ => 0))
    (hmeanY :
      TendstoInMeasure μ (fun n ω => (Pstar n ω)[Ystar n ω])
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs])
        atTop (fun _ => v))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredReal Xsim Ysim n ω -
            ((Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs] -
              (Pstar n ω)[Xstar n ω] * (Pstar n ω)[Ystar n ω]))
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredReal Xsim Ysim)
      atTop (fun _ => v) := by
  simpa using
    (chapter10_finiteReplicationCovarianceCenteredReal_tendsto_of_bootstrap_moments
      (μ := μ) (mX := 0) (mY := 0) (mXY := v)
      hmeanX hmeanY hcross hfinite)

/-- Hansen Theorem 10.9/10.11 finite-replication covariance matrix from
conditional bootstrap moment convergence.

This combines the centered finite-replication simulation-error premise with
the conditional bootstrap covariance-matrix moment bridge. It is the untrimmed
matrix analogue of the trimmed moment wrapper used for Theorem 10.12. -/
theorem chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_moments
    {k : Type*} [Fintype k]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hmean :
      TendstoInMeasure μ (bootstrapMeanVec Pstar Zstar) atTop (fun _ => m))
    (hcross :
      TendstoInMeasure μ (bootstrapCrossMomentMat Pstar Zstar) atTop
        (fun _ => M₂))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMat Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ) hfinite
    (chapter10_bootstrap_covarianceMat_tendsto_of_moments
      (μ := μ) hPstar hZ hmean hcross)

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication covariance matrix
from conditional bootstrap moment convergence, stated for Hansen's centered
estimator. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_moments
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hmean :
      TendstoInMeasure μ (bootstrapMeanVecIndexed Pstar Zstar) atTop
        (fun _ => m))
    (hcross :
      TendstoInMeasure μ (bootstrapCrossMomentMatIndexed Pstar Zstar) atTop
        (fun _ => M₂))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ) hfinite
    (chapter10_indexed_bootstrap_covarianceMat_tendsto_of_moments
      (μ := μ) hPstar hZ hmean hcross)

/-- Zero-mean finite-replication covariance-matrix wrapper for Hansen Theorem
10.11. -/
theorem chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_zero_mean_moments
    {k : Type*} [Fintype k]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {V : Matrix k k ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hmean :
      TendstoInMeasure μ (bootstrapMeanVec Pstar Zstar)
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ (bootstrapCrossMomentMat Pstar Zstar)
        atTop (fun _ => V))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMat Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => V) := by
  simpa using
    (chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_moments
      (μ := μ) (m := fun _ : k => 0) (M₂ := V)
      hPstar hZ hmean hcross hfinite)

/-- Indexed zero-mean finite-replication covariance-matrix wrapper for Hansen
Theorem 10.11, stated for Hansen's centered estimator. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_zero_mean_moments
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {V : Matrix k k ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hmean :
      TendstoInMeasure μ (bootstrapMeanVecIndexed Pstar Zstar)
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ (bootstrapCrossMomentMatIndexed Pstar Zstar)
        atTop (fun _ => V))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => V) := by
  simpa using
    (chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_moments
      (μ := μ) (m := fun _ : k => 0) (M₂ := V)
      hPstar hZ hmean hcross hfinite)

/-- Hansen Theorem 10.11/10.12 finite-replication trimmed covariance bridge.

If Hansen's centered finite-replication covariance estimator is `oₚ(1)` close
to the trimmed conditional bootstrap covariance, then any consistency theorem
for the trimmed conditional covariance transfers to the finite-replication
estimator. -/
theorem chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmedBootstrapVariance
    {k : Type*} [Fintype k]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {τ : ℕ → ℝ} {V : Matrix k k ℝ}
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMat Pstar Zstar τ n ω)
        atTop (fun _ => 0))
    (htrim :
      TendstoInMeasure μ (trimmedBootstrapCovarianceMat Pstar Zstar τ)
        atTop (fun _ => V)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => V) :=
  TendstoInMeasure.of_sub_tendsto_zero_matrix hfinite htrim

/-- Indexed Hansen Theorem 10.11/10.12 finite-replication trimmed covariance
bridge for sample-size-dependent bootstrap spaces. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmedBootstrapVariance
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {τ : ℕ → ℝ} {V : Matrix k k ℝ}
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω)
        atTop (fun _ => 0))
    (htrim :
      TendstoInMeasure μ (trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ)
        atTop (fun _ => V)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => V) :=
  TendstoInMeasure.of_sub_tendsto_zero_matrix hfinite htrim

/-- Hansen Theorem 10.11/10.12 finite-replication trimmed covariance from
trimmed conditional moments.

This combines the finite-replication simulation-error premise with the trimmed
conditional covariance moment bridge.  The remaining model-specific work is to
verify the finite-replication `oₚ(1)` error and the trimmed moment premises. -/
theorem chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_moments
    {k : Type*} [Fintype k]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {τ : ℕ → ℝ} {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ :
      ∀ n ω a,
        MemLp (fun ωs => trimmedBootstrapStatistic Zstar τ n ω ωs a) 2
          (Pstar n ω))
    (hmean :
      TendstoInMeasure μ
        (bootstrapMeanVec Pstar (trimmedBootstrapStatistic Zstar τ))
        atTop (fun _ => m))
    (hcross :
      TendstoInMeasure μ
        (bootstrapCrossMomentMat Pstar (trimmedBootstrapStatistic Zstar τ))
        atTop (fun _ => M₂))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMat Pstar Zstar τ n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmedBootstrapVariance
    (μ := μ) hfinite
    (chapter10_trimmedBootstrapVariance_tendsto_of_moments
      (μ := μ) hPstar hZ hmean hcross)

/-- Indexed Hansen Theorem 10.11/10.12 finite-replication trimmed covariance
from trimmed conditional moments. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_moments
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {τ : ℕ → ℝ} {m : k → ℝ} {M₂ : Matrix k k ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ :
      ∀ n ω a,
        MemLp
          (fun ωs => trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a) 2
          (Pstar n ω))
    (hmean :
      TendstoInMeasure μ
        (bootstrapMeanVecIndexed Pstar
          (trimmedBootstrapStatisticIndexed Zstar τ))
        atTop (fun _ => m))
    (hcross :
      TendstoInMeasure μ
        (bootstrapCrossMomentMatIndexed Pstar
          (trimmedBootstrapStatisticIndexed Zstar τ))
        atTop (fun _ => M₂))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c => M₂ a c - m a * m c) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmedBootstrapVariance
    (μ := μ) hfinite
    (chapter10_indexed_trimmedBootstrapVariance_tendsto_of_moments
      (μ := μ) hPstar hZ hmean hcross)

/-- Hansen Theorem 10.11/10.12 zero-mean finite-replication trimmed covariance
wrapper.

In the asymptotically centered case, simulation error against the trimmed
conditional covariance plus convergence of the trimmed conditional cross moment
to `V` yields consistency of Hansen's centered finite-replication covariance
estimator for `V`. -/
theorem chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_zero_mean_moments
    {k : Type*} [Fintype k]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {τ : ℕ → ℝ} {V : Matrix k k ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ :
      ∀ n ω a,
        MemLp (fun ωs => trimmedBootstrapStatistic Zstar τ n ω ωs a) 2
          (Pstar n ω))
    (hmean :
      TendstoInMeasure μ
        (bootstrapMeanVec Pstar (trimmedBootstrapStatistic Zstar τ))
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ
        (bootstrapCrossMomentMat Pstar (trimmedBootstrapStatistic Zstar τ))
        atTop (fun _ => V))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMat Pstar Zstar τ n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => V) := by
  simpa using
    (chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_moments
      (μ := μ) (m := fun _ : k => 0) (M₂ := V)
      hPstar hZ hmean hcross hfinite)

/-- Indexed Hansen Theorem 10.11/10.12 zero-mean finite-replication trimmed
covariance wrapper. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_zero_mean_moments
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {τ : ℕ → ℝ} {V : Matrix k k ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ :
      ∀ n ω a,
        MemLp
          (fun ωs => trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a) 2
          (Pstar n ω))
    (hmean :
      TendstoInMeasure μ
        (bootstrapMeanVecIndexed Pstar
          (trimmedBootstrapStatisticIndexed Zstar τ))
        atTop (fun _ => 0))
    (hcross :
      TendstoInMeasure μ
        (bootstrapCrossMomentMatIndexed Pstar
          (trimmedBootstrapStatisticIndexed Zstar τ))
        atTop (fun _ => V))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => V) := by
  simpa using
    (chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_moments
      (μ := μ) (m := fun _ : k => 0) (M₂ := V)
      hPstar hZ hmean hcross hfinite)

end FiniteReplicationVariance

section QuantileConvergence

/-- Bracketing property for a lower quantile selected from a random CDF.

For each sample point, values whose CDF is still below `p` must lie below the
selected quantile, and values whose CDF is already above `p` must lie above it.
This is the theorem-facing condition supplied by concrete bootstrap quantile
definitions such as the generalized inverse of a conditional bootstrap CDF. -/
structure CDFQuantileBracket
    (Gseq : ℕ → Ω → ℝ → ℝ) (p : ℝ) (qseq : ℕ → Ω → ℝ) : Prop where
  lower : ∀ n ω x, Gseq n ω x < p → x < qseq n ω
  upper : ∀ n ω x, p < Gseq n ω x → qseq n ω ≤ x

/-- Lower generalized inverse of a real CDF-like function. -/
noncomputable def lowerCDFQuantile (G : ℝ → ℝ) (p : ℝ) : ℝ :=
  sInf {x : ℝ | p ≤ G x}

/-- A point where the CDF-like function has reached level `p` lies weakly above
the lower generalized inverse. -/
theorem lowerCDFQuantile_le
    {G : ℝ → ℝ} {p x : ℝ}
    (hbdd : BddBelow {y : ℝ | p ≤ G y})
    (hx : p ≤ G x) :
    lowerCDFQuantile G p ≤ x := by
  simpa [lowerCDFQuantile] using
    (csInf_le (s := {y : ℝ | p ≤ G y}) hbdd hx)

/-- If a monotone CDF-like function remains below `p` just to the right of
`x`, then `x` lies strictly below the lower generalized inverse. -/
theorem lt_lowerCDFQuantile_of_exists_right_lt
    {G : ℝ → ℝ} {p x : ℝ}
    (hmono : Monotone G)
    (hne : ({y : ℝ | p ≤ G y} : Set ℝ).Nonempty)
    (hlocal : ∃ δ : ℝ, 0 < δ ∧ G (x + δ) < p) :
    x < lowerCDFQuantile G p := by
  obtain ⟨δ, hδ_pos, hxδ⟩ := hlocal
  have hbound : ∀ y ∈ ({y : ℝ | p ≤ G y} : Set ℝ), x + δ ≤ y := by
    intro y hy
    by_contra hnot
    have hylt : y < x + δ := lt_of_not_ge hnot
    have hGy_le : G y ≤ G (x + δ) := hmono hylt.le
    have hy_le : p ≤ G y := hy
    linarith
  have hle : x + δ ≤ lowerCDFQuantile G p := by
    simpa [lowerCDFQuantile] using
      (le_csInf (s := {y : ℝ | p ≤ G y}) hne hbound)
  linarith

/-- Lower generalized inverses bracket their CDF levels when the random CDFs
are monotone and locally stay below `p` immediately to the right of any point
where they are below `p`. -/
theorem lowerCDFQuantile_bracket_of_local_right_lt
    {Gseq : ℕ → Ω → ℝ → ℝ} {p : ℝ}
    (hmono : ∀ n ω, Monotone (Gseq n ω))
    (hne : ∀ n ω, ({x : ℝ | p ≤ Gseq n ω x} : Set ℝ).Nonempty)
    (hbdd : ∀ n ω, BddBelow {x : ℝ | p ≤ Gseq n ω x})
    (hlocal :
      ∀ n ω x, Gseq n ω x < p →
        ∃ δ : ℝ, 0 < δ ∧ Gseq n ω (x + δ) < p) :
    CDFQuantileBracket Gseq p
      (fun n ω => lowerCDFQuantile (Gseq n ω) p) := by
  constructor
  · intro n ω x hx
    exact lt_lowerCDFQuantile_of_exists_right_lt
      (hmono n ω) (hne n ω) (hlocal n ω x hx)
  · intro n ω x hx
    exact lowerCDFQuantile_le (hbdd n ω) (le_of_lt hx)

private theorem stieltjesFunction_exists_right_lt_of_lt
    (G : StieltjesFunction ℝ) {p x : ℝ} (hx : G x < p) :
    ∃ δ : ℝ, 0 < δ ∧ G (x + δ) < p := by
  have hcont := Metric.continuousWithinAt_iff.mp (G.right_continuous x)
  obtain ⟨δ, hδ_pos, hδ⟩ := hcont (p - G x) (sub_pos.mpr hx)
  refine ⟨δ / 2, by positivity, ?_⟩
  have hx_mem : x + δ / 2 ∈ Set.Ici x := by
    dsimp
    exact le_add_of_nonneg_right (by positivity : 0 ≤ δ / 2)
  have hdist : dist (x + δ / 2) x < δ := by
    rw [Real.dist_eq]
    have habs : |x + δ / 2 - x| = δ / 2 := by
      have hnonneg : 0 ≤ x + δ / 2 - x := by
        rwa [sub_nonneg]
      rw [abs_of_nonneg hnonneg]
      ring
    rw [habs]
    linarith
  have hdistG := hδ hx_mem hdist
  rw [Real.dist_eq] at hdistG
  have hlt := (abs_lt.mp hdistG).2
  linarith

/-- Stieltjes-function CDFs supply the right-local persistence premise for the
lower generalized inverse through right-continuity. -/
theorem lowerCDFQuantile_bracket_of_stieltjesFunction
    {Gseq : ℕ → Ω → StieltjesFunction ℝ} {p : ℝ}
    (hne :
      ∀ n ω, ({x : ℝ | p ≤ Gseq n ω x} : Set ℝ).Nonempty)
    (hbdd : ∀ n ω, BddBelow {x : ℝ | p ≤ Gseq n ω x}) :
    CDFQuantileBracket (fun n ω x => Gseq n ω x) p
      (fun n ω => lowerCDFQuantile (fun x => Gseq n ω x) p) :=
  lowerCDFQuantile_bracket_of_local_right_lt
    (hmono := fun n ω => (Gseq n ω).mono)
    hne hbdd
    (fun n ω x hx => stieltjesFunction_exists_right_lt_of_lt (Gseq n ω) (x := x) hx)

/-- Quantile convergence from pointwise CDF convergence at strict bracketing
points.

If the random CDFs `Gseq n` converge in probability to `G` at every fixed
point, the target `q` is strictly bracketed by the limiting CDF around level
`p`, and `qseq` is a lower-quantile selection for each random CDF, then
`qseq ->p q`.  This is the reusable quantile-convergence constructor behind
the percentile, percentile-`t`, and bootstrap critical-value endpoints in
Hansen Theorems 10.13, 10.14, and 10.16. -/
theorem tendstoInMeasure_quantile_of_cdf_brackets
    {Gseq : ℕ → Ω → ℝ → ℝ} {G : ℝ → ℝ} {p q : ℝ}
    {qseq : ℕ → Ω → ℝ}
    (hbracket : CDFQuantileBracket Gseq p qseq)
    (hleft : ∀ ε : ℝ, 0 < ε → G (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < G (q + ε))
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ (fun n ω => Gseq n ω x) atTop (fun _ => G x)) :
    TendstoInMeasure μ qseq atTop (fun _ => q) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ_pos : 0 < δ := by positivity
  have hδ_lt : δ < ε := by
    dsimp [δ]
    linarith
  let xL : ℝ := q - δ
  let xU : ℝ := q + δ
  let gapL : ℝ := p - G xL
  let gapU : ℝ := G xU - p
  have hgapL_pos : 0 < gapL := by
    dsimp [gapL, xL]
    exact sub_pos.mpr (hleft δ hδ_pos)
  have hgapU_pos : 0 < gapU := by
    dsimp [gapU, xU]
    exact sub_pos.mpr (hright δ hδ_pos)
  have hleft_tendsto := (tendstoInMeasure_iff_dist.mp (hG xL)) gapL hgapL_pos
  have hright_tendsto := (tendstoInMeasure_iff_dist.mp (hG xU)) gapU hgapU_pos
  have hsum :
      Tendsto
        (fun n =>
          μ {ω | gapL ≤ dist (Gseq n ω xL) (G xL)} +
            μ {ω | gapU ≤ dist (Gseq n ω xU) (G xU)})
        atTop (𝓝 0) := by
    simpa using hleft_tendsto.add hright_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le _) ?_
  intro n
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_union, Set.mem_setOf_eq] at hω ⊢
  by_cases hleft_bad : gapL ≤ dist (Gseq n ω xL) (G xL)
  · exact Or.inl hleft_bad
  · right
    by_contra hright_not_bad
    have hleft_close : dist (Gseq n ω xL) (G xL) < gapL := not_le.mp hleft_bad
    have hright_close : dist (Gseq n ω xU) (G xU) < gapU := not_le.mp hright_not_bad
    have hleft_abs : |Gseq n ω xL - G xL| < gapL := by
      simpa [Real.dist_eq] using hleft_close
    have hright_abs : |Gseq n ω xU - G xU| < gapU := by
      simpa [Real.dist_eq] using hright_close
    have hG_left_lt : Gseq n ω xL < p := by
      have hlt := (abs_lt.mp hleft_abs).2
      dsimp [gapL] at hlt
      linarith
    have hG_right_gt : p < Gseq n ω xU := by
      have hlt := (abs_lt.mp hright_abs).1
      dsimp [gapU] at hlt
      linarith
    have hq_lower : q - δ < qseq n ω := by
      simpa [xL] using hbracket.lower n ω xL hG_left_lt
    have hq_upper : qseq n ω ≤ q + δ := by
      simpa [xU] using hbracket.upper n ω xU hG_right_gt
    have hdist_lt : dist (qseq n ω) q < ε := by
      rw [Real.dist_eq]
      exact abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
    exact (not_le_of_gt hdist_lt) hω

/-- A strictly increasing limit CDF brackets its quantile level on both sides. -/
theorem strictMono_cdf_brackets
    {G : ℝ → ℝ} {p q : ℝ}
    (hstrict : StrictMono G) (hq : G q = p) :
    (∀ ε : ℝ, 0 < ε → G (q - ε) < p) ∧
      (∀ ε : ℝ, 0 < ε → p < G (q + ε)) := by
  constructor
  · intro ε hε
    rw [← hq]
    exact hstrict (by linarith)
  · intro ε hε
    rw [← hq]
    exact hstrict (by linarith)

/-- Quantile convergence from pointwise CDF convergence and a strictly
increasing limiting CDF.

This is the common calibrated-quantile specialization of
`tendstoInMeasure_quantile_of_cdf_brackets`: the strict bracketing premises are
derived from `G(q) = p` and strict monotonicity of the limiting CDF. -/
theorem tendstoInMeasure_quantile_of_strictMono_cdf
    {Gseq : ℕ → Ω → ℝ → ℝ} {G : ℝ → ℝ} {p q : ℝ}
    {qseq : ℕ → Ω → ℝ}
    (hbracket : CDFQuantileBracket Gseq p qseq)
    (hstrict : StrictMono G)
    (hq : G q = p)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ (fun n ω => Gseq n ω x) atTop (fun _ => G x)) :
    TendstoInMeasure μ qseq atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact tendstoInMeasure_quantile_of_cdf_brackets
    (μ := μ) hbracket hleft hright hG

/-- Quantile convergence for lower generalized inverses under explicit
monotonicity and right-local CDF bracketing assumptions. -/
theorem lowerCDFQuantile_tendstoInMeasure_of_cdf_brackets
    {Gseq : ℕ → Ω → ℝ → ℝ} {G : ℝ → ℝ} {p q : ℝ}
    (hmono : ∀ n ω, Monotone (Gseq n ω))
    (hne : ∀ n ω, ({x : ℝ | p ≤ Gseq n ω x} : Set ℝ).Nonempty)
    (hbdd : ∀ n ω, BddBelow {x : ℝ | p ≤ Gseq n ω x})
    (hlocal :
      ∀ n ω x, Gseq n ω x < p →
        ∃ δ : ℝ, 0 < δ ∧ Gseq n ω (x + δ) < p)
    (hleft : ∀ ε : ℝ, 0 < ε → G (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < G (q + ε))
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ (fun n ω => Gseq n ω x) atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (fun n ω => lowerCDFQuantile (Gseq n ω) p) atTop (fun _ => q) :=
  tendstoInMeasure_quantile_of_cdf_brackets
    (μ := μ)
    (hbracket := lowerCDFQuantile_bracket_of_local_right_lt
      hmono hne hbdd hlocal)
    hleft hright hG

/-- Strict-limit-CDF specialization of lower generalized-inverse convergence. -/
theorem lowerCDFQuantile_tendstoInMeasure_of_strictMono_cdf
    {Gseq : ℕ → Ω → ℝ → ℝ} {G : ℝ → ℝ} {p q : ℝ}
    (hmono : ∀ n ω, Monotone (Gseq n ω))
    (hne : ∀ n ω, ({x : ℝ | p ≤ Gseq n ω x} : Set ℝ).Nonempty)
    (hbdd : ∀ n ω, BddBelow {x : ℝ | p ≤ Gseq n ω x})
    (hlocal :
      ∀ n ω x, Gseq n ω x < p →
        ∃ δ : ℝ, 0 < δ ∧ Gseq n ω (x + δ) < p)
    (hstrict : StrictMono G)
    (hq : G q = p)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ (fun n ω => Gseq n ω x) atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (fun n ω => lowerCDFQuantile (Gseq n ω) p) atTop (fun _ => q) :=
  tendstoInMeasure_quantile_of_strictMono_cdf
    (μ := μ)
    (hbracket := lowerCDFQuantile_bracket_of_local_right_lt
      hmono hne hbdd hlocal)
    hstrict hq hG

/-- Lower generalized-inverse convergence for random Stieltjes-function CDFs. -/
theorem lowerCDFQuantile_tendstoInMeasure_of_stieltjesFunction
    {Gseq : ℕ → Ω → StieltjesFunction ℝ} {G : ℝ → ℝ} {p q : ℝ}
    (hne :
      ∀ n ω, ({x : ℝ | p ≤ Gseq n ω x} : Set ℝ).Nonempty)
    (hbdd : ∀ n ω, BddBelow {x : ℝ | p ≤ Gseq n ω x})
    (hleft : ∀ ε : ℝ, 0 < ε → G (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < G (q + ε))
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ (fun n ω => Gseq n ω x) atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (fun n ω => lowerCDFQuantile (fun x => Gseq n ω x) p)
      atTop (fun _ => q) :=
  tendstoInMeasure_quantile_of_cdf_brackets
    (μ := μ)
    (hbracket := lowerCDFQuantile_bracket_of_stieltjesFunction hne hbdd)
    hleft hright hG

/-- Strict-limit-CDF specialization for random Stieltjes-function lower
generalized inverses. -/
theorem lowerCDFQuantile_tendstoInMeasure_of_stieltjesFunction_strictMono
    {Gseq : ℕ → Ω → StieltjesFunction ℝ} {G : ℝ → ℝ} {p q : ℝ}
    (hne :
      ∀ n ω, ({x : ℝ | p ≤ Gseq n ω x} : Set ℝ).Nonempty)
    (hbdd : ∀ n ω, BddBelow {x : ℝ | p ≤ Gseq n ω x})
    (hstrict : StrictMono G)
    (hq : G q = p)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ (fun n ω => Gseq n ω x) atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (fun n ω => lowerCDFQuantile (fun x => Gseq n ω x) p)
      atTop (fun _ => q) :=
  tendstoInMeasure_quantile_of_strictMono_cdf
    (μ := μ)
    (hbracket := lowerCDFQuantile_bracket_of_stieltjesFunction hne hbdd)
    hstrict hq hG

/-- Limit scalar CDF `G(x) = P[Z ≤ x]`. -/
noncomputable def scalarCDF
    (ν : Measure Ωlim) (Z : Ωlim → ℝ) (x : ℝ) : ℝ :=
  (ν {ωlim | Z ωlim ≤ x}).toReal

/-- Limit scalar CDFs are monotone under finite limit measures. -/
theorem scalarCDF_mono
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} [IsFiniteMeasure ν] :
    Monotone (scalarCDF ν Z) := by
  intro x y hxy
  refine ENNReal.toReal_mono (measure_ne_top ν {ωlim | Z ωlim ≤ y}) ?_
  exact measure_mono fun ωlim hωlim => le_trans hωlim hxy

/-- The scalar-CDF bridge agrees with Mathlib's real-law CDF for the identity
statistic. -/
@[simp]
theorem scalarCDF_id_eq_cdf
    (η : Measure ℝ) [IsProbabilityMeasure η] :
    scalarCDF η (fun x : ℝ => x) = fun x => cdf η x := by
  funext x
  simpa [scalarCDF, Set.Iic, Measure.real] using
    (ProbabilityTheory.cdf_eq_real η x).symm

/-- Scalar CDF continuity gives continuity of the one-dimensional vector-CDF
view used by Hansen Definition 10.2. -/
theorem continuousAt_vectorCDF_unit_of_scalarCDF
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {x : ℝ}
    (hx : ContinuousAt (scalarCDF ν Z) x) :
    ContinuousAt
      (fun y : Unit → ℝ =>
        vectorCDF ν (fun ωlim (_ : Unit) => Z ωlim) y)
      (fun _ : Unit => x) := by
  have hcomp :
      ContinuousAt ((scalarCDF ν Z) ∘ (fun y : Unit → ℝ => y ()))
        (fun _ : Unit => x) := by
    exact hx.comp (continuous_apply ()).continuousAt
  have hfun :
      (fun y : Unit → ℝ =>
        vectorCDF ν (fun ωlim (_ : Unit) => Z ωlim) y) =
        (scalarCDF ν Z) ∘ (fun y : Unit → ℝ => y ()) := by
    funext y
    have hset :
        {ωlim | coordinateLE (fun _ : Unit => Z ωlim) y} =
          {ωlim | Z ωlim ≤ y ()} := by
      ext ωlim
      constructor
      · intro h
        exact h ()
      · intro h i
        simpa [Subsingleton.elim i ()] using h
    simp [scalarCDF, vectorCDF, hset]
  rw [hfun]
  exact hcomp

/-- Scalar conditional bootstrap CDF `P*[Zₙ* ≤ x]`. -/
noncomputable def bootstrapScalarCDF
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → ℝ)
    (x : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((Pstar n ω) {ωs | Zstar n ω ωs ≤ x}).toReal

/-- Conditional bootstrap scalar CDFs are monotone under finite conditional
bootstrap measures. -/
theorem bootstrapScalarCDF_mono
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {n : ℕ} {ω : Ω} [IsFiniteMeasure (Pstar n ω)] :
    Monotone (fun x => bootstrapScalarCDF Pstar Zstar x n ω) := by
  intro x y hxy
  refine ENNReal.toReal_mono
    (measure_ne_top (Pstar n ω) {ωs | Zstar n ω ωs ≤ y}) ?_
  exact measure_mono fun ωs hωs => le_trans hωs hxy

/-- Conditional bootstrap scalar CDF as Mathlib's CDF of the push-forward law. -/
theorem bootstrapScalarCDF_eq_cdf_map
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {n : ℕ} {ω : Ω}
    (hPstar : IsProbabilityMeasure (Pstar n ω))
    (hZ : AEMeasurable (Zstar n ω) (Pstar n ω)) (x : ℝ) :
    bootstrapScalarCDF Pstar Zstar x n ω =
      cdf ((Pstar n ω).map (Zstar n ω)) x := by
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar
  haveI : IsProbabilityMeasure ((Pstar n ω).map (Zstar n ω)) :=
    Measure.isProbabilityMeasure_map hZ
  rw [ProbabilityTheory.cdf_eq_real]
  rw [Measure.real]
  rw [Measure.map_apply_of_aemeasurable hZ measurableSet_Iic]
  simp [bootstrapScalarCDF, Set.Iic]

/-- Scalar conditional bootstrap CDFs remain below a level just to the right
of any point where they are strictly below it.

This is the standard right-continuity bracketing premise for lower generalized
inverse arguments, derived from Mathlib's CDF of the push-forward law. -/
theorem bootstrapScalarCDF_exists_right_lt_of_lt
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {n : ℕ} {ω : Ω}
    (hPstar : IsProbabilityMeasure (Pstar n ω))
    (hZ : AEMeasurable (Zstar n ω) (Pstar n ω))
    {p x : ℝ}
    (hx : bootstrapScalarCDF Pstar Zstar x n ω < p) :
    ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p := by
  let η : Measure ℝ := (Pstar n ω).map (Zstar n ω)
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar
  haveI : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map hZ
  have hcdf_eq :
      ∀ y : ℝ, bootstrapScalarCDF Pstar Zstar y n ω = cdf η y := by
    intro y
    exact bootstrapScalarCDF_eq_cdf_map
      (Pstar := Pstar) (Zstar := Zstar) (n := n) (ω := ω) hPstar hZ y
  have hx_cdf : cdf η x < p := by
    simpa [hcdf_eq x] using hx
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    stieltjesFunction_exists_right_lt_of_lt (cdf η) (x := x) hx_cdf
  exact ⟨δ, hδ_pos, by simpa [hcdf_eq (x + δ)] using hδ⟩

/-- A pointwise a.e.-measurability package for the local-right bracketing
premise of scalar conditional bootstrap CDFs. -/
theorem bootstrapScalarCDF_local_right_lt_of_aemeasurable
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    {p : ℝ} :
    ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
      ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p :=
  fun n ω x hx =>
    bootstrapScalarCDF_exists_right_lt_of_lt
      (Pstar := Pstar) (Zstar := Zstar) (n := n) (ω := ω)
      (x := x) (hPstar n ω) (hZ n ω) hx

/-- For a scalar conditional bootstrap CDF, every level below one is reached
somewhere. -/
theorem bootstrapScalarCDF_level_nonempty_of_aemeasurable
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    {p : ℝ} (hp : p < 1) :
    ∀ n ω,
      ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} :
        Set ℝ).Nonempty := by
  intro n ω
  let η : Measure ℝ := (Pstar n ω).map (Zstar n ω)
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  haveI : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map (hZ n ω)
  have hEventually :
      ∀ᶠ x in atTop, p < cdf η x :=
    (ProbabilityTheory.tendsto_cdf_atTop η).eventually_const_lt hp
  obtain ⟨x, hx⟩ := hEventually.exists
  refine ⟨x, ?_⟩
  have hcdf_eq :
      bootstrapScalarCDF Pstar Zstar x n ω = cdf η x :=
    bootstrapScalarCDF_eq_cdf_map
      (Pstar := Pstar) (Zstar := Zstar) (n := n) (ω := ω)
      (hPstar n ω) (hZ n ω) x
  change p ≤ bootstrapScalarCDF Pstar Zstar x n ω
  rw [hcdf_eq]
  exact le_of_lt hx

/-- For a scalar conditional bootstrap CDF, every strictly positive level has
a lower-bounded generalized-inverse set. -/
theorem bootstrapScalarCDF_level_bddBelow_of_aemeasurable
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    {p : ℝ} (hp : 0 < p) :
    ∀ n ω, BddBelow
      {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} := by
  intro n ω
  let η : Measure ℝ := (Pstar n ω).map (Zstar n ω)
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  haveI : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map (hZ n ω)
  have hEventually :
      ∀ᶠ x in atBot, cdf η x < p :=
    (ProbabilityTheory.tendsto_cdf_atBot η).eventually_lt_const hp
  obtain ⟨M, hM⟩ := eventually_atBot.mp hEventually
  refine ⟨M, ?_⟩
  intro x hx
  by_contra hnot
  have hx_le : x ≤ M := le_of_not_ge hnot
  have hcdf_lt : cdf η x < p := hM x hx_le
  have hboot_lt : bootstrapScalarCDF Pstar Zstar x n ω < p := by
    have hcdf_eq :
        bootstrapScalarCDF Pstar Zstar x n ω = cdf η x :=
      bootstrapScalarCDF_eq_cdf_map
        (Pstar := Pstar) (Zstar := Zstar) (n := n) (ω := ω)
        (hPstar n ω) (hZ n ω) x
    simpa [hcdf_eq] using hcdf_lt
  exact not_lt_of_ge hx hboot_lt

/-- Scalar CDF convergence extracted from Hansen Definition 10.2 in one
dimension.

This bridge lets scalar quantile arguments consume a one-dimensional
bootstrap-distribution convergence theorem stated in the finite-dimensional
`Unit → ℝ` API. -/
theorem TendstoInBootstrapDistribution.bootstrapScalarCDF_tendsto_unit
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    {x : ℝ}
    (hx :
      ContinuousAt
        (fun y : Unit → ℝ =>
          vectorCDF ν (fun ωlim (_ : Unit) => Z ωlim) y)
        (fun _ : Unit => x)) :
    TendstoInMeasure μ (fun n ω => bootstrapScalarCDF Pstar Zstar x n ω)
      atTop (fun _ => scalarCDF ν Z x) := by
  have hunit :=
    hZ.tendsto_cdf (x := fun _ : Unit => x) hx
  refine TendstoInMeasure.congr (fun n => ?_) ?_ hunit
  · exact ae_of_all μ fun ω => by
      simp [bootstrapScalarCDF, bootstrapVectorCDF, coordinateLE]
  · exact ae_of_all μ fun _ => by
      simp [scalarCDF, vectorCDF, coordinateLE]

/-- Scalar CDF convergence extracted from one-dimensional Hansen Definition
10.2, with continuity stated for the scalar CDF. -/
theorem TendstoInBootstrapDistribution.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    {x : ℝ}
    (hx : ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ (fun n ω => bootstrapScalarCDF Pstar Zstar x n ω)
      atTop (fun _ => scalarCDF ν Z x) :=
  hZ.bootstrapScalarCDF_tendsto_unit (x := x)
    (continuousAt_vectorCDF_unit_of_scalarCDF hx)

/-- Scalar CDF convergence from one-dimensional Hansen Definition 10.2 when
the limiting statistic is the identity under a scalar probability law. -/
theorem TendstoInBootstrapDistribution.bootstrapScalarCDF_tendsto_unit_id_cdf
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η]
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    {x : ℝ}
    (hx : ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ (fun n ω => bootstrapScalarCDF Pstar Zstar x n ω)
      atTop (fun _ => cdf η x) := by
  simpa using
    (TendstoInBootstrapDistribution.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := η)
      (Z := fun x : ℝ => x) hZ (by simpa using hx))

/-- Bootstrap scalar quantile convergence from pointwise conditional-CDF
convergence.

This is the bootstrap-specialized face of
`tendstoInMeasure_quantile_of_cdf_brackets`, stated with the scalar
conditional CDF `bootstrapScalarCDF`. -/
theorem bootstrapScalarQuantile_tendsto_of_cdf_brackets
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {G : ℝ → ℝ} {p q : ℝ} {qseq : ℕ → Ω → ℝ}
    (hbracket :
      CDFQuantileBracket
        (fun n ω x => bootstrapScalarCDF Pstar Zstar x n ω) p qseq)
    (hleft : ∀ ε : ℝ, 0 < ε → G (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < G (q + ε))
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Zstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ qseq atTop (fun _ => q) :=
  tendstoInMeasure_quantile_of_cdf_brackets
    (μ := μ) (Gseq := fun n ω x => bootstrapScalarCDF Pstar Zstar x n ω)
    hbracket hleft hright hG

/-- Bootstrap scalar quantile convergence with a strictly increasing limiting
CDF. -/
theorem bootstrapScalarQuantile_tendsto_of_strictMono_cdf
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {G : ℝ → ℝ} {p q : ℝ} {qseq : ℕ → Ω → ℝ}
    (hbracket :
      CDFQuantileBracket
        (fun n ω x => bootstrapScalarCDF Pstar Zstar x n ω) p qseq)
    (hstrict : StrictMono G)
    (hq : G q = p)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Zstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ qseq atTop (fun _ => q) :=
  tendstoInMeasure_quantile_of_strictMono_cdf
    (μ := μ) (Gseq := fun n ω x => bootstrapScalarCDF Pstar Zstar x n ω)
    hbracket hstrict hq hG

/-- Bootstrap scalar quantile convergence from one-dimensional Hansen
Definition 10.2.

This composes the one-dimensional Definition 10.2-to-scalar-CDF bridge with
the pointwise-CDF quantile constructor. -/
theorem bootstrapScalarQuantile_tendsto_of_bootstrapDistribution_unit
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    {qseq : ℕ → Ω → ℝ}
    (hbracket :
      CDFQuantileBracket
        (fun n ω x => bootstrapScalarCDF Pstar Zstar x n ω) p qseq)
    (hleft : ∀ ε : ℝ, 0 < ε → scalarCDF ν Z (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < scalarCDF ν Z (q + ε))
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ qseq atTop (fun _ => q) :=
  bootstrapScalarQuantile_tendsto_of_cdf_brackets
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (G := scalarCDF ν Z)
    hbracket hleft hright
    (fun x =>
      TendstoInBootstrapDistribution.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
        hZ (hcont x))

/-- Strict-limit-CDF specialization of scalar quantile convergence from
one-dimensional Hansen Definition 10.2. -/
theorem bootstrapScalarQuantile_tendsto_of_bootstrapDistribution_unit_strictMono
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    {qseq : ℕ → Ω → ℝ}
    (hbracket :
      CDFQuantileBracket
        (fun n ω x => bootstrapScalarCDF Pstar Zstar x n ω) p qseq)
    (hstrict : StrictMono (scalarCDF ν Z))
    (hq : scalarCDF ν Z q = p)
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ qseq atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarQuantile_tendsto_of_bootstrapDistribution_unit
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      hbracket hleft hright hZ hcont

/-- Lower generalized inverse of the scalar conditional bootstrap CDF. -/
noncomputable def bootstrapScalarLowerQuantile
    (Pstar : ℕ → Ω → Measure Ωs) (Zstar : ℕ → Ω → Ωs → ℝ)
    (p : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  lowerCDFQuantile (fun x => bootstrapScalarCDF Pstar Zstar x n ω) p

/-- Bootstrap scalar lower-quantile convergence from pointwise CDF convergence
and concrete generalized-inverse bracketing assumptions. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_cdf_brackets
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {G : ℝ → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Zstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p)
    (hleft : ∀ ε : ℝ, 0 < ε → G (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < G (q + ε))
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Zstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) :=
  lowerCDFQuantile_tendstoInMeasure_of_cdf_brackets
    (μ := μ) (Gseq := fun n ω x => bootstrapScalarCDF Pstar Zstar x n ω)
    hmono hne hbdd hlocal hleft hright hG

/-- Bootstrap scalar lower-quantile convergence with a strictly increasing
limiting CDF. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_strictMono_cdf
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {G : ℝ → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Zstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p)
    (hstrict : StrictMono G)
    (hq : G q = p)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Zstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) :=
  lowerCDFQuantile_tendstoInMeasure_of_strictMono_cdf
    (μ := μ) (Gseq := fun n ω x => bootstrapScalarCDF Pstar Zstar x n ω)
    hmono hne hbdd hlocal hstrict hq hG

/-- Bootstrap scalar lower-quantile convergence from one-dimensional Hansen
Definition 10.2.

This is the concrete generalized-inverse version of
`bootstrapScalarQuantile_tendsto_of_bootstrapDistribution_unit`. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Zstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p)
    (hleft : ∀ ε : ℝ, 0 < ε → scalarCDF ν Z (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < scalarCDF ν Z (q + ε))
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) :=
  bootstrapScalarLowerQuantile_tendsto_of_cdf_brackets
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (G := scalarCDF ν Z)
    hmono hne hbdd hlocal hleft hright
    (fun x =>
      TendstoInBootstrapDistribution.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
        hZ (hcont x))

/-- Strict-limit-CDF specialization of scalar lower-quantile convergence from
one-dimensional Hansen Definition 10.2. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_strictMono
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Zstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p)
    (hstrict : StrictMono (scalarCDF ν Z))
    (hq : scalarCDF ν Z q = p)
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      hmono hne hbdd hlocal hleft hright hZ hcont

/-- Finite conditional bootstrap measures supply the scalar-CDF monotonicity
premise in the lower-quantile Definition 10.2 wrapper. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_finite
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p)
    (hleft : ∀ ε : ℝ, 0 < ε → scalarCDF ν Z (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < scalarCDF ν Z (q + ε))
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) :=
  bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
    (fun n ω => by
      haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
      exact bootstrapScalarCDF_mono (Pstar := Pstar) (Zstar := Zstar)
        (n := n) (ω := ω))
    hne hbdd hlocal hleft hright hZ hcont

/-- Strict-limit-CDF specialization of the finite-measure scalar
lower-quantile Definition 10.2 wrapper. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_strictMono_finite
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p)
    (hstrict : StrictMono (scalarCDF ν Z))
    (hq : scalarCDF ν Z q = p)
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_finite
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      hPstar hne hbdd hlocal hleft hright hZ hcont

/-- Law-CDF specialization of the finite-measure scalar lower-quantile
Definition 10.2 wrapper.

The limiting one-dimensional statistic is the identity under the scalar law
`η`, so the limiting CDF is Mathlib's `cdf η`. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_id_cdf_finite
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p)
    (hleft : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < cdf η (q + ε))
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) := by
  exact
    bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_finite
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := η)
      (Z := fun x : ℝ => x) hPstar hne hbdd hlocal
      (by simpa using hleft) (by simpa using hright) hZ
      (by simpa using hcont)

/-- Strict law-CDF specialization of the finite-measure scalar lower-quantile
Definition 10.2 wrapper. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_strictMono_id_cdf_finite
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Zstar (x + δ) n ω < p)
    (hstrict : StrictMono (fun x => cdf η x))
    (hq : cdf η q = p)
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) := by
  exact
    bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_strictMono_finite
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := η)
      (Z := fun x : ℝ => x) hPstar hne hbdd hlocal
      (by simpa using hstrict) (by simpa using hq) hZ (by simpa using hcont)

/-- Law-CDF scalar lower-quantile wrapper with the local-right CDF bracketing
premise discharged from pointwise a.e. measurability of the bootstrap statistic. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_id_cdf_aemeasurable
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hleft : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < cdf η (q + ε))
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_id_cdf_finite
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η) (p := p)
      (q := q) hPstarFinite hne hbdd
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas)
      hleft hright hZ hcont

/-- Strict law-CDF scalar lower-quantile wrapper with the local-right CDF
bracketing premise discharged from pointwise a.e. measurability. -/
theorem
bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_strictMono_id_cdf_aemeasurable
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω} : Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow {x : ℝ | p ≤ bootstrapScalarCDF Pstar Zstar x n ω})
    (hstrict : StrictMono (fun x => cdf η x))
    (hq : cdf η q = p)
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_id_cdf_aemeasurable
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η)
      hPstar hZmeas hne hbdd hleft hright hZ hcont

/-- Law-CDF scalar lower-quantile wrapper for probability-valued conditional
bootstrap CDFs at levels `0 < p < 1`.

The probability and a.e.-measurability assumptions discharge monotonicity,
right-local persistence, nonemptiness, and bounded-below bracketing for the
lower generalized inverse. -/
theorem bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_id_cdf_probability
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hleft : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < cdf η (q + ε))
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) :=
  bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_id_cdf_aemeasurable
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η)
    hPstar hZmeas
    (bootstrapScalarCDF_level_nonempty_of_aemeasurable
      (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas hp_lt_one)
    (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
      (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas hp_pos)
    hleft hright hZ hcont

/-- Strict law-CDF scalar lower-quantile wrapper for probability-valued
conditional bootstrap CDFs at levels `0 < p < 1`. -/
theorem
bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_strictMono_id_cdf_probability
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hq : cdf η q = p)
    (hZ :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantile Pstar Zstar p) atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantile_tendsto_of_bootstrapDistribution_unit_id_cdf_probability
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η)
      hPstar hZmeas hp_pos hp_lt_one hleft hright hZ hcont

variable {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]

/-- Scalar conditional bootstrap CDF for sample-size-dependent bootstrap
spaces. -/
noncomputable def bootstrapScalarCDFIndexed
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → ℝ)
    (x : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((Pstar n ω) {ωs | Zstar n ω ωs ≤ x}).toReal

/-- Indexed scalar conditional bootstrap CDF as Mathlib's CDF of the
push-forward law. -/
theorem bootstrapScalarCDFIndexed_eq_cdf_map
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {n : ℕ} {ω : Ω}
    (hPstar : IsProbabilityMeasure (Pstar n ω))
    (hZ : AEMeasurable (Zstar n ω) (Pstar n ω)) (x : ℝ) :
    bootstrapScalarCDFIndexed Pstar Zstar x n ω =
      cdf ((Pstar n ω).map (Zstar n ω)) x := by
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar
  haveI : IsProbabilityMeasure ((Pstar n ω).map (Zstar n ω)) :=
    Measure.isProbabilityMeasure_map hZ
  rw [ProbabilityTheory.cdf_eq_real]
  rw [Measure.real]
  rw [Measure.map_apply_of_aemeasurable hZ measurableSet_Iic]
  simp [bootstrapScalarCDFIndexed, Set.Iic]

/-- Indexed scalar conditional bootstrap CDFs are monotone under finite
conditional bootstrap measures. -/
theorem bootstrapScalarCDFIndexed_mono
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {n : ℕ} {ω : Ω} [IsFiniteMeasure (Pstar n ω)] :
    Monotone (fun x => bootstrapScalarCDFIndexed Pstar Zstar x n ω) := by
  intro x y hxy
  refine ENNReal.toReal_mono
    (measure_ne_top (Pstar n ω) {ωs | Zstar n ω ωs ≤ y}) ?_
  exact measure_mono fun ωs hωs => le_trans hωs hxy

/-- Indexed scalar conditional bootstrap CDFs remain below a level just to the
right of any point where they are strictly below it. -/
theorem bootstrapScalarCDFIndexed_exists_right_lt_of_lt
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {n : ℕ} {ω : Ω}
    (hPstar : IsProbabilityMeasure (Pstar n ω))
    (hZ : AEMeasurable (Zstar n ω) (Pstar n ω))
    {p x : ℝ}
    (hx : bootstrapScalarCDFIndexed Pstar Zstar x n ω < p) :
    ∃ δ : ℝ, 0 < δ ∧
      bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p := by
  let η : Measure ℝ := (Pstar n ω).map (Zstar n ω)
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar
  haveI : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map hZ
  have hcdf_eq :
      ∀ y : ℝ, bootstrapScalarCDFIndexed Pstar Zstar y n ω = cdf η y := by
    intro y
    exact bootstrapScalarCDFIndexed_eq_cdf_map
      (Pstar := Pstar) (Zstar := Zstar) (n := n) (ω := ω) hPstar hZ y
  have hx_cdf : cdf η x < p := by
    simpa [hcdf_eq x] using hx
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    stieltjesFunction_exists_right_lt_of_lt (cdf η) (x := x) hx_cdf
  exact ⟨δ, hδ_pos, by simpa [hcdf_eq (x + δ)] using hδ⟩

/-- Pointwise a.e.-measurability package for indexed scalar conditional CDF
local-right bracketing. -/
theorem bootstrapScalarCDFIndexed_local_right_lt_of_aemeasurable
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    {p : ℝ} :
    ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
      ∃ δ : ℝ, 0 < δ ∧
        bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p :=
  fun n ω x hx =>
    bootstrapScalarCDFIndexed_exists_right_lt_of_lt
      (Pstar := Pstar) (Zstar := Zstar) (n := n) (ω := ω)
      (x := x) (hPstar n ω) (hZ n ω) hx

/-- For an indexed scalar conditional bootstrap CDF, every level below one is
reached somewhere. -/
theorem bootstrapScalarCDFIndexed_level_nonempty_of_aemeasurable
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    {p : ℝ} (hp : p < 1) :
    ∀ n ω,
      ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
        Set ℝ).Nonempty := by
  intro n ω
  let η : Measure ℝ := (Pstar n ω).map (Zstar n ω)
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  haveI : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map (hZ n ω)
  have hEventually :
      ∀ᶠ x in atTop, p < cdf η x :=
    (ProbabilityTheory.tendsto_cdf_atTop η).eventually_const_lt hp
  obtain ⟨x, hx⟩ := hEventually.exists
  refine ⟨x, ?_⟩
  have hcdf_eq :
      bootstrapScalarCDFIndexed Pstar Zstar x n ω = cdf η x :=
    bootstrapScalarCDFIndexed_eq_cdf_map
      (Pstar := Pstar) (Zstar := Zstar) (n := n) (ω := ω)
      (hPstar n ω) (hZ n ω) x
  change p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω
  rw [hcdf_eq]
  exact le_of_lt hx

/-- For an indexed scalar conditional bootstrap CDF, every strictly positive
level has a lower-bounded generalized-inverse set. -/
theorem bootstrapScalarCDFIndexed_level_bddBelow_of_aemeasurable
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    {p : ℝ} (hp : 0 < p) :
    ∀ n ω, BddBelow
      {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} := by
  intro n ω
  let η : Measure ℝ := (Pstar n ω).map (Zstar n ω)
  haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
  haveI : IsProbabilityMeasure η := Measure.isProbabilityMeasure_map (hZ n ω)
  have hEventually :
      ∀ᶠ x in atBot, cdf η x < p :=
    (ProbabilityTheory.tendsto_cdf_atBot η).eventually_lt_const hp
  obtain ⟨M, hM⟩ := eventually_atBot.mp hEventually
  refine ⟨M, ?_⟩
  intro x hx
  by_contra hnot
  have hx_le : x ≤ M := le_of_not_ge hnot
  have hcdf_lt : cdf η x < p := hM x hx_le
  have hboot_lt : bootstrapScalarCDFIndexed Pstar Zstar x n ω < p := by
    have hcdf_eq :
        bootstrapScalarCDFIndexed Pstar Zstar x n ω = cdf η x :=
      bootstrapScalarCDFIndexed_eq_cdf_map
        (Pstar := Pstar) (Zstar := Zstar) (n := n) (ω := ω)
        (hPstar n ω) (hZ n ω) x
    simpa [hcdf_eq] using hcdf_lt
  exact not_lt_of_ge hx hboot_lt

/-- Scalar CDF convergence extracted from indexed one-dimensional Hansen
Definition 10.2. -/
theorem TendstoInBootstrapDistributionIndexed.bootstrapScalarCDF_tendsto_unit
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    {x : ℝ}
    (hx :
      ContinuousAt
        (fun y : Unit → ℝ =>
          vectorCDF ν (fun ωlim (_ : Unit) => Z ωlim) y)
        (fun _ : Unit => x)) :
    TendstoInMeasure μ
      (fun n ω => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
      atTop (fun _ => scalarCDF ν Z x) := by
  have hunit :=
    hZ.tendsto_cdf (x := fun _ : Unit => x) hx
  refine TendstoInMeasure.congr (fun n => ?_) ?_ hunit
  · exact ae_of_all μ fun ω => by
      simp [bootstrapScalarCDFIndexed, bootstrapVectorCDFIndexed, coordinateLE]
  · exact ae_of_all μ fun _ => by
      simp [scalarCDF, vectorCDF, coordinateLE]

/-- Scalar CDF convergence extracted from indexed one-dimensional Hansen
Definition 10.2, with continuity stated for the scalar CDF. -/
theorem
TendstoInBootstrapDistributionIndexed.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ}
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    {x : ℝ}
    (hx : ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (fun n ω => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
      atTop (fun _ => scalarCDF ν Z x) :=
  hZ.bootstrapScalarCDF_tendsto_unit (x := x)
    (continuousAt_vectorCDF_unit_of_scalarCDF hx)

/-- Indexed scalar CDF convergence when the limiting statistic is the identity
under a scalar probability law. -/
theorem TendstoInBootstrapDistributionIndexed.bootstrapScalarCDF_tendsto_unit_id_cdf
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η]
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    {x : ℝ}
    (hx : ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (fun n ω => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
      atTop (fun _ => cdf η x) := by
  simpa using
    (TendstoInBootstrapDistributionIndexed.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := η)
      (Z := fun x : ℝ => x) hZ (by simpa using hx))

/-- Indexed bootstrap scalar quantile convergence from pointwise conditional-CDF
convergence. -/
theorem bootstrapScalarQuantileIndexed_tendsto_of_cdf_brackets
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {G : ℝ → ℝ} {p q : ℝ} {qseq : ℕ → Ω → ℝ}
    (hbracket :
      CDFQuantileBracket
        (fun n ω x => bootstrapScalarCDFIndexed Pstar Zstar x n ω) p qseq)
    (hleft : ∀ ε : ℝ, 0 < ε → G (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < G (q + ε))
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ qseq atTop (fun _ => q) :=
  tendstoInMeasure_quantile_of_cdf_brackets
    (μ := μ)
    (Gseq := fun n ω x => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
    hbracket hleft hright hG

/-- Indexed bootstrap scalar quantile convergence with a strictly increasing
limiting CDF. -/
theorem bootstrapScalarQuantileIndexed_tendsto_of_strictMono_cdf
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {G : ℝ → ℝ} {p q : ℝ} {qseq : ℕ → Ω → ℝ}
    (hbracket :
      CDFQuantileBracket
        (fun n ω x => bootstrapScalarCDFIndexed Pstar Zstar x n ω) p qseq)
    (hstrict : StrictMono G)
    (hq : G q = p)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ qseq atTop (fun _ => q) :=
  tendstoInMeasure_quantile_of_strictMono_cdf
    (μ := μ)
    (Gseq := fun n ω x => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
    hbracket hstrict hq hG

/-- Indexed bootstrap scalar quantile convergence from one-dimensional indexed
Hansen Definition 10.2. -/
theorem bootstrapScalarQuantileIndexed_tendsto_of_bootstrapDistribution_unit
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    {qseq : ℕ → Ω → ℝ}
    (hbracket :
      CDFQuantileBracket
        (fun n ω x => bootstrapScalarCDFIndexed Pstar Zstar x n ω) p qseq)
    (hleft : ∀ ε : ℝ, 0 < ε → scalarCDF ν Z (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < scalarCDF ν Z (q + ε))
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ qseq atTop (fun _ => q) :=
  bootstrapScalarQuantileIndexed_tendsto_of_cdf_brackets
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (G := scalarCDF ν Z)
    hbracket hleft hright
    (fun x =>
      TendstoInBootstrapDistributionIndexed.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
        hZ (hcont x))

/-- Strict-limit-CDF specialization of indexed scalar quantile convergence from
one-dimensional indexed Hansen Definition 10.2. -/
theorem
bootstrapScalarQuantileIndexed_tendsto_of_bootstrapDistribution_unit_strictMono
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    {qseq : ℕ → Ω → ℝ}
    (hbracket :
      CDFQuantileBracket
        (fun n ω x => bootstrapScalarCDFIndexed Pstar Zstar x n ω) p qseq)
    (hstrict : StrictMono (scalarCDF ν Z))
    (hq : scalarCDF ν Z q = p)
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ qseq atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarQuantileIndexed_tendsto_of_bootstrapDistribution_unit
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      hbracket hleft hright hZ hcont

/-- Lower generalized inverse of an indexed scalar conditional bootstrap CDF. -/
noncomputable def bootstrapScalarLowerQuantileIndexed
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Zstar : ∀ n, Ω → Ωboot n → ℝ)
    (p : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  lowerCDFQuantile (fun x => bootstrapScalarCDFIndexed Pstar Zstar x n ω) p

/-- Indexed scalar lower-quantile convergence from pointwise CDF convergence
and concrete generalized-inverse bracketing assumptions. -/
theorem bootstrapScalarLowerQuantileIndexed_tendsto_of_cdf_brackets
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {G : ℝ → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x =>
        bootstrapScalarCDFIndexed Pstar Zstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧
          bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p)
    (hleft : ∀ ε : ℝ, 0 < ε → G (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < G (q + ε))
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) :=
  lowerCDFQuantile_tendstoInMeasure_of_cdf_brackets
    (μ := μ)
    (Gseq := fun n ω x => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
    hmono hne hbdd hlocal hleft hright hG

/-- Indexed scalar lower-quantile convergence with a strictly increasing
limiting CDF. -/
theorem bootstrapScalarLowerQuantileIndexed_tendsto_of_strictMono_cdf
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {G : ℝ → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x =>
        bootstrapScalarCDFIndexed Pstar Zstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧
          bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p)
    (hstrict : StrictMono G)
    (hq : G q = p)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
          atTop (fun _ => G x)) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) :=
  lowerCDFQuantile_tendstoInMeasure_of_strictMono_cdf
    (μ := μ)
    (Gseq := fun n ω x => bootstrapScalarCDFIndexed Pstar Zstar x n ω)
    hmono hne hbdd hlocal hstrict hq hG

/-- Indexed scalar lower-quantile convergence from one-dimensional indexed
Hansen Definition 10.2. -/
theorem bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x =>
        bootstrapScalarCDFIndexed Pstar Zstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧
          bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p)
    (hleft : ∀ ε : ℝ, 0 < ε → scalarCDF ν Z (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < scalarCDF ν Z (q + ε))
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) :=
  bootstrapScalarLowerQuantileIndexed_tendsto_of_cdf_brackets
    (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (G := scalarCDF ν Z)
    hmono hne hbdd hlocal hleft hright
    (fun x =>
      TendstoInBootstrapDistributionIndexed.bootstrapScalarCDF_tendsto_unit_of_scalar_continuity
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
        hZ (hcont x))

/-- Strict-limit-CDF specialization of indexed scalar lower-quantile
convergence from one-dimensional indexed Hansen Definition 10.2. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_strictMono
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    (hmono :
      ∀ n ω, Monotone (fun x =>
        bootstrapScalarCDFIndexed Pstar Zstar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧
          bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p)
    (hstrict : StrictMono (scalarCDF ν Z))
    (hq : scalarCDF ν Z q = p)
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      hmono hne hbdd hlocal hleft hright hZ hcont

/-- Finite-measure indexed scalar lower-quantile convergence from
one-dimensional indexed Hansen Definition 10.2. -/
theorem bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_finite
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧
          bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p)
    (hleft : ∀ ε : ℝ, 0 < ε → scalarCDF ν Z (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < scalarCDF ν Z (q + ε))
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  have hmono :
      ∀ n ω, Monotone (fun x =>
        bootstrapScalarCDFIndexed Pstar Zstar x n ω) := by
    intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact bootstrapScalarCDFIndexed_mono (Pstar := Pstar) (Zstar := Zstar)
      (n := n) (ω := ω)
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      hmono hne hbdd hlocal hleft hright hZ hcont

/-- Strict finite-measure indexed scalar lower-quantile convergence from
one-dimensional indexed Hansen Definition 10.2. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_strictMono_finite
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} {p q : ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧
          bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p)
    (hstrict : StrictMono (scalarCDF ν Z))
    (hq : scalarCDF ν Z q = p)
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) ν
        (fun ωlim (_ : Unit) => Z ωlim))
    (hcont : ∀ x : ℝ, ContinuousAt (scalarCDF ν Z) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_finite
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (ν := ν) (Z := Z)
      hPstar hne hbdd hlocal hleft hright hZ hcont

/-- Law-CDF specialization of indexed scalar lower-quantile convergence from
one-dimensional indexed Hansen Definition 10.2. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_finite
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧
          bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p)
    (hleft : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < cdf η (q + ε))
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  have hmono :
      ∀ n ω, Monotone (fun x =>
        bootstrapScalarCDFIndexed Pstar Zstar x n ω) := by
    intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact bootstrapScalarCDFIndexed_mono (Pstar := Pstar) (Zstar := Zstar)
      (n := n) (ω := ω)
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_cdf_brackets
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar)
      (G := fun x => cdf η x) hmono hne hbdd hlocal
      hleft hright
      (fun x =>
        hZ.bootstrapScalarCDF_tendsto_unit_id_cdf
          (Pstar := Pstar) (Zstar := Zstar) (x := x) (hcont x))

/-- Strict law-CDF specialization of indexed scalar lower-quantile
convergence. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_strictMono_id_cdf_finite
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDFIndexed Pstar Zstar x n ω < p →
        ∃ δ : ℝ, 0 < δ ∧
          bootstrapScalarCDFIndexed Pstar Zstar (x + δ) n ω < p)
    (hstrict : StrictMono (fun x => cdf η x))
    (hq : cdf η q = p)
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_finite
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η)
      hPstar hne hbdd hlocal hleft hright hZ hcont

/-- Indexed law-CDF scalar lower-quantile wrapper with the local-right CDF
bracketing premise discharged from pointwise a.e. measurability. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_aemeasurable
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hleft : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < cdf η (q + ε))
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_finite
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η) (p := p)
      (q := q) hPstarFinite hne hbdd
      (bootstrapScalarCDFIndexed_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas)
      hleft hright hZ hcont

/-- Strict indexed law-CDF scalar lower-quantile wrapper with the local-right
CDF bracketing premise discharged from pointwise a.e. measurability. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_strictMono_id_cdf_aemeasurable
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω,
        BddBelow {x : ℝ | p ≤ bootstrapScalarCDFIndexed Pstar Zstar x n ω})
    (hstrict : StrictMono (fun x => cdf η x))
    (hq : cdf η q = p)
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_aemeasurable
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η)
      hPstar hZmeas hne hbdd hleft hright hZ hcont

/-- Indexed law-CDF scalar lower-quantile wrapper for probability-valued
conditional bootstrap CDFs at levels `0 < p < 1`. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_probability
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hleft : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < p)
    (hright : ∀ ε : ℝ, 0 < ε → p < cdf η (q + ε))
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_aemeasurable
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η) (p := p)
      (q := q) hPstar hZmeas
      (bootstrapScalarCDFIndexed_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas hp_lt_one)
      (bootstrapScalarCDFIndexed_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Zstar) hPstar hZmeas hp_pos)
      hleft hright hZ hcont

/-- Strict indexed law-CDF scalar lower-quantile wrapper for
probability-valued conditional bootstrap CDFs at levels `0 < p < 1`. -/
theorem
bootstrapScalarLowerQuantileIndexed_tendsto_of_strictMono_id_cdf_probability
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {η : Measure ℝ} [IsProbabilityMeasure η] {p q : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, AEMeasurable (Zstar n ω) (Pstar n ω))
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hq : cdf η q = p)
    (hZ :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Zstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x) :
    TendstoInMeasure μ
      (bootstrapScalarLowerQuantileIndexed Pstar Zstar p)
      atTop (fun _ => q) := by
  obtain ⟨hleft, hright⟩ := strictMono_cdf_brackets hstrict hq
  exact
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_probability
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (η := η)
      hPstar hZmeas hp_pos hp_lt_one hleft hright hZ hcont

end QuantileConvergence

section PercentileIntervals

/-- Hansen percentile confidence interval event, `qLower <= θ <= qUpper`. -/
def percentileCIEvent (θ qLower qUpper : ℝ) : Prop :=
  qLower ≤ θ ∧ θ ≤ qUpper

/-- Three-coordinate statistic used in the percentile-interval coverage proof:

* coordinate `0`: `aₙ(θhatₙ - θ)`;
* coordinate `1`: `aₙ(q*_{α/2,n} - θhatₙ)`;
* coordinate `2`: `aₙ(q*_{1-α/2,n} - θhatₙ)`.

The confidence event is the lower/upper half-space intersection encoded by
`percentileCoverageSet`. -/
noncomputable def percentileCoverageVector
    (a : ℕ → ℝ) (θ : ℝ) (θhat qLower qUpper : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then a n * (θhat n ω - θ)
    else if i = 1 then a n * (qLower n ω - θhat n ω)
    else a n * (qUpper n ω - θhat n ω)

/-- Limit vector for the percentile-interval coverage proof. -/
noncomputable def percentileCoverageLimitVector
    (ξ : Ωlim → ℝ) (qLower qUpper : ℝ) (ω : Ωlim) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then ξ ω
    else if i = 1 then qLower
    else qUpper

/-- Componentwise Slutsky constructor for the percentile-coverage joint vector.

This assembles the joint convergence premise in
`chapter10_percentileCI_coverage_tendsto_of_joint_quantile_limit` from the
scaled estimator-error limit and the two bootstrap endpoint limits. -/
theorem percentileCoverageVector_tendstoInDistribution_of_components
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℕ → ℝ} {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hlower :
      TendstoInMeasure μ
        (fun n ω => a n * (qLower n ω - θhat n ω))
        atTop (fun _ => qLowerLim))
    (hupper :
      TendstoInMeasure μ
        (fun n ω => a n * (qUpper n ω - θhat n ω))
        atTop (fun _ => qUpperLim))
    (hlower_meas :
      ∀ n, AEMeasurable (fun ω => a n * (qLower n ω - θhat n ω)) μ)
    (hupper_meas :
      ∀ n, AEMeasurable (fun ω => a n * (qUpper n ω - θhat n ω)) μ) :
    TendstoInDistribution
      (percentileCoverageVector a θ θhat qLower qUpper)
      atTop
      (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
      (fun _ => μ) ν := by
  classical
  let statSeq : ℕ → Ω → ℝ := fun n ω => a n * (θhat n ω - θ)
  let lowerSeq : ℕ → Ω → ℝ := fun n ω => a n * (qLower n ω - θhat n ω)
  let upperSeq : ℕ → Ω → ℝ := fun n ω => a n * (qUpper n ω - θhat n ω)
  let pack : (ℝ × ℝ) × ℝ → Fin 3 → ℝ :=
    fun p i => if i = 0 then p.1.1 else if i = 1 then p.1.2 else p.2
  have hpack_cont : Continuous pack := by
    refine continuous_pi ?_
    intro i
    by_cases hi0 : i = 0
    · simpa [pack, hi0] using
        ((continuous_fst : Continuous (fun p : (ℝ × ℝ) × ℝ => p.1)).fst)
    · by_cases hi1 : i = 1
      · simpa [pack, hi0, hi1] using
          ((continuous_fst : Continuous (fun p : (ℝ × ℝ) × ℝ => p.1)).snd)
      · simpa [pack, hi0, hi1] using
          (continuous_snd : Continuous (fun p : (ℝ × ℝ) × ℝ => p.2))
  have hpair :
      TendstoInDistribution
        (fun n ω => (statSeq n ω, lowerSeq n ω))
        atTop (fun ω => (ξ ω, qLowerLim)) (fun _ => μ) ν :=
    hstat.prodMk_of_tendstoInMeasure_const statSeq lowerSeq ξ
      (by simpa [lowerSeq] using hlower)
      (by simpa [lowerSeq] using hlower_meas)
  have hpacked :
      TendstoInDistribution
        (fun n ω => pack ((statSeq n ω, lowerSeq n ω), upperSeq n ω))
        atTop (fun ω => pack ((ξ ω, qLowerLim), qUpperLim))
        (fun _ => μ) ν := by
    have hraw := hpair.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := pack) hpack_cont
      (by simpa [upperSeq] using hupper)
      (by simpa [upperSeq] using hupper_meas)
    simpa [Function.comp_def] using hraw
  refine TendstoInDistribution.congr ?_ ?_ hpacked
  · intro n
    exact ae_of_all μ fun ω => by
      ext i
      by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
        simp [percentileCoverageVector, statSeq, lowerSeq, upperSeq, pack, hi0, hi1]
  · exact ae_of_all ν fun ω => by
      ext i
      by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
        simp [percentileCoverageLimitVector, pack, hi0, hi1]

/-- Limit event corresponding to percentile-interval coverage:
`qLower <= -ξ <= qUpper`. -/
def percentileCoverageSet : Set (Fin 3 → ℝ) :=
  {z | z 1 ≤ -z 0 ∧ -z 0 ≤ z 2}

theorem isClosed_percentileCoverageSet : IsClosed percentileCoverageSet := by
  have hleft : IsClosed {z : Fin 3 → ℝ | z 1 ≤ -z 0} :=
    isClosed_le (continuous_apply 1) ((continuous_apply 0).neg)
  have hright : IsClosed {z : Fin 3 → ℝ | -z 0 ≤ z 2} :=
    isClosed_le ((continuous_apply 0).neg) (continuous_apply 2)
  simpa [percentileCoverageSet] using hleft.inter hright

theorem percentileCoverageVector_mem_set_iff
    {a : ℕ → ℝ} {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {n : ℕ} {ω : Ω} (ha : 0 < a n) :
    percentileCoverageVector a θ θhat qLower qUpper n ω ∈ percentileCoverageSet ↔
      percentileCIEvent θ (qLower n ω) (qUpper n ω) := by
  change
    (a n * (qLower n ω - θhat n ω) ≤ -(a n * (θhat n ω - θ)) ∧
        -(a n * (θhat n ω - θ)) ≤ a n * (qUpper n ω - θhat n ω)) ↔
      qLower n ω ≤ θ ∧ θ ≤ qUpper n ω
  constructor
  · intro h
    constructor <;> nlinarith [ha, h.1, h.2]
  · intro h
    constructor <;> nlinarith [ha, h.1, h.2]

/-- The percentile-coverage limit vector belongs to the coverage set exactly
when the scalar limit error lies between the limiting percentile endpoints. -/
theorem percentileCoverageLimitVector_mem_set_iff
    {ξ : Ωlim → ℝ} {qLower qUpper : ℝ} {ω : Ωlim} :
    percentileCoverageLimitVector ξ qLower qUpper ω ∈ percentileCoverageSet ↔
      qLower ≤ -ξ ω ∧ -ξ ω ≤ qUpper := by
  change
    (qLower ≤ -ξ ω ∧ -ξ ω ≤ qUpper) ↔
      qLower ≤ -ξ ω ∧ -ξ ω ≤ qUpper
  rfl

/-- A scalar a.e.-measurable limit statistic yields an a.e.-measurable
percentile-coverage limit vector. -/
theorem aemeasurable_percentileCoverageLimitVector
    {ξ : Ωlim → ℝ} (hξ : AEMeasurable ξ ν) (qLower qUpper : ℝ) :
    AEMeasurable (percentileCoverageLimitVector ξ qLower qUpper) ν := by
  refine aemeasurable_pi_lambda _ ?_
  intro i
  by_cases hi0 : i = 0
  · subst i
    simpa [percentileCoverageLimitVector] using hξ
  by_cases hi1 : i = 1
  · subst i
    simp [percentileCoverageLimitVector]
  · simp [percentileCoverageLimitVector, hi0, hi1]

/-- The vector-law probability of the percentile-coverage limit set is the
scalar event probability `P[qL <= -ξ <= qU]`. -/
theorem percentileCoverageLimit_measure_set_eq
    {ξ : Ωlim → ℝ} {qLower qUpper : ℝ}
    (hξ : AEMeasurable ξ ν) :
    (ν.map (percentileCoverageLimitVector ξ qLower qUpper))
        percentileCoverageSet =
      ν {ω | qLower ≤ -ξ ω ∧ -ξ ω ≤ qUpper} := by
  rw [Measure.map_apply_of_aemeasurable
    (aemeasurable_percentileCoverageLimitVector (ν := ν) hξ qLower qUpper)
    isClosed_percentileCoverageSet.measurableSet]
  apply congrArg ν
  ext ω
  exact percentileCoverageLimitVector_mem_set_iff

/-- The frontier of the percentile-coverage set is contained in the union of
the two binding endpoint hyperplanes. -/
theorem frontier_percentileCoverageSet_subset :
    frontier percentileCoverageSet ⊆
      {z : Fin 3 → ℝ | z 1 = -z 0} ∪
        {z : Fin 3 → ℝ | -z 0 = z 2} := by
  let lowerSet : Set (Fin 3 → ℝ) := {z | z 1 ≤ -z 0}
  let upperSet : Set (Fin 3 → ℝ) := {z | -z 0 ≤ z 2}
  have hfront :
      frontier percentileCoverageSet ⊆
        frontier lowerSet ∩ closure upperSet ∪
          closure lowerSet ∩ frontier upperSet := by
    simpa [percentileCoverageSet, lowerSet, upperSet] using
      frontier_inter_subset lowerSet upperSet
  intro z hz
  rcases hfront hz with ⟨hzlower, _⟩ | ⟨_, hzupper⟩
  · exact Or.inl
      (frontier_le_subset_eq (continuous_apply 1) ((continuous_apply 0).neg) hzlower)
  · exact Or.inr
      (frontier_le_subset_eq ((continuous_apply 0).neg) (continuous_apply 2) hzupper)

/-- Scalar endpoint-boundary null mass implies the vector-law null-frontier
premise for the percentile-coverage set. -/
theorem percentileCoverage_frontier_null_of_boundary_null
    {ξ : Ωlim → ℝ} {qLower qUpper : ℝ}
    (hξ : AEMeasurable ξ ν)
    (hleft : ν {ω | qLower = -ξ ω} = 0)
    (hright : ν {ω | -ξ ω = qUpper} = 0) :
    (ν.map (percentileCoverageLimitVector ξ qLower qUpper))
      (frontier percentileCoverageSet) = 0 := by
  let boundary : Set (Fin 3 → ℝ) :=
    {z | z 1 = -z 0} ∪ {z | -z 0 = z 2}
  have hboundary_meas : MeasurableSet boundary := by
    exact
      ((isClosed_eq (continuous_apply 1) ((continuous_apply 0).neg)).measurableSet).union
        ((isClosed_eq ((continuous_apply 0).neg) (continuous_apply 2)).measurableSet)
  have hboundary_zero :
      (ν.map (percentileCoverageLimitVector ξ qLower qUpper)) boundary = 0 := by
    rw [Measure.map_apply_of_aemeasurable
      (aemeasurable_percentileCoverageLimitVector (ν := ν) hξ qLower qUpper)
      hboundary_meas]
    have hpre :
        (percentileCoverageLimitVector ξ qLower qUpper) ⁻¹' boundary =
          {ω | qLower = -ξ ω} ∪ {ω | -ξ ω = qUpper} := by
      ext ω
      simp [boundary, percentileCoverageLimitVector]
    rw [hpre]
    exact measure_union_null hleft hright
  exact measure_mono_null (μ := ν.map (percentileCoverageLimitVector ξ qLower qUpper))
    frontier_percentileCoverageSet_subset hboundary_zero

/-- The scalar percentile-coverage event can be read from the law of the
limit statistic as the interval `[-qU, -qL]`. -/
theorem percentileCoverage_scalar_event_eq_law
    {ξ : Ωlim → ℝ} {η : Measure ℝ} (hξ : HasLaw ξ η ν)
    (qLower qUpper : ℝ) :
    ν {ω | qLower ≤ -ξ ω ∧ -ξ ω ≤ qUpper} =
      η (Set.Icc (-qUpper) (-qLower)) := by
  have hpre :
      {ω | qLower ≤ -ξ ω ∧ -ξ ω ≤ qUpper} =
        ξ ⁻¹' Set.Icc (-qUpper) (-qLower) := by
    ext ω
    constructor
    · intro h
      exact ⟨by linarith [h.2], by linarith [h.1]⟩
    · intro h
      exact ⟨by linarith [h.2], by linarith [h.1]⟩
  rw [hpre]
  exact HasLaw.preimage_eq hξ measurableSet_Icc

/-- If the scalar limit law has no atoms, then the percentile-coverage
frontier has zero mass under the limit vector law. -/
theorem percentileCoverage_frontier_null_of_hasLaw_noAtoms
    {ξ : Ωlim → ℝ} {η : Measure ℝ} [NoAtoms η] (hξ : HasLaw ξ η ν)
    (qLower qUpper : ℝ) :
    (ν.map (percentileCoverageLimitVector ξ qLower qUpper))
      (frontier percentileCoverageSet) = 0 := by
  refine percentileCoverage_frontier_null_of_boundary_null
    (ν := ν) (qLower := qLower) (qUpper := qUpper)
    hξ.aemeasurable ?_ ?_
  · have hpre :
        {ω | qLower = -ξ ω} = ξ ⁻¹' ({-qLower} : Set ℝ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor <;> intro h <;> linarith
    rw [hpre, HasLaw.preimage_eq hξ (measurableSet_singleton (-qLower))]
    exact measure_singleton (-qLower)
  · have hpre :
        {ω | -ξ ω = qUpper} = ξ ⁻¹' ({-qUpper} : Set ℝ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor <;> intro h <;> linarith
    rw [hpre, HasLaw.preimage_eq hξ (measurableSet_singleton (-qUpper))]
    exact measure_singleton (-qUpper)

/-- Hansen Theorem 10.13, percentile-interval coverage bridge.

If the scaled estimator error and the scaled bootstrap percentile endpoints
jointly converge to `(ξ, qL, qU)`, and the limiting coverage boundary has zero
probability, then the percentile interval coverage converges to
`P[qL <= -ξ <= qU]`.  Hansen's symmetric continuous-limit conclusion
`1 - α` is obtained by instantiating this bridge with the appropriate
bootstrap quantile limits and symmetry identity for the limit law. -/
theorem chapter10_percentileCI_coverage_tendsto_of_joint_quantile_limit
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ}
    (hjoint :
      TendstoInDistribution
        (percentileCoverageVector a θ θhat qLower qUpper)
        atTop
        (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (percentileCoverageLimitVector ξ qLowerLim qUpperLim))
        (frontier percentileCoverageSet) = 0) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop
      (𝓝 ((ν.map (percentileCoverageLimitVector ξ qLowerLim qUpperLim))
        percentileCoverageSet)) := by
  have hset_meas : MeasurableSet percentileCoverageSet :=
    isClosed_percentileCoverageSet.measurableSet
  have hcoverage :=
    TendstoInDistribution.tendsto_measure_preimage_of_null_frontier
      (h := hjoint) hset_meas hfrontier
  have hseq_eq :
      (fun n =>
        μ {ω | percentileCoverageVector a θ θhat qLower qUpper n ω ∈
          percentileCoverageSet}) =
        fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)} := by
    funext n
    congr 1
    ext ω
    exact percentileCoverageVector_mem_set_iff (Ω := Ω) (ha n)
  simpa [hseq_eq] using hcoverage

/-- Calibrated percentile-interval coverage bridge. -/
theorem chapter10_percentileCI_coverage_tendsto
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (percentileCoverageVector a θ θhat qLower qUpper)
        atTop
        (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (percentileCoverageLimitVector ξ qLowerLim qUpperLim))
        (frontier percentileCoverageSet) = 0)
    (hcoverage :
      (ν.map (percentileCoverageLimitVector ξ qLowerLim qUpperLim))
        percentileCoverageSet = coverage) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  simpa [hcoverage] using
    chapter10_percentileCI_coverage_tendsto_of_joint_quantile_limit
      (μ := μ) (ν := ν) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      hjoint hfrontier

/-- Calibrated percentile-interval coverage bridge with the limit coverage
stated as the scalar event probability `P[qL <= -ξ <= qU]`. -/
theorem chapter10_percentileCI_coverage_tendsto_of_scalar_limit_coverage
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (percentileCoverageVector a θ θhat qLower qUpper)
        atTop
        (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (percentileCoverageLimitVector ξ qLowerLim qUpperLim))
        (frontier percentileCoverageSet) = 0)
    (hcoverage :
      ν {ω | qLowerLim ≤ -ξ ω ∧ -ξ ω ≤ qUpperLim} = coverage) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  have hcoverage_map :
      (ν.map (percentileCoverageLimitVector ξ qLowerLim qUpperLim))
        percentileCoverageSet = coverage := by
    rw [Measure.map_apply_of_aemeasurable hjoint.aemeasurable_limit
      isClosed_percentileCoverageSet.measurableSet]
    have hpre :
        {ω | percentileCoverageLimitVector ξ qLowerLim qUpperLim ω ∈
            percentileCoverageSet} =
          {ω | qLowerLim ≤ -ξ ω ∧ -ξ ω ≤ qUpperLim} := by
      ext ω
      exact percentileCoverageLimitVector_mem_set_iff
    simpa [hpre] using hcoverage
  exact
    chapter10_percentileCI_coverage_tendsto
      (μ := μ) (ν := ν) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      hjoint hfrontier hcoverage_map

/-- Calibrated percentile-interval coverage bridge with scalar endpoint
boundary-null and scalar coverage assumptions. -/
theorem chapter10_percentileCI_coverage_tendsto_of_scalar_limit
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (percentileCoverageVector a θ θhat qLower qUpper)
        atTop
        (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hξ : AEMeasurable ξ ν)
    (hleft : ν {ω | qLowerLim = -ξ ω} = 0)
    (hright : ν {ω | -ξ ω = qUpperLim} = 0)
    (hcoverage :
      ν {ω | qLowerLim ≤ -ξ ω ∧ -ξ ω ≤ qUpperLim} = coverage) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  exact
    chapter10_percentileCI_coverage_tendsto_of_scalar_limit_coverage
      (μ := μ) (ν := ν) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      hjoint
      (percentileCoverage_frontier_null_of_boundary_null
        (ν := ν) (qLower := qLowerLim) (qUpper := qUpperLim)
        hξ hleft hright)
      hcoverage

/-- Calibrated percentile-interval coverage bridge with calibration stated
under the scalar law of the limit statistic.  A non-atomic limit law supplies
the required null-frontier premise. -/
theorem chapter10_percentileCI_coverage_tendsto_of_limit_law
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [NoAtoms η]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (percentileCoverageVector a θ θhat qLower qUpper)
        atTop
        (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (hcoverage : η (Set.Icc (-qUpperLim) (-qLowerLim)) = coverage) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  refine chapter10_percentileCI_coverage_tendsto_of_scalar_limit
    (μ := μ) (ν := ν) (a := a) ha
    (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
    (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
    hjoint hξ.aemeasurable ?_ ?_ ?_
  · have hpre :
        {ω | qLowerLim = -ξ ω} = ξ ⁻¹' ({-qLowerLim} : Set ℝ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor <;> intro h <;> linarith
    rw [hpre, HasLaw.preimage_eq hξ (measurableSet_singleton (-qLowerLim))]
    exact measure_singleton (-qLowerLim)
  · have hpre :
        {ω | -ξ ω = qUpperLim} = ξ ⁻¹' ({-qUpperLim} : Set ℝ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      constructor <;> intro h <;> linarith
    rw [hpre, HasLaw.preimage_eq hξ (measurableSet_singleton (-qUpperLim))]
    exact measure_singleton (-qUpperLim)
  · rw [percentileCoverage_scalar_event_eq_law hξ qLowerLim qUpperLim]
    exact hcoverage

/-- CDF-calibrated percentile-interval coverage bridge.

For a non-atomic scalar limit law, the limiting percentile coverage
`η[-qU,-qL]` can be supplied as the CDF increment
`F(-qL) - F(-qU)`. -/
theorem chapter10_percentileCI_coverage_tendsto_of_limit_law_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim coverage : ℝ}
    (hjoint :
      TendstoInDistribution
        (percentileCoverageVector a θ θhat qLower qUpper)
        atTop
        (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (hquantiles : qLowerLim ≤ qUpperLim)
    (hcoverage : cdf η (-qLowerLim) - cdf η (-qUpperLim) = coverage) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 (ENNReal.ofReal coverage)) := by
  refine
    chapter10_percentileCI_coverage_tendsto_of_limit_law
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      (coverage := ENNReal.ofReal coverage) hjoint hξ ?_
  rw [measure_Icc_eq_ofReal_cdf_sub_of_noAtoms
    (ν := η) (a := -qUpperLim) (b := -qLowerLim)]
  · rw [hcoverage]
  · linarith

/-- Endpoint-CDF percentile-interval calibration with limiting coverage
`1 - α`.  The endpoint premises encode the limiting lower and upper
percentile masses. -/
theorem chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_limit_law_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim α : ℝ}
    (hjoint :
      TendstoInDistribution
        (percentileCoverageVector a θ θhat qLower qUpper)
        atTop
        (percentileCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (hquantiles : qLowerLim ≤ qUpperLim)
    (hlower : cdf η (-qUpperLim) = α / 2)
    (hupper : cdf η (-qLowerLim) = 1 - α / 2) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  refine
    chapter10_percentileCI_coverage_tendsto_of_limit_law_cdf
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      (coverage := 1 - α) hjoint hξ hquantiles ?_
  rw [hlower, hupper]
  ring

/-- Componentwise endpoint-CDF percentile-interval calibration with limiting
coverage `1 - α`.

This is the Theorem 10.13 coverage bridge stated directly from scalar
estimator-error convergence and bootstrap endpoint convergence in probability. -/
theorem chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_components_law_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hlower :
      TendstoInMeasure μ
        (fun n ω => a n * (qLower n ω - θhat n ω))
        atTop (fun _ => qLowerLim))
    (hupper :
      TendstoInMeasure μ
        (fun n ω => a n * (qUpper n ω - θhat n ω))
        atTop (fun _ => qUpperLim))
    (hlower_meas :
      ∀ n, AEMeasurable (fun ω => a n * (qLower n ω - θhat n ω)) μ)
    (hupper_meas :
      ∀ n, AEMeasurable (fun ω => a n * (qUpper n ω - θhat n ω)) μ)
    (hξ : HasLaw ξ η ν)
    (hquantiles : qLowerLim ≤ qUpperLim)
    (hcdfLower : cdf η (-qUpperLim) = α / 2)
    (hcdfUpper : cdf η (-qLowerLim) = 1 - α / 2) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_limit_law_cdf
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      (percentileCoverageVector_tendstoInDistribution_of_components
        (μ := μ) (ν := ν) (a := a) (θ := θ)
        (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
        (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
        hstat hlower hupper hlower_meas hupper_meas)
      hξ hquantiles hcdfLower hcdfUpper

/-- Symmetric endpoint-CDF percentile-interval calibration.

This is the Hansen Theorem 10.13 specialization where the limiting bootstrap
percentile endpoints are `-q` and `q`, and the scalar limit law has endpoint
CDF masses `α / 2` and `1 - α / 2`. -/
theorem chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hlower :
      TendstoInMeasure μ
        (fun n ω => a n * (qLower n ω - θhat n ω))
        atTop (fun _ => -q))
    (hupper :
      TendstoInMeasure μ
        (fun n ω => a n * (qUpper n ω - θhat n ω))
        atTop (fun _ => q))
    (hlower_meas :
      ∀ n, AEMeasurable (fun ω => a n * (qLower n ω - θhat n ω)) μ)
    (hupper_meas :
      ∀ n, AEMeasurable (fun ω => a n * (qUpper n ω - θhat n ω)) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n => μ {ω | percentileCIEvent θ (qLower n ω) (qUpper n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_components_law_cdf
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := -q) (qUpperLim := q) (α := α)
      hstat hlower hupper hlower_meas hupper_meas hξ
      (by linarith) hcdfLower (by simpa using hcdfUpper)

private theorem mul_add_div_sub_eq {a θ q : ℝ} (ha : a ≠ 0) :
    a * ((θ + q / a) - θ) = q := by
  field_simp [ha]
  ring

/-- Symmetric percentile-interval coverage from abstract scaled endpoint
quantiles.

This is the reusable endpoint-conversion bridge behind the lower-quantile
routes: if the scaled lower and upper endpoint deviations converge to `-q` and
`q`, then adding them to `θhat` on the original scale gives the percentile
coverage conclusion. -/
theorem
chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_scaled_quantiles
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat Qlower Qupper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hQlower : TendstoInMeasure μ Qlower atTop (fun _ => -q))
    (hQupper : TendstoInMeasure μ Qupper atTop (fun _ => q))
    (hQlower_meas : ∀ n, AEMeasurable (Qlower n) μ)
    (hQupper_meas : ∀ n, AEMeasurable (Qupper n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω + Qlower n ω / a n)
          (θhat n ω + Qupper n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let qLowerEndpoint : ℕ → Ω → ℝ :=
    fun n ω => θhat n ω + Qlower n ω / a n
  let qUpperEndpoint : ℕ → Ω → ℝ :=
    fun n ω => θhat n ω + Qupper n ω / a n
  have hlower :
      TendstoInMeasure μ
        (fun n ω => a n * (qLowerEndpoint n ω - θhat n ω))
        atTop (fun _ => -q) := by
    refine TendstoInMeasure.congr
      (f := Qlower)
      (f' := fun n ω => a n * (qLowerEndpoint n ω - θhat n ω))
      (g := fun _ : Ω => -q)
      (g' := fun _ : Ω => -q)
      (fun n => ?_) EventuallyEq.rfl hQlower
    exact ae_of_all μ fun ω =>
      (mul_add_div_sub_eq
        (a := a n) (θ := θhat n ω) (q := Qlower n ω)
        (ne_of_gt (ha n))).symm
  have hupper :
      TendstoInMeasure μ
        (fun n ω => a n * (qUpperEndpoint n ω - θhat n ω))
        atTop (fun _ => q) := by
    refine TendstoInMeasure.congr
      (f := Qupper)
      (f' := fun n ω => a n * (qUpperEndpoint n ω - θhat n ω))
      (g := fun _ : Ω => q)
      (g' := fun _ : Ω => q)
      (fun n => ?_) EventuallyEq.rfl hQupper
    exact ae_of_all μ fun ω =>
      (mul_add_div_sub_eq
        (a := a n) (θ := θhat n ω) (q := Qupper n ω)
        (ne_of_gt (ha n))).symm
  have hlower_scaled_meas :
      ∀ n,
        AEMeasurable
          (fun ω => a n * (qLowerEndpoint n ω - θhat n ω)) μ := by
    intro n
    exact (hQlower_meas n).congr
      (ae_of_all μ fun ω =>
        (mul_add_div_sub_eq
          (a := a n) (θ := θhat n ω) (q := Qlower n ω)
          (ne_of_gt (ha n))).symm)
  have hupper_scaled_meas :
      ∀ n,
        AEMeasurable
          (fun ω => a n * (qUpperEndpoint n ω - θhat n ω)) μ := by
    intro n
    exact (hQupper_meas n).congr
      (ae_of_all μ fun ω =>
        (mul_add_div_sub_eq
          (a := a n) (θ := θhat n ω) (q := Qupper n ω)
          (ne_of_gt (ha n))).symm)
  have hcoverage :=
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat)
      (qLower := qLowerEndpoint) (qUpper := qUpperEndpoint)
      (ξ := ξ) (q := q) (α := α)
      hstat hlower hupper hlower_scaled_meas hupper_scaled_meas hξ
      hq_nonneg hcdfLower hcdfUpper
  simpa [qLowerEndpoint, qUpperEndpoint] using hcoverage

/-- Symmetric percentile-interval coverage from bootstrap lower quantiles,
using local limit-CDF bracketing.

This is the non-strict-CDF version of the lower-generalized-inverse endpoint
route for Hansen Theorem 10.13.  It identifies the limiting lower and upper
bootstrap quantiles by local CDF bracketing at `-q` and `q`, then converts the
scaled bootstrap endpoints back to the original parameter scale. -/
theorem
chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Tstar x n ω))
    (hneLower :
      ∀ n ω,
        ({x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddLower :
      ∀ n ω, BddBelow
        {x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalLower :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω < α / 2)
    (hneUpper :
      ∀ n ω,
        ({x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddUpper :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalUpper :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < 1 - α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω <
          1 - α / 2)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hcdf :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Tstar x n ω)
          atTop (fun _ => cdf η x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Qlower : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantile Pstar Tstar (α / 2)
  let Qupper : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2)
  let qLowerEndpoint : ℕ → Ω → ℝ :=
    fun n ω => θhat n ω + Qlower n ω / a n
  let qUpperEndpoint : ℕ → Ω → ℝ :=
    fun n ω => θhat n ω + Qupper n ω / a n
  have hQlower :
      TendstoInMeasure μ Qlower atTop (fun _ => -q) :=
    bootstrapScalarLowerQuantile_tendsto_of_cdf_brackets
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (G := fun x => cdf η x) (p := α / 2) (q := -q)
      hmono hneLower hbddLower hlocalLower hleftLower hrightLower hcdf
  have hQupper :
      TendstoInMeasure μ Qupper atTop (fun _ => q) :=
    bootstrapScalarLowerQuantile_tendsto_of_cdf_brackets
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (G := fun x => cdf η x) (p := 1 - α / 2) (q := q)
      hmono hneUpper hbddUpper hlocalUpper hleftUpper hrightUpper hcdf
  have hlower :
      TendstoInMeasure μ
        (fun n ω => a n * (qLowerEndpoint n ω - θhat n ω))
        atTop (fun _ => -q) := by
    refine TendstoInMeasure.congr
      (f := Qlower)
      (f' := fun n ω => a n * (qLowerEndpoint n ω - θhat n ω))
      (g := fun _ : Ω => -q)
      (g' := fun _ : Ω => -q)
      (fun n => ?_) EventuallyEq.rfl hQlower
    refine ae_of_all μ fun ω => ?_
    exact (mul_add_div_sub_eq
      (a := a n) (θ := θhat n ω) (q := Qlower n ω)
      (ne_of_gt (ha n))).symm
  have hupper :
      TendstoInMeasure μ
        (fun n ω => a n * (qUpperEndpoint n ω - θhat n ω))
        atTop (fun _ => q) := by
    refine TendstoInMeasure.congr
      (f := Qupper)
      (f' := fun n ω => a n * (qUpperEndpoint n ω - θhat n ω))
      (g := fun _ : Ω => q)
      (g' := fun _ : Ω => q)
      (fun n => ?_) EventuallyEq.rfl hQupper
    refine ae_of_all μ fun ω => ?_
    exact (mul_add_div_sub_eq
      (a := a n) (θ := θhat n ω) (q := Qupper n ω)
      (ne_of_gt (ha n))).symm
  have hlower_scaled_meas :
      ∀ n,
        AEMeasurable
          (fun ω => a n * (qLowerEndpoint n ω - θhat n ω)) μ := by
    intro n
    have hQlower_meas : AEMeasurable (Qlower n) μ := by
      simpa [Qlower] using hlower_meas n
    exact hQlower_meas.congr
      (ae_of_all μ fun ω =>
        (mul_add_div_sub_eq
          (a := a n) (θ := θhat n ω) (q := Qlower n ω)
          (ne_of_gt (ha n))).symm)
  have hupper_scaled_meas :
      ∀ n,
        AEMeasurable
          (fun ω => a n * (qUpperEndpoint n ω - θhat n ω)) μ := by
    intro n
    have hQupper_meas : AEMeasurable (Qupper n) μ := by
      simpa [Qupper] using hupper_meas n
    exact hQupper_meas.congr
      (ae_of_all μ fun ω =>
        (mul_add_div_sub_eq
          (a := a n) (θ := θhat n ω) (q := Qupper n ω)
          (ne_of_gt (ha n))).symm)
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat) (qLower := qLowerEndpoint)
      (qUpper := qUpperEndpoint) (ξ := ξ) (q := q) (α := α)
      hstat hlower hupper hlower_scaled_meas hupper_scaled_meas hξ
      hq_nonneg hcdfLower hcdfUpper

/-- Symmetric percentile-interval coverage from bootstrap lower quantiles.

The bootstrap lower quantiles identify the scaled endpoint deviations
`aₙ(q* - θhatₙ)`.  Dividing by `aₙ` and adding `θhatₙ` puts the endpoints on
the original parameter scale, after which the symmetric percentile-coverage
wrapper applies. -/
theorem chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Tstar x n ω))
    (hneLower :
      ∀ n ω,
        ({x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddLower :
      ∀ n ω, BddBelow
        {x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalLower :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω < α / 2)
    (hneUpper :
      ∀ n ω,
        ({x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddUpper :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalUpper :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < 1 - α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω <
          1 - α / 2)
    (hstrict : StrictMono (fun x => cdf η x))
    (hcdf :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Tstar x n ω)
          atTop (fun _ => cdf η x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Qlower : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantile Pstar Tstar (α / 2)
  let Qupper : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2)
  let qLowerEndpoint : ℕ → Ω → ℝ :=
    fun n ω => θhat n ω + Qlower n ω / a n
  let qUpperEndpoint : ℕ → Ω → ℝ :=
    fun n ω => θhat n ω + Qupper n ω / a n
  have hQlower :
      TendstoInMeasure μ Qlower atTop (fun _ => -q) :=
    bootstrapScalarLowerQuantile_tendsto_of_strictMono_cdf
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (G := fun x => cdf η x) (p := α / 2) (q := -q)
      hmono hneLower hbddLower hlocalLower hstrict hcdfLower hcdf
  have hQupper :
      TendstoInMeasure μ Qupper atTop (fun _ => q) :=
    bootstrapScalarLowerQuantile_tendsto_of_strictMono_cdf
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (G := fun x => cdf η x) (p := 1 - α / 2) (q := q)
      hmono hneUpper hbddUpper hlocalUpper hstrict hcdfUpper hcdf
  have hlower :
      TendstoInMeasure μ
        (fun n ω => a n * (qLowerEndpoint n ω - θhat n ω))
        atTop (fun _ => -q) := by
    refine TendstoInMeasure.congr
      (f := Qlower)
      (f' := fun n ω => a n * (qLowerEndpoint n ω - θhat n ω))
      (g := fun _ : Ω => -q)
      (g' := fun _ : Ω => -q)
      (fun n => ?_) EventuallyEq.rfl hQlower
    refine ae_of_all μ fun ω => ?_
    exact (mul_add_div_sub_eq
      (a := a n) (θ := θhat n ω) (q := Qlower n ω)
      (ne_of_gt (ha n))).symm
  have hupper :
      TendstoInMeasure μ
        (fun n ω => a n * (qUpperEndpoint n ω - θhat n ω))
        atTop (fun _ => q) := by
    refine TendstoInMeasure.congr
      (f := Qupper)
      (f' := fun n ω => a n * (qUpperEndpoint n ω - θhat n ω))
      (g := fun _ : Ω => q)
      (g' := fun _ : Ω => q)
      (fun n => ?_) EventuallyEq.rfl hQupper
    refine ae_of_all μ fun ω => ?_
    exact (mul_add_div_sub_eq
      (a := a n) (θ := θhat n ω) (q := Qupper n ω)
      (ne_of_gt (ha n))).symm
  have hlower_scaled_meas :
      ∀ n,
        AEMeasurable
          (fun ω => a n * (qLowerEndpoint n ω - θhat n ω)) μ := by
    intro n
    have hQlower_meas : AEMeasurable (Qlower n) μ := by
      simpa [Qlower] using hlower_meas n
    exact hQlower_meas.congr
      (ae_of_all μ fun ω =>
        (mul_add_div_sub_eq
          (a := a n) (θ := θhat n ω) (q := Qlower n ω)
          (ne_of_gt (ha n))).symm)
  have hupper_scaled_meas :
      ∀ n,
        AEMeasurable
          (fun ω => a n * (qUpperEndpoint n ω - θhat n ω)) μ := by
    intro n
    have hQupper_meas : AEMeasurable (Qupper n) μ := by
      simpa [Qupper] using hupper_meas n
    exact hQupper_meas.congr
      (ae_of_all μ fun ω =>
        (mul_add_div_sub_eq
          (a := a n) (θ := θhat n ω) (q := Qupper n ω)
          (ne_of_gt (ha n))).symm)
  have hcoverage :=
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat)
      (qLower := qLowerEndpoint) (qUpper := qUpperEndpoint)
      (ξ := ξ) (q := q) (α := α)
      hstat hlower hupper hlower_scaled_meas hupper_scaled_meas hξ
      hq_nonneg hcdfLower hcdfUpper
  simpa [qLowerEndpoint, qUpperEndpoint, Qlower, Qupper] using hcoverage

/-- Symmetric percentile-interval coverage from bootstrap-distribution
convergence of the scaled bootstrap endpoint statistic.

This is the Definition 10.2-facing version of
`chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles`:
scalar-law CDF convergence is extracted from one-dimensional bootstrap
distribution convergence to the law `η`. -/
theorem
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_lowerQuantiles
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hneLower :
      ∀ n ω,
        ({x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddLower :
      ∀ n ω, BddBelow
        {x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalLower :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω < α / 2)
    (hneUpper :
      ∀ n ω,
        ({x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddUpper :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalUpper :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < 1 - α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω <
          1 - α / 2)
    (hstrict : StrictMono (fun x => cdf η x))
    (hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Tstar x n ω) := by
    intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact bootstrapScalarCDF_mono (Pstar := Pstar) (Zstar := Tstar)
      (n := n) (ω := ω)
  have hcdf :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Tstar x n ω)
          atTop (fun _ => cdf η x) :=
    fun x =>
      hTstar.bootstrapScalarCDF_tendsto_unit_id_cdf
        (Pstar := Pstar) (Zstar := Tstar) (x := x) (hcont x)
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (a := a) ha (θ := θ) (θhat := θhat) (ξ := ξ) (q := q)
      (α := α)
      hstat hmono hneLower hbddLower hlocalLower hneUpper hbddUpper
      hlocalUpper hstrict hcdf hlower_meas hupper_meas hξ hq_nonneg
      hcdfLower hcdfUpper

/-- Symmetric percentile-interval coverage from one-dimensional bootstrap
distribution convergence, using local limit-CDF bracketing at the lower and
upper quantiles.

This variant avoids a global strict-monotonicity premise on the scalar limit
CDF. -/
theorem
chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hneLower :
      ∀ n ω,
        ({x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddLower :
      ∀ n ω, BddBelow
        {x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalLower :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω < α / 2)
    (hneUpper :
      ∀ n ω,
        ({x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddUpper :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalUpper :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < 1 - α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω <
          1 - α / 2)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Tstar x n ω) := by
    intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact bootstrapScalarCDF_mono (Pstar := Pstar) (Zstar := Tstar)
      (n := n) (ω := ω)
  have hcdf :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Tstar x n ω)
          atTop (fun _ => cdf η x) :=
    fun x =>
      hTstar.bootstrapScalarCDF_tendsto_unit_id_cdf
        (Pstar := Pstar) (Zstar := Tstar) (x := x) (hcont x)
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles_brackets
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (a := a) ha (θ := θ) (θhat := θhat) (ξ := ξ) (q := q)
      (α := α)
      hstat hmono hneLower hbddLower hlocalLower hneUpper hbddUpper
      hlocalUpper hleftLower hrightLower hleftUpper hrightUpper hcdf
      hlower_meas hupper_meas hξ hq_nonneg hcdfLower hcdfUpper

/-- Symmetric percentile-interval coverage from one-dimensional bootstrap
distribution convergence, with probability-CDF bracketing discharged at
levels `α / 2` and `1 - α / 2`.

For `0 < α < 1`, probability conditional bootstrap laws and pointwise
a.e.-measurability of the bootstrap endpoint statistic supply the lower
generalized-inverse nonemptiness, boundedness, monotonicity, and right-local
CDF bracketing premises. -/
theorem
chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_lowerQuantiles
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (a := a) ha (θ := θ) (θhat := θhat) (ξ := ξ) (q := q)
      (α := α) hstat hPstarFinite
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : α / 2 < 1))
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 0 < α / 2))
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas)
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 1 - α / 2 < 1))
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 0 < 1 - α / 2))
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas)
      hstrict hTstar hcont hlower_meas hupper_meas hξ hq_nonneg
      hcdfLower hcdfUpper

/-- Symmetric percentile-interval coverage from one-dimensional bootstrap
distribution convergence, with bootstrap-side probability-CDF bracketing
discharged and local limit-CDF bracketing retained at `-q` and `q`. -/
theorem
chapter10_percentileCI_coverage_tendsto_one_sub_alpha_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_brackets
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (a := a) ha (θ := θ) (θhat := θhat) (ξ := ξ) (q := q)
      (α := α) hstat hPstarFinite
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : α / 2 < 1))
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 0 < α / 2))
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas)
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 1 - α / 2 < 1))
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 0 < 1 - α / 2))
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas)
      hleftLower hrightLower hleftUpper hrightUpper hTstar hcont
      hlower_meas hupper_meas hξ hq_nonneg hcdfLower hcdfUpper

variable {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]

/-- Indexed symmetric percentile-interval coverage from one-dimensional
bootstrap-distribution convergence, with bootstrap-side probability-CDF
bracketing discharged and local limit-CDF bracketing retained at `-q` and
`q`.

This is the sample-size-dependent counterpart of
`chapter10_percentileCI_coverage_tendsto_one_sub_alpha_quantile_prob_brackets`
for ordinary nonparametric bootstrap laws whose resampling spaces vary with
`n`. -/
theorem
chapter10_percentileCI_coverage_tendsto_one_sub_alpha_indexed_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Qlower : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2)
  let Qupper : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2)
  have hQlower :
      TendstoInMeasure μ Qlower atTop (fun _ => -q) :=
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_probability
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar) (η := η)
      (p := α / 2) (q := -q)
      hPstar hTmeas (by linarith : 0 < α / 2)
      (by linarith : α / 2 < 1)
      hleftLower hrightLower hTstar hcont
  have hQupper :
      TendstoInMeasure μ Qupper atTop (fun _ => q) :=
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_probability
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar) (η := η)
      (p := 1 - α / 2) (q := q)
      hPstar hTmeas (by linarith : 0 < 1 - α / 2)
      (by linarith : 1 - α / 2 < 1)
      hleftUpper hrightUpper hTstar hcont
  have hQlower_meas : ∀ n, AEMeasurable (Qlower n) μ := by
    intro n
    simpa [Qlower] using hlower_meas n
  have hQupper_meas : ∀ n, AEMeasurable (Qupper n) μ := by
    intro n
    simpa [Qupper] using hupper_meas n
  have hcoverage :=
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_of_scaled_quantiles
      (μ := μ) (ν := ν) (η := η) (a := a) ha
      (θ := θ) (θhat := θhat) (Qlower := Qlower) (Qupper := Qupper)
      (ξ := ξ) (q := q) (α := α)
      hstat hQlower hQupper hQlower_meas hQupper_meas hξ
      hq_nonneg hcdfLower hcdfUpper
  simpa [Qlower, Qupper] using hcoverage

/-- Indexed symmetric percentile-interval coverage from one-dimensional
bootstrap-distribution convergence, with probability-CDF bracketing discharged
at levels `α / 2` and `1 - α / 2`.

This is the strict-CDF counterpart of
`chapter10_percentileCI_coverage_tendsto_one_sub_alpha_indexed_quantile_prob_brackets`. -/
theorem
chapter10_percentileCI_coverage_tendsto_one_sub_alpha_indexed_bootstrapDistribution_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → ℝ}
    {a : ℕ → ℝ} (ha : ∀ n, 0 < a n)
    {θ : ℝ} {θhat : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hstat :
      TendstoInDistribution
        (fun n ω => a n * (θhat n ω - θ))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileCIEvent θ
          (θhat n ω +
            bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n ω / a n)
          (θhat n ω +
            bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n ω / a n)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨hleftLower, hrightLower⟩ :=
    strictMono_cdf_brackets hstrict hcdfLower
  obtain ⟨hleftUpper, hrightUpper⟩ :=
    strictMono_cdf_brackets hstrict hcdfUpper
  exact
    chapter10_percentileCI_coverage_tendsto_one_sub_alpha_indexed_quantile_prob_brackets
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (a := a) ha (θ := θ) (θhat := θhat) (ξ := ξ) (q := q)
      (α := α) hstat hPstar hTmeas hα_pos hα_lt_one
      hleftLower hrightLower hleftUpper hrightUpper hTstar hcont
      hlower_meas hupper_meas hξ hq_nonneg hcdfLower hcdfUpper

end PercentileIntervals

section PercentileTIntervals

/-- Percentile-`t` statistic `T = (θhat - θ) / se`. -/
noncomputable def percentileTStatistic (θ θhat se : ℝ) : ℝ :=
  (θhat - θ) / se

/-- Hansen percentile-`t` confidence interval event:
`θhat - se * qUpper <= θ <= θhat - se * qLower`. -/
def percentileTCIEvent (θ θhat se qLower qUpper : ℝ) : Prop :=
  θhat - se * qUpper ≤ θ ∧ θ ≤ θhat - se * qLower

/-- Three-coordinate statistic used in the percentile-`t` coverage proof:

* coordinate `0`: sample t-ratio `Tₙ`;
* coordinate `1`: lower bootstrap t-ratio quantile `q*_{α/2,n}`;
* coordinate `2`: upper bootstrap t-ratio quantile `q*_{1-α/2,n}`. -/
noncomputable def percentileTCoverageVector
    (θ : ℝ) (θhat se qLower qUpper : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then percentileTStatistic θ (θhat n ω) (se n ω)
    else if i = 1 then qLower n ω
    else qUpper n ω

/-- Limit vector for the percentile-`t` coverage proof. -/
noncomputable def percentileTCoverageLimitVector
    (ξ : Ωlim → ℝ) (qLower qUpper : ℝ) (ω : Ωlim) : Fin 3 → ℝ :=
  fun i =>
    if i = 0 then ξ ω
    else if i = 1 then qLower
    else qUpper

/-- Componentwise Slutsky constructor for the percentile-`t` coverage joint
vector.

This assembles the joint convergence premise in
`chapter10_percentileTCI_coverage_tendsto_of_joint_quantile_limit` from the
sample t-ratio limit and the two bootstrap percentile-`t` endpoint limits. -/
theorem percentileTCoverageVector_tendstoInDistribution_of_components
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ}
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop ξ (fun _ => μ) ν)
    (hlower : TendstoInMeasure μ qLower atTop (fun _ => qLowerLim))
    (hupper : TendstoInMeasure μ qUpper atTop (fun _ => qUpperLim))
    (hlower_meas : ∀ n, AEMeasurable (qLower n) μ)
    (hupper_meas : ∀ n, AEMeasurable (qUpper n) μ) :
    TendstoInDistribution
      (percentileTCoverageVector θ θhat se qLower qUpper)
      atTop
      (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
      (fun _ => μ) ν := by
  classical
  let tstatSeq : ℕ → Ω → ℝ :=
    fun n ω => percentileTStatistic θ (θhat n ω) (se n ω)
  let pack : (ℝ × ℝ) × ℝ → Fin 3 → ℝ :=
    fun p i => if i = 0 then p.1.1 else if i = 1 then p.1.2 else p.2
  have hpack_cont : Continuous pack := by
    refine continuous_pi ?_
    intro i
    by_cases hi0 : i = 0
    · simpa [pack, hi0] using
        ((continuous_fst : Continuous (fun p : (ℝ × ℝ) × ℝ => p.1)).fst)
    · by_cases hi1 : i = 1
      · simpa [pack, hi0, hi1] using
          ((continuous_fst : Continuous (fun p : (ℝ × ℝ) × ℝ => p.1)).snd)
      · simpa [pack, hi0, hi1] using
          (continuous_snd : Continuous (fun p : (ℝ × ℝ) × ℝ => p.2))
  have hpair :
      TendstoInDistribution
        (fun n ω => (tstatSeq n ω, qLower n ω))
        atTop (fun ω => (ξ ω, qLowerLim)) (fun _ => μ) ν :=
    htstat.prodMk_of_tendstoInMeasure_const tstatSeq qLower ξ
      hlower hlower_meas
  have hpacked :
      TendstoInDistribution
        (fun n ω => pack ((tstatSeq n ω, qLower n ω), qUpper n ω))
        atTop (fun ω => pack ((ξ ω, qLowerLim), qUpperLim))
        (fun _ => μ) ν := by
    have hraw := hpair.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := pack) hpack_cont hupper hupper_meas
    simpa [Function.comp_def] using hraw
  refine TendstoInDistribution.congr ?_ ?_ hpacked
  · intro n
    exact ae_of_all μ fun ω => by
      ext i
      by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
        simp [percentileTCoverageVector, tstatSeq, pack, hi0, hi1]
  · exact ae_of_all ν fun ω => by
      ext i
      by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
        simp [percentileTCoverageLimitVector, pack, hi0, hi1]

/-- Limit event corresponding to percentile-`t` coverage:
`qLower <= ξ <= qUpper`. -/
def percentileTCoverageSet : Set (Fin 3 → ℝ) :=
  {z | z 1 ≤ z 0 ∧ z 0 ≤ z 2}

theorem isClosed_percentileTCoverageSet : IsClosed percentileTCoverageSet := by
  have hleft : IsClosed {z : Fin 3 → ℝ | z 1 ≤ z 0} :=
    isClosed_le (continuous_apply 1) (continuous_apply 0)
  have hright : IsClosed {z : Fin 3 → ℝ | z 0 ≤ z 2} :=
    isClosed_le (continuous_apply 0) (continuous_apply 2)
  simpa [percentileTCoverageSet] using hleft.inter hright

/-- Positive standard errors turn Hansen's percentile-`t` interval event into
the t-ratio event `qLower <= T <= qUpper`. -/
theorem percentileTCIEvent_iff_tstat_between
    {θ θhat se qLower qUpper : ℝ} (hse : 0 < se) :
    percentileTCIEvent θ θhat se qLower qUpper ↔
      qLower ≤ percentileTStatistic θ θhat se ∧
        percentileTStatistic θ θhat se ≤ qUpper := by
  constructor
  · intro h
    constructor
    · have hmul : qLower * se ≤ θhat - θ := by nlinarith [h.2]
      exact (le_div_iff₀ hse).2 (by simpa [mul_comm] using hmul)
    · have hmul : θhat - θ ≤ qUpper * se := by nlinarith [h.1]
      exact (div_le_iff₀ hse).2 (by simpa [mul_comm] using hmul)
  · intro h
    constructor
    · have hmul : θhat - θ ≤ qUpper * se := by
        simpa [percentileTStatistic, mul_comm] using (div_le_iff₀ hse).1 h.2
      nlinarith
    · have hmul : qLower * se ≤ θhat - θ := by
        simpa [percentileTStatistic, mul_comm] using (le_div_iff₀ hse).1 h.1
      nlinarith

theorem percentileTCoverageVector_mem_set_iff
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {n : ℕ} {ω : Ω} (hse : 0 < se n ω) :
    percentileTCoverageVector θ θhat se qLower qUpper n ω ∈
        percentileTCoverageSet ↔
      percentileTCIEvent θ (θhat n ω) (se n ω) (qLower n ω) (qUpper n ω) := by
  change
    (qLower n ω ≤ percentileTStatistic θ (θhat n ω) (se n ω) ∧
        percentileTStatistic θ (θhat n ω) (se n ω) ≤ qUpper n ω) ↔
      percentileTCIEvent θ (θhat n ω) (se n ω) (qLower n ω) (qUpper n ω)
  exact (percentileTCIEvent_iff_tstat_between hse).symm

/-- The percentile-`t` coverage limit vector belongs to the coverage set
exactly when the scalar t-ratio limit lies between the limiting endpoints. -/
theorem percentileTCoverageLimitVector_mem_set_iff
    {ξ : Ωlim → ℝ} {qLower qUpper : ℝ} {ω : Ωlim} :
    percentileTCoverageLimitVector ξ qLower qUpper ω ∈
        percentileTCoverageSet ↔
      qLower ≤ ξ ω ∧ ξ ω ≤ qUpper := by
  change
    (qLower ≤ ξ ω ∧ ξ ω ≤ qUpper) ↔
      qLower ≤ ξ ω ∧ ξ ω ≤ qUpper
  rfl

/-- A scalar a.e.-measurable limit t-ratio yields an a.e.-measurable
percentile-`t` coverage limit vector. -/
theorem aemeasurable_percentileTCoverageLimitVector
    {ξ : Ωlim → ℝ} (hξ : AEMeasurable ξ ν) (qLower qUpper : ℝ) :
    AEMeasurable (percentileTCoverageLimitVector ξ qLower qUpper) ν := by
  refine aemeasurable_pi_lambda _ ?_
  intro i
  by_cases hi0 : i = 0
  · subst i
    simpa [percentileTCoverageLimitVector] using hξ
  by_cases hi1 : i = 1
  · subst i
    simp [percentileTCoverageLimitVector]
  · simp [percentileTCoverageLimitVector, hi0, hi1]

/-- The vector-law probability of the percentile-`t` limit set is the scalar
event probability `P[qL <= ξ <= qU]`. -/
theorem percentileTCoverageLimit_measure_set_eq
    {ξ : Ωlim → ℝ} {qLower qUpper : ℝ}
    (hξ : AEMeasurable ξ ν) :
    (ν.map (percentileTCoverageLimitVector ξ qLower qUpper))
        percentileTCoverageSet =
      ν {ω | qLower ≤ ξ ω ∧ ξ ω ≤ qUpper} := by
  rw [Measure.map_apply_of_aemeasurable
    (aemeasurable_percentileTCoverageLimitVector (ν := ν) hξ qLower qUpper)
    isClosed_percentileTCoverageSet.measurableSet]
  apply congrArg ν
  ext ω
  exact percentileTCoverageLimitVector_mem_set_iff

/-- The frontier of the percentile-`t` coverage set is contained in the union
of the two binding endpoint hyperplanes. -/
theorem frontier_percentileTCoverageSet_subset :
    frontier percentileTCoverageSet ⊆
      {z : Fin 3 → ℝ | z 1 = z 0} ∪
        {z : Fin 3 → ℝ | z 0 = z 2} := by
  let lowerSet : Set (Fin 3 → ℝ) := {z | z 1 ≤ z 0}
  let upperSet : Set (Fin 3 → ℝ) := {z | z 0 ≤ z 2}
  have hfront :
      frontier percentileTCoverageSet ⊆
        frontier lowerSet ∩ closure upperSet ∪
          closure lowerSet ∩ frontier upperSet := by
    simpa [percentileTCoverageSet, lowerSet, upperSet] using
      frontier_inter_subset lowerSet upperSet
  intro z hz
  rcases hfront hz with ⟨hzlower, _⟩ | ⟨_, hzupper⟩
  · exact Or.inl
      (frontier_le_subset_eq (continuous_apply 1) (continuous_apply 0) hzlower)
  · exact Or.inr
      (frontier_le_subset_eq (continuous_apply 0) (continuous_apply 2) hzupper)

/-- Scalar endpoint-boundary null mass implies the vector-law null-frontier
premise for the percentile-`t` coverage set. -/
theorem percentileTCoverage_frontier_null_of_boundary_null
    {ξ : Ωlim → ℝ} {qLower qUpper : ℝ}
    (hξ : AEMeasurable ξ ν)
    (hleft : ν {ω | qLower = ξ ω} = 0)
    (hright : ν {ω | ξ ω = qUpper} = 0) :
    (ν.map (percentileTCoverageLimitVector ξ qLower qUpper))
      (frontier percentileTCoverageSet) = 0 := by
  let boundary : Set (Fin 3 → ℝ) :=
    {z | z 1 = z 0} ∪ {z | z 0 = z 2}
  have hboundary_meas : MeasurableSet boundary := by
    exact
      ((isClosed_eq (continuous_apply 1) (continuous_apply 0)).measurableSet).union
        ((isClosed_eq (continuous_apply 0) (continuous_apply 2)).measurableSet)
  have hboundary_zero :
      (ν.map (percentileTCoverageLimitVector ξ qLower qUpper)) boundary = 0 := by
    rw [Measure.map_apply_of_aemeasurable
      (aemeasurable_percentileTCoverageLimitVector (ν := ν) hξ qLower qUpper)
      hboundary_meas]
    have hpre :
        (percentileTCoverageLimitVector ξ qLower qUpper) ⁻¹' boundary =
          {ω | qLower = ξ ω} ∪ {ω | ξ ω = qUpper} := by
      ext ω
      simp [boundary, percentileTCoverageLimitVector]
    rw [hpre]
    exact measure_union_null hleft hright
  exact measure_mono_null (μ := ν.map (percentileTCoverageLimitVector ξ qLower qUpper))
    frontier_percentileTCoverageSet_subset hboundary_zero

/-- The scalar percentile-`t` coverage event can be read from the law of the
limit t-ratio as the interval `[qL, qU]`. -/
theorem percentileTCoverage_scalar_event_eq_law
    {ξ : Ωlim → ℝ} {η : Measure ℝ} (hξ : HasLaw ξ η ν)
    (qLower qUpper : ℝ) :
    ν {ω | qLower ≤ ξ ω ∧ ξ ω ≤ qUpper} =
      η (Set.Icc qLower qUpper) := by
  have hpre :
      {ω | qLower ≤ ξ ω ∧ ξ ω ≤ qUpper} =
        ξ ⁻¹' Set.Icc qLower qUpper := by
    rfl
  rw [hpre]
  exact HasLaw.preimage_eq hξ measurableSet_Icc

/-- If the scalar limit law has no atoms, then the percentile-`t` coverage
frontier has zero mass under the limit vector law. -/
theorem percentileTCoverage_frontier_null_of_hasLaw_noAtoms
    {ξ : Ωlim → ℝ} {η : Measure ℝ} [NoAtoms η] (hξ : HasLaw ξ η ν)
    (qLower qUpper : ℝ) :
    (ν.map (percentileTCoverageLimitVector ξ qLower qUpper))
      (frontier percentileTCoverageSet) = 0 := by
  refine percentileTCoverage_frontier_null_of_boundary_null
    (ν := ν) (qLower := qLower) (qUpper := qUpper)
    hξ.aemeasurable ?_ ?_
  · have hpre :
        {ω | qLower = ξ ω} = ξ ⁻¹' ({qLower} : Set ℝ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact eq_comm
    rw [hpre, HasLaw.preimage_eq hξ (measurableSet_singleton qLower)]
    exact measure_singleton qLower
  · have hpre :
        {ω | ξ ω = qUpper} = ξ ⁻¹' ({qUpper} : Set ℝ) := by
      rfl
    rw [hpre, HasLaw.preimage_eq hξ (measurableSet_singleton qUpper)]
    exact measure_singleton qUpper

/-- Hansen Theorem 10.14, percentile-`t` interval coverage bridge.

If the sample t-ratio and bootstrap percentile-`t` critical values jointly
converge to `(ξ, qL, qU)`, and the limiting coverage boundary has zero
probability, then percentile-`t` interval coverage converges to
`P[qL <= ξ <= qU]`. Hansen's first-order validity conclusion `1 - α` is
obtained by instantiating this bridge with the bootstrap quantile limits from
(10.31). -/
theorem chapter10_percentileTCI_coverage_tendsto_of_joint_quantile_limit
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (hjoint :
      TendstoInDistribution
        (percentileTCoverageVector θ θhat se qLower qUpper)
        atTop
        (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (percentileTCoverageLimitVector ξ qLowerLim qUpperLim))
        (frontier percentileTCoverageSet) = 0) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop
      (𝓝 ((ν.map (percentileTCoverageLimitVector ξ qLowerLim qUpperLim))
        percentileTCoverageSet)) := by
  have hset_meas : MeasurableSet percentileTCoverageSet :=
    isClosed_percentileTCoverageSet.measurableSet
  have hcoverage :=
    TendstoInDistribution.tendsto_measure_preimage_of_null_frontier
      (h := hjoint) hset_meas hfrontier
  have hseq_eq :
      (fun n =>
        μ {ω | percentileTCoverageVector θ θhat se qLower qUpper n ω ∈
          percentileTCoverageSet}) =
        fun n =>
          μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
            (qLower n ω) (qUpper n ω)} := by
    funext n
    congr 1
    ext ω
    exact percentileTCoverageVector_mem_set_iff (Ω := Ω) (hse n ω)
  simpa [hseq_eq] using hcoverage

/-- Calibrated percentile-`t` coverage bridge. -/
theorem chapter10_percentileTCI_coverage_tendsto
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hse : ∀ n ω, 0 < se n ω)
    (hjoint :
      TendstoInDistribution
        (percentileTCoverageVector θ θhat se qLower qUpper)
        atTop
        (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (percentileTCoverageLimitVector ξ qLowerLim qUpperLim))
        (frontier percentileTCoverageSet) = 0)
    (hcoverage :
      (ν.map (percentileTCoverageLimitVector ξ qLowerLim qUpperLim))
        percentileTCoverageSet = coverage) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  simpa [hcoverage] using
    chapter10_percentileTCI_coverage_tendsto_of_joint_quantile_limit
      (μ := μ) (ν := ν) (θ := θ) (θhat := θhat) (se := se)
      (qLower := qLower) (qUpper := qUpper) (ξ := ξ)
      (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      hse hjoint hfrontier

/-- Calibrated percentile-`t` coverage bridge with the limit coverage stated
as the scalar event probability `P[qL <= ξ <= qU]`. -/
theorem chapter10_percentileTCI_coverage_tendsto_of_scalar_limit_coverage
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hse : ∀ n ω, 0 < se n ω)
    (hjoint :
      TendstoInDistribution
        (percentileTCoverageVector θ θhat se qLower qUpper)
        atTop
        (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (percentileTCoverageLimitVector ξ qLowerLim qUpperLim))
        (frontier percentileTCoverageSet) = 0)
    (hcoverage :
      ν {ω | qLowerLim ≤ ξ ω ∧ ξ ω ≤ qUpperLim} = coverage) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  have hcoverage_map :
      (ν.map (percentileTCoverageLimitVector ξ qLowerLim qUpperLim))
        percentileTCoverageSet = coverage := by
    rw [Measure.map_apply_of_aemeasurable hjoint.aemeasurable_limit
      isClosed_percentileTCoverageSet.measurableSet]
    have hpre :
        {ω | percentileTCoverageLimitVector ξ qLowerLim qUpperLim ω ∈
            percentileTCoverageSet} =
          {ω | qLowerLim ≤ ξ ω ∧ ξ ω ≤ qUpperLim} := by
      ext ω
      exact percentileTCoverageLimitVector_mem_set_iff
    simpa [hpre] using hcoverage
  exact
    chapter10_percentileTCI_coverage_tendsto
      (μ := μ) (ν := ν) (θ := θ) (θhat := θhat) (se := se)
      (qLower := qLower) (qUpper := qUpper) (ξ := ξ)
      (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      hse hjoint hfrontier hcoverage_map

/-- Calibrated percentile-`t` coverage bridge with scalar endpoint
boundary-null and scalar coverage assumptions. -/
theorem chapter10_percentileTCI_coverage_tendsto_of_scalar_limit
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hse : ∀ n ω, 0 < se n ω)
    (hjoint :
      TendstoInDistribution
        (percentileTCoverageVector θ θhat se qLower qUpper)
        atTop
        (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hξ : AEMeasurable ξ ν)
    (hleft : ν {ω | qLowerLim = ξ ω} = 0)
    (hright : ν {ω | ξ ω = qUpperLim} = 0)
    (hcoverage :
      ν {ω | qLowerLim ≤ ξ ω ∧ ξ ω ≤ qUpperLim} = coverage) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  exact
    chapter10_percentileTCI_coverage_tendsto_of_scalar_limit_coverage
      (μ := μ) (ν := ν) (θ := θ) (θhat := θhat) (se := se)
      (qLower := qLower) (qUpper := qUpper) (ξ := ξ)
      (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      hse hjoint
      (percentileTCoverage_frontier_null_of_boundary_null
        (ν := ν) (qLower := qLowerLim) (qUpper := qUpperLim)
        hξ hleft hright)
      hcoverage

/-- Calibrated percentile-`t` coverage bridge with calibration stated under
the scalar law of the limit t-ratio.  A non-atomic limit law supplies the
required null-frontier premise. -/
theorem chapter10_percentileTCI_coverage_tendsto_of_limit_law
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [NoAtoms η]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim : ℝ} {coverage : ℝ≥0∞}
    (hse : ∀ n ω, 0 < se n ω)
    (hjoint :
      TendstoInDistribution
        (percentileTCoverageVector θ θhat se qLower qUpper)
        atTop
        (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (hcoverage : η (Set.Icc qLowerLim qUpperLim) = coverage) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 coverage) := by
  refine chapter10_percentileTCI_coverage_tendsto_of_scalar_limit
    (μ := μ) (ν := ν) (θ := θ) (θhat := θhat) (se := se)
    (qLower := qLower) (qUpper := qUpper) (ξ := ξ)
    (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
    hse hjoint hξ.aemeasurable ?_ ?_ ?_
  · have hpre :
        {ω | qLowerLim = ξ ω} = ξ ⁻¹' ({qLowerLim} : Set ℝ) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact eq_comm
    rw [hpre, HasLaw.preimage_eq hξ (measurableSet_singleton qLowerLim)]
    exact measure_singleton qLowerLim
  · have hpre :
        {ω | ξ ω = qUpperLim} = ξ ⁻¹' ({qUpperLim} : Set ℝ) := by
      rfl
    rw [hpre, HasLaw.preimage_eq hξ (measurableSet_singleton qUpperLim)]
    exact measure_singleton qUpperLim
  · rw [percentileTCoverage_scalar_event_eq_law hξ qLowerLim qUpperLim]
    exact hcoverage

/-- CDF-calibrated percentile-`t` coverage bridge.

For a non-atomic scalar t-ratio limit law, the limiting coverage
`η[qL,qU]` can be supplied as the CDF increment `F(qU) - F(qL)`. -/
theorem chapter10_percentileTCI_coverage_tendsto_of_limit_law_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim coverage : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (hjoint :
      TendstoInDistribution
        (percentileTCoverageVector θ θhat se qLower qUpper)
        atTop
        (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (hquantiles : qLowerLim ≤ qUpperLim)
    (hcoverage : cdf η qUpperLim - cdf η qLowerLim = coverage) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 (ENNReal.ofReal coverage)) := by
  refine
    chapter10_percentileTCI_coverage_tendsto_of_limit_law
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      (coverage := ENNReal.ofReal coverage) hse hjoint hξ ?_
  rw [measure_Icc_eq_ofReal_cdf_sub_of_noAtoms
    (ν := η) (a := qLowerLim) (b := qUpperLim) hquantiles]
  rw [hcoverage]

/-- Endpoint-CDF percentile-`t` calibration with limiting coverage
`1 - α`.  The endpoint premises encode the limiting lower and upper
percentile-`t` masses. -/
theorem chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_limit_law_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (hjoint :
      TendstoInDistribution
        (percentileTCoverageVector θ θhat se qLower qUpper)
        atTop
        (percentileTCoverageLimitVector ξ qLowerLim qUpperLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (hquantiles : qLowerLim ≤ qUpperLim)
    (hlower : cdf η qLowerLim = α / 2)
    (hupper : cdf η qUpperLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  refine
    chapter10_percentileTCI_coverage_tendsto_of_limit_law_cdf
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      (coverage := 1 - α) hse hjoint hξ hquantiles ?_
  rw [hlower, hupper]
  ring

/-- Componentwise endpoint-CDF percentile-`t` calibration with limiting
coverage `1 - α`.

This is the Theorem 10.14 coverage bridge stated directly from sample t-ratio
convergence and bootstrap percentile-`t` endpoint convergence in probability. -/
theorem chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_law_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {qLowerLim qUpperLim α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop ξ (fun _ => μ) ν)
    (hlower : TendstoInMeasure μ qLower atTop (fun _ => qLowerLim))
    (hupper : TendstoInMeasure μ qUpper atTop (fun _ => qUpperLim))
    (hlower_meas : ∀ n, AEMeasurable (qLower n) μ)
    (hupper_meas : ∀ n, AEMeasurable (qUpper n) μ)
    (hξ : HasLaw ξ η ν)
    (hquantiles : qLowerLim ≤ qUpperLim)
    (hcdfLower : cdf η qLowerLim = α / 2)
    (hcdfUpper : cdf η qUpperLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_limit_law_cdf
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
      hse
      (percentileTCoverageVector_tendstoInDistribution_of_components
        (μ := μ) (ν := ν) (θ := θ) (θhat := θhat) (se := se)
        (qLower := qLower) (qUpper := qUpper)
        (ξ := ξ) (qLowerLim := qLowerLim) (qUpperLim := qUpperLim)
        htstat hlower hupper hlower_meas hupper_meas)
      hξ hquantiles hcdfLower hcdfUpper

/-- Symmetric endpoint-CDF percentile-`t` calibration.

This is the Hansen Theorem 10.14 specialization where the limiting bootstrap
percentile-`t` endpoints are `-q` and `q`, and the scalar t-ratio limit law has
endpoint CDF masses `α / 2` and `1 - α / 2`. -/
theorem chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {θ : ℝ} {θhat se qLower qUpper : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop ξ (fun _ => μ) ν)
    (hlower : TendstoInMeasure μ qLower atTop (fun _ => -q))
    (hupper : TendstoInMeasure μ qUpper atTop (fun _ => q))
    (hlower_meas : ∀ n, AEMeasurable (qLower n) μ)
    (hupper_meas : ∀ n, AEMeasurable (qUpper n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (qLower n ω) (qUpper n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_law_cdf
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se) (qLower := qLower) (qUpper := qUpper)
      (ξ := ξ) (qLowerLim := -q) (qUpperLim := q) (α := α)
      hse htstat hlower hupper hlower_meas hupper_meas hξ
      (by linarith) hcdfLower hcdfUpper

/-- Symmetric percentile-`t` coverage from bootstrap lower quantiles, using
local limit-CDF bracketing.

This is the non-strict-CDF version of the lower-generalized-inverse endpoint
route for Hansen Theorem 10.14. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop ξ (fun _ => μ) ν)
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Tstar x n ω))
    (hneLower :
      ∀ n ω,
        ({x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddLower :
      ∀ n ω, BddBelow
        {x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalLower :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω < α / 2)
    (hneUpper :
      ∀ n ω,
        ({x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddUpper :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalUpper :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < 1 - α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω <
          1 - α / 2)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hcdf :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Tstar x n ω)
          atTop (fun _ => cdf η x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hlower :
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantile Pstar Tstar (α / 2))
        atTop (fun _ => -q) :=
    bootstrapScalarLowerQuantile_tendsto_of_cdf_brackets
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (G := fun x => cdf η x) (p := α / 2) (q := -q)
      hmono hneLower hbddLower hlocalLower hleftLower hrightLower hcdf
  have hupper :
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2))
        atTop (fun _ => q) :=
    bootstrapScalarLowerQuantile_tendsto_of_cdf_brackets
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (G := fun x => cdf η x) (p := 1 - α / 2) (q := q)
      hmono hneUpper hbddUpper hlocalUpper hleftUpper hrightUpper hcdf
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se)
      (qLower := bootstrapScalarLowerQuantile Pstar Tstar (α / 2))
      (qUpper := bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2))
      (ξ := ξ) (q := q) (α := α)
      hse htstat hlower hupper hlower_meas hupper_meas hξ
      hq_nonneg hcdfLower hcdfUpper

/-- Symmetric percentile-`t` coverage from bootstrap lower quantiles.

Pointwise convergence in probability of the conditional bootstrap CDF, plus
the concrete lower-generalized-inverse bracketing assumptions, identifies the
bootstrap percentile-`t` endpoints at levels `α / 2` and `1 - α / 2`.  The
result then feeds those endpoint limits into the symmetric `[-q, q]` coverage
wrapper. -/
theorem chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop ξ (fun _ => μ) ν)
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Tstar x n ω))
    (hneLower :
      ∀ n ω,
        ({x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddLower :
      ∀ n ω, BddBelow
        {x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalLower :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω < α / 2)
    (hneUpper :
      ∀ n ω,
        ({x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddUpper :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalUpper :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < 1 - α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω <
          1 - α / 2)
    (hstrict : StrictMono (fun x => cdf η x))
    (hcdf :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Tstar x n ω)
          atTop (fun _ => cdf η x))
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hlower :
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantile Pstar Tstar (α / 2))
        atTop (fun _ => -q) :=
    bootstrapScalarLowerQuantile_tendsto_of_strictMono_cdf
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (G := fun x => cdf η x) (p := α / 2) (q := -q)
      hmono hneLower hbddLower hlocalLower hstrict hcdfLower hcdf
  have hupper :
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2))
        atTop (fun _ => q) :=
    bootstrapScalarLowerQuantile_tendsto_of_strictMono_cdf
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar)
      (G := fun x => cdf η x) (p := 1 - α / 2) (q := q)
      hmono hneUpper hbddUpper hlocalUpper hstrict hcdfUpper hcdf
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se)
      (qLower := bootstrapScalarLowerQuantile Pstar Tstar (α / 2))
      (qUpper := bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2))
      (ξ := ξ) (q := q) (α := α)
      hse htstat hlower hupper hlower_meas hupper_meas hξ
      hq_nonneg hcdfLower hcdfUpper

/-- Symmetric percentile-`t` coverage from bootstrap-distribution convergence
of the bootstrap t-ratio statistic.

This is the Definition 10.2-facing version of
`chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles`. -/
theorem
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_lowerQuantiles
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hneLower :
      ∀ n ω,
        ({x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddLower :
      ∀ n ω, BddBelow
        {x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalLower :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω < α / 2)
    (hneUpper :
      ∀ n ω,
        ({x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddUpper :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalUpper :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < 1 - α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω <
          1 - α / 2)
    (hstrict : StrictMono (fun x => cdf η x))
    (hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Tstar x n ω) := by
    intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact bootstrapScalarCDF_mono (Pstar := Pstar) (Zstar := Tstar)
      (n := n) (ω := ω)
  have hcdf :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Tstar x n ω)
          atTop (fun _ => cdf η x) :=
    fun x =>
      hTstar.bootstrapScalarCDF_tendsto_unit_id_cdf
        (Pstar := Pstar) (Zstar := Tstar) (x := x) (hcont x)
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (θ := θ) (θhat := θhat) (se := se) (ξ := ξ) (q := q)
      (α := α)
      hse htstat hmono hneLower hbddLower hlocalLower hneUpper hbddUpper
      hlocalUpper hstrict hcdf hlower_meas hupper_meas hξ hq_nonneg
      hcdfLower hcdfUpper

/-- Symmetric percentile-`t` coverage from bootstrap-distribution convergence,
using local limit-CDF bracketing at the lower and upper quantiles.

This variant avoids a global strict-monotonicity premise on the scalar limit
CDF. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hneLower :
      ∀ n ω,
        ({x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddLower :
      ∀ n ω, BddBelow
        {x : ℝ | α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalLower :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω < α / 2)
    (hneUpper :
      ∀ n ω,
        ({x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω} :
          Set ℝ).Nonempty)
    (hbddUpper :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α / 2 ≤ bootstrapScalarCDF Pstar Tstar x n ω})
    (hlocalUpper :
      ∀ n ω x, bootstrapScalarCDF Pstar Tstar x n ω < 1 - α / 2 →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Tstar (x + δ) n ω <
          1 - α / 2)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Tstar x n ω) := by
    intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact bootstrapScalarCDF_mono (Pstar := Pstar) (Zstar := Tstar)
      (n := n) (ω := ω)
  have hcdf :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Tstar x n ω)
          atTop (fun _ => cdf η x) :=
    fun x =>
      hTstar.bootstrapScalarCDF_tendsto_unit_id_cdf
        (Pstar := Pstar) (Zstar := Tstar) (x := x) (hcont x)
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrap_lowerQuantiles_brackets
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (θ := θ) (θhat := θhat) (se := se) (ξ := ξ) (q := q)
      (α := α)
      hse htstat hmono hneLower hbddLower hlocalLower hneUpper hbddUpper
      hlocalUpper hleftLower hrightLower hleftUpper hrightUpper hcdf
      hlower_meas hupper_meas hξ hq_nonneg hcdfLower hcdfUpper

/-- Symmetric percentile-`t` coverage from one-dimensional bootstrap
distribution convergence, with probability-CDF bracketing discharged at
levels `α / 2` and `1 - α / 2`. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_lowerQuantiles
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (θ := θ) (θhat := θhat) (se := se) (ξ := ξ) (q := q)
      (α := α) hse htstat hPstarFinite
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : α / 2 < 1))
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 0 < α / 2))
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas)
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 1 - α / 2 < 1))
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 0 < 1 - α / 2))
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas)
      hstrict hTstar hcont hlower_meas hupper_meas hξ hq_nonneg
      hcdfLower hcdfUpper

/-- Symmetric percentile-`t` coverage from bootstrap-distribution convergence,
with bootstrap-side probability-CDF bracketing discharged and local
limit-CDF bracketing retained at `-q` and `q`. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Tstar : ℕ → Ω → Ωs → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hTstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantile Pstar Tstar (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_bootstrapDistribution_brackets
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (θ := θ) (θhat := θhat) (se := se) (ξ := ξ) (q := q)
      (α := α) hse htstat hPstarFinite
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : α / 2 < 1))
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 0 < α / 2))
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas)
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 1 - α / 2 < 1))
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas
        (by linarith : 0 < 1 - α / 2))
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Tstar) hPstar hTmeas)
      hleftLower hrightLower hleftUpper hrightUpper hTstar hcont
      hlower_meas hupper_meas hξ hq_nonneg hcdfLower hcdfUpper

variable {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]

/-- Indexed symmetric percentile-`t` coverage from one-dimensional bootstrap
distribution convergence, with bootstrap-side probability-CDF bracketing
discharged and local limit-CDF bracketing retained at `-q` and `q`. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleftLower : ∀ ε : ℝ, 0 < ε → cdf η (-q - ε) < α / 2)
    (hrightLower : ∀ ε : ℝ, 0 < ε → α / 2 < cdf η (-q + ε))
    (hleftUpper : ∀ ε : ℝ, 0 < ε → cdf η (q - ε) < 1 - α / 2)
    (hrightUpper : ∀ ε : ℝ, 0 < ε → 1 - α / 2 < cdf η (q + ε))
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  let Qlower : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2)
  let Qupper : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2)
  have hQlower :
      TendstoInMeasure μ Qlower atTop (fun _ => -q) :=
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_probability
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar) (η := η)
      (p := α / 2) (q := -q)
      hPstar hTmeas (by linarith : 0 < α / 2)
      (by linarith : α / 2 < 1)
      hleftLower hrightLower hTstar hcont
  have hQupper :
      TendstoInMeasure μ Qupper atTop (fun _ => q) :=
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_probability
      (μ := μ) (Pstar := Pstar) (Zstar := Tstar) (η := η)
      (p := 1 - α / 2) (q := q)
      hPstar hTmeas (by linarith : 0 < 1 - α / 2)
      (by linarith : 1 - α / 2 < 1)
      hleftUpper hrightUpper hTstar hcont
  have hQlower_meas : ∀ n, AEMeasurable (Qlower n) μ := by
    intro n
    simpa [Qlower] using hlower_meas n
  have hQupper_meas : ∀ n, AEMeasurable (Qupper n) μ := by
    intro n
    simpa [Qupper] using hupper_meas n
  have hcoverage :=
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_of_components_symmetric_cdf
      (μ := μ) (ν := ν) (η := η) (θ := θ) (θhat := θhat)
      (se := se) (qLower := Qlower) (qUpper := Qupper) (ξ := ξ)
      (q := q) (α := α)
      hse htstat hQlower hQupper hQlower_meas hQupper_meas hξ
      hq_nonneg hcdfLower hcdfUpper
  simpa [Qlower, Qupper] using hcoverage

/-- Indexed symmetric percentile-`t` coverage from one-dimensional bootstrap
distribution convergence, with probability-CDF bracketing discharged at levels
`α / 2` and `1 - α / 2`.

This is the strict-CDF counterpart of
`chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_quantile_prob_brackets`. -/
theorem
chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_bootstrapDistribution_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → ℝ}
    {θ : ℝ} {θhat se : ℕ → Ω → ℝ}
    {ξ : Ωlim → ℝ} {q α : ℝ}
    (hse : ∀ n ω, 0 < se n ω)
    (htstat :
      TendstoInDistribution
        (fun n ω => percentileTStatistic θ (θhat n ω) (se n ω))
        atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTmeas : ∀ n ω, AEMeasurable (Tstar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrict : StrictMono (fun x => cdf η x))
    (hTstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Tstar n ω ωs) η
        (fun x (_ : Unit) => x))
    (hcont : ∀ x : ℝ, ContinuousAt (fun y => cdf η y) x)
    (hlower_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n) μ)
    (hupper_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n) μ)
    (hξ : HasLaw ξ η ν)
    (hq_nonneg : 0 ≤ q)
    (hcdfLower : cdf η (-q) = α / 2)
    (hcdfUpper : cdf η q = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | percentileTCIEvent θ (θhat n ω) (se n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (α / 2) n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Tstar (1 - α / 2) n ω)})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by
  obtain ⟨hleftLower, hrightLower⟩ :=
    strictMono_cdf_brackets hstrict hcdfLower
  obtain ⟨hleftUpper, hrightUpper⟩ :=
    strictMono_cdf_brackets hstrict hcdfUpper
  exact
    chapter10_percentileTCI_coverage_tendsto_one_sub_alpha_indexed_quantile_prob_brackets
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Tstar := Tstar)
      (θ := θ) (θhat := θhat) (se := se) (ξ := ξ) (q := q)
      (α := α) hse htstat hPstar hTmeas hα_pos hα_lt_one
      hleftLower hrightLower hleftUpper hrightUpper hTstar hcont
      hlower_meas hupper_meas hξ hq_nonneg hcdfLower hcdfUpper

end PercentileTIntervals

section BootstrapTests

/-- Two-sided bootstrap-test rejection event: reject when `crit < |T|`. -/
def bootstrapAbsTestReject (T crit : ℝ) : Prop :=
  crit < |T|

/-- Two-coordinate statistic for a two-sided bootstrap critical-value test:
coordinate `0` is the test statistic and coordinate `1` is the bootstrap
critical value. -/
noncomputable def bootstrapAbsTestVector
    (T crit : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Fin 2 → ℝ :=
  fun i => if i = 0 then T n ω else crit n ω

/-- Limit vector for the two-sided bootstrap critical-value test. -/
noncomputable def bootstrapAbsTestLimitVector
    (ξ : Ωlim → ℝ) (crit : ℝ) (ω : Ωlim) : Fin 2 → ℝ :=
  fun i => if i = 0 then ξ ω else crit

/-- Componentwise Slutsky constructor for the two-sided bootstrap-test joint
vector.

This assembles the joint convergence premise in
`chapter10_bootstrap_abs_test_rejectionProb_tendsto_of_joint_critical_value_limit`
from statistic convergence and critical-value convergence in probability. -/
theorem bootstrapAbsTestVector_tendstoInDistribution_of_components
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hcrit : TendstoInMeasure μ crit atTop (fun _ => critLim))
    (hcrit_meas : ∀ n, AEMeasurable (crit n) μ) :
    TendstoInDistribution
      (bootstrapAbsTestVector T crit)
      atTop
      (bootstrapAbsTestLimitVector ξ critLim)
      (fun _ => μ) ν := by
  classical
  let pack : ℝ × ℝ → Fin 2 → ℝ :=
    fun p i => if i = 0 then p.1 else p.2
  have hpack_cont : Continuous pack := by
    refine continuous_pi ?_
    intro i
    by_cases hi0 : i = 0
    · simpa [pack, hi0] using
        (continuous_fst : Continuous (fun p : ℝ × ℝ => p.1))
    · simpa [pack, hi0] using
        (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2))
  have hpacked :
      TendstoInDistribution
        (fun n ω => pack (T n ω, crit n ω))
        atTop (fun ω => pack (ξ ω, critLim)) (fun _ => μ) ν := by
    have hraw := hT.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := pack) hpack_cont hcrit hcrit_meas
    simpa [Function.comp_def] using hraw
  refine TendstoInDistribution.congr ?_ ?_ hpacked
  · intro n
    exact ae_of_all μ fun ω => by
      ext i
      by_cases hi0 : i = 0 <;> simp [bootstrapAbsTestVector, pack, hi0]
  · exact ae_of_all ν fun ω => by
      ext i
      by_cases hi0 : i = 0 <;> simp [bootstrapAbsTestLimitVector, pack, hi0]

/-- Rejection region for the two-sided bootstrap critical-value test. -/
def bootstrapAbsRejectionSet : Set (Fin 2 → ℝ) :=
  {z | z 1 < |z 0|}

theorem isOpen_bootstrapAbsRejectionSet : IsOpen bootstrapAbsRejectionSet := by
  simpa [bootstrapAbsRejectionSet] using
    isOpen_lt (continuous_apply 1) ((continuous_apply 0).abs)

theorem bootstrapAbsTestVector_mem_rejectionSet_iff
    {T crit : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω} :
    bootstrapAbsTestVector T crit n ω ∈ bootstrapAbsRejectionSet ↔
      bootstrapAbsTestReject (T n ω) (crit n ω) := by
  change crit n ω < |T n ω| ↔ crit n ω < |T n ω|
  rfl

/-- The bootstrap-test limit vector belongs to the rejection set exactly when
the scalar limit statistic rejects against the limiting critical value. -/
theorem bootstrapAbsTestLimitVector_mem_rejectionSet_iff
    {ξ : Ωlim → ℝ} {critLim : ℝ} {ω : Ωlim} :
    bootstrapAbsTestLimitVector ξ critLim ω ∈ bootstrapAbsRejectionSet ↔
      bootstrapAbsTestReject (ξ ω) critLim := by
  change critLim < |ξ ω| ↔ critLim < |ξ ω|
  rfl

/-- A scalar a.e.-measurable limit statistic yields an a.e.-measurable
bootstrap-test limit vector. -/
theorem aemeasurable_bootstrapAbsTestLimitVector
    {ξ : Ωlim → ℝ} (hξ : AEMeasurable ξ ν) (critLim : ℝ) :
    AEMeasurable (bootstrapAbsTestLimitVector ξ critLim) ν := by
  refine aemeasurable_pi_lambda _ ?_
  intro i
  by_cases hi0 : i = 0
  · subst i
    simpa [bootstrapAbsTestLimitVector] using hξ
  · simp [bootstrapAbsTestLimitVector, hi0]

/-- The vector-law probability of the bootstrap-test rejection set is the
scalar event probability `P[q < |ξ|]`. -/
theorem bootstrapAbsTestLimit_measure_rejectionSet_eq
    {ξ : Ωlim → ℝ} {critLim : ℝ}
    (hξ : AEMeasurable ξ ν) :
    (ν.map (bootstrapAbsTestLimitVector ξ critLim))
        bootstrapAbsRejectionSet =
      ν {ω | bootstrapAbsTestReject (ξ ω) critLim} := by
  rw [Measure.map_apply_of_aemeasurable
    (aemeasurable_bootstrapAbsTestLimitVector (ν := ν) hξ critLim)
    isOpen_bootstrapAbsRejectionSet.measurableSet]
  apply congrArg ν
  ext ω
  exact bootstrapAbsTestLimitVector_mem_rejectionSet_iff

/-- The frontier of the two-sided rejection set is contained in the binding
critical-value hyperplane. -/
theorem frontier_bootstrapAbsRejectionSet_subset :
    frontier bootstrapAbsRejectionSet ⊆
      {z : Fin 2 → ℝ | z 1 = |z 0|} :=
  frontier_lt_subset_eq (continuous_apply 1) ((continuous_apply 0).abs)

/-- Scalar critical-value boundary null mass implies the vector-law
null-frontier premise for the two-sided bootstrap rejection set. -/
theorem bootstrapAbsTest_frontier_null_of_boundary_null
    {ξ : Ωlim → ℝ} {critLim : ℝ}
    (hξ : AEMeasurable ξ ν)
    (hboundary : ν {ω | critLim = |ξ ω|} = 0) :
    (ν.map (bootstrapAbsTestLimitVector ξ critLim))
      (frontier bootstrapAbsRejectionSet) = 0 := by
  let boundary : Set (Fin 2 → ℝ) := {z | z 1 = |z 0|}
  have hboundary_meas : MeasurableSet boundary :=
    (isClosed_eq (continuous_apply 1) ((continuous_apply 0).abs)).measurableSet
  have hboundary_zero :
      (ν.map (bootstrapAbsTestLimitVector ξ critLim)) boundary = 0 := by
    rw [Measure.map_apply_of_aemeasurable
      (aemeasurable_bootstrapAbsTestLimitVector (ν := ν) hξ critLim)
      hboundary_meas]
    have hpre :
        (bootstrapAbsTestLimitVector ξ critLim) ⁻¹' boundary =
          {ω | critLim = |ξ ω|} := by
      ext ω
      simp [boundary, bootstrapAbsTestLimitVector]
    simpa [hpre] using hboundary
  exact measure_mono_null (μ := ν.map (bootstrapAbsTestLimitVector ξ critLim))
    frontier_bootstrapAbsRejectionSet_subset hboundary_zero

/-- The scalar two-sided rejection event can be read from the law of the
limit statistic. -/
theorem bootstrapAbsTest_scalar_rejection_eq_law
    {ξ : Ωlim → ℝ} {η : Measure ℝ} (hξ : HasLaw ξ η ν)
    (critLim : ℝ) :
    ν {ω | bootstrapAbsTestReject (ξ ω) critLim} =
      η {x | bootstrapAbsTestReject x critLim} := by
  have hpre :
      {ω | bootstrapAbsTestReject (ξ ω) critLim} =
        ξ ⁻¹' {x | bootstrapAbsTestReject x critLim} := by
    rfl
  rw [hpre]
  exact HasLaw.preimage_eq hξ
    ((isOpen_lt continuous_const continuous_abs).measurableSet)

/-- For a non-atomic real probability law, the two-sided rejection event
`q < |x|` has mass `1 - (F(q) - F(-q))`. -/
theorem bootstrapAbsTest_rejection_law_eq_ofReal_one_sub_cdf
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {critLim : ℝ} (hcrit : 0 ≤ critLim) :
    η {x | bootstrapAbsTestReject x critLim} =
      ENNReal.ofReal (1 - (cdf η critLim - cdf η (-critLim))) := by
  have hset :
      {x : ℝ | bootstrapAbsTestReject x critLim} =
        (Set.Icc (-critLim) critLim)ᶜ := by
    ext x
    constructor
    · intro hx hxI
      exact not_le_of_gt hx ((abs_le).2 hxI)
    · intro hx
      exact lt_of_not_ge fun hle => hx ((abs_le).1 hle)
  have hinc_nonneg : 0 ≤ cdf η critLim - cdf η (-critLim) := by
    exact sub_nonneg.2 ((ProbabilityTheory.monotone_cdf η) (by linarith))
  rw [hset, measure_compl measurableSet_Icc (measure_ne_top η (Set.Icc (-critLim) critLim)),
    measure_univ,
    measure_Icc_eq_ofReal_cdf_sub_of_noAtoms
      (ν := η) (a := -critLim) (b := critLim) (by linarith),
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (1 : ℝ) hinc_nonneg]

/-- If the scalar limit law has no atoms, then the two-sided rejection
frontier has zero mass under the limit vector law. -/
theorem bootstrapAbsTest_frontier_null_of_hasLaw_noAtoms
    {ξ : Ωlim → ℝ} {η : Measure ℝ} [NoAtoms η] (hξ : HasLaw ξ η ν)
    (critLim : ℝ) :
    (ν.map (bootstrapAbsTestLimitVector ξ critLim))
      (frontier bootstrapAbsRejectionSet) = 0 := by
  refine bootstrapAbsTest_frontier_null_of_boundary_null
    (ν := ν) (critLim := critLim) hξ.aemeasurable ?_
  have hpre_subset :
      {ω | critLim = |ξ ω|} ⊆
        ξ ⁻¹' ({critLim} ∪ {-critLim} : Set ℝ) := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff]
    by_cases hnonneg : 0 ≤ ξ ω
    · left
      simpa [abs_of_nonneg hnonneg, eq_comm] using hω
    · right
      have hneg : ξ ω < 0 := lt_of_not_ge hnonneg
      have hcrit : critLim = -(ξ ω) := by
        simpa [abs_of_neg hneg] using hω
      linarith
  refine measure_mono_null hpre_subset ?_
  rw [HasLaw.preimage_eq hξ
    ((measurableSet_singleton critLim).union
      (measurableSet_singleton (-critLim)))]
  exact measure_union_null (measure_singleton critLim) (measure_singleton (-critLim))

/-- Hansen Theorem 10.16, bootstrap critical-value rejection-probability bridge.

If the test statistic and bootstrap critical value jointly converge to
`(ξ, q)`, and the rejection boundary has zero limit mass, then the rejection
probability converges to `P[q < |ξ|]`. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_of_joint_critical_value_limit
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim : ℝ}
    (hjoint :
      TendstoInDistribution
        (bootstrapAbsTestVector T crit)
        atTop
        (bootstrapAbsTestLimitVector ξ critLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (bootstrapAbsTestLimitVector ξ critLim))
        (frontier bootstrapAbsRejectionSet) = 0) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop
      (𝓝 ((ν.map (bootstrapAbsTestLimitVector ξ critLim)) bootstrapAbsRejectionSet)) := by
  have hset_meas : MeasurableSet bootstrapAbsRejectionSet :=
    isOpen_bootstrapAbsRejectionSet.measurableSet
  have hrejection :=
    TendstoInDistribution.tendsto_measure_preimage_of_null_frontier
      (h := hjoint) hset_meas hfrontier
  have hseq_eq :
      (fun n =>
        μ {ω | bootstrapAbsTestVector T crit n ω ∈ bootstrapAbsRejectionSet}) =
        fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)} := by
    funext n
    rfl
  simpa [hseq_eq] using hrejection

/-- Calibrated form of the bootstrap critical-value bridge.

When the limiting rejection probability equals `α`, the bootstrap critical
value test has asymptotic size `α`. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim : ℝ} {α : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (bootstrapAbsTestVector T crit)
        atTop
        (bootstrapAbsTestLimitVector ξ critLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (bootstrapAbsTestLimitVector ξ critLim))
        (frontier bootstrapAbsRejectionSet) = 0)
    (halpha :
      (ν.map (bootstrapAbsTestLimitVector ξ critLim)) bootstrapAbsRejectionSet = α) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop (𝓝 α) := by
  simpa [halpha] using
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_of_joint_critical_value_limit
      (μ := μ) (ν := ν) (T := T) (crit := crit) (ξ := ξ) (critLim := critLim)
      hjoint hfrontier

/-- Calibrated bootstrap critical-value bridge with the limiting rejection
probability stated as the scalar event probability `P[q < |ξ|]`. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_scalar_limit_rejection
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim : ℝ} {α : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (bootstrapAbsTestVector T crit)
        atTop
        (bootstrapAbsTestLimitVector ξ critLim)
        (fun _ => μ) ν)
    (hfrontier :
      (ν.map (bootstrapAbsTestLimitVector ξ critLim))
        (frontier bootstrapAbsRejectionSet) = 0)
    (halpha :
      ν {ω | bootstrapAbsTestReject (ξ ω) critLim} = α) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop (𝓝 α) := by
  have halpha_map :
      (ν.map (bootstrapAbsTestLimitVector ξ critLim)) bootstrapAbsRejectionSet =
        α := by
    rw [Measure.map_apply_of_aemeasurable hjoint.aemeasurable_limit
      isOpen_bootstrapAbsRejectionSet.measurableSet]
    have hpre :
        {ω | bootstrapAbsTestLimitVector ξ critLim ω ∈
            bootstrapAbsRejectionSet} =
          {ω | bootstrapAbsTestReject (ξ ω) critLim} := by
      ext ω
      exact bootstrapAbsTestLimitVector_mem_rejectionSet_iff
    simpa [hpre] using halpha
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha
      (μ := μ) (ν := ν) (T := T) (crit := crit) (ξ := ξ) (critLim := critLim)
      hjoint hfrontier halpha_map

/-- Calibrated bootstrap critical-value bridge with scalar boundary-null and
scalar limiting rejection-probability assumptions. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_scalar_limit
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim : ℝ} {α : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (bootstrapAbsTestVector T crit)
        atTop
        (bootstrapAbsTestLimitVector ξ critLim)
        (fun _ => μ) ν)
    (hξ : AEMeasurable ξ ν)
    (hboundary : ν {ω | critLim = |ξ ω|} = 0)
    (halpha : ν {ω | bootstrapAbsTestReject (ξ ω) critLim} = α) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop (𝓝 α) := by
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_scalar_limit_rejection
      (μ := μ) (ν := ν) (T := T) (crit := crit) (ξ := ξ) (critLim := critLim)
      hjoint
      (bootstrapAbsTest_frontier_null_of_boundary_null
        (ν := ν) (critLim := critLim) hξ hboundary)
      halpha

/-- Calibrated bootstrap critical-value bridge with calibration stated under
the scalar law of the limit statistic.  A non-atomic limit law supplies the
required null-frontier premise. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_limit_law
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [NoAtoms η]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim : ℝ} {α : ℝ≥0∞}
    (hjoint :
      TendstoInDistribution
        (bootstrapAbsTestVector T crit)
        atTop
        (bootstrapAbsTestLimitVector ξ critLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (halpha : η {x | bootstrapAbsTestReject x critLim} = α) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop (𝓝 α) := by
  have hfrontier :=
    bootstrapAbsTest_frontier_null_of_hasLaw_noAtoms
      (ν := ν) (η := η) hξ critLim
  have halphaν :
      ν {ω | bootstrapAbsTestReject (ξ ω) critLim} = α := by
    rw [bootstrapAbsTest_scalar_rejection_eq_law hξ critLim]
    exact halpha
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_scalar_limit_rejection
      (μ := μ) (ν := ν) (T := T) (crit := crit) (ξ := ξ) (critLim := critLim)
      hjoint hfrontier halphaν

/-- CDF-calibrated two-sided bootstrap-test bridge.

For a non-atomic scalar limit law and nonnegative critical value, the limiting
rejection probability can be supplied as
`1 - (F(q) - F(-q))`. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_limit_law_cdf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim alpha : ℝ}
    (hjoint :
      TendstoInDistribution
        (bootstrapAbsTestVector T crit)
        atTop
        (bootstrapAbsTestLimitVector ξ critLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (hcrit : 0 ≤ critLim)
    (halpha : 1 - (cdf η critLim - cdf η (-critLim)) = alpha) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop (𝓝 (ENNReal.ofReal alpha)) := by
  refine
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_limit_law
      (μ := μ) (ν := ν) (η := η) (T := T) (crit := crit)
      (ξ := ξ) (critLim := critLim) (α := ENNReal.ofReal alpha)
      hjoint hξ ?_
  rw [bootstrapAbsTest_rejection_law_eq_ofReal_one_sub_cdf
    (η := η) (critLim := critLim) hcrit, halpha]

/-- Endpoint-CDF two-sided bootstrap-test calibration with limiting size
`α`.  The endpoint premises encode the central interval mass
`F(q) - F(-q) = 1 - α`. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_limit_law_cdf_endpoints
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hjoint :
      TendstoInDistribution
        (bootstrapAbsTestVector T crit)
        atTop
        (bootstrapAbsTestLimitVector ξ critLim)
        (fun _ => μ) ν)
    (hξ : HasLaw ξ η ν)
    (hcrit : 0 ≤ critLim)
    (hlower : cdf η (-critLim) = α / 2)
    (hupper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  refine
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_limit_law_cdf
      (μ := μ) (ν := ν) (η := η) (T := T) (crit := crit)
      (ξ := ξ) (critLim := critLim) (alpha := α) hjoint hξ hcrit ?_
  rw [hlower, hupper]
  ring

/-- Componentwise endpoint-CDF two-sided bootstrap-test calibration with
limiting size `α`.

This is the Theorem 10.16 rejection bridge stated directly from statistic
convergence and bootstrap critical-value convergence in probability. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_components_law_cdf_endpoints
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {T crit : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hcrit : TendstoInMeasure μ crit atTop (fun _ => critLim))
    (hcrit_meas : ∀ n, AEMeasurable (crit n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n => μ {ω | bootstrapAbsTestReject (T n ω) (crit n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_limit_law_cdf_endpoints
      (μ := μ) (ν := ν) (η := η) (T := T) (crit := crit)
      (ξ := ξ) (critLim := critLim) (α := α)
      (bootstrapAbsTestVector_tendstoInDistribution_of_components
        (μ := μ) (ν := ν) (T := T) (crit := crit)
        (ξ := ξ) (critLim := critLim)
      hT hcrit hcrit_meas)
      hξ hcrit_nonneg hcdfLower hcdfUpper

/-- Two-sided bootstrap-test calibration from a bootstrap lower critical
quantile, using local limit-CDF bracketing.

This is the non-strict-CDF version of the lower-generalized-inverse route for
Hansen Theorem 10.16.  It requires only that the limiting absolute-statistic
CDF lies below `1 - α` immediately to the left of `critLim` and above it
immediately to the right. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_lowerQuantile_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Astar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {Gabs : ℝ → ℝ}
    {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Astar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | 1 - α ≤ bootstrapScalarCDF Pstar Astar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α ≤ bootstrapScalarCDF Pstar Astar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Astar x n ω < 1 - α →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Astar (x + δ) n ω <
          1 - α)
    (hleft : ∀ ε : ℝ, 0 < ε → Gabs (critLim - ε) < 1 - α)
    (hright : ∀ ε : ℝ, 0 < ε → 1 - α < Gabs (critLim + ε))
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Astar x n ω)
          atTop (fun _ => Gabs x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  have hcrit :
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantile Pstar Astar (1 - α))
        atTop (fun _ => critLim) :=
    bootstrapScalarLowerQuantile_tendsto_of_cdf_brackets
      (μ := μ) (Pstar := Pstar) (Zstar := Astar)
      (G := Gabs) (p := 1 - α) (q := critLim)
      hmono hne hbdd hlocal hleft hright hG
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_components_law_cdf_endpoints
      (μ := μ) (ν := ν) (η := η)
      (T := T) (crit := bootstrapScalarLowerQuantile Pstar Astar (1 - α))
      (ξ := ξ) (critLim := critLim) (α := α)
      hT hcrit hcrit_meas hξ hcrit_nonneg hcdfLower hcdfUpper

/-- Two-sided bootstrap-test calibration from a bootstrap lower critical
quantile.

This is the theorem-facing quantile-identification route for Hansen Theorem
10.16.  A lower generalized inverse of a conditional bootstrap CDF at level
`1 - α` converges to the limiting critical value, and the existing
componentwise rejection bridge turns that into asymptotic size `α`. -/
theorem chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_lowerQuantile
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    {Pstar : ℕ → Ω → Measure Ωs} {Astar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {Gabs : ℝ → ℝ}
    {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Astar x n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | 1 - α ≤ bootstrapScalarCDF Pstar Astar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α ≤ bootstrapScalarCDF Pstar Astar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Astar x n ω < 1 - α →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Astar (x + δ) n ω <
          1 - α)
    (hstrict : StrictMono Gabs)
    (hcritLevel : Gabs critLim = 1 - α)
    (hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Astar x n ω)
          atTop (fun _ => Gabs x))
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  have hcrit :
      TendstoInMeasure μ
        (bootstrapScalarLowerQuantile Pstar Astar (1 - α))
        atTop (fun _ => critLim) :=
    bootstrapScalarLowerQuantile_tendsto_of_strictMono_cdf
      (μ := μ) (Pstar := Pstar) (Zstar := Astar)
      (G := Gabs) (p := 1 - α) (q := critLim)
      hmono hne hbdd hlocal hstrict hcritLevel hG
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_components_law_cdf_endpoints
      (μ := μ) (ν := ν) (η := η)
      (T := T) (crit := bootstrapScalarLowerQuantile Pstar Astar (1 - α))
      (ξ := ξ) (critLim := critLim) (α := α)
      hT hcrit hcrit_meas hξ hcrit_nonneg hcdfLower hcdfUpper

/-- Two-sided bootstrap-test calibration from bootstrap-distribution
convergence of the absolute bootstrap statistic.

The bootstrap critical value is a lower generalized inverse of the conditional
CDF of `Astar`.  The limiting CDF for that critical value is supplied by a
separate scalar law `ηAbs`, while the final rejection-size calibration still
uses the sample statistic law `η`. -/
theorem
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrapDistribution_lowerQuantile
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {Pstar : ℕ → Ω → Measure Ωs} {Astar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | 1 - α ≤ bootstrapScalarCDF Pstar Astar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α ≤ bootstrapScalarCDF Pstar Astar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Astar x n ω < 1 - α →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Astar (x + δ) n ω <
          1 - α)
    (hstrictAbs : StrictMono (fun x => cdf ηAbs x))
    (hcritLevel : cdf ηAbs critLim = 1 - α)
    (hAstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) ηAbs
        (fun x (_ : Unit) => x))
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  have hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Astar x n ω) := by
    intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact bootstrapScalarCDF_mono (Pstar := Pstar) (Zstar := Astar)
      (n := n) (ω := ω)
  have hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Astar x n ω)
          atTop (fun _ => cdf ηAbs x) :=
    fun x =>
      hAstar.bootstrapScalarCDF_tendsto_unit_id_cdf
        (Pstar := Pstar) (Zstar := Astar) (x := x) (hcontAbs x)
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_lowerQuantile
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Astar := Astar)
      (T := T) (ξ := ξ) (Gabs := fun x => cdf ηAbs x)
      (critLim := critLim) (α := α)
      hT hmono hne hbdd hlocal hstrictAbs hcritLevel hG hcrit_meas hξ
      hcrit_nonneg hcdfLower hcdfUpper

/-- Two-sided bootstrap-test calibration from bootstrap-distribution
convergence of the absolute bootstrap statistic, using local limit-CDF
bracketing at the critical value.

This variant avoids a global strict-monotonicity requirement on the limiting
absolute-statistic CDF; it only needs the local lower-quantile bracketing
premises around `critLim`. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrapDistribution_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {Pstar : ℕ → Ω → Measure Ωs} {Astar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hne :
      ∀ n ω,
        ({x : ℝ | 1 - α ≤ bootstrapScalarCDF Pstar Astar x n ω} :
          Set ℝ).Nonempty)
    (hbdd :
      ∀ n ω, BddBelow
        {x : ℝ | 1 - α ≤ bootstrapScalarCDF Pstar Astar x n ω})
    (hlocal :
      ∀ n ω x, bootstrapScalarCDF Pstar Astar x n ω < 1 - α →
        ∃ δ : ℝ, 0 < δ ∧ bootstrapScalarCDF Pstar Astar (x + δ) n ω <
          1 - α)
    (hleft :
      ∀ ε : ℝ, 0 < ε → cdf ηAbs (critLim - ε) < 1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε → 1 - α < cdf ηAbs (critLim + ε))
    (hAstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) ηAbs
        (fun x (_ : Unit) => x))
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  have hmono :
      ∀ n ω, Monotone (fun x => bootstrapScalarCDF Pstar Astar x n ω) := by
    intro n ω
    haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
    exact bootstrapScalarCDF_mono (Pstar := Pstar) (Zstar := Astar)
      (n := n) (ω := ω)
  have hG :
      ∀ x : ℝ,
        TendstoInMeasure μ
          (fun n ω => bootstrapScalarCDF Pstar Astar x n ω)
          atTop (fun _ => cdf ηAbs x) :=
    fun x =>
      hAstar.bootstrapScalarCDF_tendsto_unit_id_cdf
        (Pstar := Pstar) (Zstar := Astar) (x := x) (hcontAbs x)
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrap_lowerQuantile_brackets
      (μ := μ) (ν := ν) (η := η) (Pstar := Pstar) (Astar := Astar)
      (T := T) (ξ := ξ) (Gabs := fun x => cdf ηAbs x)
      (critLim := critLim) (α := α)
      hT hmono hne hbdd hlocal hleft hright hG hcrit_meas hξ
      hcrit_nonneg hcdfLower hcdfUpper

/-- Two-sided bootstrap-test calibration from bootstrap-distribution
convergence of the absolute bootstrap statistic, with probability-CDF
bracketing discharged at level `1 - α`.

For `0 < α < 1`, probability conditional bootstrap laws and pointwise
a.e.-measurability of `Astar` supply the lower generalized-inverse bracketing
premises. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrapDistribution_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {Pstar : ℕ → Ω → Measure Ωs} {Astar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrictAbs : StrictMono (fun x => cdf ηAbs x))
    (hcritLevel : cdf ηAbs critLim = 1 - α)
    (hAstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) ηAbs
        (fun x (_ : Unit) => x))
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrapDistribution_lowerQuantile
      (μ := μ) (ν := ν) (η := η) (ηAbs := ηAbs) (Pstar := Pstar)
      (Astar := Astar) (T := T) (ξ := ξ) (critLim := critLim)
      (α := α) hT hPstarFinite
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Astar) hPstar hAmeas
        (by linarith : 1 - α < 1))
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Astar) hPstar hAmeas
        (by linarith : 0 < 1 - α))
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Astar) hPstar hAmeas)
      hstrictAbs hcritLevel hAstar hcontAbs hcrit_meas hξ hcrit_nonneg
      hcdfLower hcdfUpper

/-- Two-sided bootstrap-test calibration from bootstrap-distribution
convergence of the absolute bootstrap statistic, with bootstrap-side
probability-CDF bracketing discharged and local limit-CDF bracketing retained.

This is the probability-level version of
`chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrapDistribution_brackets`.
It avoids the global strict-CDF assumption on the limiting absolute-statistic
law. -/
theorem
chapter10_bootstrap_abs_test_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {Pstar : ℕ → Ω → Measure Ωs} {Astar : ℕ → Ω → Ωs → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleft :
      ∀ ε : ℝ, 0 < ε → cdf ηAbs (critLim - ε) < 1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε → 1 - α < cdf ηAbs (critLim + ε))
    (hAstar :
      TendstoInBootstrapDistribution μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) ηAbs
        (fun x (_ : Unit) => x))
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantile Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_bootstrapDistribution_brackets
      (μ := μ) (ν := ν) (η := η) (ηAbs := ηAbs) (Pstar := Pstar)
      (Astar := Astar) (T := T) (ξ := ξ) (critLim := critLim)
      (α := α) hT hPstarFinite
      (bootstrapScalarCDF_level_nonempty_of_aemeasurable
        (Pstar := Pstar) (Zstar := Astar) hPstar hAmeas
        (by linarith : 1 - α < 1))
      (bootstrapScalarCDF_level_bddBelow_of_aemeasurable
        (Pstar := Pstar) (Zstar := Astar) hPstar hAmeas
        (by linarith : 0 < 1 - α))
      (bootstrapScalarCDF_local_right_lt_of_aemeasurable
        (Pstar := Pstar) (Zstar := Astar) hPstar hAmeas)
      hleft hright hAstar hcontAbs hcrit_meas hξ hcrit_nonneg
      hcdfLower hcdfUpper

variable {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]

/-- Indexed two-sided bootstrap-test calibration from bootstrap-distribution
convergence of the absolute bootstrap statistic, with bootstrap-side
probability-CDF bracketing discharged and local limit-CDF bracketing retained.

This is the sample-size-indexed counterpart of
`chapter10_bootstrap_abs_test_quantile_prob_brackets`, for ordinary
nonparametric bootstrap laws whose resampling spaces vary with `n`. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_quantile_prob_brackets
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Astar : ∀ n, Ω → Ωboot n → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hleft :
      ∀ ε : ℝ, 0 < ε → cdf ηAbs (critLim - ε) < 1 - α)
    (hright :
      ∀ ε : ℝ, 0 < ε → 1 - α < cdf ηAbs (critLim + ε))
    (hAstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) ηAbs
        (fun x (_ : Unit) => x))
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  let crit : ℕ → Ω → ℝ :=
    bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α)
  have hcrit :
      TendstoInMeasure μ crit atTop (fun _ => critLim) :=
    bootstrapScalarLowerQuantileIndexed_tendsto_of_bootstrapDistribution_unit_id_cdf_probability
      (μ := μ) (Pstar := Pstar) (Zstar := Astar) (η := ηAbs)
      (p := 1 - α) (q := critLim)
      hPstar hAmeas (by linarith : 0 < 1 - α)
      (by linarith : 1 - α < 1)
      hleft hright hAstar hcontAbs
  have hcrit_meas' : ∀ n, AEMeasurable (crit n) μ := by
    intro n
    simpa [crit] using hcrit_meas n
  have hreject :=
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_of_components_law_cdf_endpoints
      (μ := μ) (ν := ν) (η := η) (T := T) (crit := crit)
      (ξ := ξ) (critLim := critLim) (α := α)
      hT hcrit hcrit_meas' hξ hcrit_nonneg hcdfLower hcdfUpper
  simpa [crit] using hreject

/-- Indexed two-sided bootstrap-test calibration from bootstrap-distribution
convergence of the absolute bootstrap statistic, with probability-CDF
bracketing discharged at level `1 - α`.

This is the strict-CDF counterpart of
`chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_quantile_prob_brackets`. -/
theorem
chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_bootstrapDistribution_quantile_prob
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η ηAbs : Measure ℝ} [IsProbabilityMeasure η] [NoAtoms η]
    [IsProbabilityMeasure ηAbs]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Astar : ∀ n, Ω → Ωboot n → ℝ}
    {T : ℕ → Ω → ℝ} {ξ : Ωlim → ℝ} {critLim α : ℝ}
    (hT : TendstoInDistribution T atTop ξ (fun _ => μ) ν)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hAmeas : ∀ n ω, AEMeasurable (Astar n ω) (Pstar n ω))
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hstrictAbs : StrictMono (fun x => cdf ηAbs x))
    (hcritLevel : cdf ηAbs critLim = 1 - α)
    (hAstar :
      TendstoInBootstrapDistributionIndexed μ Pstar
        (fun n ω ωs (_ : Unit) => Astar n ω ωs) ηAbs
        (fun x (_ : Unit) => x))
    (hcontAbs : ∀ x : ℝ, ContinuousAt (fun y => cdf ηAbs y) x)
    (hcrit_meas :
      ∀ n,
        AEMeasurable
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n) μ)
    (hξ : HasLaw ξ η ν)
    (hcrit_nonneg : 0 ≤ critLim)
    (hcdfLower : cdf η (-critLim) = α / 2)
    (hcdfUpper : cdf η critLim = 1 - α / 2) :
    Tendsto
      (fun n =>
        μ {ω | bootstrapAbsTestReject (T n ω)
          (bootstrapScalarLowerQuantileIndexed Pstar Astar (1 - α) n ω)})
      atTop (𝓝 (ENNReal.ofReal α)) := by
  obtain ⟨hleft, hright⟩ :=
    strictMono_cdf_brackets hstrictAbs hcritLevel
  exact
    chapter10_bootstrap_abs_test_rejectionProb_tendsto_alpha_indexed_quantile_prob_brackets
      (μ := μ) (ν := ν) (η := η) (ηAbs := ηAbs) (Pstar := Pstar)
      (Astar := Astar) (T := T) (ξ := ξ) (critLim := critLim)
      (α := α) hT hPstar hAmeas hα_pos hα_lt_one hleft hright
      hAstar hcontAbs hcrit_meas hξ hcrit_nonneg hcdfLower hcdfUpper

end BootstrapTests

section HigherOrderRefinements

/-- Generic second-order probability transfer.

If a fixed-critical probability sequence has a scaled second-order expansion
and another probability sequence differs from it by `o(n⁻¹)`, then the second
sequence has the same scaled expansion.  This is the algebraic transfer used
after a bootstrap critical-value or quantile argument has supplied the
`o(n⁻¹)` replacement error. -/
theorem secondOrder_scaled_probability_transfer
    {fixed random : ℕ → ℝ} {target : ℝ} {bias : ℕ → ℝ}
    (hfixed :
      Tendsto (fun n : ℕ => (n : ℝ) * (fixed n - target + bias n))
        atTop (𝓝 0))
    (hreplacement :
      Tendsto (fun n : ℕ => (n : ℝ) * (random n - fixed n))
        atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) * (random n - target + bias n))
      atTop (𝓝 0) := by
  have hsum := hfixed.add hreplacement
  have heq :
      (fun n : ℕ => (n : ℝ) * (fixed n - target + bias n) +
        (n : ℝ) * (random n - fixed n)) =
      (fun n : ℕ => (n : ℝ) * (random n - target + bias n)) := by
    funext n
    ring
  simpa [heq] using hsum

/-- Percentile-`t` second-order coverage transfer from a fixed-critical
interval to a random/bootstrap-critical interval. -/
theorem chapter10_percentileT_secondOrder_interval_transfer
    {fixedCoverage randomCoverage : ℕ → ℝ} {coverage K : ℝ}
    (hfixed :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (fixedCoverage n - coverage - (n : ℝ)⁻¹ * K))
        atTop (𝓝 0))
    (hreplacement :
      Tendsto
        (fun n : ℕ => (n : ℝ) * (randomCoverage n - fixedCoverage n))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (randomCoverage n - coverage - (n : ℝ)⁻¹ * K))
      atTop (𝓝 0) :=
  secondOrder_scaled_probability_transfer
    (fixed := fixedCoverage) (random := randomCoverage)
    (target := coverage) (bias := fun n : ℕ => -((n : ℝ)⁻¹ * K))
    (by simpa [sub_eq_add_neg] using hfixed)
    hreplacement

/-- Two-sided bootstrap-test second-order rejection-probability transfer from
a fixed critical value to a random/bootstrap critical value. -/
theorem chapter10_abs_test_secondOrder_rejection_transfer
    {fixedReject randomReject : ℕ → ℝ} {alpha K : ℝ}
    (hfixed :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (fixedReject n - alpha + (n : ℝ)⁻¹ * K))
        atTop (𝓝 0))
    (hreplacement :
      Tendsto
        (fun n : ℕ => (n : ℝ) * (randomReject n - fixedReject n))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (randomReject n - alpha + (n : ℝ)⁻¹ * K))
      atTop (𝓝 0) :=
  secondOrder_scaled_probability_transfer
    (fixed := fixedReject) (random := randomReject)
    (target := alpha) (bias := fun n : ℕ => (n : ℝ)⁻¹ * K)
    hfixed hreplacement

/-- Hansen Theorem 10.15, Edgeworth component of the percentile-`t` refinement.

A second-order Edgeworth expansion for a scalar t-ratio gives the symmetric
interval probability expansion used by the percentile-`t` bootstrap interval.
The even `p₁` and odd `p₂` hypotheses encode the cancellation of the
`n^{-1/2}` Edgeworth term in two-sided intervals. -/
theorem chapter10_percentileT_secondOrder_interval_expansion
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    {c coverage : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = coverage) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          ((statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)) -
            coverage -
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) := by
  simpa [hcoverage] using
    h.symmetric_interval_scaled_remainder_tendsto_zero c hp1 hp2 hdensity

/-- Hansen Theorem 10.15 transfer form.

Once the bootstrap percentile-`t` quantile argument supplies an `o(n⁻¹)`
difference between the random interval coverage and the fixed symmetric
interval coverage, the fixed-critical Edgeworth expansion transfers to the
random/bootstrap interval. -/
theorem chapter10_percentileT_secondOrder_interval_expansion_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    {c coverage : ℝ} {randomCoverage : ℕ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = coverage)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (randomCoverage n -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (randomCoverage n -
            coverage -
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) :=
  chapter10_percentileT_secondOrder_interval_transfer
    (fixedCoverage := fun n : ℕ =>
      statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))
    (randomCoverage := randomCoverage)
    (coverage := coverage) (K := 2 * (p2 c * density c))
    (chapter10_percentileT_secondOrder_interval_expansion
      (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
      (p1 := p1) (p2 := p2) (c := c) (coverage := coverage)
      h hp1 hp2 hdensity hcoverage)
    hreplacement

/-- Polynomial-shape specialization of
`chapter10_percentileT_secondOrder_interval_expansion`.

This is the theorem-facing Chapter 10 wrapper for Hansen's even-quadratic
`p₁` and odd degree-five `p₂` Edgeworth polynomial shapes. -/
theorem chapter10_percentileT_secondOrder_interval_expansion_polynomial
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {a0 a2 b1 b3 b5 c coverage : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = coverage) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          ((statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)) -
            coverage -
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) := by
  simpa [hcoverage] using
    h.symmetric_interval_scaled_remainder_tendsto_zero_polynomial (c := c) hdensity

/-- Polynomial-shape specialization of
`chapter10_percentileT_secondOrder_interval_expansion_of_transfer`. -/
theorem chapter10_percentileT_secondOrder_interval_expansion_polynomial_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {a0 a2 b1 b3 b5 c coverage : ℝ} {randomCoverage : ℕ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c)
    (hcoverage : baseCDF c - baseCDF (-c) = coverage)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (randomCoverage n -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (randomCoverage n -
            coverage -
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) :=
  chapter10_percentileT_secondOrder_interval_expansion_of_transfer
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := edgeworthP1Polynomial a0 a2)
    (p2 := edgeworthP2Polynomial b1 b3 b5)
    (c := c) (coverage := coverage) (randomCoverage := randomCoverage)
    h (edgeworthP1Polynomial_neg a0 a2 c)
    (edgeworthP2Polynomial_neg b1 b3 b5 c) hdensity hcoverage
    hreplacement

/-- Hansen Theorem 10.17, fixed-critical Edgeworth component.

For a two-sided test using a fixed critical value `c`, the rejection probability
`1 - (Fₙ(c) - Fₙ(-c))` inherits the symmetric second-order Edgeworth expansion.
The bootstrap-quantile step of Theorem 10.17 supplies the additional
critical-value transfer premise needed to turn this fixed-critical expansion
into the `o(n^{-1})` bootstrap-test refinement. -/
theorem chapter10_abs_test_secondOrder_rejection_expansion
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    {c alpha : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c)
    (halpha : 1 - (baseCDF c - baseCDF (-c)) = alpha) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (((1 : ℝ) -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))) -
            alpha +
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) := by
  have hinterval :=
    h.symmetric_interval_scaled_remainder_tendsto_zero c hp1 hp2 hdensity
  have hneg := hinterval.neg
  have heq :
      (fun n : ℕ =>
        (n : ℝ) *
          (((1 : ℝ) -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))) -
            alpha +
            (n : ℝ)⁻¹ * (2 * (p2 c * density c)))) =ᶠ[atTop]
      (fun n : ℕ =>
        -((n : ℝ) *
          ((statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)) -
            (baseCDF c - baseCDF (-c)) -
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))) := by
    filter_upwards with n
    rw [← halpha]
    ring
  rw [tendsto_congr' heq]
  simpa using hneg

/-- Hansen Theorem 10.17 transfer form.

Once the bootstrap critical-value argument supplies an `o(n⁻¹)` difference
between the random-critical rejection probability and the fixed-critical
rejection probability, the fixed-critical Edgeworth expansion transfers to the
bootstrap test. -/
theorem chapter10_abs_test_secondOrder_rejection_expansion_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density p1 p2 : ℝ → ℝ}
    {c alpha : ℝ} {randomReject : ℕ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density p1 p2)
    (hp1 : p1 (-c) = p1 c) (hp2 : p2 (-c) = -p2 c)
    (hdensity : density (-c) = density c)
    (halpha : 1 - (baseCDF c - baseCDF (-c)) = alpha)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (randomReject n -
              ((1 : ℝ) -
                (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (randomReject n - alpha +
            (n : ℝ)⁻¹ * (2 * (p2 c * density c))))
      atTop (𝓝 0) :=
  chapter10_abs_test_secondOrder_rejection_transfer
    (fixedReject := fun n : ℕ =>
      (1 : ℝ) - (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)))
    (randomReject := randomReject)
    (alpha := alpha) (K := 2 * (p2 c * density c))
    (chapter10_abs_test_secondOrder_rejection_expansion
      (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
      (p1 := p1) (p2 := p2) (c := c) (alpha := alpha)
      h hp1 hp2 hdensity halpha)
    hreplacement

/-- Polynomial-shape specialization of
`chapter10_abs_test_secondOrder_rejection_expansion`. -/
theorem chapter10_abs_test_secondOrder_rejection_expansion_polynomial
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {a0 a2 b1 b3 b5 c alpha : ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c)
    (halpha : 1 - (baseCDF c - baseCDF (-c)) = alpha) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (((1 : ℝ) -
              (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c))) -
            alpha +
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) := by
  exact
    chapter10_abs_test_secondOrder_rejection_expansion
      (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
      (p1 := edgeworthP1Polynomial a0 a2)
      (p2 := edgeworthP2Polynomial b1 b3 b5)
      (c := c) (alpha := alpha) h
      (edgeworthP1Polynomial_neg a0 a2 c)
      (edgeworthP2Polynomial_neg b1 b3 b5 c)
      hdensity halpha

/-- Polynomial-shape specialization of
`chapter10_abs_test_secondOrder_rejection_expansion_of_transfer`. -/
theorem chapter10_abs_test_secondOrder_rejection_expansion_polynomial_of_transfer
    [IsProbabilityMeasure μ]
    {T : ℕ → Ω → ℝ} {baseCDF density : ℝ → ℝ}
    {a0 a2 b1 b3 b5 c alpha : ℝ} {randomReject : ℕ → ℝ}
    (h : SecondOrderEdgeworthExpansion μ T baseCDF density
      (edgeworthP1Polynomial a0 a2) (edgeworthP2Polynomial b1 b3 b5))
    (hdensity : density (-c) = density c)
    (halpha : 1 - (baseCDF c - baseCDF (-c)) = alpha)
    (hreplacement :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (randomReject n -
              ((1 : ℝ) -
                (statisticCDFReal μ T n c - statisticCDFReal μ T n (-c)))))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) *
          (randomReject n - alpha +
            (n : ℝ)⁻¹ *
              (2 * (edgeworthP2Polynomial b1 b3 b5 c * density c))))
      atTop (𝓝 0) :=
  chapter10_abs_test_secondOrder_rejection_expansion_of_transfer
    (μ := μ) (T := T) (baseCDF := baseCDF) (density := density)
    (p1 := edgeworthP1Polynomial a0 a2)
    (p2 := edgeworthP2Polynomial b1 b3 b5)
    (c := c) (alpha := alpha) (randomReject := randomReject)
    h (edgeworthP1Polynomial_neg a0 a2 c)
    (edgeworthP2Polynomial_neg b1 b3 b5 c) hdensity halpha
    hreplacement

end HigherOrderRefinements

end HansenEconometrics
