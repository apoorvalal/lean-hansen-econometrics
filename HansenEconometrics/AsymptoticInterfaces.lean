import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Topology.Instances.Matrix

/-!
# Stable interfaces for econometric limit theory

This module contains the small capability structures that form the reusable
boundary between model-specific constructors and downstream econometric
theorems. It deliberately contains no chapter assumptions or estimator
definitions.

The main public interfaces are:

* `MatrixEstimatorConsistent` and `CovarianceEstimatorConsistent`;
* `GramConsistency`;
* `AsymptoticallyLinearEstimator` and
  `BiasedAsymptoticallyLinearEstimator`;
* `GaussianLimit`, with `ScoreCLT` as its score-facing name;
* `FeasibleStandardErrorConsistent`.

New formalizations should consume these structures when they need the stated
capability. Concrete iid, triangular-array, regression, bootstrap, IV, or GMM
assumptions belong in constructor theorems outside this module.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

/-- Stable interface for consistency of a rectangular matrix estimator. -/
structure MatrixEstimatorConsistent
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k q : Type*} [Fintype k] [Fintype q]
    (Mhat : ℕ → Ω → Matrix k q ℝ) (M : Matrix k q ℝ) where
  matrix_measurable : ∀ n, AEStronglyMeasurable (Mhat n) μ
  consistent : TendstoInMeasure μ Mhat atTop (fun _ => M)

/-- Constructor for matrix-estimator consistency from its two defining fields. -/
theorem matrixEstimatorConsistent_of_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {k q : Type*} [Fintype k] [Fintype q]
    (Mhat : ℕ → Ω → Matrix k q ℝ) (M : Matrix k q ℝ)
    (hM_meas : ∀ n, AEStronglyMeasurable (Mhat n) μ)
    (hM : TendstoInMeasure μ Mhat atTop (fun _ => M)) :
    MatrixEstimatorConsistent μ Mhat M where
  matrix_measurable := hM_meas
  consistent := hM

/-- Stable interface for consistency of a covariance-matrix estimator. -/
structure CovarianceEstimatorConsistent
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : Type*} [Fintype k]
    (Vhat : ℕ → Ω → Matrix k k ℝ) (V : Matrix k k ℝ) where
  covariance_measurable : ∀ n, AEStronglyMeasurable (Vhat n) μ
  consistent : TendstoInMeasure μ Vhat atTop (fun _ => V)

/-- Constructor for covariance-estimator consistency from its two defining fields. -/
theorem covarianceEstimatorConsistent_of_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : Type*} [Fintype k]
    (Vhat : ℕ → Ω → Matrix k k ℝ) (V : Matrix k k ℝ)
    (hV_meas : ∀ n, AEStronglyMeasurable (Vhat n) μ)
    (hV : TendstoInMeasure μ Vhat atTop (fun _ => V)) :
    CovarianceEstimatorConsistent μ Vhat V where
  covariance_measurable := hV_meas
  consistent := hV

/-- Stable interface for convergence of a sample Gram matrix to a nonsingular
population Gram matrix. -/
structure GramConsistency
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : Type*} [Fintype k] [DecidableEq k]
    (Qhat : ℕ → Ω → Matrix k k ℝ) (Q : Matrix k k ℝ) where
  gram_measurable : ∀ n, AEStronglyMeasurable (Qhat n) μ
  consistent : TendstoInMeasure μ Qhat atTop (fun _ => Q)
  nonsingular : IsUnit Q.det

/-- Constructor for Gram consistency from measurability, convergence, and
nonsingularity. -/
theorem gramConsistency_of_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : Type*} [Fintype k] [DecidableEq k]
    (Qhat : ℕ → Ω → Matrix k k ℝ) (Q : Matrix k k ℝ)
    (hQ_meas : ∀ n, AEStronglyMeasurable (Qhat n) μ)
    (hQ : TendstoInMeasure μ Qhat atTop (fun _ => Q))
    (hQ_nonsing : IsUnit Q.det) :
    GramConsistency μ Qhat Q where
  gram_measurable := hQ_meas
  consistent := hQ
  nonsingular := hQ_nonsing

/-- Stable interface for an estimator or statistic with an asymptotic linear
representation.

The statistic `Y` is the scaled estimator error, `A` is the fixed linear map,
and `T` is the driving score or statistic sequence. -/
structure AsymptoticallyLinearEstimator
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : Type*} [Fintype k]
    (Y : ℕ → Ω → k → ℝ) (A : Matrix k k ℝ) (T : ℕ → Ω → k → ℝ) where
  scaled_measurable : ∀ n, AEMeasurable (Y n) μ
  expansion : TendstoInMeasure μ (Y - fun n ω => A *ᵥ T n ω) atTop (fun _ => 0)

/-- Constructor for an asymptotically linear estimator from measurability and
its `oₚ(1)` expansion. -/
theorem asymptoticallyLinearEstimator_of_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : Type*} [Fintype k]
    (Y : ℕ → Ω → k → ℝ) (A : Matrix k k ℝ) (T : ℕ → Ω → k → ℝ)
    (hY : ∀ n, AEMeasurable (Y n) μ)
    (hrem : TendstoInMeasure μ (Y - fun n ω => A *ᵥ T n ω) atTop (fun _ => 0)) :
    AsymptoticallyLinearEstimator μ Y A T where
  scaled_measurable := hY
  expansion := hrem

/-- Stable interface for a linearized estimator with a fixed
local-asymptotic bias. -/
structure BiasedAsymptoticallyLinearEstimator
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : Type*} [Fintype k]
    (Y : ℕ → Ω → k → ℝ) (A : Matrix k k ℝ) (T : ℕ → Ω → k → ℝ)
    (bias : k → ℝ) where
  scaled_measurable : ∀ n, AEMeasurable (Y n) μ
  expansion :
    TendstoInMeasure μ (Y - fun n ω => A *ᵥ T n ω + bias)
      atTop (fun _ => 0)

/-- Constructor for a biased asymptotically linear estimator from its defining
measurability and remainder fields. -/
theorem biasedAsymptoticallyLinearEstimator_of_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : Type*} [Fintype k]
    (Y : ℕ → Ω → k → ℝ) (A : Matrix k k ℝ) (T : ℕ → Ω → k → ℝ)
    (bias : k → ℝ)
    (hY : ∀ n, AEMeasurable (Y n) μ)
    (hrem : TendstoInMeasure μ (Y - fun n ω => A *ᵥ T n ω + bias)
      atTop (fun _ => 0)) :
    BiasedAsymptoticallyLinearEstimator μ Y A T bias where
  scaled_measurable := hY
  expansion := hrem

/-- Stable interface for a centered multivariate Gaussian limit of a driving
statistic. -/
structure GaussianLimit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    (T : ℕ → Ω → k → ℝ) (S : Matrix k k ℝ) where
  covariance_posSemidef : S.PosSemidef
  limit :
    TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 S)

/-- Score-facing name for the generic centered Gaussian-limit capability. -/
abbrev ScoreCLT
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    (score : ℕ → Ω → k → ℝ) (S : Matrix k k ℝ) :=
  GaussianLimit μ score S

/-- Constructor for the generic Gaussian-limit interface from covariance
positivity and distributional convergence. -/
theorem gaussianLimit_of_tendstoInDistribution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {k : Type*} [Fintype k] [DecidableEq k]
    (T : ℕ → Ω → k → ℝ) (S : Matrix k k ℝ)
    (hS : S.PosSemidef)
    (hT : TendstoInDistribution T atTop (fun z : EuclideanSpace ℝ k => z.ofLp)
      (fun _ => μ) (multivariateGaussian 0 S)) :
    GaussianLimit μ T S where
  covariance_posSemidef := hS
  limit := hT

/-- Stable interface for consistency of a feasible standard-error scale. -/
structure FeasibleStandardErrorConsistent
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (sehat : ℕ → Ω → ℝ) (se : ℝ) where
  standardError_measurable : ∀ n, AEMeasurable (sehat n) μ
  consistent : TendstoInMeasure μ sehat atTop (fun _ => se)

/-- Constructor for feasible standard-error consistency from its two defining
fields. -/
theorem feasibleStandardErrorConsistent_of_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (sehat : ℕ → Ω → ℝ) (se : ℝ)
    (hmeas : ∀ n, AEMeasurable (sehat n) μ)
    (hse : TendstoInMeasure μ sehat atTop (fun _ => se)) :
    FeasibleStandardErrorConsistent μ sehat se where
  standardError_measurable := hmeas
  consistent := hse

end HansenEconometrics
