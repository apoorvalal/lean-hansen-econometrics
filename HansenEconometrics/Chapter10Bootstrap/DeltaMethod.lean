import HansenEconometrics.Chapter10Bootstrap.WeakDistribution

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Elementwise Function

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

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

/-- Hansen Theorem 10.6, Gaussian event-probability specialization.

The matrix-linear bootstrap Delta method implies convergence of conditional
bootstrap probabilities for events whose transformed Gaussian limit-law
frontier has zero mass. -/
theorem chapter10_bootstrap_delta_method_gaussian_event_probability
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbability Pstar
        (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs)) A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) := by
  have hweak :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_bootstrap_delta_method_gaussian
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (V := V) G hV hT
  have hZstar :
      ∀ n ω,
        Measurable (fun ωs => matrixContinuousLinearMap G (Tstar n ω ωs)) := by
    intro n ω
    exact (matrixContinuousLinearMap G).continuous.measurable.comp (hTstar n ω)
  have hfrontier_map :
      ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
          (fun z : EuclideanSpace ℝ r => z)) (frontier A) = 0 := by
    simpa using hfrontier
  have hres :=
    hweak.event_probability_tendsto_of_null_frontier
      hPstar hZstar
      (aemeasurable_id :
        AEMeasurable (fun z : EuclideanSpace ℝ r => z)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
      hA hfrontier_map
  simpa using hres

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

/-- Hansen Theorem 10.6 Gaussian Delta-method wrapper from compact-range
bootstrap-probability closeness to the derivative-linearized statistic.

If the nonlinear statistic and its derivative-linearized approximation both
stay in a fixed compact set and are close in conditional bootstrap probability,
then the derivative-linearized Gaussian bootstrap limit transfers to the
nonlinear statistic. -/
theorem chapter10_bootstrap_delta_method_gaussian_of_compact_range_closeness
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistribution μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) := by
  have hlinearizedMeas :
      ∀ n ω,
        Measurable (fun ωs => matrixContinuousLinearMap G (Tstar n ω ωs)) := by
    intro n ω
    exact (matrixContinuousLinearMap G).continuous.measurable.comp (hTstar n ω)
  have hdelta :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_bootstrap_delta_method_gaussian
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (V := V) G hV hT
  exact
    hdelta.of_bootstrap_dist_tendsto_zero_compact_range hK hPstar hlinearizedMeas
      hthetaStar hlinearized_mem hthetaStar_mem hclose

/-- Hansen Theorem 10.6 Gaussian Delta-method event-probability wrapper from
compact-range bootstrap-probability closeness to the derivative-linearized
statistic. -/
theorem
    chapter10_bootstrap_delta_method_gaussian_event_probability_of_compact_range_closeness
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0))
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) := by
  have hweak :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_bootstrap_delta_method_gaussian_of_compact_range_closeness
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
      hlinearized_mem hthetaStar_mem hclose
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hfrontier_map :
      ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
          (fun z : EuclideanSpace ℝ r => z)) (frontier A) = 0 := by
    simpa using hfrontier
  have hres :=
    hweak.event_probability_tendsto_of_null_frontier
      hPfinite hthetaStar
      (aemeasurable_id :
        AEMeasurable (fun z : EuclideanSpace ℝ r => z)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
      hA hfrontier_map
  simpa using hres

/-- Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from compact-range
bootstrap-probability closeness to the derivative-linearized statistic. -/
theorem
    chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_range_closeness
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0))
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
    chapter10_bootstrap_delta_method_gaussian_of_compact_range_closeness
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
      hlinearized_mem hthetaStar_mem hclose
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstar :
      ∀ n ω, Measurable (fun ωs => coord (thetaStar n ω ωs)) := by
    intro n ω
    exact hcoord.measurable.comp (hthetaStar n ω)
  exact
    chapter10_bootstrap_continuous_mapping_distribution_of_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := coord) hweak hcoord hPfinite hZstar hcoord.aemeasurable hfrontier

/-- Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from compact-range
bootstrap-probability closeness with positive definite transformed covariance. -/
theorem
    chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_range_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_range_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem hclose
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hGVG x)

/-- Hansen Theorem 10.6 Gaussian Delta-method wrapper from noncompact
compact-tail bootstrap-probability closeness to the derivative-linearized
statistic.

This is the noncompact counterpart of
`chapter10_bootstrap_delta_method_gaussian_of_compact_range_closeness`: instead
of requiring both statistics to lie in a fixed compact set, it asks for compact
sets whose conditional bootstrap tails are asymptotically negligible for both
the derivative-linearized and nonlinear statistics. -/
theorem chapter10_bootstrap_delta_method_gaussian_of_compact_tail_closeness
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
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistribution μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) := by
  have hlinearizedMeas :
      ∀ n ω,
        Measurable (fun ωs => matrixContinuousLinearMap G (Tstar n ω ωs)) := by
    intro n ω
    exact (matrixContinuousLinearMap G).continuous.measurable.comp (hTstar n ω)
  have hdelta :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_bootstrap_delta_method_gaussian
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (V := V) G hV hT
  exact
    hdelta.of_bootstrap_dist_tendsto_zero_tight
      hPstar hlinearizedMeas hthetaStar hTail hclose

/-- Hansen Theorem 10.6 Gaussian Delta-method event-probability wrapper from
noncompact compact-tail bootstrap-probability closeness. -/
theorem
    chapter10_bootstrap_delta_method_gaussian_event_probability_of_compact_tail_closeness
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0))
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) := by
  have hweak :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_bootstrap_delta_method_gaussian_of_compact_tail_closeness
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
      hTail hclose
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hfrontier_map :
      ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
          (fun z : EuclideanSpace ℝ r => z)) (frontier A) = 0 := by
    simpa using hfrontier
  have hres :=
    hweak.event_probability_tendsto_of_null_frontier
      hPfinite hthetaStar
      (aemeasurable_id :
        AEMeasurable (fun z : EuclideanSpace ℝ r => z)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
      hA hfrontier_map
  simpa using hres

/-- Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from noncompact
compact-tail bootstrap-probability closeness. -/
theorem
    chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_tail_closeness
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
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0))
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
    chapter10_bootstrap_delta_method_gaussian_of_compact_tail_closeness
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
      hTail hclose
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstar :
      ∀ n ω, Measurable (fun ωs => coord (thetaStar n ω ωs)) := by
    intro n ω
    exact hcoord.measurable.comp (hthetaStar n ω)
  exact
    chapter10_bootstrap_continuous_mapping_distribution_of_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := coord) hweak hcoord hPfinite hZstar hcoord.aemeasurable hfrontier

/-- Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from noncompact
compact-tail bootstrap-probability closeness with positive definite
transformed covariance. -/
theorem
    chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_tail_posDef
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
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_tail_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
    hTail hclose
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hGVG x)

/-- Hansen Theorem 10.6 Gaussian Delta-method wrapper from a noncompact
compact-tail pointwise remainder bound.

The scalar envelope `R` supplies the conditional bootstrap-probability
closeness between the nonlinear statistic and its derivative-linearized
approximation; asymptotic compact-tail control for both statistics supplies the
noncompact uniform-continuity localization. -/
theorem
    chapter10_bootstrap_delta_method_gaussian_of_compact_tail_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs)
          (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs) :
    TendstoInBootstrapWeakDistribution μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_bootstrap_delta_method_gaussian_of_compact_tail_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
    hTail
    (TendstoInBootstrapWeakDistribution.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) (R := R) hPstar hR_tail hR_bound)

/-- Hansen Theorem 10.6 Gaussian Delta-method event-probability wrapper from
a noncompact compact-tail pointwise remainder bound. -/
theorem
    chapter10_bootstrap_delta_method_gaussian_event_probability_of_compact_tail_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs)
          (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_bootstrap_delta_method_gaussian_event_probability_of_compact_tail_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
    hTail
    (TendstoInBootstrapWeakDistribution.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) (R := R) hPstar hR_tail hR_bound)
    hA hfrontier

/-- Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from a noncompact
compact-tail pointwise remainder bound. -/
theorem
    chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_tail_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs)
          (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
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
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_tail_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
    hTail
    (TendstoInBootstrapWeakDistribution.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) (R := R) hPstar hR_tail hR_bound)
    hfrontier

/-- Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from a noncompact
compact-tail pointwise remainder bound with positive definite transformed
covariance. -/
theorem
    chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_tail_remainder_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs)
          (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_tail_posDef
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hGVG hT hPstar hTstar hthetaStar
    hTail
    (TendstoInBootstrapWeakDistribution.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) (R := R) hPstar hR_tail hR_bound)

/-- Hansen Theorem 10.6 Gaussian Delta-method wrapper from a compact-range
pointwise remainder bound.

The scalar envelope `R` supplies the conditional bootstrap-probability
closeness between the nonlinear statistic and its derivative-linearized
approximation; the existing compact-range Delta-method bridge then transfers
the Gaussian weak limit. -/
theorem
    chapter10_bootstrap_delta_method_gaussian_of_compact_range_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs)
          (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs) :
    TendstoInBootstrapWeakDistribution μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_bootstrap_delta_method_gaussian_of_compact_range_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (TendstoInBootstrapWeakDistribution.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) hPstar hR_tail hR_bound)

/-- Hansen Theorem 10.6 Gaussian Delta-method event-probability wrapper from a
compact-range pointwise remainder bound. -/
theorem
    chapter10_bootstrap_delta_method_gaussian_event_probability_of_compact_range_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs)
          (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_bootstrap_delta_method_gaussian_event_probability_of_compact_range_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (TendstoInBootstrapWeakDistribution.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) hPstar hR_tail hR_bound)
    hA hfrontier

/-- Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from a compact-range
pointwise remainder bound. -/
theorem
    chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_range_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs)
          (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
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
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_range_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (TendstoInBootstrapWeakDistribution.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) hPstar hR_tail hR_bound)
    hfrontier

/-- Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from a compact-range
pointwise remainder bound with positive definite transformed covariance. -/
theorem
    chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_range_remainder_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs)
          (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_range_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (R := R) (V := V) G hV hT hK hPstar hTstar
    hthetaStar hlinearized_mem hthetaStar_mem hR_tail hR_bound
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

/-- Indexed Hansen Theorem 10.6, Gaussian event-probability specialization for
sample-size-dependent bootstrap spaces. -/
theorem chapter10_indexed_bootstrap_delta_method_gaussian_event_probability
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ
      (bootstrapEventProbabilityIndexed Pstar
        (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs)) A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) := by
  have hweak :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_indexed_bootstrap_delta_method_gaussian
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (V := V) G hV hT
  have hZstar :
      ∀ n ω,
        Measurable (fun ωs => matrixContinuousLinearMap G (Tstar n ω ωs)) := by
    intro n ω
    exact (matrixContinuousLinearMap G).continuous.measurable.comp (hTstar n ω)
  have hfrontier_map :
      ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
          (fun z : EuclideanSpace ℝ r => z)) (frontier A) = 0 := by
    simpa using hfrontier
  have hres :=
    hweak.event_probability_tendsto_of_null_frontier
      hPstar hZstar
      (aemeasurable_id :
        AEMeasurable (fun z : EuclideanSpace ℝ r => z)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
      hA hfrontier_map
  simpa using hres

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

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method wrapper from
compact-range bootstrap-probability closeness to the derivative-linearized
statistic. -/
theorem
    chapter10_indexed_bootstrap_delta_method_gaussian_of_compact_range_closeness
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) := by
  have hlinearizedMeas :
      ∀ n ω,
        Measurable (fun ωs => matrixContinuousLinearMap G (Tstar n ω ωs)) := by
    intro n ω
    exact (matrixContinuousLinearMap G).continuous.measurable.comp (hTstar n ω)
  have hdelta :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_indexed_bootstrap_delta_method_gaussian
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (V := V) G hV hT
  exact
    hdelta.of_bootstrap_dist_tendsto_zero_compact_range hK hPstar hlinearizedMeas
      hthetaStar hlinearized_mem hthetaStar_mem hclose

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method event-probability
wrapper from compact-range bootstrap-probability closeness to the
derivative-linearized statistic. -/
theorem
    chapter10_indexed_bootstrap_delta_method_gaussian_event_probability_of_compact_range_closeness
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0))
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) := by
  have hweak :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_indexed_bootstrap_delta_method_gaussian_of_compact_range_closeness
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
      hlinearized_mem hthetaStar_mem hclose
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hfrontier_map :
      ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
          (fun z : EuclideanSpace ℝ r => z)) (frontier A) = 0 := by
    simpa using hfrontier
  have hres :=
    hweak.event_probability_tendsto_of_null_frontier
      hPfinite hthetaStar
      (aemeasurable_id :
        AEMeasurable (fun z : EuclideanSpace ℝ r => z)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
      hA hfrontier_map
  simpa using hres

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from
compact-range bootstrap-probability closeness to the derivative-linearized
statistic. -/
theorem
    chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_range_closeness
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0))
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
    chapter10_indexed_bootstrap_delta_method_gaussian_of_compact_range_closeness
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
      hlinearized_mem hthetaStar_mem hclose
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstar :
      ∀ n ω, Measurable (fun ωs => coord (thetaStar n ω ωs)) := by
    intro n ω
    exact hcoord.measurable.comp (hthetaStar n ω)
  exact
    chapter10_indexed_bootstrap_continuous_mapping_distribution_of_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := coord) hweak hcoord hPfinite hZstar hcoord.aemeasurable hfrontier

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from
compact-range bootstrap-probability closeness with positive definite
transformed covariance. -/
theorem
    chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_range_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_range_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem hclose
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hGVG x)

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method wrapper from noncompact
compact-tail bootstrap-probability closeness to the derivative-linearized
statistic. -/
theorem
    chapter10_indexed_bootstrap_delta_method_gaussian_of_compact_tail_closeness
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
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) := by
  have hlinearizedMeas :
      ∀ n ω,
        Measurable (fun ωs => matrixContinuousLinearMap G (Tstar n ω ωs)) := by
    intro n ω
    exact (matrixContinuousLinearMap G).continuous.measurable.comp (hTstar n ω)
  have hdelta :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_indexed_bootstrap_delta_method_gaussian
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (V := V) G hV hT
  exact
    hdelta.of_bootstrap_dist_tendsto_zero_tight
      hPstar hlinearizedMeas hthetaStar hTail hclose

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method event-probability
wrapper from noncompact compact-tail bootstrap-probability closeness. -/
theorem
    chapter10_indexed_bootstrap_delta_method_gaussian_event_probability_of_compact_tail_closeness
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0))
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) := by
  have hweak :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_indexed_bootstrap_delta_method_gaussian_of_compact_tail_closeness
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
      hTail hclose
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hfrontier_map :
      ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
          (fun z : EuclideanSpace ℝ r => z)) (frontier A) = 0 := by
    simpa using hfrontier
  have hres :=
    hweak.event_probability_tendsto_of_null_frontier
      hPfinite hthetaStar
      (aemeasurable_id :
        AEMeasurable (fun z : EuclideanSpace ℝ r => z)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
      hA hfrontier_map
  simpa using hres

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from
noncompact compact-tail bootstrap-probability closeness. -/
theorem
    chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_tail_closeness
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
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0))
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
    chapter10_indexed_bootstrap_delta_method_gaussian_of_compact_tail_closeness
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
      hTail hclose
  have hPfinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    letI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hZstar :
      ∀ n ω, Measurable (fun ωs => coord (thetaStar n ω ωs)) := by
    intro n ω
    exact hcoord.measurable.comp (hthetaStar n ω)
  exact
    chapter10_indexed_bootstrap_continuous_mapping_distribution_of_null_frontiers
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := coord) hweak hcoord hPfinite hZstar hcoord.aemeasurable hfrontier

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from
noncompact compact-tail bootstrap-probability closeness with positive definite
transformed covariance. -/
theorem
    chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_tail_posDef
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
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_tail_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
    hTail hclose
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hGVG x)

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method wrapper from a
noncompact compact-tail pointwise remainder bound. -/
theorem
    chapter10_indexed_bootstrap_delta_method_gaussian_of_compact_tail_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs)
          (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_of_compact_tail_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
    hTail
    (TendstoInBootstrapWeakDistributionIndexed.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) (R := R) hPstar hR_tail hR_bound)

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method event-probability
wrapper from a noncompact compact-tail pointwise remainder bound. -/
theorem
    chapter10_indexed_bootstrap_delta_method_gaussian_event_of_compact_tail_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs)
          (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_event_probability_of_compact_tail_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
    hTail
    (TendstoInBootstrapWeakDistributionIndexed.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) (R := R) hPstar hR_tail hR_bound)
    hA hfrontier

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from a
noncompact compact-tail pointwise remainder bound. -/
theorem
    chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_tail_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs)
          (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
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
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_tail_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
    hTail
    (TendstoInBootstrapWeakDistributionIndexed.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) (R := R) hPstar hR_tail hR_bound)
    hfrontier

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from a
noncompact compact-tail pointwise remainder bound with positive definite
transformed covariance. -/
theorem
    chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_tail_remainder_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs)
          (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_tail_posDef
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hGVG hT hPstar hTstar hthetaStar
    hTail
    (TendstoInBootstrapWeakDistributionIndexed.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) (R := R) hPstar hR_tail hR_bound)

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method wrapper from a
compact-range pointwise remainder bound. -/
theorem
    chapter10_indexed_bootstrap_delta_method_gaussian_of_compact_range_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs)
          (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_of_compact_range_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (TendstoInBootstrapWeakDistributionIndexed.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) hPstar hR_tail hR_bound)

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method event-probability wrapper
from a compact-range pointwise remainder bound. -/
theorem
    chapter10_indexed_bootstrap_delta_method_gaussian_event_of_compact_range_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs)
          (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_event_probability_of_compact_range_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (TendstoInBootstrapWeakDistributionIndexed.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) hPstar hR_tail hR_bound)
    hA hfrontier

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from a
compact-range pointwise remainder bound. -/
theorem
    chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_range_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs)
          (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
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
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_range_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem
    (TendstoInBootstrapWeakDistributionIndexed.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) hPstar hR_tail hR_bound)
    hfrontier

/-- Indexed Hansen Theorem 10.6 Gaussian Delta-method CDF wrapper from a
compact-range pointwise remainder bound with positive definite transformed
covariance. -/
theorem
    chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_range_remainder_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs)
          (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_range_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (R := R) (V := V) G hV hT hK hPstar hTstar
    hthetaStar hlinearized_mem hthetaStar_mem hR_tail hR_bound
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

/-- Hansen Theorem 10.7 smooth-function Gaussian event-probability wrapper
from exact derivative linearization. -/
theorem chapter10_bootstrap_smooth_function_gaussian_event_probability_of_linearization
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0)
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs)) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) := by
  have hweak :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_bootstrap_smooth_function_gaussian_of_linearization
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  have hthetaStar : ∀ n ω, Measurable (thetaStar n ω) := by
    intro n ω
    have heq :
        thetaStar n ω =
          fun ωs => matrixContinuousLinearMap G (Tstar n ω ωs) := by
      funext ωs
      exact hlinearization n ω ωs
    rw [heq]
    exact (matrixContinuousLinearMap G).continuous.measurable.comp (hTstar n ω)
  have hfrontier_map :
      ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
          (fun z : EuclideanSpace ℝ r => z)) (frontier A) = 0 := by
    simpa using hfrontier
  have hres :=
    hweak.event_probability_tendsto_of_null_frontier
      hPstar hthetaStar
      (aemeasurable_id :
        AEMeasurable (fun z : EuclideanSpace ℝ r => z)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
      hA hfrontier_map
  simpa using hres

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

/-- Hansen Theorem 10.7 smooth-function Gaussian event-probability wrapper
from bounded-continuous test-function linearization. -/
theorem
    chapter10_bootstrap_smooth_function_gaussian_event_probability_of_integral_linearization
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
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
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) := by
  have hweak :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_bootstrap_smooth_function_gaussian_of_integral_linearization
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  have hfrontier_map :
      ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
          (fun z : EuclideanSpace ℝ r => z)) (frontier A) = 0 := by
    simpa using hfrontier
  have hres :=
    hweak.event_probability_tendsto_of_null_frontier
      hPstar hthetaStar
      (aemeasurable_id :
        AEMeasurable (fun z : EuclideanSpace ℝ r => z)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
      hA hfrontier_map
  simpa using hres

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

/-- Hansen Theorem 10.7 smooth-function Gaussian wrapper from compact-range
bootstrap-probability closeness to the derivative-linearized statistic.

This is the compact-range version of
`chapter10_bootstrap_smooth_function_gaussian_of_integral_linearization`: if
the nonlinear statistic and its derivative-linearized approximation both stay
in a fixed compact set and are close in conditional bootstrap probability,
then the bounded-continuous integral-linearization premise follows by uniform
continuity. -/
theorem chapter10_bootstrap_smooth_function_gaussian_of_compact_range_closeness
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistribution μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_bootstrap_delta_method_gaussian_of_compact_range_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem hclose

/-- Hansen Theorem 10.7 smooth-function Gaussian wrapper from noncompact
compact-tail bootstrap-probability closeness to the derivative-linearized
statistic. -/
theorem chapter10_bootstrap_smooth_function_gaussian_of_compact_tail_closeness
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
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistribution μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_bootstrap_delta_method_gaussian_of_compact_tail_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
    hTail hclose

/-- Hansen Theorem 10.7 smooth-function Gaussian event-probability wrapper
from noncompact compact-tail bootstrap-probability closeness. -/
theorem
    chapter10_bootstrap_smooth_function_gaussian_event_probability_of_compact_tail_closeness
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0))
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_bootstrap_delta_method_gaussian_event_probability_of_compact_tail_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
    hTail hclose hA hfrontier

/-- Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from noncompact
compact-tail bootstrap-probability closeness. -/
theorem
    chapter10_bootstrap_smooth_function_gaussian_distribution_of_compact_tail_closeness
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
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0))
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
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_tail_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
    hTail hclose hfrontier

/-- Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from noncompact
compact-tail bootstrap-probability closeness with positive definite
transformed covariance. -/
theorem
    chapter10_bootstrap_smooth_function_gaussian_distribution_of_compact_tail_posDef
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
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_tail_posDef
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hGVG hT hPstar hTstar hthetaStar
    hTail hclose

/-- Hansen Theorem 10.7 smooth-function Gaussian wrapper from a noncompact
compact-tail pointwise remainder bound. -/
theorem
    chapter10_bootstrap_smooth_function_gaussian_of_compact_tail_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs) :
    TendstoInBootstrapWeakDistribution μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_bootstrap_delta_method_gaussian_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (R := R) (V := V) G hV hT hPstar hTstar
    hthetaStar hTail hR_tail hR_bound

/-- Hansen Theorem 10.7 smooth-function Gaussian event-probability wrapper
from a noncompact compact-tail pointwise remainder bound. -/
theorem
    chapter10_bootstrap_smooth_function_gaussian_event_probability_of_compact_tail_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_bootstrap_delta_method_gaussian_event_probability_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (R := R) (V := V) G hV hT hPstar hTstar
    hthetaStar hTail hR_tail hR_bound hA hfrontier

/-- Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from a noncompact
compact-tail pointwise remainder bound. -/
theorem
    chapter10_bootstrap_smooth_function_gaussian_distribution_of_compact_tail_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
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
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (R := R) (V := V) G hV hT hPstar hTstar
    hthetaStar hTail hR_tail hR_bound hfrontier

/-- Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from a noncompact
compact-tail pointwise remainder bound with positive definite transformed
covariance. -/
theorem
    chapter10_bootstrap_smooth_function_gaussian_distribution_of_compact_tail_remainder_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_tail_remainder_posDef
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (R := R) (V := V) G hV hGVG hT hPstar hTstar
    hthetaStar hTail hR_tail hR_bound

/-- Hansen Theorem 10.7 smooth-function Gaussian wrapper from a compact-range
remainder bound.

This is the `o_p*` remainder form of the compact-range route: a smooth-model
Taylor argument may supply the pointwise distance bound, while the bootstrap
tail premise states that the bound is negligible in conditional bootstrap
probability. -/
theorem
    chapter10_bootstrap_smooth_function_gaussian_of_compact_range_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs) :
    TendstoInBootstrapWeakDistribution μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) := by
  have hlinearizedMeas :
      ∀ n ω,
        Measurable (fun ωs => matrixContinuousLinearMap G (Tstar n ω ωs)) := by
    intro n ω
    exact (matrixContinuousLinearMap G).continuous.measurable.comp (hTstar n ω)
  have hdelta :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_bootstrap_delta_method_gaussian
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (V := V) G hV hT
  exact
    hdelta.of_bootstrap_dist_tendsto_zero_compact_range_of_dist_bound
      hK hPstar hlinearizedMeas hthetaStar hlinearized_mem hthetaStar_mem
      hR_tail hR_bound

/-- Hansen Theorem 10.7 smooth-function Gaussian event-probability wrapper
from a compact-range remainder bound. -/
theorem
    chapter10_bootstrap_smooth_function_gaussian_event_probability_of_compact_range_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) := by
  have hclose :
      ∀ δ : ℝ, 0 < δ →
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | δ ≤ dist (thetaStar n ω ωs)
                (matrixContinuousLinearMap G (Tstar n ω ωs))})
          atTop (fun _ => 0) :=
    TendstoInBootstrapWeakDistribution.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) (R := R) hPstar hR_tail hR_bound
  exact
    chapter10_bootstrap_delta_method_gaussian_event_probability_of_compact_range_closeness
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
      hlinearized_mem hthetaStar_mem hclose hA hfrontier

/-- Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from a
compact-range remainder bound. -/
theorem
    chapter10_bootstrap_smooth_function_gaussian_distribution_of_compact_range_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
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
  have hclose :
      ∀ δ : ℝ, 0 < δ →
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | δ ≤ dist (thetaStar n ω ωs)
                (matrixContinuousLinearMap G (Tstar n ω ωs))})
          atTop (fun _ => 0) :=
    TendstoInBootstrapWeakDistribution.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) (R := R) hPstar hR_tail hR_bound
  exact
    chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_range_closeness
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
      hlinearized_mem hthetaStar_mem hclose hfrontier

/-- Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from a
compact-range remainder bound with positive definite transformed covariance. -/
theorem
    chapter10_bootstrap_smooth_function_gaussian_distribution_of_compact_range_remainder_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_smooth_function_gaussian_distribution_of_compact_range_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (R := R) (V := V) G hV hT hK hPstar hTstar
    hthetaStar hlinearized_mem hthetaStar_mem hR_tail hR_bound
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hGVG x)

/-- Hansen Theorem 10.7 smooth-function Gaussian event-probability wrapper
from compact-range bootstrap-probability closeness to the
derivative-linearized statistic. -/
theorem
    chapter10_bootstrap_smooth_function_gaussian_event_probability_of_compact_range_closeness
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0))
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbability Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_bootstrap_delta_method_gaussian_event_probability_of_compact_range_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem hclose hA hfrontier

/-- Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from compact-range
bootstrap-probability closeness to the derivative-linearized statistic. -/
theorem
    chapter10_bootstrap_smooth_function_gaussian_distribution_of_compact_range_closeness
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0))
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
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_range_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem hclose hfrontier

/-- Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from compact-range
bootstrap-probability closeness with positive definite transformed covariance. -/
theorem
    chapter10_bootstrap_smooth_function_gaussian_distribution_of_compact_range_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistribution μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_bootstrap_delta_method_gaussian_distribution_of_compact_range_posDef
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hGVG hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem hclose

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

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian event-probability
wrapper from exact derivative linearization. -/
theorem chapter10_indexed_bootstrap_smooth_gaussian_event_probability_of_linearization
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0)
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs)) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) := by
  have hweak :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_indexed_bootstrap_smooth_function_gaussian_of_linearization
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  have hthetaStar : ∀ n ω, Measurable (thetaStar n ω) := by
    intro n ω
    have heq :
        thetaStar n ω =
          fun ωs => matrixContinuousLinearMap G (Tstar n ω ωs) := by
      funext ωs
      exact hlinearization n ω ωs
    rw [heq]
    exact (matrixContinuousLinearMap G).continuous.measurable.comp (hTstar n ω)
  have hfrontier_map :
      ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
          (fun z : EuclideanSpace ℝ r => z)) (frontier A) = 0 := by
    simpa using hfrontier
  have hres :=
    hweak.event_probability_tendsto_of_null_frontier
      hPstar hthetaStar
      (aemeasurable_id :
        AEMeasurable (fun z : EuclideanSpace ℝ r => z)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
      hA hfrontier_map
  simpa using hres

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

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian event-probability
wrapper from bounded-continuous test-function linearization. -/
theorem
    chapter10_indexed_bootstrap_smooth_gaussian_event_probability_of_integral_linearization
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
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
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) := by
  have hweak :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_indexed_bootstrap_smooth_function_gaussian_of_integral_linearization
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  have hfrontier_map :
      ((multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).map
          (fun z : EuclideanSpace ℝ r => z)) (frontier A) = 0 := by
    simpa using hfrontier
  have hres :=
    hweak.event_probability_tendsto_of_null_frontier
      hPstar hthetaStar
      (aemeasurable_id :
        AEMeasurable (fun z : EuclideanSpace ℝ r => z)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
      hA hfrontier_map
  simpa using hres

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

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian wrapper from
compact-range bootstrap-probability closeness to the derivative-linearized
statistic. -/
theorem
    chapter10_indexed_bootstrap_smooth_function_gaussian_of_compact_range_closeness
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_of_compact_range_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem hclose

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian wrapper from
noncompact compact-tail bootstrap-probability closeness to the
derivative-linearized statistic. -/
theorem
    chapter10_indexed_bootstrap_smooth_function_gaussian_of_compact_tail_closeness
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
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_of_compact_tail_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
    hTail hclose

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian event-probability
wrapper from noncompact compact-tail bootstrap-probability closeness. -/
theorem
    chapter10_indexed_bootstrap_smooth_gaussian_event_probability_of_compact_tail_closeness
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0))
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_event_probability_of_compact_tail_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
    hTail hclose hA hfrontier

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from
noncompact compact-tail bootstrap-probability closeness. -/
theorem
    chapter10_indexed_bootstrap_smooth_function_gaussian_distribution_of_compact_tail_closeness
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
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0))
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
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_tail_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hPstar hTstar hthetaStar
    hTail hclose hfrontier

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from
noncompact compact-tail bootstrap-probability closeness with positive definite
transformed covariance. -/
theorem
    chapter10_indexed_bootstrap_smooth_function_gaussian_distribution_of_compact_tail_posDef
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
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_tail_posDef
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hGVG hT hPstar hTstar hthetaStar
    hTail hclose

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian wrapper from a
noncompact compact-tail pointwise remainder bound. -/
theorem
    chapter10_indexed_bootstrap_smooth_function_gaussian_of_compact_tail_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (R := R) (V := V) G hV hT hPstar hTstar
    hthetaStar hTail hR_tail hR_bound

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian event-probability
wrapper from a noncompact compact-tail pointwise remainder bound. -/
theorem
    chapter10_indexed_bootstrap_smooth_gaussian_event_probability_of_compact_tail_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_event_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (R := R) (V := V) G hV hT hPstar hTstar
    hthetaStar hTail hR_tail hR_bound hA hfrontier

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from a
noncompact compact-tail pointwise remainder bound. -/
theorem
    chapter10_indexed_bootstrap_smooth_gaussian_distribution_of_compact_tail_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
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
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_tail_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (R := R) (V := V) G hV hT hPstar hTstar
    hthetaStar hTail hR_tail hR_bound hfrontier

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from a
noncompact compact-tail pointwise remainder bound with positive definite
transformed covariance. -/
theorem
    chapter10_indexed_bootstrap_smooth_gaussian_distribution_of_compact_tail_remainder_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_tail_remainder_posDef
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (R := R) (V := V) G hV hGVG hT hPstar hTstar
    hthetaStar hTail hR_tail hR_bound

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian wrapper from a
compact-range remainder bound. -/
theorem
    chapter10_indexed_bootstrap_smooth_function_gaussian_of_compact_range_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => z) := by
  have hlinearizedMeas :
      ∀ n ω,
        Measurable (fun ωs => matrixContinuousLinearMap G (Tstar n ω ωs)) := by
    intro n ω
    exact (matrixContinuousLinearMap G).continuous.measurable.comp (hTstar n ω)
  have hdelta :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (fun z : EuclideanSpace ℝ r => z) :=
    chapter10_indexed_bootstrap_delta_method_gaussian
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (V := V) G hV hT
  exact
    hdelta.of_bootstrap_dist_tendsto_zero_compact_range_of_dist_bound
      hK hPstar hlinearizedMeas hthetaStar hlinearized_mem hthetaStar_mem
      hR_tail hR_bound

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian event-probability
wrapper from a compact-range remainder bound. -/
theorem
    chapter10_indexed_bootstrap_smooth_gaussian_event_probability_of_compact_range_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) := by
  have hclose :
      ∀ δ : ℝ, 0 < δ →
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | δ ≤ dist (thetaStar n ω ωs)
                (matrixContinuousLinearMap G (Tstar n ω ωs))})
          atTop (fun _ => 0) :=
    TendstoInBootstrapWeakDistributionIndexed.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) (R := R) hPstar hR_tail hR_bound
  exact
    chapter10_indexed_bootstrap_delta_method_gaussian_event_probability_of_compact_range_closeness
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
      hlinearized_mem hthetaStar_mem hclose hA hfrontier

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from a
compact-range remainder bound. -/
theorem
    chapter10_indexed_bootstrap_smooth_function_gaussian_distribution_of_compact_remainder_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs)
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
  have hclose :
      ∀ δ : ℝ, 0 < δ →
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | δ ≤ dist (thetaStar n ω ωs)
                (matrixContinuousLinearMap G (Tstar n ω ωs))})
          atTop (fun _ => 0) :=
    TendstoInBootstrapWeakDistributionIndexed.bootstrap_dist_tendsto_zero_of_dist_bound
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => matrixContinuousLinearMap G (Tstar n ω ωs))
      (Zstar' := thetaStar) (R := R) hPstar hR_tail hR_bound
  exact
    chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_range_closeness
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
      hlinearized_mem hthetaStar_mem hclose hfrontier

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from a
compact-range remainder bound with positive definite transformed covariance. -/
theorem
    chapter10_indexed_bootstrap_smooth_function_gaussian_distribution_of_compact_remainder_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hR_tail : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω => (Pstar n ω).real {ωs | δ ≤ R n ω ωs})
        atTop (fun _ => 0))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        R n ω ωs) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_smooth_function_gaussian_distribution_of_compact_remainder_bound
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (R := R) (V := V) G hV hT hK hPstar hTstar
    hthetaStar hlinearized_mem hthetaStar_mem hR_tail hR_bound
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hGVG x)

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian event-probability
wrapper from compact-range bootstrap-probability closeness to the
derivative-linearized statistic. -/
theorem
    chapter10_indexed_bootstrap_smooth_gaussian_event_probability_of_compact_range_closeness
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {A K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0))
    (hA : MeasurableSet A)
    (hfrontier :
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (frontier A) = 0) :
    TendstoInMeasure μ (bootstrapEventProbabilityIndexed Pstar thetaStar A)
      atTop
        (fun _ =>
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)).real A) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_event_probability_of_compact_range_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem hclose hA hfrontier

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from
compact-range bootstrap-probability closeness to the derivative-linearized
statistic. -/
theorem
    chapter10_indexed_bootstrap_smooth_function_gaussian_distribution_of_compact_range_closeness
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0))
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
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_range_closeness
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem hclose hfrontier

/-- Indexed Hansen Theorem 10.7 smooth-function Gaussian CDF wrapper from
compact-range bootstrap-probability closeness with positive definite
transformed covariance. -/
theorem
    chapter10_indexed_bootstrap_smooth_function_gaussian_distribution_of_compact_range_posDef
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {K : Set (EuclideanSpace ℝ r)}
    (hV : V.PosSemidef)
    (hGVG : (G * V * Gᵀ).PosDef)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hclose : ∀ δ : ℝ, 0 < δ →
      TendstoInMeasure μ
        (fun n ω =>
          (Pstar n ω).real
            {ωs | δ ≤ dist (thetaStar n ω ωs)
              (matrixContinuousLinearMap G (Tstar n ω ωs))})
        atTop (fun _ => 0)) :
    TendstoInBootstrapDistributionIndexed μ Pstar
      (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
      (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
  chapter10_indexed_bootstrap_delta_method_gaussian_distribution_of_compact_range_posDef
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hGVG hT hK hPstar hTstar hthetaStar
    hlinearized_mem hthetaStar_mem hclose

end BootstrapDeltaMethod

end HansenEconometrics
