import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Elementwise Function

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

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
statistic converges in bootstrap distribution to that Gaussian law. Later
ordinary-bootstrap wrappers discharge this premise through pathwise weak
convergence, scalar projection/characteristic-function routes, and the iid
covariance-tail route. -/
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

end HansenEconometrics
