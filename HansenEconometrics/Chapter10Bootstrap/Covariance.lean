import HansenEconometrics.Chapter10Bootstrap.Variance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Elementwise Function

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

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

/-- Moment-form conditional bootstrap covariance of two real statistics. -/
noncomputable def bootstrapCovarianceReal
    (Pstar : ℕ → Ω → Measure Ωs)
    (Xstar Ystar : ℕ → Ω → Ωs → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs] -
    (Pstar n ω)[Xstar n ω] * (Pstar n ω)[Ystar n ω]

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

/-- Indexed moment-form conditional bootstrap covariance of two real
statistics. -/
noncomputable def bootstrapCovarianceRealIndexed
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    (Pstar : ∀ n, Ω → Measure (Ωboot n))
    (Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Pstar n ω)[fun ωs => Xstar n ω ωs * Ystar n ω ωs] -
    (Pstar n ω)[Xstar n ω] * (Pstar n ω)[Ystar n ω]

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

/-- Indexed conditional mean of the normalized ordinary nonparametric-bootstrap
mean.

For the `Fin (n+1) -> Fin (n+1)` resampling space, Hansen's CLT-scaled
centered bootstrap mean has exact conditional mean zero. -/
theorem bootstrapMeanVecIndexed_normalized_finSucc_resampleMean_sub_empiricalMean_eq_zero
    [Fintype k] (Y : ℕ → Ω → k → ℝ) (n : ℕ) (ω : Ω) :
    bootstrapMeanVecIndexed
        (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
        (fun n _ =>
          ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
        n ω =
      0 := by
  ext a
  simpa [bootstrapMeanVecIndexed] using
    integral_normalized_finSucc_resampleMean_sub_empiricalMean_apply_eq_zero
      (Y := Y) n ω a

/-- Indexed conditional cross moments of the normalized ordinary
nonparametric-bootstrap mean.

The CLT-scaled centered bootstrap mean has raw cross moments equal to the
finite empirical one-draw covariance matrix. -/
theorem
    bootstrapCrossMomentMatIndexed_normalized_finSucc_resampleMean_sub_empiricalMean_eq_covMat
    [Fintype k] (Y : ℕ → Ω → k → ℝ) (n : ℕ) (ω : Ω) :
    bootstrapCrossMomentMatIndexed
        (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
        (fun n _ =>
          ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
        n ω =
      covMat
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1)))
        (fun i a => Y i.val ω a) := by
  ext a b
  simpa [bootstrapCrossMomentMatIndexed] using
    integral_mul_normalized_finSucc_resampleMean_sub_empiricalMean_eq_covMat
      (Y := Y) n ω a b

/-- Indexed conditional covariance matrix of the normalized ordinary
nonparametric-bootstrap mean.

This packages the finite `Fin (n+1)` covariance identity in the indexed
conditional covariance API used by the Chapter 10 variance and regression
wrappers. -/
theorem
    bootstrapCovarianceMatIndexed_normalized_finSucc_resampleMean_sub_empiricalMean_eq_covMat
    [Fintype k] (Y : ℕ → Ω → k → ℝ) (n : ℕ) (ω : Ω) :
    bootstrapCovarianceMatIndexed
        (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
        (fun n _ =>
          ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
        n ω =
      covMat
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1)))
        (fun i a => Y i.val ω a) := by
  simpa [bootstrapCovarianceMatIndexed] using
    covMat_normalized_finSucc_resampleMean_sub_empiricalMean_eq
      (Y := Y) n ω

/-- Shifted empirical-uniform WLLN on `Fin (n+1)`.

The reusable WLLN in `AsymptoticUtils` is stated for averages over
`Finset.range n`.  Ordinary finite nonparametric bootstrap support uses
`Fin (n+1)` to avoid the empty sample at `n = 0`; this bridge rewrites the
uniform empirical integral into the shifted range average. -/
theorem integral_uniformOn_finSucc_tendstoInMeasure_wlln
    [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hint : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    TendstoInMeasure μ
      (fun n ω =>
        ∫ i : Fin (n + 1), X i.val ω
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
            Measure (Fin (n + 1))))
      atTop (fun _ => ∫ ω, X 0 ω ∂μ) := by
  have hbase :=
    tendstoInMeasure_wlln (μ := μ) X hint hindep hident
  have hshift :
      TendstoInMeasure μ
        (fun n ω =>
          (((n + 1 : ℕ) : ℝ)⁻¹) •
            ∑ i ∈ Finset.range (n + 1), X i ω)
        atTop (fun _ => ∫ ω, X 0 ω ∂μ) := by
    rw [tendstoInMeasure_iff_dist] at hbase ⊢
    intro ε hε
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (hbase ε hε).comp (tendsto_add_atTop_nat 1)
  refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hshift
  exact ae_of_all μ fun ω => by
    have hfinite :
        ∫ i : Fin (n + 1), X i.val ω
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
            Measure (Fin (n + 1))) =
        ((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal •
          ∑ i : Fin (n + 1), X i.val ω :=
      integral_uniformOn_univ_eq_card_inv_smul_sum
        (Y := fun i : Fin (n + 1) => X i.val ω)
    have hcoeff :
        (((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal) =
          ((n + 1 : ℝ)⁻¹) := by
      have htoReal :
          ((Fintype.card (Fin (n + 1)) : ℝ≥0∞).toReal) =
            (n + 1 : ℝ) := by
        rw [Fintype.card_fin]
        simpa using ENNReal.toReal_natCast (n + 1)
      rw [ENNReal.toReal_inv, htoReal]
    have hsum :
        (∑ i : Fin (n + 1), X i.val ω) =
          ∑ i ∈ Finset.range (n + 1), X i ω := by
      rw [Finset.sum_range]
    rw [hcoeff, hsum] at hfinite
    simpa [Nat.cast_add, Nat.cast_one] using hfinite.symm

/-- Shifted empirical-uniform WLLN with a textbook iid independence premise.

This is the `iIndepFun`-facing wrapper around
`integral_uniformOn_finSucc_tendstoInMeasure_wlln`; the core theorem only needs
pairwise independence. -/
theorem integral_uniformOn_finSucc_tendstoInMeasure_wlln_of_iIndep
    [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hint : Integrable (X 0) μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    TendstoInMeasure μ
      (fun n ω =>
        ∫ i : Fin (n + 1), X i.val ω
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
            Measure (Fin (n + 1))))
      atTop (fun _ => ∫ ω, X 0 ω ∂μ) := by
  exact integral_uniformOn_finSucc_tendstoInMeasure_wlln
    (μ := μ) X hint (fun _ _ hij => hindep.indepFun hij) hident

/-- Shifted empirical-uniform strong law on `Fin (n+1)`.

This is the almost-sure counterpart of
`integral_uniformOn_finSucc_tendstoInMeasure_wlln`, keeping the pathwise
convergence supplied by Mathlib's strong law.  It is used by the
characteristic-function route for Hansen Theorem 10.4, where the conditional
bootstrap characteristic functions are first handled pathwise. -/
theorem integral_uniformOn_finSucc_tendsto_ae_wlln
    [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hint : Integrable (X 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          ∫ i : Fin (n + 1), X i.val ω
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))))
        atTop (𝓝 (∫ ω, X 0 ω ∂μ)) := by
  have hbase :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
          atTop (𝓝 (∫ ω, X 0 ω ∂μ)) := by
    simpa using ProbabilityTheory.strong_law_ae X hint hindep hident
  filter_upwards [hbase] with ω hω
  have hshift :
      Tendsto
        (fun n : ℕ =>
          (((n + 1 : ℕ) : ℝ)⁻¹) •
            ∑ i ∈ Finset.range (n + 1), X i ω)
        atTop (𝓝 (∫ ω, X 0 ω ∂μ)) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hω.comp (tendsto_add_atTop_nat 1)
  refine hshift.congr' ?_
  exact Eventually.of_forall fun n => by
    have hfinite :
        ∫ i : Fin (n + 1), X i.val ω
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
            Measure (Fin (n + 1))) =
        ((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal •
          ∑ i : Fin (n + 1), X i.val ω :=
      integral_uniformOn_univ_eq_card_inv_smul_sum
        (Y := fun i : Fin (n + 1) => X i.val ω)
    have hcoeff :
        (((Fintype.card (Fin (n + 1)) : ℝ≥0∞)⁻¹).toReal) =
          ((n + 1 : ℝ)⁻¹) := by
      have htoReal :
          ((Fintype.card (Fin (n + 1)) : ℝ≥0∞).toReal) =
            (n + 1 : ℝ) := by
        rw [Fintype.card_fin]
        simpa using ENNReal.toReal_natCast (n + 1)
      rw [ENNReal.toReal_inv, htoReal]
    have hsum :
        (∑ i : Fin (n + 1), X i.val ω) =
          ∑ i ∈ Finset.range (n + 1), X i ω := by
      rw [Finset.sum_range]
    rw [hcoeff, hsum] at hfinite
    simpa [Nat.cast_add, Nat.cast_one] using hfinite.symm

/-- Shifted empirical-uniform strong law with a textbook iid independence
premise. -/
theorem integral_uniformOn_finSucc_tendsto_ae_wlln_of_iIndep
    [IsFiniteMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hint : Integrable (X 0) μ)
    (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          ∫ i : Fin (n + 1), X i.val ω
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))))
        atTop (𝓝 (∫ ω, X 0 ω ∂μ)) := by
  exact integral_uniformOn_finSucc_tendsto_ae_wlln
    (μ := μ) X hint (fun _ _ hij => hindep.indepFun hij) hident

/-- Shifted empirical square-tail strong law on `Fin (n+1)`.

For every fixed threshold `R`, the empirical uncentered square-tail integral
converges almost surely to the corresponding population square tail.  This is
the fixed-threshold strong-law input for the centered moving-tail
characteristic-function remainder bridge. -/
theorem empiricalTailSqFinSucc_tendsto_ae_wlln
    [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (R : ℝ)
    (hY : MemLp (Y 0) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          empiricalTailSqFinSucc (fun i => Y i ω) n R)
        atTop
        (𝓝
          (∫ ω, Set.indicator {ω | R ≤ |Y 0 ω|}
            (fun ω => (Y 0 ω) ^ 2) ω ∂μ)) := by
  let tailMap : ℝ → ℝ :=
    fun x => Set.indicator {y : ℝ | R ≤ |y|} (fun y => y ^ 2) x
  have htail_meas : Measurable tailMap := by
    dsimp [tailMap]
    have hsq : Measurable (fun y : ℝ => y ^ 2) := by fun_prop
    exact hsq.indicator
      (measurableSet_le measurable_const continuous_abs.measurable)
  have hint : Integrable (fun ω => tailMap (Y 0 ω)) μ := by
    simpa [tailMap] using
      integrable_tail_sq_indicator_of_memLp (P := μ) (Y := Y 0) hY R
  have hindep_tail :
      Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => tailMap (Y i ω)) := by
    intro i j hij
    exact IndepFun.comp (hindep hij) htail_meas htail_meas
  have hident_tail :
      ∀ i,
        IdentDistrib
          (fun ω => tailMap (Y i ω))
          (fun ω => tailMap (Y 0 ω)) μ μ := by
    intro i
    exact (hident i).comp htail_meas
  have hbase :=
    integral_uniformOn_finSucc_tendsto_ae_wlln
      (μ := μ) (X := fun i ω => tailMap (Y i ω))
      hint hindep_tail hident_tail
  filter_upwards [hbase] with ω hω
  refine hω.congr' ?_
  exact Eventually.of_forall fun n => by
    refine integral_congr_ae ?_
    exact ae_of_all _ fun i => by
      by_cases hi : R ≤ |Y i.val ω| <;>
        simp [tailMap, hi]

/-- Shifted empirical square-tail strong law on `Fin (n+1)` with the textbook
`iIndepFun` premise. -/
theorem empiricalTailSqFinSucc_tendsto_ae_wlln_of_iIndep
    [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (R : ℝ)
    (hY : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          empiricalTailSqFinSucc (fun i => Y i ω) n R)
        atTop
        (𝓝
          (∫ ω, Set.indicator {ω | R ≤ |Y 0 ω|}
            (fun ω => (Y 0 ω) ^ 2) ω ∂μ)) :=
  empiricalTailSqFinSucc_tendsto_ae_wlln
    (μ := μ) Y R hY (fun _ _ hij => hindep.indepFun hij) hident

/-- Almost-sure fixed-threshold empirical square tails are eventually small
under iid finite second moments.

This countable-grid bridge combines the fixed-threshold shifted strong law with
the population square-tail truncation lemma.  It is the pathwise input required
by `centeredEmpiricalTailSqFinSucc_tendsto_zero_of_empiricalMean_tendsto_tail`.
-/
theorem empiricalTailSqFinSucc_eventually_small_ae_of_iid
    [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hY : MemLp (Y 0) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ᶠ n in atTop, empiricalTailSqFinSucc (fun i => Y i ω) n R ≤ ε := by
  classical
  let γ : ℕ → ℝ := fun m => (((m + 1 : ℕ) : ℝ))⁻¹
  have hγ_pos : ∀ m, 0 < γ m := by
    intro m
    dsimp [γ]
    positivity
  have hchoose : ∀ m : ℕ, ∃ R : ℝ, 1 ≤ R ∧
      (∫ ω, Set.indicator {ω | R ≤ |Y 0 ω|}
        (fun ω => (Y 0 ω) ^ 2) ω ∂μ) ≤ γ m / 2 := by
    intro m
    rcases integral_tail_sq_eventual_le_of_memLp_two
        (μ := μ) (Y := Y 0) hY (γ m / 2) (by positivity) with
      ⟨R, hR, htailR⟩
    exact ⟨R, hR, htailR R le_rfl⟩
  choose R hR_one hR_tail using hchoose
  have htail_grid : ∀ m : ℕ, ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          empiricalTailSqFinSucc (fun i => Y i ω) n (R m))
        atTop
        (𝓝
          (∫ ω, Set.indicator {ω | R m ≤ |Y 0 ω|}
            (fun ω => (Y 0 ω) ^ 2) ω ∂μ)) := by
    intro m
    exact empiricalTailSqFinSucc_tendsto_ae_wlln
      (μ := μ) Y (R m) hY hindep hident
  have htail_all : ∀ᵐ ω ∂μ, ∀ m : ℕ,
      Tendsto
        (fun n : ℕ =>
          empiricalTailSqFinSucc (fun i => Y i ω) n (R m))
        atTop
        (𝓝
          (∫ ω, Set.indicator {ω | R m ≤ |Y 0 ω|}
            (fun ω => (Y 0 ω) ^ 2) ω ∂μ)) :=
    ae_all_iff.2 htail_grid
  filter_upwards [htail_all] with ω hω
  intro ε hε
  rcases exists_nat_one_div_lt hε with ⟨m, hm⟩
  refine ⟨R m, hR_one m, ?_⟩
  have hlimit_lt :
      (∫ ω, Set.indicator {ω | R m ≤ |Y 0 ω|}
        (fun ω => (Y 0 ω) ^ 2) ω ∂μ) < ε := by
    have hhalf_lt : γ m / 2 < γ m := by
      linarith [hγ_pos m]
    have hγ_lt : γ m < ε := by
      simpa [γ, Nat.cast_add, Nat.cast_one, one_div] using hm
    exact lt_of_le_of_lt (hR_tail m) (hhalf_lt.trans hγ_lt)
  filter_upwards [(hω m).eventually (Iio_mem_nhds hlimit_lt)] with n hn
  exact le_of_lt hn

/-- Almost-sure fixed-threshold empirical square tails are eventually small
under iid finite second moments, with the textbook `iIndepFun` premise. -/
theorem empiricalTailSqFinSucc_eventually_small_ae_of_iIndep
    [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hY : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ᶠ n in atTop, empiricalTailSqFinSucc (fun i => Y i ω) n R ≤ ε :=
  empiricalTailSqFinSucc_eventually_small_ae_of_iid
    (μ := μ) Y hY (fun _ _ hij => hindep.indepFun hij) hident

/-- Centered moving empirical square tails vanish almost surely under iid
finite second moments.

The empirical mean converges by the shifted strong law.  The centered-tail
truncation bridge then reduces the moving `1 / sqrt (n+1)` tail to the
fixed-threshold uncentered empirical square tails controlled above. -/
theorem centeredEmpiricalTailSqFinSucc_tendsto_ae_of_iid
    [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hY : MemLp (Y 0) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ, ∀ δ : ℝ, 0 < δ →
      Tendsto
        (fun n : ℕ =>
          centeredEmpiricalTailSqFinSucc (fun i => Y i ω) n
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) δ)
        atTop (𝓝 0) := by
  have hY_int : Integrable (Y 0) μ :=
    memLp_one_iff_integrable.mp (hY.mono_exponent one_le_two)
  have hmean :
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ =>
            ∫ i : Fin (n + 1), Y i.val ω
              ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                Measure (Fin (n + 1))))
          atTop (𝓝 (∫ ω, Y 0 ω ∂μ)) :=
    integral_uniformOn_finSucc_tendsto_ae_wlln
      (μ := μ) Y hY_int hindep hident
  have htail :=
    empiricalTailSqFinSucc_eventually_small_ae_of_iid
      (μ := μ) Y hY hindep hident
  filter_upwards [hmean, htail] with ω hmeanω htailω
  intro t δ hδ
  refine centeredEmpiricalTailSqFinSucc_tendsto_zero_of_empiricalMean_tendsto_tail
    (Y := fun i => Y i ω) (m := ∫ ω, Y 0 ω ∂μ) ?_ htailω t hδ
  refine hmeanω.congr' ?_
  exact Eventually.of_forall fun n => by
    simpa using
      (integral_uniformOn_univ_eq_empiricalMean
        (Y := fun i : Fin (n + 1) => Y i.val ω))

/-- Centered moving empirical square tails vanish almost surely under iid
finite second moments, with the textbook `iIndepFun` premise. -/
theorem centeredEmpiricalTailSqFinSucc_tendsto_ae_of_iIndep
    [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hY : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ, ∀ δ : ℝ, 0 < δ →
      Tendsto
        (fun n : ℕ =>
          centeredEmpiricalTailSqFinSucc (fun i => Y i ω) n
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) δ)
        atTop (𝓝 0) :=
  centeredEmpiricalTailSqFinSucc_tendsto_ae_of_iid
    (μ := μ) Y hY (fun _ _ hij => hindep.indepFun hij) hident

/-- A finite-dimensional dot product is bounded by the `L¹` coefficient norm
times the ambient sup norm. -/
theorem abs_dotProduct_le_l1_mul_norm
    {k : Type*} [Fintype k] (x a : k → ℝ) :
    |x ⬝ᵥ a| ≤ (∑ j : k, |a j|) * ‖x‖ := by
  have hsum_abs :
      |∑ j : k, x j * a j| ≤ ∑ j : k, |x j * a j| :=
    Finset.abs_sum_le_sum_abs (fun j : k => x j * a j) Finset.univ
  have hterm :
      ∑ j : k, |x j * a j| ≤ ∑ j : k, |a j| * ‖x‖ := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    have hxj : |x j| ≤ ‖x‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm x j
    calc
      |x j * a j| = |a j| * |x j| := by rw [abs_mul, mul_comm]
      _ ≤ |a j| * ‖x‖ :=
        mul_le_mul_of_nonneg_left hxj (abs_nonneg (a j))
  calc
    |x ⬝ᵥ a| = |∑ j : k, x j * a j| := by rfl
    _ ≤ ∑ j : k, |x j * a j| := hsum_abs
    _ ≤ ∑ j : k, |a j| * ‖x‖ := hterm
    _ = (∑ j : k, |a j|) * ‖x‖ := by
      rw [Finset.sum_mul]

/-- Fixed uncentered projection tails are dominated by vector norm tails.

The threshold is inflated by the `L¹` coefficient bound `A`; on the projected
tail event, the vector norm must be in the corresponding norm tail, and the
projected square is bounded by `A² ‖Yᵢ‖²`. -/
theorem empiricalTailSqFinSucc_dotProduct_le_const_mul_norm_tail
    {k : Type*} [Fintype k]
    (Y : ℕ → k → ℝ) (n : ℕ) (a : k → ℝ) {R A : ℝ}
    (hA : max 1 (∑ j : k, |a j|) ≤ A) :
    empiricalTailSqFinSucc (fun i => Y i ⬝ᵥ a) n (A * R) ≤
      A ^ 2 * empiricalTailSqFinSucc (fun i => ‖Y i‖) n R := by
  classical
  let P : Measure (Fin (n + 1)) :=
    ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1)))
  have hA_one : 1 ≤ A := (le_max_left _ _).trans hA
  have hA_pos : 0 < A := zero_lt_one.trans_le hA_one
  have hA_nonneg : 0 ≤ A := hA_pos.le
  change
    ∫ i : Fin (n + 1),
        Set.indicator {i : Fin (n + 1) | A * R ≤ |Y i.val ⬝ᵥ a|}
          (fun i => (Y i.val ⬝ᵥ a) ^ 2) i ∂P ≤
      A ^ 2 *
        ∫ i : Fin (n + 1),
          Set.indicator {i : Fin (n + 1) | R ≤ |‖Y i.val‖|}
            (fun i => ‖Y i.val‖ ^ 2) i ∂P
  rw [← integral_const_mul]
  refine integral_mono Integrable.of_finite Integrable.of_finite ?_
  intro i
  by_cases hproj : A * R ≤ |Y i.val ⬝ᵥ a|
  · have hdot_le : |Y i.val ⬝ᵥ a| ≤ A * ‖Y i.val‖ := by
      calc
        |Y i.val ⬝ᵥ a| ≤ (∑ j : k, |a j|) * ‖Y i.val‖ :=
          abs_dotProduct_le_l1_mul_norm (Y i.val) a
        _ ≤ A * ‖Y i.val‖ :=
          mul_le_mul_of_nonneg_right
            ((le_max_right (1 : ℝ) (∑ j : k, |a j|)).trans hA)
            (norm_nonneg _)
    have hnorm_tail : R ≤ ‖Y i.val‖ :=
      le_of_mul_le_mul_left (hproj.trans hdot_le) hA_pos
    have hnorm_tail_abs : R ≤ |‖Y i.val‖| := by
      simpa [abs_of_nonneg (norm_nonneg (Y i.val))] using hnorm_tail
    have hproj_mem :
        i ∈ {i : Fin (n + 1) | A * R ≤ |Y i.val ⬝ᵥ a|} := hproj
    have hnorm_mem :
        i ∈ {i : Fin (n + 1) | R ≤ |‖Y i.val‖|} := hnorm_tail_abs
    rw [Set.indicator_of_mem hproj_mem]
    change (Y i.val ⬝ᵥ a) ^ 2 ≤
      A ^ 2 *
        Set.indicator {i : Fin (n + 1) | R ≤ |‖Y i.val‖|}
          (fun i => ‖Y i.val‖ ^ 2) i
    rw [Set.indicator_of_mem hnorm_mem]
    have hsq :=
      pow_le_pow_left₀ (abs_nonneg (Y i.val ⬝ᵥ a)) hdot_le 2
    simpa [sq_abs, mul_pow] using hsq
  · have hnot :
        i ∉ {i : Fin (n + 1) | A * R ≤ |Y i.val ⬝ᵥ a|} := hproj
    rw [Set.indicator_of_notMem hnot]
    exact mul_nonneg (sq_nonneg A)
      (Set.indicator_nonneg (fun i _ => sq_nonneg ‖Y i.val‖) i)

/-- Pathwise norm-tail control implies pathwise fixed uncentered tail control
for every scalar projection. -/
theorem empiricalTailSqFinSucc_dotProduct_eventually_small_of_norm_tail
    {k : Type*} [Fintype k]
    (Y : ℕ → k → ℝ)
    (hnormTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ᶠ n in atTop, empiricalTailSqFinSucc (fun i => ‖Y i‖) n R ≤ ε)
    (a : k → ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ᶠ n in atTop, empiricalTailSqFinSucc (fun i => Y i ⬝ᵥ a) n R ≤ ε := by
  classical
  intro ε hε
  let A : ℝ := max 1 (∑ j : k, |a j|)
  have hA_one : 1 ≤ A := by
    dsimp [A]
    exact le_max_left _ _
  have hA_pos : 0 < A := zero_lt_one.trans_le hA_one
  let C : ℝ := A ^ 2
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hCden_pos : 0 < C + 1 := by positivity
  let εnorm : ℝ := ε / (C + 1)
  have hεnorm_pos : 0 < εnorm := by
    dsimp [εnorm]
    positivity
  rcases hnormTail εnorm hεnorm_pos with ⟨Rnorm, hRnorm, htailnorm⟩
  refine ⟨A * Rnorm, ?_, ?_⟩
  · have hA_nonneg : 0 ≤ A := zero_le_one.trans hA_one
    have hmul :=
      mul_le_mul hA_one hRnorm (zero_le_one : (0 : ℝ) ≤ 1) hA_nonneg
    simpa using hmul
  · have hC_eps_lt : C * εnorm < ε := by
      have hfrac : C / (C + 1) < 1 := by
        rw [div_lt_one hCden_pos]
        linarith
      have heq : C * εnorm = ε * (C / (C + 1)) := by
        dsimp [εnorm]
        field_simp [hCden_pos.ne']
      rw [heq]
      calc
        ε * (C / (C + 1)) < ε * 1 :=
          mul_lt_mul_of_pos_left hfrac hε
        _ = ε := by ring
    filter_upwards [htailnorm] with n hn
    have hle :=
      empiricalTailSqFinSucc_dotProduct_le_const_mul_norm_tail
        (Y := Y) (n := n) (a := a) (R := Rnorm) (A := A) le_rfl
    have hmul_le : C * empiricalTailSqFinSucc (fun i => ‖Y i‖) n Rnorm ≤
        C * εnorm :=
      mul_le_mul_of_nonneg_left hn hC_nonneg
    exact le_trans hle (le_of_lt (lt_of_le_of_lt hmul_le hC_eps_lt))

/-- Pathwise vector empirical-mean and norm-tail controls imply centered
moving-tail convergence for every scalar projection. -/
theorem centeredEmpiricalTailSqFinSucc_dotProduct_tendsto_zero_of_empiricalMean_tendsto_norm_tail
    {k : Type*} [Fintype k]
    (Y : ℕ → k → ℝ) {m : k → ℝ}
    (hmean :
      Tendsto
        (fun n : ℕ =>
          empiricalMean (fun i : Fin (n + 1) => Y i.val))
        atTop (𝓝 m))
    (hnormTail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ᶠ n in atTop, empiricalTailSqFinSucc (fun i => ‖Y i‖) n R ≤ ε)
    (a : k → ℝ) (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun n : ℕ =>
        centeredEmpiricalTailSqFinSucc (fun i => Y i ⬝ᵥ a) n
          ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) δ)
      atTop (𝓝 0) := by
  have hmean_proj :
      Tendsto
        (fun n : ℕ =>
          empiricalMean (fun i : Fin (n + 1) => Y i.val ⬝ᵥ a))
        atTop (𝓝 (m ⬝ᵥ a)) := by
    have hdot :
        Tendsto
          (fun n : ℕ =>
            empiricalMean (fun i : Fin (n + 1) => Y i.val) ⬝ᵥ a)
          atTop (𝓝 (m ⬝ᵥ a)) :=
      ((continuous_id.dotProduct continuous_const).tendsto m).comp hmean
    refine hdot.congr' ?_
    exact Eventually.of_forall fun n =>
      empiricalMean_dotProduct (Y := fun i : Fin (n + 1) => Y i.val) a
  exact
    centeredEmpiricalTailSqFinSucc_tendsto_zero_of_empiricalMean_tendsto_tail
      (Y := fun i => Y i ⬝ᵥ a) (m := m ⬝ᵥ a) hmean_proj
      (empiricalTailSqFinSucc_dotProduct_eventually_small_of_norm_tail
        (Y := Y) hnormTail a)
      t hδ

/-- Centered projected moving empirical square tails vanish almost surely for
finite-dimensional iid observations with finite second moments.

The proof constructs one pathwise set: coordinate empirical means converge on
that set, and the scalar strong law applied to the vector norm supplies a
single norm-tail control.  The deterministic norm-tail bridge then gives every
projection simultaneously. -/
theorem centeredEmpiricalTailSqFinSucc_dotProduct_tendsto_ae_of_iid
    [IsProbabilityMeasure μ] [Fintype k]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ, ∀ δ : ℝ, 0 < δ →
      Tendsto
        (fun n : ℕ =>
          centeredEmpiricalTailSqFinSucc (fun i => Y i ω ⬝ᵥ a) n
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) δ)
        atTop (𝓝 0) := by
  classical
  have hY0 : MemLp (Y 0) 2 μ := MemLp.of_eval hYmem
  have hnorm_mem : MemLp (fun ω => ‖Y 0 ω‖) 2 μ := by
    have hnorm_aesm : AEStronglyMeasurable (fun ω => ‖Y 0 ω‖) μ :=
      hY0.aestronglyMeasurable.norm
    refine (memLp_two_iff_integrable_sq hnorm_aesm).2 ?_
    exact (memLp_two_iff_integrable_sq_norm hY0.aestronglyMeasurable).1 hY0
  have hnorm_meas : Measurable (fun x : k → ℝ => ‖x‖) :=
    continuous_norm.measurable
  have hindep_norm :
      Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => ‖Y i ω‖) := by
    intro i j hij
    exact IndepFun.comp (hindep hij) hnorm_meas hnorm_meas
  have hident_norm :
      ∀ i, IdentDistrib (fun ω => ‖Y i ω‖) (fun ω => ‖Y 0 ω‖) μ μ := by
    intro i
    exact (hident i).comp hnorm_meas
  have hnorm_tail :
      ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
        ∀ᶠ n in atTop,
          empiricalTailSqFinSucc (fun i => ‖Y i ω‖) n R ≤ ε :=
    empiricalTailSqFinSucc_eventually_small_ae_of_iid
      (μ := μ) (Y := fun i ω => ‖Y i ω‖)
      hnorm_mem hindep_norm hident_norm
  have hmean_coord : ∀ a : k,
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ =>
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω a))
          atTop (𝓝 (∫ ω, Y 0 ω a ∂μ)) := by
    intro a
    let evalA : (k → ℝ) → ℝ := fun y => y a
    have heval : Measurable evalA := by
      dsimp [evalA]
      fun_prop
    have hYint : Integrable (fun ω => Y 0 ω a) μ :=
      memLp_one_iff_integrable.mp ((hYmem a).mono_exponent one_le_two)
    have hindep_a :
        Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => Y i ω a) := by
      intro i j hij
      simpa [evalA] using IndepFun.comp (hindep hij) heval heval
    have hident_a :
        ∀ i, IdentDistrib (fun ω => Y i ω a) (fun ω => Y 0 ω a) μ μ := by
      intro i
      simpa [evalA] using (hident i).comp heval
    have hmean_int :=
      integral_uniformOn_finSucc_tendsto_ae_wlln
        (μ := μ) (X := fun i ω => Y i ω a)
        hYint hindep_a hident_a
    filter_upwards [hmean_int] with ω hω
    refine hω.congr' ?_
    exact Eventually.of_forall fun n => by
      simpa using
        (integral_uniformOn_univ_eq_empiricalMean
          (Y := fun i : Fin (n + 1) => Y i.val ω a))
  have hmean_all : ∀ᵐ ω ∂μ, ∀ a : k,
      Tendsto
        (fun n : ℕ =>
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω a))
        atTop (𝓝 (∫ ω, Y 0 ω a ∂μ)) :=
    ae_all_iff.2 hmean_coord
  filter_upwards [hmean_all, hnorm_tail] with ω hmeanω hnormTailω
  let m : k → ℝ := fun a => ∫ ω, Y 0 ω a ∂μ
  have hmean_vec :
      Tendsto
        (fun n : ℕ =>
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω))
        atTop (𝓝 m) := by
    refine tendsto_pi_nhds.2 ?_
    intro a
    refine (hmeanω a).congr' ?_
    exact Eventually.of_forall fun n => by
      simp [empiricalMean]
  intro a t δ hδ
  exact
    centeredEmpiricalTailSqFinSucc_dotProduct_tendsto_zero_of_empiricalMean_tendsto_norm_tail
      (Y := fun i => Y i ω) (m := m) hmean_vec hnormTailω a t hδ

/-- Centered projected moving empirical square tails vanish almost surely for
finite-dimensional iid observations with finite second moments, using the
textbook `iIndepFun` premise. -/
theorem centeredEmpiricalTailSqFinSucc_dotProduct_tendsto_ae_of_iIndep
    [IsProbabilityMeasure μ] [Fintype k]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ, ∀ δ : ℝ, 0 < δ →
      Tendsto
        (fun n : ℕ =>
          centeredEmpiricalTailSqFinSucc (fun i => Y i ω ⬝ᵥ a) n
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) δ)
        atTop (𝓝 0) :=
  centeredEmpiricalTailSqFinSucc_dotProduct_tendsto_ae_of_iid
    (μ := μ) Y hYmem (fun _ _ hij => hindep.indepFun hij) hident

/-- Empirical scalar variance convergence from empirical first and second
moments.

This is the scalar counterpart of
`covMat_uniformOn_finSucc_tendsto_of_mean_cross_moments`: once the empirical
mean and raw second moment on `Fin (n+1)` converge, the finite empirical
variance converges to the population variance. -/
theorem variance_uniformOn_finSucc_tendsto_of_mean_second_moments
    [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (fun ω => Y 0 ω) 2 μ)
    (hmean :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ i : Fin (n + 1), Y i.val ω
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))))
        atTop (fun _ => ∫ ω, Y 0 ω ∂μ))
    (hsecond :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ i : Fin (n + 1), (Y i.val ω) ^ 2
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))))
        atTop (fun _ => ∫ ω, (Y 0 ω) ^ 2 ∂μ)) :
    TendstoInMeasure μ
      (fun n ω =>
        Var[fun i : Fin (n + 1) => Y i.val ω;
          (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
            Measure (Fin (n + 1)))])
      atTop (fun _ => Var[fun ω => Y 0 ω; μ]) := by
  have hmean_sq :
      TendstoInMeasure μ
        (fun n ω =>
          (∫ i : Fin (n + 1), Y i.val ω
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))) *
            (∫ i : Fin (n + 1), Y i.val ω
              ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                Measure (Fin (n + 1)))))
        atTop (fun _ => (∫ ω, Y 0 ω ∂μ) * (∫ ω, Y 0 ω ∂μ)) :=
    TendstoInMeasure.mul_limits_real hmean hmean
  have hentry :
      TendstoInMeasure μ
        (fun n ω =>
          (∫ i : Fin (n + 1), (Y i.val ω) ^ 2
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))) -
            (∫ i : Fin (n + 1), Y i.val ω
              ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                Measure (Fin (n + 1)))) *
              (∫ i : Fin (n + 1), Y i.val ω
                ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                  Measure (Fin (n + 1)))))
        atTop
        (fun _ =>
          (∫ ω, (Y 0 ω) ^ 2 ∂μ) -
            (∫ ω, Y 0 ω ∂μ) * (∫ ω, Y 0 ω ∂μ)) := by
    have hsecond0 := TendstoInMeasure.sub_limit_zero_real hsecond
    have hmean_sq0 := TendstoInMeasure.sub_limit_zero_real hmean_sq
    have hdiff0 :
        TendstoInMeasure μ
          (fun n ω =>
            (((∫ i : Fin (n + 1), (Y i.val ω) ^ 2
              ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                Measure (Fin (n + 1)))) -
              (∫ i : Fin (n + 1), Y i.val ω
                ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                  Measure (Fin (n + 1)))) *
                (∫ i : Fin (n + 1), Y i.val ω
                  ∂(ProbabilityTheory.uniformOn
                    (Set.univ : Set (Fin (n + 1))) :
                      Measure (Fin (n + 1))))) -
              ((∫ ω, (Y 0 ω) ^ 2 ∂μ) -
                (∫ ω, Y 0 ω ∂μ) * (∫ ω, Y 0 ω ∂μ))))
          atTop (fun _ => 0) := by
      have hsub := TendstoInMeasure.sub_zero_real hsecond0 hmean_sq0
      refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hsub
      exact ae_of_all μ fun ω => by ring
    exact TendstoInMeasure.of_sub_limit_zero_real hdiff0
  have hlimit :
      Var[fun ω => Y 0 ω; μ] =
        (∫ ω, (Y 0 ω) ^ 2 ∂μ) -
          (∫ ω, Y 0 ω ∂μ) * (∫ ω, Y 0 ω ∂μ) := by
    simpa [pow_two] using
      (ProbabilityTheory.variance_eq_sub (μ := μ)
        (X := fun ω => Y 0 ω) hYmem)
  refine TendstoInMeasure.congr
    (f := fun n ω =>
      (∫ i : Fin (n + 1), (Y i.val ω) ^ 2
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1)))) -
        (∫ i : Fin (n + 1), Y i.val ω
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
            Measure (Fin (n + 1)))) *
          (∫ i : Fin (n + 1), Y i.val ω
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))))
    (f' := fun n ω =>
      Var[fun i : Fin (n + 1) => Y i.val ω;
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1)))])
    (g := fun _ : Ω =>
      (∫ ω, (Y 0 ω) ^ 2 ∂μ) -
        (∫ ω, Y 0 ω ∂μ) * (∫ ω, Y 0 ω ∂μ))
    (g' := fun _ : Ω => Var[fun ω => Y 0 ω; μ])
    (fun n => ?_) ?_ hentry
  · exact ae_of_all μ fun ω => by
      let P : Measure (Fin (n + 1)) :=
        ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1)))
      haveI : IsProbabilityMeasure P := inferInstance
      have hYi : MemLp (fun i : Fin (n + 1) => Y i.val ω) 2 P :=
        memLp_two_uniformOn_univ
          (Y := fun i : Fin (n + 1) => Y i.val ω)
      have hsource :
          Var[fun i : Fin (n + 1) => Y i.val ω; P] =
            (∫ i : Fin (n + 1), (Y i.val ω) ^ 2 ∂P) -
              (∫ i : Fin (n + 1), Y i.val ω ∂P) *
                (∫ i : Fin (n + 1), Y i.val ω ∂P) := by
        simpa [pow_two] using
          (ProbabilityTheory.variance_eq_sub (μ := P)
            (X := fun i : Fin (n + 1) => Y i.val ω) hYi)
      simpa [P] using hsource.symm
  · exact ae_of_all μ fun _ => hlimit.symm

/-- Empirical scalar variance convergence for iid real observations. -/
theorem variance_uniformOn_finSucc_tendsto_of_iid
    [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (fun ω => Y 0 ω) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInMeasure μ
      (fun n ω =>
        Var[fun i : Fin (n + 1) => Y i.val ω;
          (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
            Measure (Fin (n + 1)))])
      atTop (fun _ => Var[fun ω => Y 0 ω; μ]) := by
  have hmean :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ i : Fin (n + 1), Y i.val ω
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))))
        atTop (fun _ => ∫ ω, Y 0 ω ∂μ) := by
    have hint : Integrable (fun ω => Y 0 ω) μ :=
      memLp_one_iff_integrable.mp (hYmem.mono_exponent one_le_two)
    exact integral_uniformOn_finSucc_tendstoInMeasure_wlln
      (μ := μ) (X := Y) hint hindep hident
  have hsecond :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ i : Fin (n + 1), (Y i.val ω) ^ 2
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))))
        atTop (fun _ => ∫ ω, (Y 0 ω) ^ 2 ∂μ) := by
    let sqMap : ℝ → ℝ := fun x => x ^ 2
    have hsq_meas : Measurable sqMap := by
      dsimp [sqMap]
      fun_prop
    have hint : Integrable (fun ω => (Y 0 ω) ^ 2) μ := by
      simpa [pow_two] using hYmem.integrable_mul hYmem
    have hindep_sq :
        Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => (Y i ω) ^ 2) := by
      intro i j hij
      simpa [sqMap] using IndepFun.comp (hindep hij) hsq_meas hsq_meas
    have hident_sq :
        ∀ i,
          IdentDistrib
            (fun ω => (Y i ω) ^ 2) (fun ω => (Y 0 ω) ^ 2) μ μ := by
      intro i
      simpa [sqMap] using (hident i).comp hsq_meas
    exact integral_uniformOn_finSucc_tendstoInMeasure_wlln
      (μ := μ) (X := fun i ω => (Y i ω) ^ 2)
      hint hindep_sq hident_sq
  exact variance_uniformOn_finSucc_tendsto_of_mean_second_moments
    (μ := μ) Y hYmem hmean hsecond

/-- Empirical scalar variance convergence for iid real observations with the
textbook `iIndepFun` premise. -/
theorem variance_uniformOn_finSucc_tendsto_of_iIndep
    [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (fun ω => Y 0 ω) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInMeasure μ
      (fun n ω =>
        Var[fun i : Fin (n + 1) => Y i.val ω;
          (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
            Measure (Fin (n + 1)))])
      atTop (fun _ => Var[fun ω => Y 0 ω; μ]) :=
  variance_uniformOn_finSucc_tendsto_of_iid
    (μ := μ) Y hYmem (fun _ _ hij => hindep.indepFun hij) hident

/-- Iid-facing scalar ordinary nonparametric-bootstrap variance constructor.

For the normalized bootstrap mean `sqrt (n+1) (Ybar* - Ybar)`, the conditional
bootstrap variance converges in probability to the population variance. -/
theorem chapter10_indexed_bootstrap_variance_finSucc_resampleMean_tendsto_of_iid
    [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (fun ω => Y 0 ω) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed
        (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
        (fun n _ =>
          ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω))))
      atTop (fun _ => Var[fun ω => Y 0 ω; μ]) :=
  chapter10_indexed_bootstrap_variance_finSucc_resampleMean_tendsto_of_empirical_variance
    (μ := μ) Y
    (variance_uniformOn_finSucc_tendsto_of_iid
      (μ := μ) Y hYmem hindep hident)

/-- Iid-facing scalar ordinary nonparametric-bootstrap variance constructor
with the textbook `iIndepFun` premise. -/
theorem chapter10_indexed_bootstrap_variance_finSucc_resampleMean_tendsto_of_iIndep
    [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (fun ω => Y 0 ω) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed
        (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
        (fun n _ =>
          ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω))))
      atTop (fun _ => Var[fun ω => Y 0 ω; μ]) :=
  chapter10_indexed_bootstrap_variance_finSucc_resampleMean_tendsto_of_iid
    (μ := μ) Y hYmem (fun _ _ hij => hindep.indepFun hij) hident

/-- Empirical covariance convergence from empirical first and cross moments.

This is the finite empirical bridge behind the ordinary-bootstrap CLT path:
once every coordinate mean and cross moment of the empirical distribution on
`Fin (n+1)` converges in probability to its population counterpart, the finite
empirical covariance matrix converges to `covMat μ (Y 0)`. -/
theorem covMat_uniformOn_finSucc_tendsto_of_mean_cross_moments
    [IsProbabilityMeasure μ] [Fintype k]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hmean : ∀ a,
      TendstoInMeasure μ
        (fun n ω =>
          ∫ i : Fin (n + 1), Y i.val ω a
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))))
        atTop (fun _ => ∫ ω, Y 0 ω a ∂μ))
    (hcross : ∀ a b,
      TendstoInMeasure μ
        (fun n ω =>
          ∫ i : Fin (n + 1), Y i.val ω a * Y i.val ω b
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))))
        atTop (fun _ => ∫ ω, Y 0 ω a * Y 0 ω b ∂μ)) :
    TendstoInMeasure μ
      (fun n ω =>
        covMat
          (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
            Measure (Fin (n + 1)))
          (fun i a => Y i.val ω a))
      atTop (fun _ => covMat μ (Y 0)) := by
  refine tendstoInMeasure_pi (fun a => ?_)
  refine tendstoInMeasure_pi (fun b => ?_)
  have hmean_prod :
      TendstoInMeasure μ
        (fun n ω =>
          (∫ i : Fin (n + 1), Y i.val ω a
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))) *
            (∫ i : Fin (n + 1), Y i.val ω b
              ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                Measure (Fin (n + 1)))))
        atTop
        (fun _ =>
          (∫ ω, Y 0 ω a ∂μ) * (∫ ω, Y 0 ω b ∂μ)) :=
    TendstoInMeasure.mul_limits_real (hmean a) (hmean b)
  have hentry :
      TendstoInMeasure μ
        (fun n ω =>
          (∫ i : Fin (n + 1), Y i.val ω a * Y i.val ω b
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))) -
            (∫ i : Fin (n + 1), Y i.val ω a
              ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                Measure (Fin (n + 1)))) *
              (∫ i : Fin (n + 1), Y i.val ω b
                ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                  Measure (Fin (n + 1)))))
        atTop
        (fun _ =>
          (∫ ω, Y 0 ω a * Y 0 ω b ∂μ) -
            (∫ ω, Y 0 ω a ∂μ) * (∫ ω, Y 0 ω b ∂μ)) :=
    by
      have hcross0 := TendstoInMeasure.sub_limit_zero_real (hcross a b)
      have hmean_prod0 := TendstoInMeasure.sub_limit_zero_real hmean_prod
      have hdiff0 :
          TendstoInMeasure μ
            (fun n ω =>
              (((∫ i : Fin (n + 1), Y i.val ω a * Y i.val ω b
                ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                  Measure (Fin (n + 1)))) -
                (∫ i : Fin (n + 1), Y i.val ω a
                  ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                    Measure (Fin (n + 1)))) *
                  (∫ i : Fin (n + 1), Y i.val ω b
                    ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                      Measure (Fin (n + 1))))) -
                ((∫ ω, Y 0 ω a * Y 0 ω b ∂μ) -
                  (∫ ω, Y 0 ω a ∂μ) * (∫ ω, Y 0 ω b ∂μ))))
            atTop (fun _ => 0) := by
        have hsub := TendstoInMeasure.sub_zero_real hcross0 hmean_prod0
        refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl hsub
        exact ae_of_all μ fun ω => by ring
      exact TendstoInMeasure.of_sub_limit_zero_real hdiff0
  have hlimit :
      covMat μ (Y 0) a b =
        (∫ ω, Y 0 ω a * Y 0 ω b ∂μ) -
          (∫ ω, Y 0 ω a ∂μ) * (∫ ω, Y 0 ω b ∂μ) := by
    simpa [covMat, Pi.mul_apply] using
      (ProbabilityTheory.covariance_eq_sub (hYmem a) (hYmem b))
  refine TendstoInMeasure.congr
    (f := fun n ω =>
      (∫ i : Fin (n + 1), Y i.val ω a * Y i.val ω b
        ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1)))) -
        (∫ i : Fin (n + 1), Y i.val ω a
          ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
            Measure (Fin (n + 1)))) *
          (∫ i : Fin (n + 1), Y i.val ω b
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))))
    (f' := fun n ω =>
      covMat
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1)))
        (fun i a => Y i.val ω a) a b)
    (g := fun _ : Ω =>
      (∫ ω, Y 0 ω a * Y 0 ω b ∂μ) -
        (∫ ω, Y 0 ω a ∂μ) * (∫ ω, Y 0 ω b ∂μ))
    (g' := fun _ : Ω => covMat μ (Y 0) a b)
    (fun n => ?_) ?_ hentry
  · exact ae_of_all μ fun ω => by
      let P : Measure (Fin (n + 1)) :=
        ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1)))
      haveI : IsProbabilityMeasure P := inferInstance
      have hYa : MemLp (fun i : Fin (n + 1) => Y i.val ω a) 2 P :=
        memLp_two_uniformOn_univ
          (Y := fun i : Fin (n + 1) => Y i.val ω a)
      have hYb : MemLp (fun i : Fin (n + 1) => Y i.val ω b) 2 P :=
        memLp_two_uniformOn_univ
          (Y := fun i : Fin (n + 1) => Y i.val ω b)
      have hsource :
          covMat P (fun i a => Y i.val ω a) a b =
            (∫ i : Fin (n + 1), Y i.val ω a * Y i.val ω b ∂P) -
              (∫ i : Fin (n + 1), Y i.val ω a ∂P) *
                (∫ i : Fin (n + 1), Y i.val ω b ∂P) := by
        simpa [covMat, Pi.mul_apply] using
          (ProbabilityTheory.covariance_eq_sub hYa hYb)
      simpa [P] using hsource.symm
  · exact ae_of_all μ fun _ => hlimit.symm

/-- Empirical covariance convergence for iid finite-dimensional observations.

This discharges the first- and cross-moment premises of
`covMat_uniformOn_finSucc_tendsto_of_mean_cross_moments` with the shifted
empirical-uniform WLLN.  The finite-second-moment coordinate assumption supplies
integrability of both coordinates and their products by Hölder. -/
theorem covMat_uniformOn_finSucc_tendsto_of_iid
    [IsProbabilityMeasure μ] [Fintype k]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInMeasure μ
      (fun n ω =>
        covMat
          (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
            Measure (Fin (n + 1)))
          (fun i a => Y i.val ω a))
      atTop (fun _ => covMat μ (Y 0)) := by
  have hmean : ∀ a,
      TendstoInMeasure μ
        (fun n ω =>
          ∫ i : Fin (n + 1), Y i.val ω a
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))))
        atTop (fun _ => ∫ ω, Y 0 ω a ∂μ) := by
    intro a
    let evalA : (k → ℝ) → ℝ := fun y => y a
    have heval : Measurable evalA := by
      dsimp [evalA]
      fun_prop
    have hint : Integrable (fun ω => Y 0 ω a) μ :=
      memLp_one_iff_integrable.mp ((hYmem a).mono_exponent one_le_two)
    have hindep_a :
        Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => Y i ω a) := by
      intro i j hij
      simpa [evalA] using IndepFun.comp (hindep hij) heval heval
    have hident_a :
        ∀ i, IdentDistrib (fun ω => Y i ω a) (fun ω => Y 0 ω a) μ μ := by
      intro i
      simpa [evalA] using (hident i).comp heval
    exact integral_uniformOn_finSucc_tendstoInMeasure_wlln
      (μ := μ) (X := fun i ω => Y i ω a) hint hindep_a hident_a
  have hcross : ∀ a b,
      TendstoInMeasure μ
        (fun n ω =>
          ∫ i : Fin (n + 1), Y i.val ω a * Y i.val ω b
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))))
        atTop (fun _ => ∫ ω, Y 0 ω a * Y 0 ω b ∂μ) := by
    intro a b
    let crossAB : (k → ℝ) → ℝ := fun y => y a * y b
    have hcross_meas : Measurable crossAB := by
      dsimp [crossAB]
      fun_prop
    have hint : Integrable (fun ω => Y 0 ω a * Y 0 ω b) μ :=
      (hYmem a).integrable_mul (hYmem b)
    have hindep_ab :
        Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => Y i ω a * Y i ω b) := by
      intro i j hij
      simpa [crossAB] using IndepFun.comp (hindep hij) hcross_meas hcross_meas
    have hident_ab :
        ∀ i,
          IdentDistrib
            (fun ω => Y i ω a * Y i ω b)
            (fun ω => Y 0 ω a * Y 0 ω b) μ μ := by
      intro i
      simpa [crossAB] using (hident i).comp hcross_meas
    exact integral_uniformOn_finSucc_tendstoInMeasure_wlln
      (μ := μ) (X := fun i ω => Y i ω a * Y i ω b)
      hint hindep_ab hident_ab
  exact covMat_uniformOn_finSucc_tendsto_of_mean_cross_moments
    (μ := μ) Y hYmem hmean hcross

/-- Empirical covariance convergence for iid finite-dimensional observations,
with the textbook `iIndepFun` premise. -/
theorem covMat_uniformOn_finSucc_tendsto_of_iIndep
    [IsProbabilityMeasure μ] [Fintype k]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInMeasure μ
      (fun n ω =>
        covMat
          (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
            Measure (Fin (n + 1)))
          (fun i a => Y i.val ω a))
      atTop (fun _ => covMat μ (Y 0)) :=
  covMat_uniformOn_finSucc_tendsto_of_iid
    (μ := μ) Y hYmem (fun _ _ hij => hindep.indepFun hij) hident

/-- Pathwise empirical covariance convergence from pathwise empirical first and
cross moments.

This is the almost-sure counterpart of
`covMat_uniformOn_finSucc_tendsto_of_mean_cross_moments`, used by the
characteristic-function proof of Hansen Theorem 10.4. -/
theorem covMat_uniformOn_finSucc_tendsto_ae_of_mean_cross_moments
    [IsProbabilityMeasure μ] [Countable k]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hmean : ∀ a,
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ =>
            ∫ i : Fin (n + 1), Y i.val ω a
              ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                Measure (Fin (n + 1))))
          atTop (𝓝 (∫ ω, Y 0 ω a ∂μ)))
    (hcross : ∀ a b,
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ =>
            ∫ i : Fin (n + 1), Y i.val ω a * Y i.val ω b
              ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                Measure (Fin (n + 1))))
          atTop (𝓝 (∫ ω, Y 0 ω a * Y 0 ω b ∂μ))) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          covMat
            (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))
            (fun i a => Y i.val ω a))
        atTop (𝓝 (covMat μ (Y 0))) := by
  have hmean_all :
      ∀ᵐ ω ∂μ, ∀ a,
        Tendsto
          (fun n : ℕ =>
            ∫ i : Fin (n + 1), Y i.val ω a
              ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                Measure (Fin (n + 1))))
          atTop (𝓝 (∫ ω, Y 0 ω a ∂μ)) :=
    ae_all_iff.2 hmean
  have hcross_all :
      ∀ᵐ ω ∂μ, ∀ a b,
        Tendsto
          (fun n : ℕ =>
            ∫ i : Fin (n + 1), Y i.val ω a * Y i.val ω b
              ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                Measure (Fin (n + 1))))
          atTop (𝓝 (∫ ω, Y 0 ω a * Y 0 ω b ∂μ)) := by
    exact ae_all_iff.2 fun a => ae_all_iff.2 fun b => hcross a b
  filter_upwards [hmean_all, hcross_all] with ω hmeanω hcrossω
  refine tendsto_pi_nhds.2 fun a => ?_
  refine tendsto_pi_nhds.2 fun b => ?_
  have hmean_prod :
      Tendsto
        (fun n : ℕ =>
          (∫ i : Fin (n + 1), Y i.val ω a
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))) *
            (∫ i : Fin (n + 1), Y i.val ω b
              ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                Measure (Fin (n + 1)))))
        atTop
        (𝓝 ((∫ ω, Y 0 ω a ∂μ) * (∫ ω, Y 0 ω b ∂μ))) :=
    (hmeanω a).mul (hmeanω b)
  have hentry :
      Tendsto
        (fun n : ℕ =>
          (∫ i : Fin (n + 1), Y i.val ω a * Y i.val ω b
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))) -
            (∫ i : Fin (n + 1), Y i.val ω a
              ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                Measure (Fin (n + 1)))) *
              (∫ i : Fin (n + 1), Y i.val ω b
                ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                  Measure (Fin (n + 1)))))
        atTop
        (𝓝 ((∫ ω, Y 0 ω a * Y 0 ω b ∂μ) -
          (∫ ω, Y 0 ω a ∂μ) * (∫ ω, Y 0 ω b ∂μ))) :=
    (hcrossω a b).sub hmean_prod
  have hlimit :
      covMat μ (Y 0) a b =
        (∫ ω, Y 0 ω a * Y 0 ω b ∂μ) -
          (∫ ω, Y 0 ω a ∂μ) * (∫ ω, Y 0 ω b ∂μ) := by
    simpa [covMat, Pi.mul_apply] using
      (ProbabilityTheory.covariance_eq_sub (hYmem a) (hYmem b))
  rw [hlimit]
  refine hentry.congr' ?_
  exact Eventually.of_forall fun n => by
    let P : Measure (Fin (n + 1)) :=
      ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1)))
    haveI : IsProbabilityMeasure P := inferInstance
    have hYa : MemLp (fun i : Fin (n + 1) => Y i.val ω a) 2 P :=
      memLp_two_uniformOn_univ
        (Y := fun i : Fin (n + 1) => Y i.val ω a)
    have hYb : MemLp (fun i : Fin (n + 1) => Y i.val ω b) 2 P :=
      memLp_two_uniformOn_univ
        (Y := fun i : Fin (n + 1) => Y i.val ω b)
    have hsource :
        covMat P (fun i a => Y i.val ω a) a b =
          (∫ i : Fin (n + 1), Y i.val ω a * Y i.val ω b ∂P) -
            (∫ i : Fin (n + 1), Y i.val ω a ∂P) *
              (∫ i : Fin (n + 1), Y i.val ω b ∂P) := by
      simpa [covMat, Pi.mul_apply] using
        (ProbabilityTheory.covariance_eq_sub hYa hYb)
    simpa [P] using hsource.symm

/-- Pathwise empirical covariance convergence for iid finite-dimensional
observations.

The finite-second-moment coordinate assumption supplies integrability of both
coordinates and cross products; the pathwise shifted empirical-uniform strong
law supplies the coordinate mean and cross-moment limits. -/
theorem covMat_uniformOn_finSucc_tendsto_ae_of_iid
    [IsProbabilityMeasure μ] [Countable k]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          covMat
            (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))
            (fun i a => Y i.val ω a))
        atTop (𝓝 (covMat μ (Y 0))) := by
  have hmean : ∀ a,
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ =>
            ∫ i : Fin (n + 1), Y i.val ω a
              ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                Measure (Fin (n + 1))))
          atTop (𝓝 (∫ ω, Y 0 ω a ∂μ)) := by
    intro a
    let evalA : (k → ℝ) → ℝ := fun y => y a
    have heval : Measurable evalA := by
      dsimp [evalA]
      fun_prop
    have hint : Integrable (fun ω => Y 0 ω a) μ :=
      memLp_one_iff_integrable.mp ((hYmem a).mono_exponent one_le_two)
    have hindep_a :
        Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => Y i ω a) := by
      intro i j hij
      simpa [evalA] using IndepFun.comp (hindep hij) heval heval
    have hident_a :
        ∀ i, IdentDistrib (fun ω => Y i ω a) (fun ω => Y 0 ω a) μ μ := by
      intro i
      simpa [evalA] using (hident i).comp heval
    exact integral_uniformOn_finSucc_tendsto_ae_wlln
      (μ := μ) (X := fun i ω => Y i ω a) hint hindep_a hident_a
  have hcross : ∀ a b,
      ∀ᵐ ω ∂μ,
        Tendsto
          (fun n : ℕ =>
            ∫ i : Fin (n + 1), Y i.val ω a * Y i.val ω b
              ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
                Measure (Fin (n + 1))))
          atTop (𝓝 (∫ ω, Y 0 ω a * Y 0 ω b ∂μ)) := by
    intro a b
    let crossAB : (k → ℝ) → ℝ := fun y => y a * y b
    have hcross_meas : Measurable crossAB := by
      dsimp [crossAB]
      fun_prop
    have hint : Integrable (fun ω => Y 0 ω a * Y 0 ω b) μ :=
      (hYmem a).integrable_mul (hYmem b)
    have hindep_ab :
        Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω => Y i ω a * Y i ω b) := by
      intro i j hij
      simpa [crossAB] using IndepFun.comp (hindep hij) hcross_meas hcross_meas
    have hident_ab :
        ∀ i,
          IdentDistrib
            (fun ω => Y i ω a * Y i ω b)
            (fun ω => Y 0 ω a * Y 0 ω b) μ μ := by
      intro i
      simpa [crossAB] using (hident i).comp hcross_meas
    exact integral_uniformOn_finSucc_tendsto_ae_wlln
      (μ := μ) (X := fun i ω => Y i ω a * Y i ω b)
      hint hindep_ab hident_ab
  exact covMat_uniformOn_finSucc_tendsto_ae_of_mean_cross_moments
    (μ := μ) Y hYmem hmean hcross

/-- Pathwise empirical covariance convergence for iid finite-dimensional
observations with the textbook `iIndepFun` premise. -/
theorem covMat_uniformOn_finSucc_tendsto_ae_of_iIndep
    [IsProbabilityMeasure μ] [Countable k]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          covMat
            (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))
            (fun i a => Y i.val ω a))
        atTop (𝓝 (covMat μ (Y 0))) :=
  covMat_uniformOn_finSucc_tendsto_ae_of_iid
    (μ := μ) Y hYmem (fun _ _ hij => hindep.indepFun hij) hident

/-- Iid-facing ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian
CLT through the covariance-matrix characteristic-function remainder route.

The iid finite-second-moment assumptions supply pathwise empirical covariance
convergence via `covMat_uniformOn_finSucc_tendsto_ae_of_iid`; the remaining
analytic input is the explicit diagonal characteristic-function Taylor
remainder. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_iid_covMat_remainder
    [Fintype k] [DecidableEq k] [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hrem : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ,
      ((fun n : ℕ =>
          centeredEmpiricalCharFunFinSucc (fun i => Y i ω ⬝ᵥ a) n
              ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) -
            (1 +
              scalarGaussianCharFunExponent t
                  (empiricalVarianceFinSucc (fun i => Y i ω ⬝ᵥ a) n) *
                complexInvNatSucc n)) =o[atTop]
        (fun n : ℕ => complexInvNatSucc n)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) (covMat μ (Y 0)))
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian
            (0 : EuclideanSpace ℝ k) (covMat μ (Y 0))).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (covMat μ (Y 0)))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  have hY0 : MemLp (Y 0) 2 μ := MemLp.of_eval hYmem
  have hYae : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ := by
    intro i a
    let evalA : (k → ℝ) → ℝ := fun y => y a
    have heval : Measurable evalA := by
      dsimp [evalA]
      fun_prop
    have hcoord :
        IdentDistrib (fun ω => Y i ω a) (fun ω => Y 0 ω a) μ μ := by
      simpa [evalA] using (hident i).comp heval
    exact hcoord.aemeasurable_fst
  exact
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_covMat_remainder
      (μ := μ) (Y := Y) (S := covMat μ (Y 0))
      (covMat_posSemidef (μ := μ) hY0) hYae
      (covMat_uniformOn_finSucc_tendsto_ae_of_iid
        (μ := μ) Y hYmem hindep hident)
      hrem hfrontier

/-- Positive-definite iid-facing ordinary nonparametric-bootstrap Hansen
Theorem 10.4 Gaussian CLT through the covariance-matrix
characteristic-function remainder route. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_iid_covMat_remainder_posDef
    [Fintype k] [DecidableEq k] [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hS : (covMat μ (Y 0)).PosDef)
    (hrem : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ,
      ((fun n : ℕ =>
          centeredEmpiricalCharFunFinSucc (fun i => Y i ω ⬝ᵥ a) n
              ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) -
            (1 +
              scalarGaussianCharFunExponent t
                  (empiricalVarianceFinSucc (fun i => Y i ω ⬝ᵥ a) n) *
                complexInvNatSucc n)) =o[atTop]
        (fun n : ℕ => complexInvNatSucc n))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (covMat μ (Y 0)))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_iid_covMat_remainder
    (μ := μ) Y hYmem hindep hident hrem
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Iid-facing ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian
CLT through the covariance-matrix characteristic-function remainder route, with
the textbook `iIndepFun` premise. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_iIndep_covMat_remainder
    [Fintype k] [DecidableEq k] [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hrem : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ,
      ((fun n : ℕ =>
          centeredEmpiricalCharFunFinSucc (fun i => Y i ω ⬝ᵥ a) n
              ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) -
            (1 +
              scalarGaussianCharFunExponent t
                  (empiricalVarianceFinSucc (fun i => Y i ω ⬝ᵥ a) n) *
                complexInvNatSucc n)) =o[atTop]
        (fun n : ℕ => complexInvNatSucc n)))
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) (covMat μ (Y 0)))
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian
            (0 : EuclideanSpace ℝ k) (covMat μ (Y 0))).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (covMat μ (Y 0)))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_iid_covMat_remainder
    (μ := μ) Y hYmem (fun _ _ hij => hindep.indepFun hij) hident hrem hfrontier

/-- Positive-definite iid-facing ordinary nonparametric-bootstrap Hansen
Theorem 10.4 Gaussian CLT through the covariance-matrix
characteristic-function remainder route, with the textbook `iIndepFun`
premise. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_iIndep_covMat_remainder_posDef
    [Fintype k] [DecidableEq k] [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hS : (covMat μ (Y 0)).PosDef)
    (hrem : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ,
      ((fun n : ℕ =>
          centeredEmpiricalCharFunFinSucc (fun i => Y i ω ⬝ᵥ a) n
              ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) -
            (1 +
              scalarGaussianCharFunExponent t
                  (empiricalVarianceFinSucc (fun i => Y i ω ⬝ᵥ a) n) *
                complexInvNatSucc n)) =o[atTop]
        (fun n : ℕ => complexInvNatSucc n))) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (covMat μ (Y 0)))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_iid_covMat_remainder_posDef
    (μ := μ) Y hYmem (fun _ _ hij => hindep.indepFun hij) hident hS hrem

/-- Iid-facing ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian
CLT through the covariance-matrix centered-tail route.

The iid finite-second-moment assumptions supply both pathwise empirical
covariance convergence and the centered projected Lindeberg tails, leaving only
the Gaussian frontier condition for possibly singular covariance matrices. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_iid_covMat_tail
    [Fintype k] [DecidableEq k] [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) (covMat μ (Y 0)))
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian
            (0 : EuclideanSpace ℝ k) (covMat μ (Y 0))).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (covMat μ (Y 0)))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  have hY0 : MemLp (Y 0) 2 μ := MemLp.of_eval hYmem
  have hYae : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ := by
    intro i a
    let evalA : (k → ℝ) → ℝ := fun y => y a
    have heval : Measurable evalA := by
      dsimp [evalA]
      fun_prop
    have hcoord :
        IdentDistrib (fun ω => Y i ω a) (fun ω => Y 0 ω a) μ μ := by
      simpa [evalA] using (hident i).comp heval
    exact hcoord.aemeasurable_fst
  exact
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_covMat_tail
      (μ := μ) (Y := Y) (S := covMat μ (Y 0))
      (covMat_posSemidef (μ := μ) hY0) hYae
      (covMat_uniformOn_finSucc_tendsto_ae_of_iid
        (μ := μ) Y hYmem hindep hident)
      (centeredEmpiricalTailSqFinSucc_dotProduct_tendsto_ae_of_iid
        (μ := μ) Y hYmem hindep hident)
      hfrontier

/-- Positive-definite iid-facing ordinary nonparametric-bootstrap Hansen
Theorem 10.4 Gaussian CLT through the covariance-matrix centered-tail route. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_iid_covMat_tail_posDef
    [Fintype k] [DecidableEq k] [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hS : (covMat μ (Y 0)).PosDef) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (covMat μ (Y 0)))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_iid_covMat_tail
    (μ := μ) Y hYmem hindep hident
    (fun x _hx => multivariateGaussian_coordinateLE_frontier_null_of_posDef hS x)

/-- Iid-facing ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian
CLT through the covariance-matrix centered-tail route, with the textbook
`iIndepFun` premise. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_iIndep_covMat_tail
    [Fintype k] [DecidableEq k] [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hfrontier : ∀ x : k → ℝ,
      ContinuousAt
          (fun y =>
            vectorCDF
              (multivariateGaussian (0 : EuclideanSpace ℝ k) (covMat μ (Y 0)))
              (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) y) x →
        ((multivariateGaussian
            (0 : EuclideanSpace ℝ k) (covMat μ (Y 0))).map
            (fun z : EuclideanSpace ℝ k => (z : k → ℝ)))
          (frontier {z : k → ℝ | coordinateLE z x}) = 0) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (covMat μ (Y 0)))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_iid_covMat_tail
    (μ := μ) Y hYmem (fun _ _ hij => hindep.indepFun hij) hident hfrontier

/-- Positive-definite iid-facing ordinary nonparametric-bootstrap Hansen
Theorem 10.4 Gaussian CLT through the covariance-matrix centered-tail route,
with the textbook `iIndepFun` premise. -/
theorem
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_iIndep_covMat_tail_posDef
    [Fintype k] [DecidableEq k] [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hS : (covMat μ (Y 0)).PosDef) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (covMat μ (Y 0)))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) :=
  chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_iid_covMat_tail_posDef
    (μ := μ) Y hYmem (fun _ _ hij => hindep.indepFun hij) hident hS

/-- Weak ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian CLT from
almost-sure characteristic-function convergence for projected bootstrap means.

This is the bounded-continuous-test-function version of
`chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_ae_charFun`;
it is the reusable input for continuous mappings such as absolute values. -/
theorem
    chapter10_indexed_bootstrap_weak_clt_gaussian_finSucc_resampleMean_of_ae_charFun
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hchar : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ,
      Tendsto
        (fun n =>
          charFun
            ((ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1))).map
              (fun ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a))))
            t)
        atTop
        (𝓝 (charFun
          ((multivariateGaussian 0 S).map
            (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a))
          t))) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  letI : ∀ n, Ω → IsProbabilityMeasure
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))) := fun n _ => by
    infer_instance
  have hmeas :
      ∀ f : BoundedContinuousFunction (k → ℝ) ℝ, ∀ n,
        AEStronglyMeasurable
          (fun ω =>
            bootstrapBoundedContinuousIntegralIndexed
              (fun n _ =>
                (ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                    Measure (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs a =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs a -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
              f n ω) μ :=
    bootstrapBoundedContinuousIntegralIndexed_normalized_finSucc_resampleMean_aestronglyMeasurable
      (μ := μ) (Y := Y) hY
  refine
    TendstoInBootstrapWeakDistributionIndexed.of_ae_tendstoInDistribution
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Zstar := fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (Z := fun z : EuclideanSpace ℝ k => (z : k → ℝ))
      hmeas ?_
  refine hchar.mono ?_
  intro ω hω
  have hclt :
      MultivariateIndexedLindebergCLTConditions
        (fun n => Fin (n + 1) → Fin (n + 1))
        (fun n =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
        S := by
    refine
      { aemeasurable := fun n =>
          (normalized_finSucc_resampleMean_sub_empiricalMean_measurable
            (Y := Y) n ω).aemeasurable
        projection_clt := ?_ }
    intro a
    have hscalar :
        TendstoInDistribution
          (fun n (ωs : Fin (n + 1) → Fin (n + 1)) =>
            Real.sqrt (n + 1 : ℝ) *
              (empiricalBootstrapResampleMean
                  (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a)
                  (fun ωs t => ωs t) ωs -
                empiricalMean (fun i : Fin (n + 1) => Y i.val ω ⬝ᵥ a)))
          atTop
          (fun z : EuclideanSpace ℝ k => z.ofLp ⬝ᵥ a)
          (fun n =>
            (ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1))))
          (multivariateGaussian 0 S) := by
      refine TendstoInDistribution.of_tendsto_charFun_indexed ?_ ?_ (hω a)
      · intro n
        have hvec : AEMeasurable
            (fun ωs : Fin (n + 1) → Fin (n + 1) => fun b =>
              Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs b -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω) b))
            (ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1))) :=
          (normalized_finSucc_resampleMean_sub_empiricalMean_measurable
            (Y := Y) n ω).aemeasurable
        have hdot : AEMeasurable
            (fun ωs : Fin (n + 1) → Fin (n + 1) =>
              (fun b =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs b -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω) b)) ⬝ᵥ a)
            (ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1))) :=
          ((continuous_id.dotProduct continuous_const).measurable.comp_aemeasurable hvec)
        exact hdot.congr
          (ae_of_all
            (ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
                Measure (Fin (n + 1) → Fin (n + 1))) fun ωs =>
            dotProduct_normalized_finSucc_resampleMean_sub_empiricalMean_eq
              (Y := Y) n ω ωs a)
      · exact ((continuous_id.dotProduct continuous_const).measurable.comp_aemeasurable
          ((PiLp.continuous_ofLp 2 (fun _ : k => ℝ)).measurable.aemeasurable))
    refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hscalar
    intro n
    exact ae_of_all
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))) (fun ωs =>
        (dotProduct_normalized_finSucc_resampleMean_sub_empiricalMean_eq
          (Y := Y) n ω ωs a).symm)
  have hEuclid := multivariateIndexedLindebergCLT_tendstoInDistribution hclt
  have hMap := TendstoInDistribution.continuous_comp
    (g := (WithLp.ofLp : EuclideanSpace ℝ k → k → ℝ))
    (PiLp.continuous_ofLp 2 (fun _ : k => ℝ)) hEuclid
  simpa [Function.comp_def] using hMap

/-- Weak ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian CLT from
almost-sure empirical variance convergence and centered Lindeberg tails. -/
theorem
    chapter10_indexed_bootstrap_weak_clt_gaussian_finSucc_resampleMean_of_ae_charFun_tail
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hS : S.PosSemidef)
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hvar : ∀ᵐ ω ∂μ, ∀ a : k → ℝ,
      Tendsto
        (fun n : ℕ =>
          empiricalVarianceFinSucc (fun i => Y i ω ⬝ᵥ a) n)
        atTop (𝓝 (a ⬝ᵥ (S *ᵥ a))))
    (htail : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ, ∀ δ : ℝ, 0 < δ →
      Tendsto
        (fun n : ℕ =>
          centeredEmpiricalTailSqFinSucc (fun i => Y i ω ⬝ᵥ a) n
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) δ)
        atTop (𝓝 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  refine
    chapter10_indexed_bootstrap_weak_clt_gaussian_finSucc_resampleMean_of_ae_charFun
      (μ := μ) (Y := Y) (S := S) hY ?_
  filter_upwards [hvar, htail] with ω hvarω htailω
  intro a t
  have hrem :=
    centeredEmpiricalCharFunFinSucc_remainder_isLittleO_of_variance_tendsto_tail
      (Y := fun i => Y i ω ⬝ᵥ a) (hvarω a) t (htailω a t)
  have hchar :=
    charFun_normalized_finSucc_resampleMean_sub_empiricalMean_tendsto_of_variance_tendsto
      (Y := fun i ω => Y i ω ⬝ᵥ a) (ω := ω)
      (σ2 := a ⬝ᵥ (S *ᵥ a)) (hvarω a) t hrem
  simpa [charFun_map_multivariateGaussian_zero_dotProduct_eq_exp hS a t] using hchar

/-- Weak ordinary nonparametric-bootstrap Hansen Theorem 10.4 Gaussian CLT from
almost-sure empirical covariance convergence and centered Lindeberg tails. -/
theorem
    chapter10_indexed_bootstrap_weak_clt_gaussian_finSucc_resampleMean_of_ae_covMat_tail
    [Fintype k] [DecidableEq k] [IsFiniteMeasure μ]
    {Y : ℕ → Ω → k → ℝ} {S : Matrix k k ℝ}
    (hS : S.PosSemidef)
    (hY : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ)
    (hcov : ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ =>
          covMat
            (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1)))
            (fun i a => Y i.val ω a))
        atTop (𝓝 S))
    (htail : ∀ᵐ ω ∂μ, ∀ a : k → ℝ, ∀ t : ℝ, ∀ δ : ℝ, 0 < δ →
      Tendsto
        (fun n : ℕ =>
          centeredEmpiricalTailSqFinSucc (fun i => Y i ω ⬝ᵥ a) n
            ((Real.sqrt (n + 1 : ℝ))⁻¹ * t) δ)
        atTop (𝓝 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) S)
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  refine
    chapter10_indexed_bootstrap_weak_clt_gaussian_finSucc_resampleMean_of_ae_charFun_tail
      (μ := μ) (Y := Y) (S := S) hS hY ?_ htail
  filter_upwards [hcov] with ω hcovω
  intro a
  exact empiricalVarianceFinSucc_dotProduct_tendsto_of_covMat_tendsto
    (Y := fun i a => Y i ω a) hcovω a

/-- Weak positive-definite iid-facing ordinary nonparametric-bootstrap Hansen
Theorem 10.4 Gaussian CLT through the covariance-tail route, with the textbook
`iIndepFun` premise. -/
theorem
    chapter10_indexed_bootstrap_weak_clt_gaussian_finSucc_resampleMean_of_iIndep_covMat_tail_posDef
    [Fintype k] [DecidableEq k] [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hS : (covMat μ (Y 0)).PosDef) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
      (multivariateGaussian (0 : EuclideanSpace ℝ k) (covMat μ (Y 0)))
      (fun z : EuclideanSpace ℝ k => (z : k → ℝ)) := by
  have hYae : ∀ i a, AEMeasurable (fun ω => Y i ω a) μ := by
    intro i a
    let evalA : (k → ℝ) → ℝ := fun y => y a
    have heval : Measurable evalA := by
      dsimp [evalA]
      fun_prop
    have hcoord :
        IdentDistrib (fun ω => Y i ω a) (fun ω => Y 0 ω a) μ μ := by
      simpa [evalA] using (hident i).comp heval
    exact hcoord.aemeasurable_fst
  exact
    chapter10_indexed_bootstrap_weak_clt_gaussian_finSucc_resampleMean_of_ae_covMat_tail
      (μ := μ) (Y := Y) (S := covMat μ (Y 0))
      hS.posSemidef hYae
      (covMat_uniformOn_finSucc_tendsto_ae_of_iIndep
        (μ := μ) Y hYmem hindep hident)
      (centeredEmpiricalTailSqFinSucc_dotProduct_tendsto_ae_of_iIndep
        (μ := μ) Y hYmem hindep hident)

/-- Weak scalar `Unit`-coordinate ordinary nonparametric-bootstrap Hansen
Theorem 10.4 Gaussian CLT through the iid covariance-tail route.

This bounded-continuous-test-function face feeds continuous transformations of
the concrete scalar `Fin (n+1)` resample-mean statistic, such as the absolute
value used by two-sided bootstrap critical values. -/
theorem
    chapter10_indexed_bootstrap_weak_clt_scalar_finSucc_resampleMean_of_iIndep_tail_posDef
    [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hS : (covMat μ (fun ω (_ : Unit) => Y 0 ω)).PosDef) :
    TendstoInBootstrapWeakDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
      (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (covMat μ (fun ω (_ : Unit) => Y 0 ω)))
      (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) := by
  let Yunit : ℕ → Ω → Unit → ℝ := fun i ω _ => Y i ω
  have hYmemUnit : ∀ a : Unit, MemLp (fun ω => Yunit 0 ω a) 2 μ := by
    intro a
    simpa [Yunit] using hYmem
  let embed : ℝ → Unit → ℝ := fun x _ => x
  have hembed : Measurable embed := by
    dsimp [embed]
    fun_prop
  have hindepUnit : iIndepFun Yunit μ := by
    simpa [Yunit, embed] using
      hindep.comp (fun _ x => embed x) (fun _ => hembed)
  have hidentUnit : ∀ i, IdentDistrib (Yunit i) (Yunit 0) μ μ := by
    intro i
    simpa [Yunit, embed] using (hident i).comp hembed
  have hSUnit : (covMat μ (Yunit 0)).PosDef := by
    simpa [Yunit] using hS
  have hvec :
      TendstoInBootstrapWeakDistributionIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Yunit i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Yunit i.val ω) a))
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit) (covMat μ (Yunit 0)))
        (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) :=
    chapter10_indexed_bootstrap_weak_clt_gaussian_finSucc_resampleMean_of_iIndep_covMat_tail_posDef
      (μ := μ) Yunit hYmemUnit hindepUnit hidentUnit hSUnit
  have hcoord :
      TendstoInBootstrapWeakDistributionIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs =>
          (fun a =>
            Real.sqrt (n + 1 : ℝ) *
              (empiricalBootstrapResampleMean
                  (fun i : Fin (n + 1) => Yunit i.val ω)
                  (fun ωs t => ωs t) ωs a -
                empiricalMean (fun i : Fin (n + 1) => Yunit i.val ω) a)) ())
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit) (covMat μ (Yunit 0)))
        (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Zstar := fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Yunit i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Yunit i.val ω) a))
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ Unit) (covMat μ (Yunit 0)))
      (Z := fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ))
      (g := fun z : Unit → ℝ => z ()) hvec (continuous_apply ())
  have hscalar :
      TendstoInBootstrapWeakDistributionIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit) (covMat μ (Yunit 0)))
        (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ) ()) := by
    refine hcoord.congr ?_ ?_
    · intro n ω ωs
      simp [Yunit, empiricalBootstrapResampleMean, empiricalMean]
    · intro z
      rfl
  simpa [Yunit] using hscalar

/-- Scalar `Unit`-coordinate ordinary nonparametric-bootstrap Hansen Theorem
10.4 Gaussian CLT through the iid covariance-tail route.

This is the one-dimensional face used by scalar percentile and critical-value
constructors: the bootstrap statistic is the concrete normalized
`Fin (n+1) -> Fin (n+1)` resample mean, while the limiting probability space is
the corresponding one-coordinate multivariate Gaussian. -/
theorem
    chapter10_indexed_bootstrap_clt_scalar_finSucc_resampleMean_of_iIndep_tail_posDef
    [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (Y 0) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hS : (covMat μ (fun ω (_ : Unit) => Y 0 ω)).PosDef) :
    TendstoInBootstrapDistributionIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs (_ : Unit) =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
      (multivariateGaussian (0 : EuclideanSpace ℝ Unit)
        (covMat μ (fun ω (_ : Unit) => Y 0 ω)))
      (fun z : EuclideanSpace ℝ Unit => fun _ : Unit => (z : Unit → ℝ) ()) := by
  let Yunit : ℕ → Ω → Unit → ℝ := fun i ω _ => Y i ω
  have hYmemUnit : ∀ a : Unit, MemLp (fun ω => Yunit 0 ω a) 2 μ := by
    intro a
    simpa [Yunit] using hYmem
  let embed : ℝ → Unit → ℝ := fun x _ => x
  have hembed : Measurable embed := by
    dsimp [embed]
    fun_prop
  have hindepUnit : iIndepFun Yunit μ := by
    simpa [Yunit, embed] using
      hindep.comp (fun _ x => embed x) (fun _ => hembed)
  have hidentUnit : ∀ i, IdentDistrib (Yunit i) (Yunit 0) μ μ := by
    intro i
    simpa [Yunit, embed] using (hident i).comp hembed
  have hSUnit : (covMat μ (Yunit 0)).PosDef := by
    simpa [Yunit] using hS
  have hvec :
      TendstoInBootstrapDistributionIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Yunit i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Yunit i.val ω) a))
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit) (covMat μ (Yunit 0)))
        (fun z : EuclideanSpace ℝ Unit => (z : Unit → ℝ)) :=
    chapter10_indexed_bootstrap_clt_gaussian_finSucc_resampleMean_of_iIndep_covMat_tail_posDef
      (μ := μ) Yunit hYmemUnit hindepUnit hidentUnit hSUnit
  have hscalar :
      TendstoInBootstrapDistributionIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs (_ : Unit) =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
        (multivariateGaussian (0 : EuclideanSpace ℝ Unit) (covMat μ (Yunit 0)))
        (fun z : EuclideanSpace ℝ Unit => fun _ : Unit => (z : Unit → ℝ) ()) := by
    refine hvec.congr ?_ ?_
    · intro n ω ωs
      funext u
      simp [Yunit, empiricalBootstrapResampleMean, empiricalMean]
    · intro z
      funext u
      simp [Subsingleton.elim u ()]
  simpa [Yunit] using hscalar

/-- Indexed normalized ordinary-bootstrap cross moments converge once the
finite empirical one-draw covariance converges through first and cross moments.

The exact finite identity proved above reduces the conditional raw cross
moment matrix of `sqrt (n+1) (Ybar* - Ybar)` to the empirical covariance
matrix, so this theorem packages the remaining moment-convergence bridge. -/
theorem
    bootstrapCrossMomentMatIndexed_normalized_finSucc_tendsto_of_mean_cross_moments
    [IsProbabilityMeasure μ] [Fintype k]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hmean : ∀ a,
      TendstoInMeasure μ
        (fun n ω =>
          ∫ i : Fin (n + 1), Y i.val ω a
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))))
        atTop (fun _ => ∫ ω, Y 0 ω a ∂μ))
    (hcross : ∀ a b,
      TendstoInMeasure μ
        (fun n ω =>
          ∫ i : Fin (n + 1), Y i.val ω a * Y i.val ω b
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))))
        atTop (fun _ => ∫ ω, Y 0 ω a * Y 0 ω b ∂μ)) :
    TendstoInMeasure μ
      (bootstrapCrossMomentMatIndexed
        (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
        (fun n _ =>
          ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a)))
      atTop (fun _ => covMat μ (Y 0)) := by
  refine TendstoInMeasure.congr
    (f := fun n ω =>
      covMat
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1)))
        (fun i a => Y i.val ω a))
    (f' := bootstrapCrossMomentMatIndexed
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a)))
    (g := fun _ : Ω => covMat μ (Y 0))
    (g' := fun _ : Ω => covMat μ (Y 0))
    (fun n => ?_) EventuallyEq.rfl
    (covMat_uniformOn_finSucc_tendsto_of_mean_cross_moments
      (μ := μ) Y hYmem hmean hcross)
  exact ae_of_all μ fun ω =>
    (bootstrapCrossMomentMatIndexed_normalized_finSucc_resampleMean_sub_empiricalMean_eq_covMat
      (Y := Y) n ω).symm

/-- Indexed normalized ordinary-bootstrap cross moments converge for iid
finite-dimensional observations.

This composes the iid empirical-covariance WLLN with the exact finite
normalization identity for `sqrt (n+1) (Ybar* - Ybar)`. -/
theorem bootstrapCrossMomentMatIndexed_normalized_finSucc_tendsto_of_iid
    [IsProbabilityMeasure μ] [Fintype k]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInMeasure μ
      (bootstrapCrossMomentMatIndexed
        (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
        (fun n _ =>
          ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a)))
      atTop (fun _ => covMat μ (Y 0)) := by
  refine TendstoInMeasure.congr
    (f := fun n ω =>
      covMat
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1)))
        (fun i a => Y i.val ω a))
    (f' := bootstrapCrossMomentMatIndexed
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a)))
    (g := fun _ : Ω => covMat μ (Y 0))
    (g' := fun _ : Ω => covMat μ (Y 0))
    (fun n => ?_) EventuallyEq.rfl
    (covMat_uniformOn_finSucc_tendsto_of_iid
      (μ := μ) Y hYmem hindep hident)
  exact ae_of_all μ fun ω =>
    (bootstrapCrossMomentMatIndexed_normalized_finSucc_resampleMean_sub_empiricalMean_eq_covMat
      (Y := Y) n ω).symm

/-- Indexed normalized ordinary-bootstrap cross moments converge for iid
finite-dimensional observations with the textbook `iIndepFun` premise. -/
theorem bootstrapCrossMomentMatIndexed_normalized_finSucc_tendsto_of_iIndep
    [IsProbabilityMeasure μ] [Fintype k]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInMeasure μ
      (bootstrapCrossMomentMatIndexed
        (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
        (fun n _ =>
          ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a)))
      atTop (fun _ => covMat μ (Y 0)) :=
  bootstrapCrossMomentMatIndexed_normalized_finSucc_tendsto_of_iid
    (μ := μ) Y hYmem (fun _ _ hij => hindep.indepFun hij) hident

/-- Indexed normalized ordinary-bootstrap covariance matrices converge once
the finite empirical one-draw covariance converges through first and cross
moments.

This is the `cov`-API counterpart of
`bootstrapCrossMomentMatIndexed_normalized_finSucc_tendsto_of_mean_cross_moments`,
used by later covariance and regression-facing Chapter 10 wrappers. -/
theorem
    bootstrapCovarianceMatIndexed_normalized_finSucc_tendsto_of_mean_cross_moments
    [IsProbabilityMeasure μ] [Fintype k]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hmean : ∀ a,
      TendstoInMeasure μ
        (fun n ω =>
          ∫ i : Fin (n + 1), Y i.val ω a
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))))
        atTop (fun _ => ∫ ω, Y 0 ω a ∂μ))
    (hcross : ∀ a b,
      TendstoInMeasure μ
        (fun n ω =>
          ∫ i : Fin (n + 1), Y i.val ω a * Y i.val ω b
            ∂(ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
              Measure (Fin (n + 1))))
        atTop (fun _ => ∫ ω, Y 0 ω a * Y 0 ω b ∂μ)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMatIndexed
        (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
        (fun n _ =>
          ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a)))
      atTop (fun _ => covMat μ (Y 0)) := by
  refine TendstoInMeasure.congr
    (f := fun n ω =>
      covMat
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1)))
        (fun i a => Y i.val ω a))
    (f' := bootstrapCovarianceMatIndexed
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a)))
    (g := fun _ : Ω => covMat μ (Y 0))
    (g' := fun _ : Ω => covMat μ (Y 0))
    (fun n => ?_) EventuallyEq.rfl
    (covMat_uniformOn_finSucc_tendsto_of_mean_cross_moments
      (μ := μ) Y hYmem hmean hcross)
  exact ae_of_all μ fun ω =>
    (bootstrapCovarianceMatIndexed_normalized_finSucc_resampleMean_sub_empiricalMean_eq_covMat
      (Y := Y) n ω).symm

/-- Indexed normalized ordinary-bootstrap covariance matrices converge for iid
finite-dimensional observations.

This is the `cov`-API counterpart of
`bootstrapCrossMomentMatIndexed_normalized_finSucc_tendsto_of_iid`. -/
theorem bootstrapCovarianceMatIndexed_normalized_finSucc_tendsto_of_iid
    [IsProbabilityMeasure μ] [Fintype k]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInMeasure μ
      (bootstrapCovarianceMatIndexed
        (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
        (fun n _ =>
          ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a)))
      atTop (fun _ => covMat μ (Y 0)) := by
  refine TendstoInMeasure.congr
    (f := fun n ω =>
      covMat
        (ProbabilityTheory.uniformOn (Set.univ : Set (Fin (n + 1))) :
          Measure (Fin (n + 1)))
        (fun i a => Y i.val ω a))
    (f' := bootstrapCovarianceMatIndexed
      (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
      (fun n _ =>
        ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs a =>
        Real.sqrt (n + 1 : ℝ) *
          (empiricalBootstrapResampleMean
              (fun i : Fin (n + 1) => Y i.val ω)
              (fun ωs t => ωs t) ωs a -
            empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a)))
    (g := fun _ : Ω => covMat μ (Y 0))
    (g' := fun _ : Ω => covMat μ (Y 0))
    (fun n => ?_) EventuallyEq.rfl
    (covMat_uniformOn_finSucc_tendsto_of_iid
      (μ := μ) Y hYmem hindep hident)
  exact ae_of_all μ fun ω =>
    (bootstrapCovarianceMatIndexed_normalized_finSucc_resampleMean_sub_empiricalMean_eq_covMat
      (Y := Y) n ω).symm

/-- Indexed normalized ordinary-bootstrap covariance matrices converge for iid
finite-dimensional observations with the textbook `iIndepFun` premise. -/
theorem bootstrapCovarianceMatIndexed_normalized_finSucc_tendsto_of_iIndep
    [IsProbabilityMeasure μ] [Fintype k]
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) :
    TendstoInMeasure μ
      (bootstrapCovarianceMatIndexed
        (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
        (fun n _ =>
          ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
        (fun n ω ωs a =>
          Real.sqrt (n + 1 : ℝ) *
            (empiricalBootstrapResampleMean
                (fun i : Fin (n + 1) => Y i.val ω)
                (fun ωs t => ωs t) ωs a -
              empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a)))
      atTop (fun _ => covMat μ (Y 0)) :=
  bootstrapCovarianceMatIndexed_normalized_finSucc_tendsto_of_iid
    (μ := μ) Y hYmem (fun _ _ hij => hindep.indepFun hij) hident

/-- Theorem 10.8 ordinary-bootstrap covariance-input route with a deterministic
Jacobian plug-in and iid finite-dimensional observations.

The `Fin (n+1)` ordinary nonparametric-bootstrap covariance matrix supplies the
covariance input `V*`; ordinary convergence of the deterministic Jacobian source
supplies `G*`.  The smooth plug-in covariance CMT then gives convergence of
`G*' V* G*` to `G' V G`. -/
theorem
    chapter10_indexed_smoothVariance_detJacobian_finSuccCovariance_iid
    [IsProbabilityMeasure μ] [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Useq : ℕ → Ω → A} {u : A} {Gfun : A → Matrix d r ℝ}
    (Y : ℕ → Ω → d → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hU : TendstoInMeasure μ Useq atTop (fun _ => u))
    (hG : ContinuousAt Gfun u) :
    TendstoInBootstrapProbabilityIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gfun (Useq n ω))
          (bootstrapCovarianceMatIndexed
            (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
            (fun n _ =>
              ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs a =>
              Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs a -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
            n ω))
      (fun _ => smoothFunctionVarianceFunctional (Gfun u) (covMat μ (Y 0))) := by
  have hPstar : ∀ n (ω : Ω),
      IsProbabilityMeasure
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) := by
    intro n ω
    infer_instance
  exact
    chapter10_indexed_bootstrap_smooth_variance_consistency_of_deterministic_jacobian
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Useq := Useq) (u := u) (Gfun := Gfun)
      (Vseq := fun n ω =>
        bootstrapCovarianceMatIndexed
          (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
          (fun n _ =>
            ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
          (fun n ω ωs a =>
            Real.sqrt (n + 1 : ℝ) *
              (empiricalBootstrapResampleMean
                  (fun i : Fin (n + 1) => Y i.val ω)
                  (fun ωs t => ωs t) ωs a -
                empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
          n ω)
      (V := covMat μ (Y 0)) hPstar hU hG
      (bootstrapCovarianceMatIndexed_normalized_finSucc_tendsto_of_iid
        (μ := μ) Y hYmem hindep hident)

/-- Theorem 10.8 ordinary-bootstrap covariance-input route with a deterministic
Jacobian plug-in and the textbook `iIndepFun` premise. -/
theorem
    chapter10_indexed_smoothVariance_detJacobian_finSuccCovariance_iIndep
    [IsProbabilityMeasure μ] [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Useq : ℕ → Ω → A} {u : A} {Gfun : A → Matrix d r ℝ}
    (Y : ℕ → Ω → d → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hU : TendstoInMeasure μ Useq atTop (fun _ => u))
    (hG : ContinuousAt Gfun u) :
    TendstoInBootstrapProbabilityIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gfun (Useq n ω))
          (bootstrapCovarianceMatIndexed
            (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
            (fun n _ =>
              ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs a =>
              Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs a -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
            n ω))
      (fun _ => smoothFunctionVarianceFunctional (Gfun u) (covMat μ (Y 0))) :=
  chapter10_indexed_smoothVariance_detJacobian_finSuccCovariance_iid
    (μ := μ) (Useq := Useq) (u := u) (Gfun := Gfun) Y hYmem
    (fun _ _ hij => hindep.indepFun hij) hident hU hG

/-- Theorem 10.8 ordinary-bootstrap covariance-input route with a stochastic
continuous Jacobian plug-in and iid finite-dimensional observations.

The `Fin (n+1)` ordinary nonparametric-bootstrap covariance matrix supplies the
covariance input `V*`; the bootstrap-probability convergence premise for
`U*_n` supplies the stochastic continuous Jacobian `G(U*_n)`. -/
theorem
    chapter10_indexed_smoothVariance_contJacobian_finSuccCovariance_iid
    [IsProbabilityMeasure μ] [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Ustar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → A}
    {u : A} {Gfun : A → Matrix d r ℝ}
    (Y : ℕ → Ω → d → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hU :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        Ustar (fun _ => u))
    (hG : ContinuousAt Gfun u) :
    TendstoInBootstrapProbabilityIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gfun (Ustar n ω ωs))
          (bootstrapCovarianceMatIndexed
            (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
            (fun n _ =>
              ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs a =>
              Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs a -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
            n ω))
      (fun _ => smoothFunctionVarianceFunctional (Gfun u) (covMat μ (Y 0))) := by
  have hPstar : ∀ n (ω : Ω),
      IsProbabilityMeasure
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))) := by
    intro n ω
    infer_instance
  exact
    chapter10_indexed_bootstrap_smooth_variance_consistency_of_continuous_jacobian
      (μ := μ)
      (Pstar := fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (Ustar := Ustar) (u := u) (Gfun := Gfun)
      (Vstar := fun n ω _ =>
        bootstrapCovarianceMatIndexed
          (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
          (fun n _ =>
            ProbabilityTheory.uniformOn
              (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
          (fun n ω ωs a =>
            Real.sqrt (n + 1 : ℝ) *
              (empiricalBootstrapResampleMean
                  (fun i : Fin (n + 1) => Y i.val ω)
                  (fun ωs t => ωs t) ωs a -
                empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
          n ω)
      (V := covMat μ (Y 0)) hPstar hU hG
      (tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure
        (μ := μ)
        (Pstar := fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        hPstar
        (bootstrapCovarianceMatIndexed_normalized_finSucc_tendsto_of_iid
          (μ := μ) Y hYmem hindep hident))

/-- Theorem 10.8 ordinary-bootstrap covariance-input route with a stochastic
continuous Jacobian plug-in and the textbook `iIndepFun` premise. -/
theorem
    chapter10_indexed_smoothVariance_contJacobian_finSuccCovariance_iIndep
    [IsProbabilityMeasure μ] [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Ustar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → A}
    {u : A} {Gfun : A → Matrix d r ℝ}
    (Y : ℕ → Ω → d → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hU :
      TendstoInBootstrapProbabilityIndexed μ
        (fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        Ustar (fun _ => u))
    (hG : ContinuousAt Gfun u) :
    TendstoInBootstrapProbabilityIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gfun (Ustar n ω ωs))
          (bootstrapCovarianceMatIndexed
            (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
            (fun n _ =>
              ProbabilityTheory.uniformOn
                (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
            (fun n ω ωs a =>
              Real.sqrt (n + 1 : ℝ) *
                (empiricalBootstrapResampleMean
                    (fun i : Fin (n + 1) => Y i.val ω)
                    (fun ωs t => ωs t) ωs a -
                  empiricalMean (fun i : Fin (n + 1) => Y i.val ω) a))
            n ω))
      (fun _ => smoothFunctionVarianceFunctional (Gfun u) (covMat μ (Y 0))) :=
  chapter10_indexed_smoothVariance_contJacobian_finSuccCovariance_iid
    (μ := μ) (Ustar := Ustar) (u := u) (Gfun := Gfun) Y hYmem
    (fun _ _ hij => hindep.indepFun hij) hident hU hG

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

/-- Hansen Theorem 10.9/10.12 covariance matrix from bootstrap weak
convergence and fourth-moment tail controls.

This theorem-facing wrapper discharges the scalar coordinate and coordinate-sum
uniform-square-tail assumptions from conditional fourth-moment convergence plus
eventual squared-tail bounds for the weak limit law. -/
theorem chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_fourthMoment_tails
    [Fintype k] [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ}
    {Bcoord : k → ℝ} {Bsum : k → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoord :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω => ∫ ωs, (Zstar n ω ωs a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordInt :
      ∀ n ω a, Integrable (fun ωs => (Zstar n ω ωs a) ^ 4) (Pstar n ω))
    (hLimitTailCoord :
      ∀ a ε, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim a|}
            (fun ωlim => (Z ωlim a) ^ 2) ωlim ∂ν) ≤ ε)
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSum :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs, (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumInt :
      ∀ n ω a c,
        Integrable
          (fun ωs => (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4)
          (Pstar n ω))
    (hLimitTailSum :
      ∀ a c ε, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim a + Z ωlim c|}
            (fun ωlim => (Z ωlim a + Z ωlim c) ^ 2) ωlim ∂ν) ≤ ε) :
    TendstoInMeasure μ (bootstrapCovarianceMat Pstar Zstar) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
    (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z)
    hPstar hZmem hZlim hweak
    (fun a =>
      bootstrapUniformSquareTail_of_fourthMoment_tendstoInMeasure_of_eventual_limit_tail
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a)
        (ν := ν) (Z := fun ωlim => Z ωlim a)
        (B := Bcoord a)
        (hBcoord a) (hFourthCoord a)
        (fun n ω => hFourthCoordInt n ω a)
        (hLimitTailCoord a))
    (fun a c =>
      bootstrapUniformSquareTail_of_fourthMoment_tendstoInMeasure_of_eventual_limit_tail
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c)
        (ν := ν) (Z := fun ωlim => Z ωlim a + Z ωlim c)
        (B := Bsum a c)
        (hBsum a c) (hFourthSum a c)
        (fun n ω => hFourthSumInt n ω a c)
        (hLimitTailSum a c))

/-- Hansen Theorem 10.9/10.12 covariance matrix from bootstrap weak convergence
and fourth-moment convergence, with weak-limit coordinate and coordinate-sum
tail premises discharged by `MemLp`. -/
theorem
    chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_fourthMoment_memLp_limit
    [Fintype k] [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ}
    {Bcoord : k → ℝ} {Bsum : k → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoord :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω => ∫ ωs, (Zstar n ω ωs a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordInt :
      ∀ n ω a, Integrable (fun ωs => (Zstar n ω ωs a) ^ 4) (Pstar n ω))
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSum :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs, (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumInt :
      ∀ n ω a c,
        Integrable
          (fun ωs => (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4)
          (Pstar n ω)) :
    TendstoInMeasure μ (bootstrapCovarianceMat Pstar Zstar) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
    (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z)
    hPstar hZmem hZlim hweak
    (fun a =>
      bootstrapUniformSquareTail_of_fourthMoment_tendstoInMeasure_of_memLp_limit
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a)
        (ν := ν) (Z := fun ωlim => Z ωlim a)
        (B := Bcoord a)
        (hBcoord a) (hZlim a) (hFourthCoord a)
        (fun n ω => hFourthCoordInt n ω a))
    (fun a c =>
      bootstrapUniformSquareTail_of_fourthMoment_tendstoInMeasure_of_memLp_limit
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c)
        (ν := ν) (Z := fun ωlim => Z ωlim a + Z ωlim c)
        (B := Bsum a c)
        (hBsum a c) ((hZlim a).add (hZlim c)) (hFourthSum a c)
        (fun n ω => hFourthSumInt n ω a c))

/-- Hansen Theorem 10.9/10.12 covariance matrix from bootstrap weak
convergence and eventual deterministic coordinate and coordinate-sum bounds.

The coordinate bounds discharge the scalar mean/second-moment tail conditions;
the coordinate-sum bounds discharge the cross-moment tails used by the
polarization identity. -/
theorem
    chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_eventualBound_memLp_limit
    [Fintype k] [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ}
    {Ccoord : k → ℝ} {Csum : k → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs a| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |Zstar n ω ωs a + Zstar n ω ωs c| ≤ Csum a c) :
    TendstoInMeasure μ (bootstrapCovarianceMat Pstar Zstar) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
    (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z)
    hPstar hZmem hZlim hweak
    (fun a =>
      bootstrapUniformSquareTail_of_eventually_bound_memLp_limit
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a)
        (ν := ν) (Z := fun ωlim => Z ωlim a)
        (C := Ccoord a) (hZlim a) (hboundCoord a))
    (fun a c =>
      bootstrapUniformSquareTail_of_eventually_bound_memLp_limit
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c)
        (ν := ν) (Z := fun ωlim => Z ωlim a + Z ωlim c)
        (C := Csum a c) ((hZlim a).add (hZlim c)) (hboundSum a c))

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

/-- Indexed Hansen Theorem 10.9/10.12 covariance matrix from bootstrap weak
convergence and fourth-moment tail controls. -/
theorem
    chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_fourthMoment_tails
    [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ}
    {Bcoord : k → ℝ} {Bsum : k → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoord :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω => ∫ ωs, (Zstar n ω ωs a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordInt :
      ∀ n ω a, Integrable (fun ωs => (Zstar n ω ωs a) ^ 4) (Pstar n ω))
    (hLimitTailCoord :
      ∀ a ε, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim a|}
            (fun ωlim => (Z ωlim a) ^ 2) ωlim ∂ν) ≤ ε)
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSum :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs, (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumInt :
      ∀ n ω a c,
        Integrable
          (fun ωs => (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4)
          (Pstar n ω))
    (hLimitTailSum :
      ∀ a c ε, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim a + Z ωlim c|}
            (fun ωlim => (Z ωlim a + Z ωlim c) ^ 2) ωlim ∂ν) ≤ ε) :
    TendstoInMeasure μ (bootstrapCovarianceMatIndexed Pstar Zstar) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
    (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z)
    hPstar hZmem hZlim hweak
    (fun a =>
      bootstrapUniformSquareTailIndexed_of_fourthMoment_tendstoInMeasure_of_eventual_limit_tail
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a)
        (ν := ν) (Z := fun ωlim => Z ωlim a)
        (B := Bcoord a)
        (hBcoord a) (hFourthCoord a)
        (fun n ω => hFourthCoordInt n ω a)
        (hLimitTailCoord a))
    (fun a c =>
      bootstrapUniformSquareTailIndexed_of_fourthMoment_tendstoInMeasure_of_eventual_limit_tail
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c)
        (ν := ν) (Z := fun ωlim => Z ωlim a + Z ωlim c)
        (B := Bsum a c)
        (hBsum a c) (hFourthSum a c)
        (fun n ω => hFourthSumInt n ω a c)
        (hLimitTailSum a c))

/-- Indexed Hansen Theorem 10.9/10.12 covariance matrix from bootstrap weak
convergence and fourth-moment convergence, with weak-limit coordinate and
coordinate-sum tail premises discharged by `MemLp`. -/
theorem
    chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_fourthMoment_memLp_limit
    [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ}
    {Bcoord : k → ℝ} {Bsum : k → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoord :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω => ∫ ωs, (Zstar n ω ωs a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordInt :
      ∀ n ω a, Integrable (fun ωs => (Zstar n ω ωs a) ^ 4) (Pstar n ω))
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSum :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs, (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumInt :
      ∀ n ω a c,
        Integrable
          (fun ωs => (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4)
          (Pstar n ω)) :
    TendstoInMeasure μ (bootstrapCovarianceMatIndexed Pstar Zstar) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
    (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z)
    hPstar hZmem hZlim hweak
    (fun a =>
      bootstrapUniformSquareTailIndexed_of_fourthMoment_tendstoInMeasure_of_memLp_limit
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a)
        (ν := ν) (Z := fun ωlim => Z ωlim a)
        (B := Bcoord a)
        (hBcoord a) (hZlim a) (hFourthCoord a)
        (fun n ω => hFourthCoordInt n ω a))
    (fun a c =>
      bootstrapUniformSquareTailIndexed_of_fourthMoment_tendstoInMeasure_of_memLp_limit
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c)
        (ν := ν) (Z := fun ωlim => Z ωlim a + Z ωlim c)
        (B := Bsum a c)
        (hBsum a c) ((hZlim a).add (hZlim c)) (hFourthSum a c)
        (fun n ω => hFourthSumInt n ω a c))

/-- Indexed Hansen Theorem 10.9/10.12 covariance matrix from bootstrap weak
convergence and eventual deterministic coordinate and coordinate-sum bounds. -/
theorem
    chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_eventualBound_memLp_limit
    [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ}
    {Ccoord : k → ℝ} {Csum : k → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs a| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |Zstar n ω ωs a + Zstar n ω ωs c| ≤ Csum a c) :
    TendstoInMeasure μ (bootstrapCovarianceMatIndexed Pstar Zstar) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
    (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z)
    hPstar hZmem hZlim hweak
    (fun a =>
      bootstrapUniformSquareTailIndexed_of_eventually_bound_memLp_limit
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a)
        (ν := ν) (Z := fun ωlim => Z ωlim a)
        (C := Ccoord a) (hZlim a) (hboundCoord a))
    (fun a c =>
      bootstrapUniformSquareTailIndexed_of_eventually_bound_memLp_limit
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c)
        (ν := ν) (Z := fun ωlim => Z ωlim a + Z ωlim c)
        (C := Csum a c) ((hZlim a).add (hZlim c)) (hboundSum a c))

theorem memLp_multivariateGaussian_coord_two
    {r : Type*} [Fintype r] [DecidableEq r] {S : Matrix r r ℝ} (a : r) :
    MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ r) S) := by
  let L : EuclideanSpace ℝ r →L[ℝ] ℝ := EuclideanSpace.proj a
  have h :=
    ContinuousLinearMap.comp_memLp' L
      (IsGaussian.memLp_two_id
        (μ := multivariateGaussian (0 : EuclideanSpace ℝ r) S))
  simpa [L, Function.comp_def] using h

private theorem multivariateGaussian_covarianceIntegralMat_eq
    {r : Type*} [Fintype r] [DecidableEq r]
    {S : Matrix r r ℝ} (hS : S.PosSemidef)
    (hmem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) S)) :
    (fun a c =>
      (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a *
          ((z : EuclideanSpace ℝ r) : r → ℝ) c
        ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) -
      (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
        ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) *
      (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) c
        ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S)) = S := by
  ext a c
  haveI :
      IsProbabilityMeasure
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S) :=
    inferInstance
  have hcovSub :=
    ProbabilityTheory.covariance_eq_sub (hmem a) (hmem c)
  have hcov :=
    multivariateGaussian_covariance_eval
      (μ := (0 : EuclideanSpace ℝ r)) (S := S) hS a c
  simpa using hcovSub.symm.trans hcov

/-- Hansen Theorem 10.10/10.12 smooth-function conditional covariance
consistency from a noncompact compact-tail remainder linearization and named
uniform-square-tail coordinate and coordinate-sum controls.

Theorem 10.7 supplies the smooth Gaussian weak limit through the compact-tail
pointwise remainder route; Theorem 10.9's covariance-matrix wrapper supplies
the conditional covariance target from coordinate and coordinate-sum tails. -/
theorem
    chapter10_smooth_covarianceMat_tendsto_of_compact_tail_remainder_uniformSquareTail
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
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
    (hTailCoord :
      ∀ a,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
          (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a))
    (hTailSum :
      ∀ a c,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs =>
            (thetaStar n ω ωs : r → ℝ) a +
              (thetaStar n ω ωs : r → ℝ) c)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
          (fun z : EuclideanSpace ℝ r =>
            (z : r → ℝ) a + (z : r → ℝ) c)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMat Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  let S : Matrix r r ℝ := G * V * Gᵀ
  have hS : S.PosSemidef := by
    dsimp [S]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.mul_mul_conjTranspose_same G
  have hGaussianEuclidean :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z) := by
    dsimp [S]
    exact
      chapter10_bootstrap_smooth_function_gaussian_of_compact_tail_remainder_bound
        (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
        (thetaStar := thetaStar) (R := R) (V := V) G hV hT hPstar hTstar
        hthetaStar hCompactTail hR_tail hR_bound
  have hGaussian :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hGaussianEuclidean (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hcov :
      TendstoInMeasure μ
        (bootstrapCovarianceMat Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
        atTop
        (fun _ => fun a c =>
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a *
              ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) *
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S)) :=
    chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hPstar hcoordMem (by simpa [S] using hlimMem) hGaussian
      (by simpa [S] using hTailCoord) (by simpa [S] using hTailSum)
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hcov
  exact ae_of_all μ fun _ => by
    simpa [S] using
      (multivariateGaussian_covarianceIntegralMat_eq
        (S := S) hS (by simpa [S] using hlimMem))

/-- Hansen Theorem 10.10/10.12 smooth-function conditional covariance
consistency from a noncompact compact-tail remainder linearization and
eventual deterministic coordinate and coordinate-sum bounds. -/
theorem
    chapter10_smooth_covarianceMat_tendsto_of_compact_tail_remainder_eventualBound_memLp
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Ccoord : r → ℝ} {Csum : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
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
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a +
          (thetaStar n ω ωs : r → ℝ) c)| ≤ Csum a c) :
    TendstoInMeasure μ
      (bootstrapCovarianceMat Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) :=
  chapter10_smooth_covarianceMat_tendsto_of_compact_tail_remainder_uniformSquareTail
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (R := R) (V := V) G hV hPstar hT hTstar
    hthetaStar hcoordMem hlimMem hCompactTail hR_tail hR_bound
    (fun a =>
      bootstrapUniformSquareTail_of_eventually_bound_memLp_limit
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
        (C := Ccoord a) (hlimMem a) (hboundCoord a))
    (fun a c =>
      bootstrapUniformSquareTail_of_eventually_bound_memLp_limit
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs =>
          (thetaStar n ω ωs : r → ℝ) a +
            (thetaStar n ω ωs : r → ℝ) c)
        (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (Z := fun z : EuclideanSpace ℝ r =>
          (z : r → ℝ) a + (z : r → ℝ) c)
        (C := Csum a c) ((hlimMem a).add (hlimMem c))
        (hboundSum a c))

/-- Indexed sample-size-dependent counterpart of
`chapter10_smooth_covarianceMat_tendsto_of_compact_tail_remainder_uniformSquareTail`. -/
theorem
    chapter10_indexed_smooth_covarianceMat_tendsto_of_tail_remainder_uniformSquareTail
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
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
    (hTailCoord :
      ∀ a,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
          (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a))
    (hTailSum :
      ∀ a c,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs =>
            (thetaStar n ω ωs : r → ℝ) a +
              (thetaStar n ω ωs : r → ℝ) c)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
          (fun z : EuclideanSpace ℝ r =>
            (z : r → ℝ) a + (z : r → ℝ) c)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  let S : Matrix r r ℝ := G * V * Gᵀ
  have hS : S.PosSemidef := by
    dsimp [S]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.mul_mul_conjTranspose_same G
  have hGaussianEuclidean :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z) := by
    dsimp [S]
    exact
      chapter10_indexed_bootstrap_smooth_function_gaussian_of_compact_tail_remainder_bound
        (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
        (thetaStar := thetaStar) (R := R) (V := V) G hV hT hPstar hTstar
        hthetaStar hCompactTail hR_tail hR_bound
  have hGaussian :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hGaussianEuclidean (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hcov :
      TendstoInMeasure μ
        (bootstrapCovarianceMatIndexed Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
        atTop
        (fun _ => fun a c =>
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a *
              ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) *
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S)) :=
    chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hPstar hcoordMem (by simpa [S] using hlimMem) hGaussian
      (by simpa [S] using hTailCoord) (by simpa [S] using hTailSum)
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hcov
  exact ae_of_all μ fun _ => by
    simpa [S] using
      (multivariateGaussian_covarianceIntegralMat_eq
        (S := S) hS (by simpa [S] using hlimMem))

/-- Indexed sample-size-dependent counterpart of
`chapter10_smooth_covarianceMat_tendsto_of_compact_tail_remainder_eventualBound_memLp`. -/
theorem
    chapter10_indexed_smooth_covarianceMat_tendsto_of_tail_remainder_eventualBound_memLp
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Ccoord : r → ℝ} {Csum : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
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
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a +
          (thetaStar n ω ωs : r → ℝ) c)| ≤ Csum a c) :
    TendstoInMeasure μ
      (bootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_smooth_covarianceMat_tendsto_of_tail_remainder_uniformSquareTail
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (R := R) (V := V) G hV hPstar hT hTstar
    hthetaStar hcoordMem hlimMem hCompactTail hR_tail hR_bound
    (fun a =>
      bootstrapUniformSquareTailIndexed_of_eventually_bound_memLp_limit
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
        (C := Ccoord a) (hlimMem a) (hboundCoord a))
    (fun a c =>
      bootstrapUniformSquareTailIndexed_of_eventually_bound_memLp_limit
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs =>
          (thetaStar n ω ωs : r → ℝ) a +
            (thetaStar n ω ωs : r → ℝ) c)
        (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
        (Z := fun z : EuclideanSpace ℝ r =>
          (z : r → ℝ) a + (z : r → ℝ) c)
        (C := Csum a c) ((hlimMem a).add (hlimMem c))
        (hboundSum a c))

/-- Hansen Theorem 10.10/10.12 smooth-function conditional covariance
consistency from a noncompact compact-tail remainder linearization and a norm
fourth-moment premise on the nonlinear smooth statistic.

The norm fourth moment of `thetaStar` supplies both coordinate and
coordinate-sum uniform-square-tail controls before applying the compact-tail
remainder covariance wrapper. -/
theorem
    chapter10_smooth_covarianceMat_tendsto_of_compact_tail_remainder_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
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
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖thetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖thetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMat Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  exact
    chapter10_smooth_covarianceMat_tendsto_of_compact_tail_remainder_uniformSquareTail
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (R := R) (V := V) G hV hPstar hT hTstar
      hthetaStar hcoordMem hlimMem hCompactTail hR_tail hR_bound
      (fun a =>
        bootstrapUniformSquareTail_of_normFourth_coord
          (μ := μ)
          (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
          (Pstar := Pstar) (Zstar := thetaStar)
          (Z := fun z : EuclideanSpace ℝ r => z)
          (B := B) a hB (hlimMem a) hNormFourth hNormFourthInt)
      (fun a c =>
        bootstrapUniformSquareTail_of_normFourth_coord_add
          (μ := μ)
          (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
          (Pstar := Pstar) (Zstar := thetaStar)
          (Z := fun z : EuclideanSpace ℝ r => z)
          (B := B) a c hB ((hlimMem a).add (hlimMem c))
          hNormFourth hNormFourthInt)

/-- Hansen Theorem 10.10/10.12 smooth-function conditional covariance
consistency from a quadratic Taylor-remainder envelope and norm fourth-moment
premises.

The quadratic envelope supplies the compact-tail remainder-tail condition,
while the norm fourth-moment premise on `thetaStar` supplies all coordinate and
coordinate-sum uniform-square-tail controls. -/
theorem
    chapter10_smooth_covarianceMat_tendsto_of_quadratic_remainder_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Bθ BT : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hBθ : 0 ≤ Bθ)
    (hThetaNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖thetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bθ))
    (hThetaNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖thetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMat Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) :=
  chapter10_smooth_covarianceMat_tendsto_of_compact_tail_remainder_normFourthMoment
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hPstar hT hTstar hthetaStar hcoordMem hlimMem
    hCompactTail
    (bootstrapRemainderTail_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hBθ hThetaNormFourth hThetaNormFourthInt

/-- Indexed sample-size-dependent counterpart of
`chapter10_smooth_covarianceMat_tendsto_of_compact_tail_remainder_normFourthMoment`. -/
theorem
    chapter10_indexed_smooth_covarianceMat_tendsto_of_tail_remainder_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
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
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖thetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖thetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  exact
    chapter10_indexed_smooth_covarianceMat_tendsto_of_tail_remainder_uniformSquareTail
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (R := R) (V := V) G hV hPstar hT hTstar
      hthetaStar hcoordMem hlimMem hCompactTail hR_tail hR_bound
      (fun a =>
        bootstrapUniformSquareTailIndexed_of_normFourth_coord
          (μ := μ)
          (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
          (Pstar := Pstar) (Zstar := thetaStar)
          (Z := fun z : EuclideanSpace ℝ r => z)
          (B := B) a hB (hlimMem a) hNormFourth hNormFourthInt)
      (fun a c =>
        bootstrapUniformSquareTailIndexed_of_normFourth_coord_add
          (μ := μ)
          (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))
          (Pstar := Pstar) (Zstar := thetaStar)
          (Z := fun z : EuclideanSpace ℝ r => z)
          (B := B) a c hB ((hlimMem a).add (hlimMem c))
          hNormFourth hNormFourthInt)

/-- Indexed sample-size-dependent counterpart of
`chapter10_smooth_covarianceMat_tendsto_of_quadratic_remainder_normFourthMoment`. -/
theorem
    chapter10_indexed_smooth_covarianceMat_tendsto_of_quadratic_remainder_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Bθ BT : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hCompactTail : ∀ η : ℝ, 0 < η →
      ∃ K : Set (EuclideanSpace ℝ r), IsCompact K ∧
        TendstoInMeasure μ
          (fun n ω =>
            (Pstar n ω).real
              {ωs | matrixContinuousLinearMap G (Tstar n ω ωs) ∉ K})
          atTop (fun _ => 0) ∧
        TendstoInMeasure μ
          (fun n ω => (Pstar n ω).real {ωs | thetaStar n ω ωs ∉ K})
          atTop (fun _ => 0))
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hBθ : 0 ≤ Bθ)
    (hThetaNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖thetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bθ))
    (hThetaNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖thetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_smooth_covarianceMat_tendsto_of_tail_remainder_normFourthMoment
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar)
    (R := fun n ω ωs => ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (V := V) G hV hPstar hT hTstar hthetaStar hcoordMem hlimMem
    hCompactTail
    (bootstrapRemainderTailIndexed_tendsto_zero_of_quadratic_norm_bound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (ρ := ρ) (B := BT) hPstar hρsq hTNormFourth hTNormFourthInt)
    hR_bound hBθ hThetaNormFourth hThetaNormFourthInt

/-- Hansen Theorem 10.10/10.12 smooth-function conditional covariance
consistency from a compact-range quadratic Taylor-remainder envelope and norm
fourth-moment premises.

The fixed compact range removes the noncompact compact-tail premise, while the
quadratic envelope and fourth moment of the linearized statistic discharge the
remainder-tail premise. The separate norm fourth-moment premise on
`thetaStar` supplies all coordinate and coordinate-sum uniform-square-tail
conditions for the covariance matrix. -/
theorem
    chapter10_smooth_covarianceMat_tendsto_of_compact_range_quadratic_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hBθ : 0 ≤ Bθ)
    (hThetaNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖thetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bθ))
    (hThetaNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖thetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMat Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  let S : Matrix r r ℝ := G * V * Gᵀ
  have hS : S.PosSemidef := by
    dsimp [S]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.mul_mul_conjTranspose_same G
  have hGaussianEuclidean :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z) := by
    dsimp [S]
    exact
      chapter10_smooth_gaussian_of_compact_range_quadratic_normFourth
        (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
        (thetaStar := thetaStar) (ρ := ρ) (BT := BT) (V := V) G
        hV hT hK hPstar hTstar hthetaStar hlinearized_mem
        hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound
  have hGaussian :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hGaussianEuclidean (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hcov :
      TendstoInMeasure μ
        (bootstrapCovarianceMat Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
        atTop
        (fun _ => fun a c =>
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a *
              ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) *
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S)) :=
    chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hPstar hcoordMem (by simpa [S] using hlimMem) hGaussian
      (fun a =>
        bootstrapUniformSquareTail_of_normFourth_coord
          (μ := μ)
          (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
          (Pstar := Pstar) (Zstar := thetaStar)
          (Z := fun z : EuclideanSpace ℝ r => z)
          (B := Bθ) a hBθ (by simpa [S] using hlimMem a)
          hThetaNormFourth hThetaNormFourthInt)
      (fun a c =>
        bootstrapUniformSquareTail_of_normFourth_coord_add
          (μ := μ)
          (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
          (Pstar := Pstar) (Zstar := thetaStar)
          (Z := fun z : EuclideanSpace ℝ r => z)
          (B := Bθ) a c hBθ
          (by simpa [S] using (hlimMem a).add (hlimMem c))
          hThetaNormFourth hThetaNormFourthInt)
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hcov
  exact ae_of_all μ fun _ => by
    simpa [S] using
      (multivariateGaussian_covarianceIntegralMat_eq
        (S := S) hS (by simpa [S] using hlimMem))

/-- Indexed sample-size-dependent counterpart of
`chapter10_smooth_covarianceMat_tendsto_of_compact_range_quadratic_normFourthMoment`. -/
theorem
    chapter10_indexed_smooth_covarianceMat_tendsto_of_compact_range_quadratic_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hBθ : 0 ≤ Bθ)
    (hThetaNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖thetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bθ))
    (hThetaNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖thetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  let S : Matrix r r ℝ := G * V * Gᵀ
  have hS : S.PosSemidef := by
    dsimp [S]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.mul_mul_conjTranspose_same G
  have hGaussianEuclidean :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z) := by
    dsimp [S]
    exact
      chapter10_indexed_smooth_gaussian_of_compact_range_quadratic_normFourth
        (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
        (thetaStar := thetaStar) (ρ := ρ) (BT := BT) (V := V) G
        hV hT hK hPstar hTstar hthetaStar hlinearized_mem
        hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound
  have hGaussian :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hGaussianEuclidean (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hcov :
      TendstoInMeasure μ
        (bootstrapCovarianceMatIndexed Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
        atTop
        (fun _ => fun a c =>
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a *
              ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) *
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S)) :=
    chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hPstar hcoordMem (by simpa [S] using hlimMem) hGaussian
      (fun a =>
        bootstrapUniformSquareTailIndexed_of_normFourth_coord
          (μ := μ)
          (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
          (Pstar := Pstar) (Zstar := thetaStar)
          (Z := fun z : EuclideanSpace ℝ r => z)
          (B := Bθ) a hBθ (by simpa [S] using hlimMem a)
          hThetaNormFourth hThetaNormFourthInt)
      (fun a c =>
        bootstrapUniformSquareTailIndexed_of_normFourth_coord_add
          (μ := μ)
          (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
          (Pstar := Pstar) (Zstar := thetaStar)
          (Z := fun z : EuclideanSpace ℝ r => z)
          (B := Bθ) a c hBθ
          (by simpa [S] using (hlimMem a).add (hlimMem c))
          hThetaNormFourth hThetaNormFourthInt)
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hcov
  exact ae_of_all μ fun _ => by
    simpa [S] using
      (multivariateGaussian_covarianceIntegralMat_eq
        (S := S) hS (by simpa [S] using hlimMem))

/-- Hansen Theorem 10.10/10.12 smooth-function conditional covariance
consistency from a compact-range quadratic Taylor-remainder envelope.

The fixed compact range gives deterministic coordinate and coordinate-sum
bounds, so this wrapper does not require a separate nonlinear norm-fourth
premise on `thetaStar`. -/
theorem
    chapter10_smooth_covarianceMat_tendsto_of_compact_range_quadratic_eventualBound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {BT : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInMeasure μ
      (bootstrapCovarianceMat Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  let S : Matrix r r ℝ := G * V * Gᵀ
  let Ccoord : r → ℝ := fun a =>
    Classical.choose (isCompact_abs_coord_bound hK a)
  let Csum : r → r → ℝ := fun a c =>
    Classical.choose (isCompact_abs_coord_add_bound hK a c)
  have hCcoord :
      ∀ a x, x ∈ K → |((x : EuclideanSpace ℝ r) : r → ℝ) a| ≤ Ccoord a := by
    intro a
    exact Classical.choose_spec (isCompact_abs_coord_bound hK a)
  have hCsum :
      ∀ a c x, x ∈ K →
        |((x : EuclideanSpace ℝ r) : r → ℝ) a +
          ((x : EuclideanSpace ℝ r) : r → ℝ) c| ≤ Csum a c := by
    intro a c
    exact Classical.choose_spec (isCompact_abs_coord_add_bound hK a c)
  have hS : S.PosSemidef := by
    dsimp [S]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.mul_mul_conjTranspose_same G
  have hGaussianEuclidean :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z) := by
    dsimp [S]
    exact
      chapter10_smooth_gaussian_of_compact_range_quadratic_normFourth
        (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
        (thetaStar := thetaStar) (ρ := ρ) (BT := BT) (V := V) G
        hV hT hK hPstar hTstar hthetaStar hlinearized_mem
        hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound
  have hGaussian :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hGaussianEuclidean (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hcov :
      TendstoInMeasure μ
        (bootstrapCovarianceMat Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
        atTop
        (fun _ => fun a c =>
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a *
              ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) *
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S)) :=
    chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      (Ccoord := Ccoord) (Csum := Csum)
      hPstar hcoordMem (by simpa [S] using hlimMem) hGaussian
      (fun a => Eventually.of_forall fun n ω ωs =>
        hCcoord a _ (hthetaStar_mem n ω ωs))
      (fun a c => Eventually.of_forall fun n ω ωs =>
        hCsum a c _ (hthetaStar_mem n ω ωs))
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hcov
  exact ae_of_all μ fun _ => by
    simpa [S] using
      (multivariateGaussian_covarianceIntegralMat_eq
        (S := S) hS (by simpa [S] using hlimMem))

/-- Indexed sample-size-dependent counterpart of
`chapter10_smooth_covarianceMat_tendsto_of_compact_range_quadratic_eventualBound`. -/
theorem
    chapter10_indexed_smooth_covarianceMat_tendsto_of_compact_range_quadratic_eventualBound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {BT : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap G (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap G (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2) :
    TendstoInMeasure μ
      (bootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  let S : Matrix r r ℝ := G * V * Gᵀ
  let Ccoord : r → ℝ := fun a =>
    Classical.choose (isCompact_abs_coord_bound hK a)
  let Csum : r → r → ℝ := fun a c =>
    Classical.choose (isCompact_abs_coord_add_bound hK a c)
  have hCcoord :
      ∀ a x, x ∈ K → |((x : EuclideanSpace ℝ r) : r → ℝ) a| ≤ Ccoord a := by
    intro a
    exact Classical.choose_spec (isCompact_abs_coord_bound hK a)
  have hCsum :
      ∀ a c x, x ∈ K →
        |((x : EuclideanSpace ℝ r) : r → ℝ) a +
          ((x : EuclideanSpace ℝ r) : r → ℝ) c| ≤ Csum a c := by
    intro a c
    exact Classical.choose_spec (isCompact_abs_coord_add_bound hK a c)
  have hS : S.PosSemidef := by
    dsimp [S]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.mul_mul_conjTranspose_same G
  have hGaussianEuclidean :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z) := by
    dsimp [S]
    exact
      chapter10_indexed_smooth_gaussian_of_compact_range_quadratic_normFourth
        (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
        (thetaStar := thetaStar) (ρ := ρ) (BT := BT) (V := V) G
        hV hT hK hPstar hTstar hthetaStar hlinearized_mem
        hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound
  have hGaussian :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hGaussianEuclidean (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hcov :
      TendstoInMeasure μ
        (bootstrapCovarianceMatIndexed Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
        atTop
        (fun _ => fun a c =>
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a *
              ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) *
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S)) :=
    chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      (Ccoord := Ccoord) (Csum := Csum)
      hPstar hcoordMem (by simpa [S] using hlimMem) hGaussian
      (fun a => Eventually.of_forall fun n ω ωs =>
        hCcoord a _ (hthetaStar_mem n ω ωs))
      (fun a c => Eventually.of_forall fun n ω ωs =>
        hCsum a c _ (hthetaStar_mem n ω ωs))
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hcov
  exact ae_of_all μ fun _ => by
    simpa [S] using
      (multivariateGaussian_covarianceIntegralMat_eq
        (S := S) hS (by simpa [S] using hlimMem))

/-- Hansen Theorem 10.10/10.12 smooth-function conditional covariance
consistency from exact derivative linearization and eventual deterministic
coordinate and coordinate-sum bounds.

The bounded-statistic Theorem 10.9 covariance route supplies the coordinate and
coordinate-sum uniform-square-tail premises, and the exact linearization
identifies the Gaussian target covariance as `G V Gᵀ`. -/
theorem
    chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_eventualBound_memLp
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Ccoord : r → ℝ} {Csum : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a +
          (thetaStar n ω ωs : r → ℝ) c)| ≤ Csum a c) :
    TendstoInMeasure μ
      (bootstrapCovarianceMat Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  let S : Matrix r r ℝ := G * V * Gᵀ
  have hS : S.PosSemidef := by
    dsimp [S]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.mul_mul_conjTranspose_same G
  have hGaussianEuclidean :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z) := by
    dsimp [S]
    exact
      chapter10_bootstrap_smooth_function_gaussian_of_linearization
        (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
        (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  have hGaussian :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hGaussianEuclidean (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hcov :
      TendstoInMeasure μ
        (bootstrapCovarianceMat Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
        atTop
        (fun _ => fun a c =>
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a *
              ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) *
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S)) :=
    chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      (Ccoord := Ccoord) (Csum := Csum)
      hPstar hcoordMem (by simpa [S] using hlimMem) hGaussian
      hboundCoord hboundSum
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hcov
  exact ae_of_all μ fun _ => by
    simpa [S] using
      (multivariateGaussian_covarianceIntegralMat_eq
        (S := S) hS (by simpa [S] using hlimMem))

/-- Indexed sample-size-dependent counterpart of
`chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_eventualBound_memLp`. -/
theorem
    chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_eventualBound_memLp
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Ccoord : r → ℝ} {Csum : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a +
          (thetaStar n ω ωs : r → ℝ) c)| ≤ Csum a c) :
    TendstoInMeasure μ
      (bootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  let S : Matrix r r ℝ := G * V * Gᵀ
  have hS : S.PosSemidef := by
    dsimp [S]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.mul_mul_conjTranspose_same G
  have hGaussianEuclidean :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z) := by
    dsimp [S]
    exact
      chapter10_indexed_bootstrap_smooth_function_gaussian_of_linearization
        (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
        (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  have hGaussian :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hGaussianEuclidean (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hcov :
      TendstoInMeasure μ
        (bootstrapCovarianceMatIndexed Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
        atTop
        (fun _ => fun a c =>
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a *
              ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) *
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S)) :=
    chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      (Ccoord := Ccoord) (Csum := Csum)
      hPstar hcoordMem (by simpa [S] using hlimMem) hGaussian
      hboundCoord hboundSum
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hcov
  exact ae_of_all μ fun _ => by
    simpa [S] using
      (multivariateGaussian_covarianceIntegralMat_eq
        (S := S) hS (by simpa [S] using hlimMem))

/-- Hansen Theorem 10.10/10.12 smooth-function conditional covariance
consistency from exact derivative linearization and a norm fourth-moment
premise on the underlying bootstrap statistic.

The norm fourth-moment premise supplies the coordinate and coordinate-sum
uniform-square-tail controls needed by the covariance-matrix version of
Theorem 10.9; the exact linearization supplies the smooth Gaussian weak limit
from Theorem 10.7. -/
theorem
    chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMat Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  let S : Matrix r r ℝ := G * V * Gᵀ
  have hS : S.PosSemidef := by
    dsimp [S]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.mul_mul_conjTranspose_same G
  have hGaussianEuclidean :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z) := by
    dsimp [S]
    exact
      chapter10_bootstrap_smooth_function_gaussian_of_linearization
        (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
        (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  have hGaussian :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hGaussianEuclidean (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hTailCoord :
      ∀ a,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
          (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) := by
    intro a
    exact
      bootstrapUniformSquareTail_of_linearization_coord_normFourth
        (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (Pstar := Pstar) (Tstar := Tstar)
        (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
        (B := B) G a hB (by simpa [S] using hlimMem a)
        (fun n ω ωs => by
          simpa [matrixContinuousLinearMap_apply] using
            congrArg (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
              (hlinearization n ω ωs))
        hNormFourth hNormFourthInt
  have hTailSum :
      ∀ a c,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs =>
            (thetaStar n ω ωs : r → ℝ) a +
              (thetaStar n ω ωs : r → ℝ) c)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
          (fun z : EuclideanSpace ℝ r =>
            (z : r → ℝ) a + (z : r → ℝ) c) := by
    intro a c
    let H : Matrix Unit d ℝ := fun _ j => G a j + G c j
    exact
      bootstrapUniformSquareTail_of_linearization_coord_normFourth
        (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (Pstar := Pstar) (Tstar := Tstar)
        (Zstar := fun n ω ωs =>
          (thetaStar n ω ωs : r → ℝ) a +
            (thetaStar n ω ωs : r → ℝ) c)
        (Z := fun z : EuclideanSpace ℝ r =>
          (z : r → ℝ) a + (z : r → ℝ) c)
        (B := B) H () hB
        (by simpa [S] using (hlimMem a).add (hlimMem c))
        (fun n ω ωs => by
          have ha :
              (thetaStar n ω ωs : r → ℝ) a =
                (G *ᵥ (Tstar n ω ωs).ofLp) a := by
            simpa [matrixContinuousLinearMap_apply] using
              congrArg (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
                (hlinearization n ω ωs)
          have hc :
              (thetaStar n ω ωs : r → ℝ) c =
                (G *ᵥ (Tstar n ω ωs).ofLp) c := by
            simpa [matrixContinuousLinearMap_apply] using
              congrArg (fun z : EuclideanSpace ℝ r => (z : r → ℝ) c)
                (hlinearization n ω ωs)
          change (thetaStar n ω ωs : r → ℝ) a +
              (thetaStar n ω ωs : r → ℝ) c =
            (((matrixContinuousLinearMap H (Tstar n ω ωs) :
              EuclideanSpace ℝ Unit) : Unit → ℝ) ())
          rw [ha, hc]
          simp [H, matrixContinuousLinearMap_apply, Matrix.mulVec, dotProduct,
            Finset.sum_add_distrib, add_mul])
        hNormFourth hNormFourthInt
  have hcov :
      TendstoInMeasure μ
        (bootstrapCovarianceMat Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
        atTop
        (fun _ => fun a c =>
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a *
              ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) *
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S)) :=
    chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hPstar hcoordMem (by simpa [S] using hlimMem) hGaussian
      hTailCoord hTailSum
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hcov
  exact ae_of_all μ fun _ => by
    simpa [S] using
      (multivariateGaussian_covarianceIntegralMat_eq
        (S := S) hS (by simpa [S] using hlimMem))

/-- Indexed sample-size-dependent counterpart of
`chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_normFourthMoment`. -/
theorem
    chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  let S : Matrix r r ℝ := G * V * Gᵀ
  have hS : S.PosSemidef := by
    dsimp [S]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.mul_mul_conjTranspose_same G
  have hGaussianEuclidean :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z) := by
    dsimp [S]
    exact
      chapter10_indexed_bootstrap_smooth_function_gaussian_of_linearization
        (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
        (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  have hGaussian :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hGaussianEuclidean (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hTailCoord :
      ∀ a,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
          (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) := by
    intro a
    exact
      bootstrapUniformSquareTailIndexed_of_linearization_coord_normFourth
        (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (Pstar := Pstar) (Tstar := Tstar)
        (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
        (B := B) G a hB (by simpa [S] using hlimMem a)
        (fun n ω ωs => by
          simpa [matrixContinuousLinearMap_apply] using
            congrArg (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
              (hlinearization n ω ωs))
        hNormFourth hNormFourthInt
  have hTailSum :
      ∀ a c,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs =>
            (thetaStar n ω ωs : r → ℝ) a +
              (thetaStar n ω ωs : r → ℝ) c)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
          (fun z : EuclideanSpace ℝ r =>
            (z : r → ℝ) a + (z : r → ℝ) c) := by
    intro a c
    let H : Matrix Unit d ℝ := fun _ j => G a j + G c j
    exact
      bootstrapUniformSquareTailIndexed_of_linearization_coord_normFourth
        (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (Pstar := Pstar) (Tstar := Tstar)
        (Zstar := fun n ω ωs =>
          (thetaStar n ω ωs : r → ℝ) a +
            (thetaStar n ω ωs : r → ℝ) c)
        (Z := fun z : EuclideanSpace ℝ r =>
          (z : r → ℝ) a + (z : r → ℝ) c)
        (B := B) H () hB
        (by simpa [S] using (hlimMem a).add (hlimMem c))
        (fun n ω ωs => by
          have ha :
              (thetaStar n ω ωs : r → ℝ) a =
                (G *ᵥ (Tstar n ω ωs).ofLp) a := by
            simpa [matrixContinuousLinearMap_apply] using
              congrArg (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
                (hlinearization n ω ωs)
          have hc :
              (thetaStar n ω ωs : r → ℝ) c =
                (G *ᵥ (Tstar n ω ωs).ofLp) c := by
            simpa [matrixContinuousLinearMap_apply] using
              congrArg (fun z : EuclideanSpace ℝ r => (z : r → ℝ) c)
                (hlinearization n ω ωs)
          change (thetaStar n ω ωs : r → ℝ) a +
              (thetaStar n ω ωs : r → ℝ) c =
            (((matrixContinuousLinearMap H (Tstar n ω ωs) :
              EuclideanSpace ℝ Unit) : Unit → ℝ) ())
          rw [ha, hc]
          simp [H, matrixContinuousLinearMap_apply, Matrix.mulVec, dotProduct,
            Finset.sum_add_distrib, add_mul])
        hNormFourth hNormFourthInt
  have hcov :
      TendstoInMeasure μ
        (bootstrapCovarianceMatIndexed Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
        atTop
        (fun _ => fun a c =>
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a *
              ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) *
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S)) :=
    chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hPstar hcoordMem (by simpa [S] using hlimMem) hGaussian
      hTailCoord hTailSum
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hcov
  exact ae_of_all μ fun _ => by
    simpa [S] using
      (multivariateGaussian_covarianceIntegralMat_eq
        (S := S) hS (by simpa [S] using hlimMem))

/-- Smooth exact-linearization covariance route with Gaussian-limit coordinate
`MemLp 2` premises discharged automatically. -/
theorem
    chapter10_smooth_covarianceMat_linearization_normFourth_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {B : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMat Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_normFourthMoment
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
    (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
    hlinearization hB hNormFourth hNormFourthInt

/-- Indexed smooth exact-linearization covariance route with automatic
Gaussian-limit coordinate `MemLp 2` premises. -/
theorem
    chapter10_indexed_smooth_covarianceMat_linearization_normFourth_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {B : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_normFourthMoment
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
    (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
    (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
    hlinearization hB hNormFourth hNormFourthInt

/-- Hansen Theorem 10.10/10.12 smooth-function conditional covariance
consistency from exact derivative linearization and linearized coordinate and
coordinate-sum fourth-moment premises.

This is the coordinate-fourth-moment counterpart of the norm-fourth covariance
route: exact linearization rewrites the smooth statistic's coordinate and
coordinate-sum fourth moments to the derivative-linearized statistic before
the covariance fourth-moment constructor is applied. -/
theorem
    chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_fourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Bcoord : r → ℝ} {Bsum : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoordLinear :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordLinearInt :
      ∀ n ω a,
        Integrable
          (fun ωs =>
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4)
          (Pstar n ω))
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSumLinear :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              ((((matrixContinuousLinearMap G (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) a) +
                (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                  EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumLinearInt :
      ∀ n ω a c,
        Integrable
          (fun ωs =>
            ((((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) +
              (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4)
          (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMat Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  let S : Matrix r r ℝ := G * V * Gᵀ
  have hS : S.PosSemidef := by
    dsimp [S]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.mul_mul_conjTranspose_same G
  have hGaussianEuclidean :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z) := by
    dsimp [S]
    exact
      chapter10_bootstrap_smooth_function_gaussian_of_linearization
        (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
        (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  have hGaussian :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hGaussianEuclidean (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hFourthCoordTheta :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs, ((thetaStar n ω ωs : r → ℝ) a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a) := by
    intro a
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl
      (hFourthCoordLinear a)
    refine ae_of_all μ fun ω => ?_
    have hfun :
        (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 4) =
          fun ωs =>
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 := by
      funext ωs
      rw [hlinearization n ω ωs]
    simp [hfun]
  have hFourthCoordThetaInt :
      ∀ n ω a,
        Integrable (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 4)
          (Pstar n ω) := by
    intro n ω a
    have hfun :
        (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 4) =
          fun ωs =>
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 := by
      funext ωs
      rw [hlinearization n ω ωs]
    simpa [hfun] using hFourthCoordLinearInt n ω a
  have hFourthSumTheta :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              ((thetaStar n ω ωs : r → ℝ) a +
                (thetaStar n ω ωs : r → ℝ) c) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c) := by
    intro a c
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl
      (hFourthSumLinear a c)
    refine ae_of_all μ fun ω => ?_
    have hfun :
        (fun ωs =>
          ((thetaStar n ω ωs : r → ℝ) a +
            (thetaStar n ω ωs : r → ℝ) c) ^ 4) =
          fun ωs =>
            ((((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) +
              (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4 := by
      funext ωs
      rw [hlinearization n ω ωs]
    simp [hfun]
  have hFourthSumThetaInt :
      ∀ n ω a c,
        Integrable
          (fun ωs =>
            ((thetaStar n ω ωs : r → ℝ) a +
              (thetaStar n ω ωs : r → ℝ) c) ^ 4)
          (Pstar n ω) := by
    intro n ω a c
    have hfun :
        (fun ωs =>
          ((thetaStar n ω ωs : r → ℝ) a +
            (thetaStar n ω ωs : r → ℝ) c) ^ 4) =
          fun ωs =>
            ((((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) +
              (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4 := by
      funext ωs
      rw [hlinearization n ω ωs]
    simpa [hfun] using hFourthSumLinearInt n ω a c
  have hcov :
      TendstoInMeasure μ
        (bootstrapCovarianceMat Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
        atTop
        (fun _ => fun a c =>
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a *
              ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) *
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S)) :=
    chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_fourthMoment_memLp_limit
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      (Bcoord := Bcoord) (Bsum := Bsum)
      hPstar hcoordMem (by simpa [S] using hlimMem) hGaussian
      hBcoord hFourthCoordTheta hFourthCoordThetaInt
      hBsum hFourthSumTheta hFourthSumThetaInt
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hcov
  exact ae_of_all μ fun _ => by
    simpa [S] using
      (multivariateGaussian_covarianceIntegralMat_eq
        (S := S) hS (by simpa [S] using hlimMem))

/-- Indexed sample-size-dependent counterpart of
`chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_fourthMoment`. -/
theorem
    chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_fourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Bcoord : r → ℝ} {Bsum : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoordLinear :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordLinearInt :
      ∀ n ω a,
        Integrable
          (fun ωs =>
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4)
          (Pstar n ω))
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSumLinear :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              ((((matrixContinuousLinearMap G (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) a) +
                (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                  EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumLinearInt :
      ∀ n ω a c,
        Integrable
          (fun ωs =>
            ((((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) +
              (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4)
          (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  let S : Matrix r r ℝ := G * V * Gᵀ
  have hS : S.PosSemidef := by
    dsimp [S]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.mul_mul_conjTranspose_same G
  have hGaussianEuclidean :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z) := by
    dsimp [S]
    exact
      chapter10_indexed_bootstrap_smooth_function_gaussian_of_linearization
        (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
        (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  have hGaussian :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hGaussianEuclidean (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hFourthCoordTheta :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs, ((thetaStar n ω ωs : r → ℝ) a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a) := by
    intro a
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl
      (hFourthCoordLinear a)
    refine ae_of_all μ fun ω => ?_
    have hfun :
        (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 4) =
          fun ωs =>
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 := by
      funext ωs
      rw [hlinearization n ω ωs]
    simp [hfun]
  have hFourthCoordThetaInt :
      ∀ n ω a,
        Integrable (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 4)
          (Pstar n ω) := by
    intro n ω a
    have hfun :
        (fun ωs => ((thetaStar n ω ωs : r → ℝ) a) ^ 4) =
          fun ωs =>
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 := by
      funext ωs
      rw [hlinearization n ω ωs]
    simpa [hfun] using hFourthCoordLinearInt n ω a
  have hFourthSumTheta :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              ((thetaStar n ω ωs : r → ℝ) a +
                (thetaStar n ω ωs : r → ℝ) c) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c) := by
    intro a c
    refine TendstoInMeasure.congr (fun n => ?_) EventuallyEq.rfl
      (hFourthSumLinear a c)
    refine ae_of_all μ fun ω => ?_
    have hfun :
        (fun ωs =>
          ((thetaStar n ω ωs : r → ℝ) a +
            (thetaStar n ω ωs : r → ℝ) c) ^ 4) =
          fun ωs =>
            ((((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) +
              (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4 := by
      funext ωs
      rw [hlinearization n ω ωs]
    simp [hfun]
  have hFourthSumThetaInt :
      ∀ n ω a c,
        Integrable
          (fun ωs =>
            ((thetaStar n ω ωs : r → ℝ) a +
              (thetaStar n ω ωs : r → ℝ) c) ^ 4)
          (Pstar n ω) := by
    intro n ω a c
    have hfun :
        (fun ωs =>
          ((thetaStar n ω ωs : r → ℝ) a +
            (thetaStar n ω ωs : r → ℝ) c) ^ 4) =
          fun ωs =>
            ((((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) +
              (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4 := by
      funext ωs
      rw [hlinearization n ω ωs]
    simpa [hfun] using hFourthSumLinearInt n ω a c
  have hcov :
      TendstoInMeasure μ
        (bootstrapCovarianceMatIndexed Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
        atTop
        (fun _ => fun a c =>
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a *
              ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) *
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S)) :=
    chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_fourthMoment_memLp_limit
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      (Bcoord := Bcoord) (Bsum := Bsum)
      hPstar hcoordMem (by simpa [S] using hlimMem) hGaussian
      hBcoord hFourthCoordTheta hFourthCoordThetaInt
      hBsum hFourthSumTheta hFourthSumThetaInt
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hcov
  exact ae_of_all μ fun _ => by
    simpa [S] using
      (multivariateGaussian_covarianceIntegralMat_eq
        (S := S) hS (by simpa [S] using hlimMem))

/-- Smooth exact-linearization covariance route from coordinate and
coordinate-sum fourth-moment premises, with Gaussian-limit coordinate
`MemLp 2` premises discharged automatically. -/
theorem
    chapter10_smooth_covarianceMat_linearization_fourthMoment_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {Bcoord : r → ℝ} {Bsum : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoordLinear :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordLinearInt :
      ∀ n ω a,
        Integrable
          (fun ωs =>
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4)
          (Pstar n ω))
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSumLinear :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              ((((matrixContinuousLinearMap G (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) a) +
                (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                  EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumLinearInt :
      ∀ n ω a c,
        Integrable
          (fun ωs =>
            ((((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) +
              (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4)
          (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMat Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hBcoord hFourthCoordLinear hFourthCoordLinearInt
      hBsum hFourthSumLinear hFourthSumLinearInt

/-- Indexed smooth exact-linearization covariance route from coordinate and
coordinate-sum fourth-moment premises, with Gaussian-limit coordinate
`MemLp 2` premises discharged automatically. -/
theorem
    chapter10_indexed_smooth_covarianceMat_linearization_fourthMoment_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {Bcoord : r → ℝ} {Bsum : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoordLinear :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordLinearInt :
      ∀ n ω a,
        Integrable
          (fun ωs =>
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4)
          (Pstar n ω))
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSumLinear :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              ((((matrixContinuousLinearMap G (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) a) +
                (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                  EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumLinearInt :
      ∀ n ω a c,
        Integrable
          (fun ωs =>
            ((((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) +
              (((matrixContinuousLinearMap G (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4)
          (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      atTop (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hBcoord hFourthCoordLinear hFourthCoordLinearInt
      hBsum hFourthSumLinear hFourthSumLinearInt

/-- Smooth exact-linearization scalar variance route with the automatic
Gaussian-limit coordinate `MemLp 2` premise discharged. -/
theorem
    chapter10_smooth_bootstrap_variance_linearization_normFourth_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceReal Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_smooth_bootstrap_variance_consistency_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt

/-- Indexed smooth exact-linearization scalar variance route with the
automatic Gaussian-limit coordinate `MemLp 2` premise discharged. -/
theorem
    chapter10_indexed_smooth_bootstrap_variance_linearization_normFourth_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt

/-- Smooth exact-linearization scalar variance route from a linearized
coordinate fourth-moment premise, with the automatic Gaussian-limit coordinate
`MemLp 2` premise discharged. -/
theorem
    chapter10_smooth_bootstrap_variance_linearization_fourthMoment_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hB : 0 ≤ B)
    (hFourthLinear :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthLinearInt :
      ∀ n ω,
        Integrable
          (fun ωs =>
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4)
          (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceReal Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_smooth_bootstrap_variance_consistency_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hFourthLinear hFourthLinearInt

/-- Indexed smooth exact-linearization scalar variance route from a
linearized coordinate fourth-moment premise, with the automatic Gaussian-limit
coordinate `MemLp 2` premise discharged. -/
theorem
    chapter10_indexed_smooth_bootstrap_variance_linearization_fourthMoment_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hB : 0 ≤ B)
    (hFourthLinear :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthLinearInt :
      ∀ n ω,
        Integrable
          (fun ωs =>
            (((matrixContinuousLinearMap G (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4)
          (Pstar n ω)) :
    TendstoInMeasure μ
      (bootstrapVarianceRealIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a))
      atTop
        (fun _ =>
          ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hFourthLinear hFourthLinearInt

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

/-- Trimming changes the bootstrap statistic only on the large-norm tail. -/
theorem norm_sub_trimmedBootstrapStatistic_le_tail_norm
    {k : Type*} [Fintype k]
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω) (ωs : Ωs) :
    ‖Zstar n ω ωs - trimmedBootstrapStatistic Zstar τ n ω ωs‖ ≤
      Set.indicator {ωs | τ n < ‖Zstar n ω ωs‖}
        (fun ωs => ‖Zstar n ω ωs‖) ωs := by
  by_cases htrim : ‖Zstar n ω ωs‖ ≤ τ n
  · have hnot :
        ωs ∉ {x | τ n < ‖Zstar n ω x‖} := by
      simpa using not_lt.mpr htrim
    simp [trimmedBootstrapStatistic, htrim, hnot]
  · have htail :
        ωs ∈ {x | τ n < ‖Zstar n ω x‖} := by
      simpa using lt_of_not_ge htrim
    simp [trimmedBootstrapStatistic, htrim, htail]

/-- Coordinate version of `norm_sub_trimmedBootstrapStatistic_le_tail_norm`. -/
theorem abs_sub_trimmedBootstrapStatistic_apply_le_tail_norm
    {k : Type*} [Fintype k]
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω) (ωs : Ωs) (a : k) :
    |Zstar n ω ωs a - trimmedBootstrapStatistic Zstar τ n ω ωs a| ≤
      Set.indicator {ωs | τ n < ‖Zstar n ω ωs‖}
        (fun ωs => ‖Zstar n ω ωs‖) ωs := by
  have hcoord :
      |Zstar n ω ωs a - trimmedBootstrapStatistic Zstar τ n ω ωs a| ≤
        ‖Zstar n ω ωs - trimmedBootstrapStatistic Zstar τ n ω ωs‖ := by
    simpa [Pi.sub_apply, Real.norm_eq_abs] using
      norm_le_pi_norm
        (Zstar n ω ωs - trimmedBootstrapStatistic Zstar τ n ω ωs) a
  exact hcoord.trans
    (norm_sub_trimmedBootstrapStatistic_le_tail_norm
      (Zstar := Zstar) (τ := τ) n ω ωs)

/-- Indexed trimming changes the bootstrap statistic only on the large-norm
tail. -/
theorem norm_sub_trimmedBootstrapStatisticIndexed_le_tail_norm
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω) (ωs : Ωboot n) :
    ‖Zstar n ω ωs - trimmedBootstrapStatisticIndexed Zstar τ n ω ωs‖ ≤
      Set.indicator {ωs | τ n < ‖Zstar n ω ωs‖}
        (fun ωs => ‖Zstar n ω ωs‖) ωs := by
  by_cases htrim : ‖Zstar n ω ωs‖ ≤ τ n
  · have hnot :
        ωs ∉ {x | τ n < ‖Zstar n ω x‖} := by
      simpa using not_lt.mpr htrim
    simp [trimmedBootstrapStatisticIndexed, htrim, hnot]
  · have htail :
        ωs ∈ {x | τ n < ‖Zstar n ω x‖} := by
      simpa using lt_of_not_ge htrim
    simp [trimmedBootstrapStatisticIndexed, htrim, htail]

/-- Indexed coordinate version of
`norm_sub_trimmedBootstrapStatisticIndexed_le_tail_norm`. -/
theorem abs_sub_trimmedBootstrapStatisticIndexed_apply_le_tail_norm
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω) (ωs : Ωboot n) (a : k) :
    |Zstar n ω ωs a -
      trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a| ≤
      Set.indicator {ωs | τ n < ‖Zstar n ω ωs‖}
        (fun ωs => ‖Zstar n ω ωs‖) ωs := by
  have hcoord :
      |Zstar n ω ωs a -
        trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a| ≤
        ‖Zstar n ω ωs -
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs‖ := by
    simpa [Pi.sub_apply, Real.norm_eq_abs] using
      norm_le_pi_norm
        (Zstar n ω ωs -
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs) a
  exact hcoord.trans
    (norm_sub_trimmedBootstrapStatisticIndexed_le_tail_norm
      (Zstar := Zstar) (τ := τ) n ω ωs)

/-- Bounded-continuous test-function integrals of `Z**` and `Z*` differ only
on the original large-norm trimming tail. -/
theorem abs_bootstrapBoundedContinuousIntegral_trimmedBootstrapStatistic_sub_le_tailProb
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (f : BoundedContinuousFunction (k → ℝ) ℝ) (n : ℕ) (ω : Ω) :
    |bootstrapBoundedContinuousIntegral Pstar
        (trimmedBootstrapStatistic Zstar τ) f n ω -
      bootstrapBoundedContinuousIntegral Pstar Zstar f n ω| ≤
      2 * ‖f‖ *
        ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal := by
  classical
  haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
  let tail : Set Ωs := {ωs | τ n < ‖Zstar n ω ωs‖}
  have hnorm_meas : Measurable fun ωs => ‖Zstar n ω ωs‖ :=
    continuous_norm.measurable.comp (hZmeas n ω)
  have htail_meas : MeasurableSet tail := by
    simpa [tail] using measurableSet_lt measurable_const hnorm_meas
  have htrimSet_meas : MeasurableSet {ωs | ‖Zstar n ω ωs‖ ≤ τ n} := by
    exact measurableSet_le hnorm_meas measurable_const
  have htrim_meas :
      Measurable fun ωs => trimmedBootstrapStatistic Zstar τ n ω ωs := by
    simpa [trimmedBootstrapStatistic] using
      Measurable.ite htrimSet_meas (hZmeas n ω) measurable_const
  have htrim_int :
      Integrable
        (fun ωs => f (trimmedBootstrapStatistic Zstar τ n ω ωs))
        (Pstar n ω) := by
    refine Integrable.of_bound
      ((f.continuous.measurable.comp htrim_meas).aestronglyMeasurable)
      ‖f‖ ?_
    exact ae_of_all (Pstar n ω) fun _ => f.norm_coe_le_norm _
  have hstar_int :
      Integrable (fun ωs => f (Zstar n ω ωs)) (Pstar n ω) := by
    refine Integrable.of_bound
      ((f.continuous.measurable.comp (hZmeas n ω)).aestronglyMeasurable)
      ‖f‖ ?_
    exact ae_of_all (Pstar n ω) fun _ => f.norm_coe_le_norm _
  have hbound_point :
      ∀ ωs,
        ‖f (trimmedBootstrapStatistic Zstar τ n ω ωs) -
            f (Zstar n ω ωs)‖ ≤
          tail.indicator (fun _ => 2 * ‖f‖) ωs := by
    intro ωs
    by_cases htail : ωs ∈ tail
    · rw [Set.indicator_of_mem htail]
      calc
        ‖f (trimmedBootstrapStatistic Zstar τ n ω ωs) -
            f (Zstar n ω ωs)‖ ≤
            ‖f (trimmedBootstrapStatistic Zstar τ n ω ωs)‖ +
              ‖f (Zstar n ω ωs)‖ := norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ :=
            add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
        _ = 2 * ‖f‖ := by ring
    · have hnot : ¬ τ n < ‖Zstar n ω ωs‖ := by
        simpa [tail] using htail
      have htrim : ‖Zstar n ω ωs‖ ≤ τ n := le_of_not_gt hnot
      rw [Set.indicator_of_notMem htail]
      simp [trimmedBootstrapStatistic, htrim]
  have hbound_int :
      ‖∫ ωs,
          f (trimmedBootstrapStatistic Zstar τ n ω ωs) -
            f (Zstar n ω ωs) ∂Pstar n ω‖ ≤
        ∫ ωs, tail.indicator (fun _ => 2 * ‖f‖) ωs ∂Pstar n ω := by
    have hIntBound :
        Integrable (fun ωs => tail.indicator (fun _ => 2 * ‖f‖) ωs)
          (Pstar n ω) :=
      (integrable_const (2 * ‖f‖)).indicator htail_meas
    exact norm_integral_le_of_norm_le hIntBound
      (ae_of_all (Pstar n ω) hbound_point)
  have hdiff_eq :
      bootstrapBoundedContinuousIntegral Pstar
          (trimmedBootstrapStatistic Zstar τ) f n ω -
        bootstrapBoundedContinuousIntegral Pstar Zstar f n ω =
      ∫ ωs,
        f (trimmedBootstrapStatistic Zstar τ n ω ωs) -
          f (Zstar n ω ωs) ∂Pstar n ω := by
    simpa [bootstrapBoundedContinuousIntegral] using
      (integral_sub htrim_int hstar_int).symm
  calc
    |bootstrapBoundedContinuousIntegral Pstar
        (trimmedBootstrapStatistic Zstar τ) f n ω -
      bootstrapBoundedContinuousIntegral Pstar Zstar f n ω| =
        ‖∫ ωs,
          f (trimmedBootstrapStatistic Zstar τ n ω ωs) -
            f (Zstar n ω ωs) ∂Pstar n ω‖ := by
          rw [hdiff_eq]
          rfl
    _ ≤ ∫ ωs, tail.indicator (fun _ => 2 * ‖f‖) ωs ∂Pstar n ω := hbound_int
    _ = 2 * ‖f‖ *
        ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal := by
          rw [integral_indicator_const (2 * ‖f‖) htail_meas]
          simp [tail, measureReal_def, smul_eq_mul, mul_comm, mul_assoc]

/-- Indexed bounded-continuous test-function integrals of `Z**` and `Z*`
differ only on the original large-norm trimming tail. -/
theorem
    abs_bootstrapBoundedContinuousIntegral_trimmedBootstrapStatisticIndexed_sub_le_tailProb
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    (hPstar : ∀ n ω, IsFiniteMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (f : BoundedContinuousFunction (k → ℝ) ℝ) (n : ℕ) (ω : Ω) :
    |bootstrapBoundedContinuousIntegralIndexed Pstar
        (trimmedBootstrapStatisticIndexed Zstar τ) f n ω -
      bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω| ≤
      2 * ‖f‖ *
        ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal := by
  classical
  haveI : IsFiniteMeasure (Pstar n ω) := hPstar n ω
  let tail : Set (Ωboot n) := {ωs | τ n < ‖Zstar n ω ωs‖}
  have hnorm_meas : Measurable fun ωs => ‖Zstar n ω ωs‖ :=
    continuous_norm.measurable.comp (hZmeas n ω)
  have htail_meas : MeasurableSet tail := by
    simpa [tail] using measurableSet_lt measurable_const hnorm_meas
  have htrimSet_meas : MeasurableSet {ωs | ‖Zstar n ω ωs‖ ≤ τ n} := by
    exact measurableSet_le hnorm_meas measurable_const
  have htrim_meas :
      Measurable fun ωs => trimmedBootstrapStatisticIndexed Zstar τ n ω ωs := by
    simpa [trimmedBootstrapStatisticIndexed] using
      Measurable.ite htrimSet_meas (hZmeas n ω) measurable_const
  have htrim_int :
      Integrable
        (fun ωs => f (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs))
        (Pstar n ω) := by
    refine Integrable.of_bound
      ((f.continuous.measurable.comp htrim_meas).aestronglyMeasurable)
      ‖f‖ ?_
    exact ae_of_all (Pstar n ω) fun _ => f.norm_coe_le_norm _
  have hstar_int :
      Integrable (fun ωs => f (Zstar n ω ωs)) (Pstar n ω) := by
    refine Integrable.of_bound
      ((f.continuous.measurable.comp (hZmeas n ω)).aestronglyMeasurable)
      ‖f‖ ?_
    exact ae_of_all (Pstar n ω) fun _ => f.norm_coe_le_norm _
  have hbound_point :
      ∀ ωs,
        ‖f (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs) -
            f (Zstar n ω ωs)‖ ≤
          tail.indicator (fun _ => 2 * ‖f‖) ωs := by
    intro ωs
    by_cases htail : ωs ∈ tail
    · rw [Set.indicator_of_mem htail]
      calc
        ‖f (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs) -
            f (Zstar n ω ωs)‖ ≤
            ‖f (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs)‖ +
              ‖f (Zstar n ω ωs)‖ := norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ :=
            add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
        _ = 2 * ‖f‖ := by ring
    · have hnot : ¬ τ n < ‖Zstar n ω ωs‖ := by
        simpa [tail] using htail
      have htrim : ‖Zstar n ω ωs‖ ≤ τ n := le_of_not_gt hnot
      rw [Set.indicator_of_notMem htail]
      simp [trimmedBootstrapStatisticIndexed, htrim]
  have hbound_int :
      ‖∫ ωs,
          f (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs) -
            f (Zstar n ω ωs) ∂Pstar n ω‖ ≤
        ∫ ωs, tail.indicator (fun _ => 2 * ‖f‖) ωs ∂Pstar n ω := by
    have hIntBound :
        Integrable (fun ωs => tail.indicator (fun _ => 2 * ‖f‖) ωs)
          (Pstar n ω) :=
      (integrable_const (2 * ‖f‖)).indicator htail_meas
    exact norm_integral_le_of_norm_le hIntBound
      (ae_of_all (Pstar n ω) hbound_point)
  have hdiff_eq :
      bootstrapBoundedContinuousIntegralIndexed Pstar
          (trimmedBootstrapStatisticIndexed Zstar τ) f n ω -
        bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω =
      ∫ ωs,
        f (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs) -
          f (Zstar n ω ωs) ∂Pstar n ω := by
    simpa [bootstrapBoundedContinuousIntegralIndexed] using
      (integral_sub htrim_int hstar_int).symm
  calc
    |bootstrapBoundedContinuousIntegralIndexed Pstar
        (trimmedBootstrapStatisticIndexed Zstar τ) f n ω -
      bootstrapBoundedContinuousIntegralIndexed Pstar Zstar f n ω| =
        ‖∫ ωs,
          f (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs) -
            f (Zstar n ω ωs) ∂Pstar n ω‖ := by
          rw [hdiff_eq]
          rfl
    _ ≤ ∫ ωs, tail.indicator (fun _ => 2 * ‖f‖) ωs ∂Pstar n ω := hbound_int
    _ = 2 * ‖f‖ *
        ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal := by
          rw [integral_indicator_const (2 * ‖f‖) htail_meas]
          simp [tail, measureReal_def, smul_eq_mul, mul_comm, mul_assoc]

/-- Markov bound for a strict large-norm tail.

This is the trimming-tail form used by Hansen Theorem 10.12: if the trimming
threshold is positive, the conditional probability of `τ < ‖Z*‖` is bounded by
`τ⁻² E*[‖Z*‖²]`. -/
theorem measure_strict_norm_gt_le_inv_sq_mul_integral_norm_sq
    [NormedAddCommGroup E]
    {P : Measure Ωs} {Z : Ωs → E} (hP : IsProbabilityMeasure P)
    (hZ : MemLp Z 2 P) {τ : ℝ} (hτ : 0 < τ) :
    (P {ωs | τ < ‖Z ωs‖}).toReal ≤
      (τ ^ 2)⁻¹ * ∫ ωs, ‖Z ωs‖ ^ 2 ∂P := by
  haveI : IsProbabilityMeasure P := hP
  let A : Set Ωs := {ωs | τ < ‖Z ωs‖}
  let B : Set Ωs := {ωs | τ ^ 2 ≤ ‖Z ωs‖ ^ 2}
  have hAB : A ⊆ B := by
    intro ωs hωs
    have hnorm : τ ≤ ‖Z ωs‖ := le_of_lt hωs
    exact pow_le_pow_left₀ hτ.le hnorm 2
  have hA_le_B : P.real A ≤ P.real B := measureReal_mono hAB
  have hInt : Integrable (fun ωs => ‖Z ωs‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hZ.1).1 hZ
  have hmarkov :
      τ ^ 2 * P.real B ≤ ∫ ωs, ‖Z ωs‖ ^ 2 ∂P := by
    simpa [B] using
      (mul_meas_ge_le_integral_of_nonneg
        (μ := P) (f := fun ωs => ‖Z ωs‖ ^ 2)
        (ae_of_all _ fun ωs => pow_nonneg (norm_nonneg (Z ωs)) 2)
        hInt (τ ^ 2))
  have hB_le :
      P.real B ≤ (τ ^ 2)⁻¹ * ∫ ωs, ‖Z ωs‖ ^ 2 ∂P :=
    (le_inv_mul_iff₀ (sq_pos_of_pos hτ)).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmarkov)
  calc
    (P {ωs | τ < ‖Z ωs‖}).toReal = P.real A := by
      simp [A, measureReal_def]
    _ ≤ P.real B := hA_le_B
    _ ≤ (τ ^ 2)⁻¹ * ∫ ωs, ‖Z ωs‖ ^ 2 ∂P := hB_le

/-- Fixed-space trimming-tail constructor from a diverging threshold and a
bounded conditional second moment.

The deterministic premise `((τ n)^2)⁻¹ -> 0` is the formal diverging-threshold
input.  Conditional second-moment convergence then makes the large-norm tail
probability `P*(τ_n < ‖Z*_n‖)` vanish in ordinary probability. -/
theorem trimmedTailProb_tendsto_zero_of_integral_norm_sq
    [NormedAddCommGroup E]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → E}
    {τ : ℕ → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => B)) :
    TendstoInMeasure μ
      (fun n ω => ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
      atTop (fun _ => 0) := by
  have hscale :
      TendstoInMeasure μ (fun n (_ : Ω) => ((τ n) ^ 2)⁻¹)
        atTop (fun _ => 0) :=
    tendstoInMeasure_const_real (μ := μ) hτinv
  have hprod :
      TendstoInMeasure μ
        (fun n ω =>
          ((τ n) ^ 2)⁻¹ *
            ∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => 0) := by
    simpa using TendstoInMeasure.mul_limits_real hscale hSecond
  refine tendstoInMeasure_zero_of_nonneg_le (μ := μ) ?_ ?_ hprod
  · intro n ω
    exact ENNReal.toReal_nonneg
  · intro n ω
    exact
      measure_strict_norm_gt_le_inv_sq_mul_integral_norm_sq
        (P := Pstar n ω) (Z := Zstar n ω) (hPstar n ω)
        (hZ n ω) (hτpos n)

/-- Indexed trimming-tail constructor from a diverging threshold and a bounded
conditional second moment. -/
theorem trimmedTailProbIndexed_tendsto_zero_of_integral_norm_sq
    [NormedAddCommGroup E]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → E}
    {τ : ℕ → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZ : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => B)) :
    TendstoInMeasure μ
      (fun n ω => ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
      atTop (fun _ => 0) := by
  have hscale :
      TendstoInMeasure μ (fun n (_ : Ω) => ((τ n) ^ 2)⁻¹)
        atTop (fun _ => 0) :=
    tendstoInMeasure_const_real (μ := μ) hτinv
  have hprod :
      TendstoInMeasure μ
        (fun n ω =>
          ((τ n) ^ 2)⁻¹ *
            ∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => 0) := by
    simpa using TendstoInMeasure.mul_limits_real hscale hSecond
  refine tendstoInMeasure_zero_of_nonneg_le (μ := μ) ?_ ?_ hprod
  · intro n ω
    exact ENNReal.toReal_nonneg
  · intro n ω
    exact
      measure_strict_norm_gt_le_inv_sq_mul_integral_norm_sq
        (P := Pstar n ω) (Z := Zstar n ω) (hPstar n ω)
        (hZ n ω) (hτpos n)

/-- If the original large-norm trimming tail has conditional probability
`oₚ(1)`, weak bootstrap convergence transfers from `Z*` to `Z**`. -/
theorem TendstoInBootstrapWeakDistribution.trimmedBootstrapStatistic_of_tailProb
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (trimmedBootstrapStatistic Zstar τ) ν Z := by
  refine hweak.of_integral_difference_zero ?_
  intro f
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hscaled :
      TendstoInMeasure μ
        (fun n ω =>
          (2 * ‖f‖) *
            ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
        atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real (μ := μ) (2 * ‖f‖) hTailProb
  refine TendstoInMeasure.of_abs_le_zero_real hscaled ?_
  intro n ω
  have hbound :=
    abs_bootstrapBoundedContinuousIntegral_trimmedBootstrapStatistic_sub_le_tailProb
      (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
      hPstarFinite hZmeas f n ω
  have htail_nonneg :
      0 ≤
        (2 * ‖f‖) *
          ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal :=
    mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg f)) ENNReal.toReal_nonneg
  simpa [abs_of_nonneg htail_nonneg] using hbound

/-- Fixed-space weak-transfer constructor for Hansen's trimmed statistic from
conditional second moments and a diverging trim threshold. -/
theorem TendstoInBootstrapWeakDistribution.trimmed_of_integral_norm_sq
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → k → ℝ} {B : ℝ}
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => B)) :
    TendstoInBootstrapWeakDistribution μ Pstar
      (trimmedBootstrapStatistic Zstar τ) ν Z :=
  hweak.trimmedBootstrapStatistic_of_tailProb hPstar hZmeas
    (trimmedTailProb_tendsto_zero_of_integral_norm_sq
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
      hPstar hZmem hτpos hτinv hSecond)

/-- Indexed version of
`TendstoInBootstrapWeakDistribution.trimmedBootstrapStatistic_of_tailProb`. -/
theorem
    TendstoInBootstrapWeakDistributionIndexed.trimmedBootstrapStatistic_of_tailProb
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → k → ℝ}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
        atTop (fun _ => 0)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (trimmedBootstrapStatisticIndexed Zstar τ) ν Z := by
  refine hweak.of_integral_difference_zero ?_
  intro f
  have hPstarFinite : ∀ n ω, IsFiniteMeasure (Pstar n ω) := by
    intro n ω
    haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
    infer_instance
  have hscaled :
      TendstoInMeasure μ
        (fun n ω =>
          (2 * ‖f‖) *
            ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
        atTop (fun _ => 0) :=
    TendstoInMeasure.const_mul_zero_real (μ := μ) (2 * ‖f‖) hTailProb
  refine TendstoInMeasure.of_abs_le_zero_real hscaled ?_
  intro n ω
  have hbound :=
    abs_bootstrapBoundedContinuousIntegral_trimmedBootstrapStatisticIndexed_sub_le_tailProb
      (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
      hPstarFinite hZmeas f n ω
  have htail_nonneg :
      0 ≤
        (2 * ‖f‖) *
          ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal :=
    mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg f)) ENNReal.toReal_nonneg
  simpa [abs_of_nonneg htail_nonneg] using hbound

/-- Indexed weak-transfer constructor for Hansen's trimmed statistic from
conditional second moments and a diverging trim threshold. -/
theorem TendstoInBootstrapWeakDistributionIndexed.trimmed_of_integral_norm_sq
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → k → ℝ} {B : ℝ}
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => B)) :
    TendstoInBootstrapWeakDistributionIndexed μ Pstar
      (trimmedBootstrapStatisticIndexed Zstar τ) ν Z :=
  hweak.trimmedBootstrapStatistic_of_tailProb hPstar hZmeas
    (trimmedTailProbIndexed_tendsto_zero_of_integral_norm_sq
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
      hPstar hZmem hτpos hτinv hSecond)

/-- The norm of Hansen's trimmed bootstrap statistic is bounded by
`max (τ n) 0` pointwise. -/
private theorem norm_trimmedBootstrapStatistic_le_max
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

/-- The coordinate-product squared tail of a trimmed statistic is zero above
the squared trim threshold. -/
theorem integral_tail_sq_mul_trimmedBootstrapStatistic_apply_eq_zero_of_lt
    {k : Type*} [Fintype k]
    {P : Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) {R : ℝ} (hR : (τ n) ^ 2 < R)
    (ω : Ω) (a c : k) :
    (∫ ωs, Set.indicator
      {ωs |
        R ≤ |trimmedBootstrapStatistic Zstar τ n ω ωs a *
          trimmedBootstrapStatistic Zstar τ n ω ωs c|}
      (fun ωs =>
        (trimmedBootstrapStatistic Zstar τ n ω ωs a *
          trimmedBootstrapStatistic Zstar τ n ω ωs c) ^ 2)
      ωs ∂P) = 0 := by
  refine integral_eq_zero_of_ae ?_
  exact ae_of_all P fun ωs => by
    have hprod :=
      abs_mul_trimmedBootstrapStatistic_apply_le_sq_of_nonneg
        (Zstar := Zstar) (τ := τ) hτ ω ωs a c
    have hnotmem :
        ωs ∉
          {x |
            R ≤ |trimmedBootstrapStatistic Zstar τ n ω x a *
              trimmedBootstrapStatistic Zstar τ n ω x c|} :=
      not_le.mpr (lt_of_le_of_lt hprod hR)
    rw [Set.indicator_of_notMem hnotmem]
    simp

/-- Coordinate squared tails of the trimmed statistic are pointwise dominated
by the corresponding original-statistic squared tails. -/
theorem tail_sq_trimmedBootstrapStatistic_apply_le_tail_sq
    {k : Type*} [Fintype k]
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω) (ωs : Ωs) (a : k) (R : ℝ) :
    Set.indicator
      {ωs | R ≤ |trimmedBootstrapStatistic Zstar τ n ω ωs a|}
      (fun ωs => (trimmedBootstrapStatistic Zstar τ n ω ωs a) ^ 2)
      ωs ≤
    Set.indicator {ωs | R ≤ |Zstar n ω ωs a|}
      (fun ωs => (Zstar n ω ωs a) ^ 2) ωs := by
  by_cases htrim : ‖Zstar n ω ωs‖ ≤ τ n
  · simp [Set.indicator, trimmedBootstrapStatistic, htrim]
  · have hnonneg :
        0 ≤
          Set.indicator {x | R ≤ |Zstar n ω x a|}
            (fun x => (Zstar n ω x a) ^ 2) ωs :=
      Set.indicator_nonneg (fun x _ => sq_nonneg (Zstar n ω x a)) ωs
    simpa [Set.indicator, trimmedBootstrapStatistic, htrim] using hnonneg

/-- Coordinate-sum squared tails of the trimmed statistic are pointwise
dominated by the corresponding original-statistic squared tails. -/
theorem tail_sq_add_trimmedBootstrapStatistic_apply_le_tail_sq
    {k : Type*} [Fintype k]
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω) (ωs : Ωs) (a c : k) (R : ℝ) :
    Set.indicator
      {ωs |
        R ≤ |trimmedBootstrapStatistic Zstar τ n ω ωs a +
          trimmedBootstrapStatistic Zstar τ n ω ωs c|}
      (fun ωs =>
        (trimmedBootstrapStatistic Zstar τ n ω ωs a +
          trimmedBootstrapStatistic Zstar τ n ω ωs c) ^ 2)
      ωs ≤
    Set.indicator {ωs | R ≤ |Zstar n ω ωs a + Zstar n ω ωs c|}
      (fun ωs => (Zstar n ω ωs a + Zstar n ω ωs c) ^ 2) ωs := by
  by_cases htrim : ‖Zstar n ω ωs‖ ≤ τ n
  · simp [Set.indicator, trimmedBootstrapStatistic, htrim]
  · have hnonneg :
        0 ≤
          Set.indicator {x | R ≤ |Zstar n ω x a + Zstar n ω x c|}
            (fun x => (Zstar n ω x a + Zstar n ω x c) ^ 2) ωs :=
      Set.indicator_nonneg
        (fun x _ => sq_nonneg (Zstar n ω x a + Zstar n ω x c)) ωs
    simpa [Set.indicator, trimmedBootstrapStatistic, htrim] using hnonneg

/-- Coordinate-product squared tails of the trimmed statistic are pointwise
dominated by the corresponding original-statistic squared tails. -/
theorem tail_sq_mul_trimmedBootstrapStatistic_apply_le_tail_sq
    {k : Type*} [Fintype k]
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω) (ωs : Ωs) (a c : k) (R : ℝ) :
    Set.indicator
      {ωs |
        R ≤ |trimmedBootstrapStatistic Zstar τ n ω ωs a *
          trimmedBootstrapStatistic Zstar τ n ω ωs c|}
      (fun ωs =>
        (trimmedBootstrapStatistic Zstar τ n ω ωs a *
          trimmedBootstrapStatistic Zstar τ n ω ωs c) ^ 2)
      ωs ≤
    Set.indicator {ωs | R ≤ |Zstar n ω ωs a * Zstar n ω ωs c|}
      (fun ωs => (Zstar n ω ωs a * Zstar n ω ωs c) ^ 2) ωs := by
  by_cases htrim : ‖Zstar n ω ωs‖ ≤ τ n
  · simp [Set.indicator, trimmedBootstrapStatistic, htrim]
  · have hnonneg :
        0 ≤
          Set.indicator {x | R ≤ |Zstar n ω x a * Zstar n ω x c|}
            (fun x => (Zstar n ω x a * Zstar n ω x c) ^ 2) ωs :=
      Set.indicator_nonneg
        (fun x _ => sq_nonneg (Zstar n ω x a * Zstar n ω x c)) ωs
    simpa [Set.indicator, trimmedBootstrapStatistic, htrim] using hnonneg

/-- Integral form of `tail_sq_trimmedBootstrapStatistic_apply_le_tail_sq`. -/
theorem integral_tail_sq_trimmedBootstrapStatistic_apply_le_tail_sq
    {k : Type*} [Fintype k]
    {P : Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω) (a : k) (R : ℝ)
    (hInt :
      Integrable
        (Set.indicator {ωs | R ≤ |Zstar n ω ωs a|}
          (fun ωs => (Zstar n ω ωs a) ^ 2)) P) :
    (∫ ωs, Set.indicator
      {ωs | R ≤ |trimmedBootstrapStatistic Zstar τ n ω ωs a|}
      (fun ωs => (trimmedBootstrapStatistic Zstar τ n ω ωs a) ^ 2)
      ωs ∂P) ≤
    ∫ ωs, Set.indicator {ωs | R ≤ |Zstar n ω ωs a|}
      (fun ωs => (Zstar n ω ωs a) ^ 2) ωs ∂P := by
  refine integral_mono_of_nonneg ?_ hInt ?_
  · exact ae_of_all P fun ωs =>
      Set.indicator_nonneg
        (fun x _ => sq_nonneg (trimmedBootstrapStatistic Zstar τ n ω x a)) ωs
  · exact ae_of_all P fun ωs =>
      tail_sq_trimmedBootstrapStatistic_apply_le_tail_sq
        (Zstar := Zstar) (τ := τ) n ω ωs a R

/-- Integral form of
`tail_sq_add_trimmedBootstrapStatistic_apply_le_tail_sq`. -/
theorem integral_tail_sq_add_trimmedBootstrapStatistic_apply_le_tail_sq
    {k : Type*} [Fintype k]
    {P : Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω) (a c : k) (R : ℝ)
    (hInt :
      Integrable
        (Set.indicator {ωs | R ≤ |Zstar n ω ωs a + Zstar n ω ωs c|}
          (fun ωs => (Zstar n ω ωs a + Zstar n ω ωs c) ^ 2)) P) :
    (∫ ωs, Set.indicator
      {ωs |
        R ≤ |trimmedBootstrapStatistic Zstar τ n ω ωs a +
          trimmedBootstrapStatistic Zstar τ n ω ωs c|}
      (fun ωs =>
        (trimmedBootstrapStatistic Zstar τ n ω ωs a +
          trimmedBootstrapStatistic Zstar τ n ω ωs c) ^ 2)
      ωs ∂P) ≤
    ∫ ωs, Set.indicator {ωs | R ≤ |Zstar n ω ωs a + Zstar n ω ωs c|}
      (fun ωs => (Zstar n ω ωs a + Zstar n ω ωs c) ^ 2) ωs ∂P := by
  refine integral_mono_of_nonneg ?_ hInt ?_
  · exact ae_of_all P fun ωs =>
      Set.indicator_nonneg
        (fun x _ =>
          sq_nonneg
            (trimmedBootstrapStatistic Zstar τ n ω x a +
              trimmedBootstrapStatistic Zstar τ n ω x c)) ωs
  · exact ae_of_all P fun ωs =>
      tail_sq_add_trimmedBootstrapStatistic_apply_le_tail_sq
        (Zstar := Zstar) (τ := τ) n ω ωs a c R

/-- Integral form of
`tail_sq_mul_trimmedBootstrapStatistic_apply_le_tail_sq`. -/
theorem integral_tail_sq_mul_trimmedBootstrapStatistic_apply_le_tail_sq
    {k : Type*} [Fintype k]
    {P : Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω) (a c : k) (R : ℝ)
    (hInt :
      Integrable
        (Set.indicator {ωs | R ≤ |Zstar n ω ωs a * Zstar n ω ωs c|}
          (fun ωs => (Zstar n ω ωs a * Zstar n ω ωs c) ^ 2)) P) :
    (∫ ωs, Set.indicator
      {ωs |
        R ≤ |trimmedBootstrapStatistic Zstar τ n ω ωs a *
          trimmedBootstrapStatistic Zstar τ n ω ωs c|}
      (fun ωs =>
        (trimmedBootstrapStatistic Zstar τ n ω ωs a *
          trimmedBootstrapStatistic Zstar τ n ω ωs c) ^ 2)
      ωs ∂P) ≤
    ∫ ωs, Set.indicator {ωs | R ≤ |Zstar n ω ωs a * Zstar n ω ωs c|}
      (fun ωs => (Zstar n ω ωs a * Zstar n ω ωs c) ^ 2) ωs ∂P := by
  refine integral_mono_of_nonneg ?_ hInt ?_
  · exact ae_of_all P fun ωs =>
      Set.indicator_nonneg
        (fun x _ =>
          sq_nonneg
            (trimmedBootstrapStatistic Zstar τ n ω x a *
              trimmedBootstrapStatistic Zstar τ n ω x c)) ωs
  · exact ae_of_all P fun ωs =>
      tail_sq_mul_trimmedBootstrapStatistic_apply_le_tail_sq
        (Zstar := Zstar) (τ := τ) n ω ωs a c R

/-- Original coordinate uniform square-tail control transfers to Hansen's
trimmed bootstrap statistic. -/
theorem bootstrapUniformSquareTail_trimmedBootstrapStatistic_apply
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} (a : k)
    (hTail :
      BootstrapUniformSquareTail μ Pstar
        (fun n ω ωs => Zstar n ω ωs a) ν Z)
    (hZmem :
      ∀ n ω, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω)) :
    BootstrapUniformSquareTail μ Pstar
      (fun n ω ωs => trimmedBootstrapStatistic Zstar τ n ω ωs a) ν Z :=
  bootstrapUniformSquareTail_of_integral_tail_sq_le
    (μ := μ) (Pstar := Pstar) hTail
    (fun n ω R =>
      integral_tail_sq_trimmedBootstrapStatistic_apply_le_tail_sq
        (P := Pstar n ω) (Zstar := Zstar) (τ := τ) n ω a R
        (integrable_tail_sq_indicator_of_memLp
          (P := Pstar n ω) (Y := fun ωs => Zstar n ω ωs a)
          (hZmem n ω) R))

/-- Original coordinate-sum uniform square-tail control transfers to Hansen's
trimmed bootstrap statistic. -/
theorem bootstrapUniformSquareTail_add_trimmedBootstrapStatistic_apply
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} (a c : k)
    (hTail :
      BootstrapUniformSquareTail μ Pstar
        (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) ν Z)
    (hZmem :
      ∀ n ω,
        MemLp (fun ωs => Zstar n ω ωs a + Zstar n ω ωs c) 2
          (Pstar n ω)) :
    BootstrapUniformSquareTail μ Pstar
      (fun n ω ωs =>
        trimmedBootstrapStatistic Zstar τ n ω ωs a +
          trimmedBootstrapStatistic Zstar τ n ω ωs c) ν Z :=
  bootstrapUniformSquareTail_of_integral_tail_sq_le
    (μ := μ) (Pstar := Pstar) hTail
    (fun n ω R =>
      integral_tail_sq_add_trimmedBootstrapStatistic_apply_le_tail_sq
        (P := Pstar n ω) (Zstar := Zstar) (τ := τ) n ω a c R
        (integrable_tail_sq_indicator_of_memLp
          (P := Pstar n ω)
          (Y := fun ωs => Zstar n ω ωs a + Zstar n ω ωs c)
          (hZmem n ω) R))

/-- Original coordinate-product uniform square-tail control transfers to
Hansen's trimmed bootstrap statistic. -/
theorem bootstrapUniformSquareTail_mul_trimmedBootstrapStatistic_apply
    {k : Type*} [Fintype k]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} (a c : k)
    (hTail :
      BootstrapUniformSquareTail μ Pstar
        (fun n ω ωs => Zstar n ω ωs a * Zstar n ω ωs c) ν Z)
    (hZmem :
      ∀ n ω,
        MemLp (fun ωs => Zstar n ω ωs a * Zstar n ω ωs c) 2
          (Pstar n ω)) :
    BootstrapUniformSquareTail μ Pstar
      (fun n ω ωs =>
        trimmedBootstrapStatistic Zstar τ n ω ωs a *
          trimmedBootstrapStatistic Zstar τ n ω ωs c) ν Z :=
  bootstrapUniformSquareTail_of_integral_tail_sq_le
    (μ := μ) (Pstar := Pstar) hTail
    (fun n ω R =>
      integral_tail_sq_mul_trimmedBootstrapStatistic_apply_le_tail_sq
        (P := Pstar n ω) (Zstar := Zstar) (τ := τ) n ω a c R
        (integrable_tail_sq_indicator_of_memLp
          (P := Pstar n ω)
          (Y := fun ωs => Zstar n ω ωs a * Zstar n ω ωs c)
          (hZmem n ω) R))

/-- Hansen's trimmed bootstrap statistic is a.e. strongly measurable whenever
the original bootstrap statistic is. -/
theorem aestronglyMeasurable_trimmedBootstrapStatistic_of_aestronglyMeasurable
    {k : Type*} [Fintype k]
    {P : Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω)
    (hZ : AEStronglyMeasurable (fun ωs => Zstar n ω ωs) P) :
    AEStronglyMeasurable
      (fun ωs => trimmedBootstrapStatistic Zstar τ n ω ωs) P := by
  let trimSet : Set Ωs := {ωs | ‖Zstar n ω ωs‖ ≤ τ n}
  have htrimSet : NullMeasurableSet trimSet P :=
    (hZ.norm.nullMeasurableSet_le aestronglyMeasurable_const)
  have hind :
      AEStronglyMeasurable
        (trimSet.indicator (fun ωs => Zstar n ω ωs)) P :=
    hZ.indicator₀ htrimSet
  refine hind.congr ?_
  exact ae_of_all P fun ωs => by
    by_cases htrim : ‖Zstar n ω ωs‖ ≤ τ n
    · simp [trimSet, trimmedBootstrapStatistic, htrim]
    · simp [trimSet, trimmedBootstrapStatistic, htrim]

/-- Coordinate measurability of Hansen's trimmed bootstrap statistic. -/
theorem
    aestronglyMeasurable_trimmedBootstrapStatistic_apply_of_aestronglyMeasurable
    {k : Type*} [Fintype k]
    {P : Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω) (a : k)
    (hZ : AEStronglyMeasurable (fun ωs => Zstar n ω ωs) P) :
    AEStronglyMeasurable
      (fun ωs => trimmedBootstrapStatistic Zstar τ n ω ωs a) P :=
  (continuous_apply a).comp_aestronglyMeasurable
    (aestronglyMeasurable_trimmedBootstrapStatistic_of_aestronglyMeasurable
      (Zstar := Zstar) (τ := τ) n ω hZ)

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

/-- A coordinate of Hansen's trimmed bootstrap statistic is in every
finite-measure `Lᵖ` space whenever the original vector statistic is a.e.
strongly measurable and the trim threshold is nonnegative. -/
theorem memLp_trimmedBootstrapStatistic_apply_of_aestronglyMeasurable
    {k : Type*} [Fintype k]
    {P : Measure Ωs} [IsFiniteMeasure P]
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) (ω : Ω) (a : k) {p : ℝ≥0∞}
    (hZ : AEStronglyMeasurable (fun ωs => Zstar n ω ωs) P) :
    MemLp (fun ωs => trimmedBootstrapStatistic Zstar τ n ω ωs a) p P :=
  memLp_trimmedBootstrapStatistic_apply_of_aestronglyMeasurable_of_nonneg
    (Zstar := Zstar) (τ := τ) hτ ω a
    (aestronglyMeasurable_trimmedBootstrapStatistic_apply_of_aestronglyMeasurable
      (Zstar := Zstar) (τ := τ) n ω a hZ)

/-- A coordinate sum of Hansen's trimmed bootstrap statistic is in every
finite-measure `Lᵖ` space under the nonnegative threshold bound. -/
theorem memLp_add_trimmedBootstrapStatistic_apply_of_aestronglyMeasurable
    {k : Type*} [Fintype k]
    {P : Measure Ωs} [IsFiniteMeasure P]
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) (ω : Ω) (a c : k) {p : ℝ≥0∞}
    (hZ : AEStronglyMeasurable (fun ωs => Zstar n ω ωs) P) :
    MemLp
      (fun ωs =>
        trimmedBootstrapStatistic Zstar τ n ω ωs a +
          trimmedBootstrapStatistic Zstar τ n ω ωs c) p P := by
  have ha :=
    aestronglyMeasurable_trimmedBootstrapStatistic_apply_of_aestronglyMeasurable
      (Zstar := Zstar) (τ := τ) n ω a hZ
  have hc :=
    aestronglyMeasurable_trimmedBootstrapStatistic_apply_of_aestronglyMeasurable
      (Zstar := Zstar) (τ := τ) n ω c hZ
  refine MemLp.of_bound (ha.add hc) (2 * τ n) ?_
  exact ae_of_all P fun ωs => by
    simpa [Real.norm_eq_abs] using
      abs_add_trimmedBootstrapStatistic_apply_le_two_mul_of_nonneg
        (Zstar := Zstar) (τ := τ) hτ ω ωs a c

/-- A coordinate product of Hansen's trimmed bootstrap statistic is in every
finite-measure `Lᵖ` space under the nonnegative threshold bound. -/
theorem memLp_mul_trimmedBootstrapStatistic_apply_of_aestronglyMeasurable
    {k : Type*} [Fintype k]
    {P : Measure Ωs} [IsFiniteMeasure P]
    {Zstar : ℕ → Ω → Ωs → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} (hτ : 0 ≤ τ n) (ω : Ω) (a c : k) {p : ℝ≥0∞}
    (hZ : AEStronglyMeasurable (fun ωs => Zstar n ω ωs) P) :
    MemLp
      (fun ωs =>
        trimmedBootstrapStatistic Zstar τ n ω ωs a *
          trimmedBootstrapStatistic Zstar τ n ω ωs c) p P := by
  have ha :=
    aestronglyMeasurable_trimmedBootstrapStatistic_apply_of_aestronglyMeasurable
      (Zstar := Zstar) (τ := τ) n ω a hZ
  have hc :=
    aestronglyMeasurable_trimmedBootstrapStatistic_apply_of_aestronglyMeasurable
      (Zstar := Zstar) (τ := τ) n ω c hZ
  refine MemLp.of_bound (ha.mul hc) ((τ n) ^ 2) ?_
  exact ae_of_all P fun ωs => by
    simpa [Real.norm_eq_abs] using
      abs_mul_trimmedBootstrapStatistic_apply_le_sq_of_nonneg
        (Zstar := Zstar) (τ := τ) hτ ω ωs a c

/-- Indexed version of `norm_trimmedBootstrapStatistic_le_max`. -/
private theorem norm_trimmedBootstrapStatisticIndexed_le_max
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

/-- Indexed coordinate-product squared tail of a trimmed statistic is zero
above the squared trim threshold. -/
theorem integral_tail_sq_mul_trimmedBootstrapStatisticIndexed_apply_eq_zero_of_lt
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} {P : Measure (Ωboot n)}
    (hτ : 0 ≤ τ n) {R : ℝ} (hR : (τ n) ^ 2 < R)
    (ω : Ω) (a c : k) :
    (∫ ωs, Set.indicator
      {ωs |
        R ≤ |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a *
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c|}
      (fun ωs =>
        (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a *
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c) ^ 2)
      ωs ∂P) = 0 := by
  refine integral_eq_zero_of_ae ?_
  exact ae_of_all P fun ωs => by
    have hprod :=
      abs_mul_trimmedBootstrapStatisticIndexed_apply_le_sq_of_nonneg
        (Zstar := Zstar) (τ := τ) hτ ω ωs a c
    have hnotmem :
        ωs ∉
          {x |
            R ≤ |trimmedBootstrapStatisticIndexed Zstar τ n ω x a *
              trimmedBootstrapStatisticIndexed Zstar τ n ω x c|} :=
      not_le.mpr (lt_of_le_of_lt hprod hR)
    rw [Set.indicator_of_notMem hnotmem]
    simp

/-- Indexed coordinate squared tails of the trimmed statistic are pointwise
dominated by the corresponding original-statistic squared tails. -/
theorem tail_sq_trimmedBootstrapStatisticIndexed_apply_le_tail_sq
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω) (ωs : Ωboot n) (a : k) (R : ℝ) :
    Set.indicator
      {ωs | R ≤ |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a|}
      (fun ωs => (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a) ^ 2)
      ωs ≤
    Set.indicator {ωs | R ≤ |Zstar n ω ωs a|}
      (fun ωs => (Zstar n ω ωs a) ^ 2) ωs := by
  by_cases htrim : ‖Zstar n ω ωs‖ ≤ τ n
  · simp [Set.indicator, trimmedBootstrapStatisticIndexed, htrim]
  · have hnonneg :
        0 ≤
          Set.indicator {x | R ≤ |Zstar n ω x a|}
            (fun x => (Zstar n ω x a) ^ 2) ωs :=
      Set.indicator_nonneg (fun x _ => sq_nonneg (Zstar n ω x a)) ωs
    simpa [Set.indicator, trimmedBootstrapStatisticIndexed, htrim] using hnonneg

/-- Indexed coordinate-sum squared tails of the trimmed statistic are
pointwise dominated by the corresponding original-statistic squared tails. -/
theorem tail_sq_add_trimmedBootstrapStatisticIndexed_apply_le_tail_sq
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω) (ωs : Ωboot n) (a c : k) (R : ℝ) :
    Set.indicator
      {ωs |
        R ≤ |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a +
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c|}
      (fun ωs =>
        (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a +
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c) ^ 2)
      ωs ≤
    Set.indicator {ωs | R ≤ |Zstar n ω ωs a + Zstar n ω ωs c|}
      (fun ωs => (Zstar n ω ωs a + Zstar n ω ωs c) ^ 2) ωs := by
  by_cases htrim : ‖Zstar n ω ωs‖ ≤ τ n
  · simp [Set.indicator, trimmedBootstrapStatisticIndexed, htrim]
  · have hnonneg :
        0 ≤
          Set.indicator {x | R ≤ |Zstar n ω x a + Zstar n ω x c|}
            (fun x => (Zstar n ω x a + Zstar n ω x c) ^ 2) ωs :=
      Set.indicator_nonneg
        (fun x _ => sq_nonneg (Zstar n ω x a + Zstar n ω x c)) ωs
    simpa [Set.indicator, trimmedBootstrapStatisticIndexed, htrim] using hnonneg

/-- Indexed coordinate-product squared tails of the trimmed statistic are
pointwise dominated by the corresponding original-statistic squared tails. -/
theorem tail_sq_mul_trimmedBootstrapStatisticIndexed_apply_le_tail_sq
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    (n : ℕ) (ω : Ω) (ωs : Ωboot n) (a c : k) (R : ℝ) :
    Set.indicator
      {ωs |
        R ≤ |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a *
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c|}
      (fun ωs =>
        (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a *
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c) ^ 2)
      ωs ≤
    Set.indicator {ωs | R ≤ |Zstar n ω ωs a * Zstar n ω ωs c|}
      (fun ωs => (Zstar n ω ωs a * Zstar n ω ωs c) ^ 2) ωs := by
  by_cases htrim : ‖Zstar n ω ωs‖ ≤ τ n
  · simp [Set.indicator, trimmedBootstrapStatisticIndexed, htrim]
  · have hnonneg :
        0 ≤
          Set.indicator {x | R ≤ |Zstar n ω x a * Zstar n ω x c|}
            (fun x => (Zstar n ω x a * Zstar n ω x c) ^ 2) ωs :=
      Set.indicator_nonneg
        (fun x _ => sq_nonneg (Zstar n ω x a * Zstar n ω x c)) ωs
    simpa [Set.indicator, trimmedBootstrapStatisticIndexed, htrim] using hnonneg

/-- Indexed integral form of
`tail_sq_trimmedBootstrapStatisticIndexed_apply_le_tail_sq`. -/
theorem integral_tail_sq_trimmedBootstrapStatisticIndexed_apply_le_tail_sq
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} {P : Measure (Ωboot n)}
    (ω : Ω) (a : k) (R : ℝ)
    (hInt :
      Integrable
        (Set.indicator {ωs | R ≤ |Zstar n ω ωs a|}
          (fun ωs => (Zstar n ω ωs a) ^ 2)) P) :
    (∫ ωs, Set.indicator
      {ωs | R ≤ |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a|}
      (fun ωs => (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a) ^ 2)
      ωs ∂P) ≤
    ∫ ωs, Set.indicator {ωs | R ≤ |Zstar n ω ωs a|}
      (fun ωs => (Zstar n ω ωs a) ^ 2) ωs ∂P := by
  refine integral_mono_of_nonneg ?_ hInt ?_
  · exact ae_of_all P fun ωs =>
      Set.indicator_nonneg
        (fun x _ => sq_nonneg (trimmedBootstrapStatisticIndexed Zstar τ n ω x a)) ωs
  · exact ae_of_all P fun ωs =>
      tail_sq_trimmedBootstrapStatisticIndexed_apply_le_tail_sq
        (Zstar := Zstar) (τ := τ) n ω ωs a R

/-- Indexed integral form of
`tail_sq_add_trimmedBootstrapStatisticIndexed_apply_le_tail_sq`. -/
theorem integral_tail_sq_add_trimmedBootstrapStatisticIndexed_apply_le_tail_sq
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} {P : Measure (Ωboot n)}
    (ω : Ω) (a c : k) (R : ℝ)
    (hInt :
      Integrable
        (Set.indicator {ωs | R ≤ |Zstar n ω ωs a + Zstar n ω ωs c|}
          (fun ωs => (Zstar n ω ωs a + Zstar n ω ωs c) ^ 2)) P) :
    (∫ ωs, Set.indicator
      {ωs |
        R ≤ |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a +
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c|}
      (fun ωs =>
        (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a +
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c) ^ 2)
      ωs ∂P) ≤
    ∫ ωs, Set.indicator {ωs | R ≤ |Zstar n ω ωs a + Zstar n ω ωs c|}
      (fun ωs => (Zstar n ω ωs a + Zstar n ω ωs c) ^ 2) ωs ∂P := by
  refine integral_mono_of_nonneg ?_ hInt ?_
  · exact ae_of_all P fun ωs =>
      Set.indicator_nonneg
        (fun x _ =>
          sq_nonneg
            (trimmedBootstrapStatisticIndexed Zstar τ n ω x a +
              trimmedBootstrapStatisticIndexed Zstar τ n ω x c)) ωs
  · exact ae_of_all P fun ωs =>
      tail_sq_add_trimmedBootstrapStatisticIndexed_apply_le_tail_sq
        (Zstar := Zstar) (τ := τ) n ω ωs a c R

/-- Indexed integral form of
`tail_sq_mul_trimmedBootstrapStatisticIndexed_apply_le_tail_sq`. -/
theorem integral_tail_sq_mul_trimmedBootstrapStatisticIndexed_apply_le_tail_sq
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} {P : Measure (Ωboot n)}
    (ω : Ω) (a c : k) (R : ℝ)
    (hInt :
      Integrable
        (Set.indicator {ωs | R ≤ |Zstar n ω ωs a * Zstar n ω ωs c|}
          (fun ωs => (Zstar n ω ωs a * Zstar n ω ωs c) ^ 2)) P) :
    (∫ ωs, Set.indicator
      {ωs |
        R ≤ |trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a *
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c|}
      (fun ωs =>
        (trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a *
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c) ^ 2)
      ωs ∂P) ≤
    ∫ ωs, Set.indicator {ωs | R ≤ |Zstar n ω ωs a * Zstar n ω ωs c|}
      (fun ωs => (Zstar n ω ωs a * Zstar n ω ωs c) ^ 2) ωs ∂P := by
  refine integral_mono_of_nonneg ?_ hInt ?_
  · exact ae_of_all P fun ωs =>
      Set.indicator_nonneg
        (fun x _ =>
          sq_nonneg
            (trimmedBootstrapStatisticIndexed Zstar τ n ω x a *
              trimmedBootstrapStatisticIndexed Zstar τ n ω x c)) ωs
  · exact ae_of_all P fun ωs =>
      tail_sq_mul_trimmedBootstrapStatisticIndexed_apply_le_tail_sq
        (Zstar := Zstar) (τ := τ) n ω ωs a c R

/-- Indexed original coordinate uniform square-tail control transfers to
Hansen's trimmed bootstrap statistic. -/
theorem bootstrapUniformSquareTail_trimmedBootstrapStatisticIndexed_apply
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} (a : k)
    (hTail :
      BootstrapUniformSquareTailIndexed μ Pstar
        (fun n ω ωs => Zstar n ω ωs a) ν Z)
    (hZmem :
      ∀ n ω, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω)) :
    BootstrapUniformSquareTailIndexed μ Pstar
      (fun n ω ωs => trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a) ν Z :=
  bootstrapUniformSquareTailIndexed_of_integral_tail_sq_le
    (μ := μ) (Pstar := Pstar) hTail
    (fun n ω R =>
      integral_tail_sq_trimmedBootstrapStatisticIndexed_apply_le_tail_sq
        (P := Pstar n ω) (Zstar := Zstar) (τ := τ) (n := n) ω a R
        (integrable_tail_sq_indicator_of_memLp
          (P := Pstar n ω) (Y := fun ωs => Zstar n ω ωs a)
          (hZmem n ω) R))

/-- Indexed original coordinate-sum uniform square-tail control transfers to
Hansen's trimmed bootstrap statistic. -/
theorem bootstrapUniformSquareTail_add_trimmedBootstrapStatisticIndexed_apply
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} (a c : k)
    (hTail :
      BootstrapUniformSquareTailIndexed μ Pstar
        (fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c) ν Z)
    (hZmem :
      ∀ n ω,
        MemLp (fun ωs => Zstar n ω ωs a + Zstar n ω ωs c) 2
          (Pstar n ω)) :
    BootstrapUniformSquareTailIndexed μ Pstar
      (fun n ω ωs =>
        trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a +
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c) ν Z :=
  bootstrapUniformSquareTailIndexed_of_integral_tail_sq_le
    (μ := μ) (Pstar := Pstar) hTail
    (fun n ω R =>
      integral_tail_sq_add_trimmedBootstrapStatisticIndexed_apply_le_tail_sq
        (P := Pstar n ω) (Zstar := Zstar) (τ := τ) (n := n) ω a c R
        (integrable_tail_sq_indicator_of_memLp
          (P := Pstar n ω)
          (Y := fun ωs => Zstar n ω ωs a + Zstar n ω ωs c)
          (hZmem n ω) R))

/-- Indexed original coordinate-product uniform square-tail control transfers
to Hansen's trimmed bootstrap statistic. -/
theorem bootstrapUniformSquareTail_mul_trimmedBootstrapStatisticIndexed_apply
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {ν : Measure Ωlim} {Z : Ωlim → ℝ} (a c : k)
    (hTail :
      BootstrapUniformSquareTailIndexed μ Pstar
        (fun n ω ωs => Zstar n ω ωs a * Zstar n ω ωs c) ν Z)
    (hZmem :
      ∀ n ω,
        MemLp (fun ωs => Zstar n ω ωs a * Zstar n ω ωs c) 2
          (Pstar n ω)) :
    BootstrapUniformSquareTailIndexed μ Pstar
      (fun n ω ωs =>
        trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a *
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c) ν Z :=
  bootstrapUniformSquareTailIndexed_of_integral_tail_sq_le
    (μ := μ) (Pstar := Pstar) hTail
    (fun n ω R =>
      integral_tail_sq_mul_trimmedBootstrapStatisticIndexed_apply_le_tail_sq
        (P := Pstar n ω) (Zstar := Zstar) (τ := τ) (n := n) ω a c R
        (integrable_tail_sq_indicator_of_memLp
          (P := Pstar n ω)
          (Y := fun ωs => Zstar n ω ωs a * Zstar n ω ωs c)
          (hZmem n ω) R))

/-- Indexed Hansen trimmed bootstrap statistic is a.e. strongly measurable
whenever the original indexed bootstrap statistic is. -/
theorem
    aestronglyMeasurable_trimmedBootstrapStatisticIndexed_of_aestronglyMeasurable
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} {P : Measure (Ωboot n)} (ω : Ω)
    (hZ : AEStronglyMeasurable (fun ωs => Zstar n ω ωs) P) :
    AEStronglyMeasurable
      (fun ωs => trimmedBootstrapStatisticIndexed Zstar τ n ω ωs) P := by
  let trimSet : Set (Ωboot n) := {ωs | ‖Zstar n ω ωs‖ ≤ τ n}
  have htrimSet : NullMeasurableSet trimSet P :=
    (hZ.norm.nullMeasurableSet_le aestronglyMeasurable_const)
  have hind :
      AEStronglyMeasurable
        (trimSet.indicator (fun ωs => Zstar n ω ωs)) P :=
    hZ.indicator₀ htrimSet
  refine hind.congr ?_
  exact ae_of_all P fun ωs => by
    by_cases htrim : ‖Zstar n ω ωs‖ ≤ τ n
    · simp [trimSet, trimmedBootstrapStatisticIndexed, htrim]
    · simp [trimSet, trimmedBootstrapStatisticIndexed, htrim]

/-- Indexed coordinate measurability of Hansen's trimmed bootstrap statistic. -/
theorem
    aestronglyMeasurable_trimmedBootstrapStatisticIndexed_apply_of_aestronglyMeasurable
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} {P : Measure (Ωboot n)} (ω : Ω) (a : k)
    (hZ : AEStronglyMeasurable (fun ωs => Zstar n ω ωs) P) :
    AEStronglyMeasurable
      (fun ωs => trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a) P :=
  (continuous_apply a).comp_aestronglyMeasurable
    (aestronglyMeasurable_trimmedBootstrapStatisticIndexed_of_aestronglyMeasurable
      (Zstar := Zstar) (τ := τ) ω hZ)

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

/-- Indexed coordinates of Hansen's trimmed bootstrap statistic are in every
finite-measure `Lᵖ` space whenever the original vector statistic is a.e.
strongly measurable and the trim threshold is nonnegative. -/
theorem memLp_trimmedBootstrapStatisticIndexed_apply_of_aestronglyMeasurable
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} {P : Measure (Ωboot n)} [IsFiniteMeasure P]
    (hτ : 0 ≤ τ n) (ω : Ω) (a : k) {p : ℝ≥0∞}
    (hZ : AEStronglyMeasurable (fun ωs => Zstar n ω ωs) P) :
    MemLp (fun ωs => trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a) p P :=
  memLp_trimmedBootstrapStatisticIndexed_apply_of_aestronglyMeasurable_of_nonneg
    (Zstar := Zstar) (τ := τ) hτ ω a
    (aestronglyMeasurable_trimmedBootstrapStatisticIndexed_apply_of_aestronglyMeasurable
      (Zstar := Zstar) (τ := τ) ω a hZ)

/-- Indexed coordinate sums of Hansen's trimmed bootstrap statistic are in
every finite-measure `Lᵖ` space under the nonnegative threshold bound. -/
theorem memLp_add_trimmedBootstrapStatisticIndexed_apply_of_aestronglyMeasurable
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} {P : Measure (Ωboot n)} [IsFiniteMeasure P]
    (hτ : 0 ≤ τ n) (ω : Ω) (a c : k) {p : ℝ≥0∞}
    (hZ : AEStronglyMeasurable (fun ωs => Zstar n ω ωs) P) :
    MemLp
      (fun ωs =>
        trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a +
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c) p P := by
  have ha :=
    aestronglyMeasurable_trimmedBootstrapStatisticIndexed_apply_of_aestronglyMeasurable
      (Zstar := Zstar) (τ := τ) ω a hZ
  have hc :=
    aestronglyMeasurable_trimmedBootstrapStatisticIndexed_apply_of_aestronglyMeasurable
      (Zstar := Zstar) (τ := τ) ω c hZ
  refine MemLp.of_bound (ha.add hc) (2 * τ n) ?_
  exact ae_of_all P fun ωs => by
    simpa [Real.norm_eq_abs] using
      abs_add_trimmedBootstrapStatisticIndexed_apply_le_two_mul_of_nonneg
        (Zstar := Zstar) (τ := τ) hτ ω ωs a c

/-- Indexed coordinate products of Hansen's trimmed bootstrap statistic are in
every finite-measure `Lᵖ` space under the nonnegative threshold bound. -/
theorem memLp_mul_trimmedBootstrapStatisticIndexed_apply_of_aestronglyMeasurable
    {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ} {τ : ℕ → ℝ}
    {n : ℕ} {P : Measure (Ωboot n)} [IsFiniteMeasure P]
    (hτ : 0 ≤ τ n) (ω : Ω) (a c : k) {p : ℝ≥0∞}
    (hZ : AEStronglyMeasurable (fun ωs => Zstar n ω ωs) P) :
    MemLp
      (fun ωs =>
        trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a *
          trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c) p P := by
  have ha :=
    aestronglyMeasurable_trimmedBootstrapStatisticIndexed_apply_of_aestronglyMeasurable
      (Zstar := Zstar) (τ := τ) ω a hZ
  have hc :=
    aestronglyMeasurable_trimmedBootstrapStatisticIndexed_apply_of_aestronglyMeasurable
      (Zstar := Zstar) (τ := τ) ω c hZ
  refine MemLp.of_bound (ha.mul hc) ((τ n) ^ 2) ?_
  exact ae_of_all P fun ωs => by
    simpa [Real.norm_eq_abs] using
      abs_mul_trimmedBootstrapStatisticIndexed_apply_le_sq_of_nonneg
        (Zstar := Zstar) (τ := τ) hτ ω ωs a c

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

/-- Hansen Theorem 10.12 trimmed covariance from weak convergence and
uniform-square-tail controls.

If `Z*` converges weakly conditionally, the large-norm trimming event has
conditional probability `oₚ(1)`, and the original coordinate and coordinate-sum
statistics satisfy the scalar uniform-square-tail premises, then Hansen's
trimmed covariance matrix converges to the covariance matrix of the weak
limit. -/
theorem
    chapter10_trimmedBootstrapVariance_tendsto_of_weak_distribution_uniformSquareTail
    [Fintype k] [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
        atTop (fun _ => 0))
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
    TendstoInMeasure μ (trimmedBootstrapCovarianceMat Pstar Zstar τ) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) := by
  have hweakTrim :
      TendstoInBootstrapWeakDistribution μ Pstar
        (trimmedBootstrapStatistic Zstar τ) ν Z :=
    hweak.trimmedBootstrapStatistic_of_tailProb hPstar hZmeas hTailProb
  have hTrimMem :
      ∀ n ω a,
        MemLp (fun ωs => trimmedBootstrapStatistic Zstar τ n ω ωs a) 2
          (Pstar n ω) := by
    intro n ω a
    haveI : IsFiniteMeasure (Pstar n ω) := by
      haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      infer_instance
    exact
      memLp_trimmedBootstrapStatistic_apply_of_aestronglyMeasurable
        (P := Pstar n ω) (Zstar := Zstar) (τ := τ)
        (hτ n) ω a ((hZmeas n ω).aestronglyMeasurable)
  have hTailCoordTrim :
      ∀ a,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs => trimmedBootstrapStatistic Zstar τ n ω ωs a) ν
          (fun ωlim => Z ωlim a) :=
    fun a =>
      bootstrapUniformSquareTail_trimmedBootstrapStatistic_apply
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
        a (hTailCoord a) (fun n ω => hZmem n ω a)
  have hTailSumTrim :
      ∀ a c,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs =>
            trimmedBootstrapStatistic Zstar τ n ω ωs a +
              trimmedBootstrapStatistic Zstar τ n ω ωs c) ν
          (fun ωlim => Z ωlim a + Z ωlim c) :=
    fun a c =>
      bootstrapUniformSquareTail_add_trimmedBootstrapStatistic_apply
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
        a c (hTailSum a c)
        (fun n ω => (hZmem n ω a).add (hZmem n ω c))
  simpa [trimmedBootstrapCovarianceMat] using
    chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := ν) (Pstar := Pstar)
      (Zstar := trimmedBootstrapStatistic Zstar τ) (Z := Z)
      hPstar hTrimMem hZlim hweakTrim hTailCoordTrim hTailSumTrim

/-- Hansen Theorem 10.12 trimmed covariance from weak convergence,
uniform-square-tail controls, and a second-moment Markov trimming-tail bound.

This wrapper replaces the raw `P*(τ_n < ‖Z*_n‖) = oₚ(1)` premise in
`chapter10_trimmedBootstrapVariance_tendsto_of_weak_distribution_uniformSquareTail`
with the standard sufficient condition: `τ_n` diverges and the conditional
second moment of `Z*_n` converges in probability. -/
theorem
    chapter10_trimmedBootstrapVariance_tendsto_of_uniformSquareTail_integral_norm_sq
    [Fintype k] [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hZmemVec : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hSecond :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => B))
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
    TendstoInMeasure μ (trimmedBootstrapCovarianceMat Pstar Zstar τ) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_trimmedBootstrapVariance_tendsto_of_weak_distribution_uniformSquareTail
    (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z) (τ := τ)
    hPstar (fun n => (hτpos n).le) hZmeas hZmem hZlim hweak
    (trimmedTailProb_tendsto_zero_of_integral_norm_sq
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
      hPstar hZmemVec hτpos hτinv hSecond)
    hTailCoord hTailSum

/-- Hansen Theorem 10.12 trimmed covariance from weak convergence and an
eventually bounded trim threshold.

The trimming-tail probability transfers weak convergence from `Z*` to `Z**`.
Once the nonnegative threshold is eventually bounded, the trimmed coordinates
and coordinate sums are eventually deterministically bounded, so Hansen's
uniform-square-tail premise follows from the bounded-statistic constructor. -/
theorem
    chapter10_trimmedBootstrapVariance_tendsto_of_eventualBound_memLp_limit
    [Fintype k] [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ} {C : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hτBound : ∀ᶠ n in atTop, τ n ≤ C)
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (trimmedBootstrapCovarianceMat Pstar Zstar τ) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) := by
  have hweakTrim :
      TendstoInBootstrapWeakDistribution μ Pstar
        (trimmedBootstrapStatistic Zstar τ) ν Z :=
    hweak.trimmedBootstrapStatistic_of_tailProb hPstar hZmeas hTailProb
  have hTrimMem :
      ∀ n ω a,
        MemLp (fun ωs => trimmedBootstrapStatistic Zstar τ n ω ωs a) 2
          (Pstar n ω) := by
    intro n ω a
    haveI : IsFiniteMeasure (Pstar n ω) := by
      haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      infer_instance
    exact
      memLp_trimmedBootstrapStatistic_apply_of_aestronglyMeasurable
        (P := Pstar n ω) (Zstar := Zstar) (τ := τ)
        (hτ n) ω a ((hZmeas n ω).aestronglyMeasurable)
  simpa [trimmedBootstrapCovarianceMat] using
    chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := ν) (Pstar := Pstar)
      (Zstar := trimmedBootstrapStatistic Zstar τ) (Z := Z)
      hPstar hTrimMem hZlim hweakTrim
      (Ccoord := fun _ => C) (Csum := fun _ _ => 2 * C)
      (fun a => by
        filter_upwards [hτBound] with n hτC
        intro ω ωs
        exact
          (abs_trimmedBootstrapStatistic_apply_le_of_nonneg
            (Zstar := Zstar) (τ := τ) (hτ n) ω ωs a).trans hτC)
      (fun a c => by
        filter_upwards [hτBound] with n hτC
        intro ω ωs
        exact
          (abs_add_trimmedBootstrapStatistic_apply_le_two_mul_of_nonneg
            (Zstar := Zstar) (τ := τ) (hτ n) ω ωs a c).trans
            (by nlinarith))

/-- Hansen Theorem 10.12 trimmed covariance from weak convergence and
fourth-moment tail controls.

The original bootstrap statistic supplies weak convergence and an `oₚ(1)`
large-norm trimming event.  Conditional fourth-moment convergence for each
coordinate and coordinate sum discharges the uniform-square-tail assumptions
used by the trimmed covariance wrapper. -/
theorem
    chapter10_trimmedBootstrapVariance_tendsto_of_weak_distribution_fourthMoment_tails
    [Fintype k] [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ}
    {Bcoord : k → ℝ} {Bsum : k → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
        atTop (fun _ => 0))
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoord :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω => ∫ ωs, (Zstar n ω ωs a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordInt :
      ∀ n ω a, Integrable (fun ωs => (Zstar n ω ωs a) ^ 4) (Pstar n ω))
    (hLimitTailCoord :
      ∀ a ε, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim a|}
            (fun ωlim => (Z ωlim a) ^ 2) ωlim ∂ν) ≤ ε)
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSum :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs, (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumInt :
      ∀ n ω a c,
        Integrable
          (fun ωs => (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4)
          (Pstar n ω))
    (hLimitTailSum :
      ∀ a c ε, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim a + Z ωlim c|}
            (fun ωlim => (Z ωlim a + Z ωlim c) ^ 2) ωlim ∂ν) ≤ ε) :
    TendstoInMeasure μ (trimmedBootstrapCovarianceMat Pstar Zstar τ) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_trimmedBootstrapVariance_tendsto_of_weak_distribution_uniformSquareTail
    (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z) (τ := τ)
    hPstar hτ hZmeas hZmem hZlim hweak hTailProb
    (fun a =>
      bootstrapUniformSquareTail_of_fourthMoment_tendstoInMeasure_of_eventual_limit_tail
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a)
        (ν := ν) (Z := fun ωlim => Z ωlim a)
        (B := Bcoord a)
        (hBcoord a) (hFourthCoord a)
        (fun n ω => hFourthCoordInt n ω a)
        (hLimitTailCoord a))
    (fun a c =>
      bootstrapUniformSquareTail_of_fourthMoment_tendstoInMeasure_of_eventual_limit_tail
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c)
        (ν := ν) (Z := fun ωlim => Z ωlim a + Z ωlim c)
        (B := Bsum a c)
        (hBsum a c) (hFourthSum a c)
        (fun n ω => hFourthSumInt n ω a c)
        (hLimitTailSum a c))

/-- Hansen Theorem 10.12 trimmed covariance from weak convergence and
fourth-moment convergence, with weak-limit coordinate and coordinate-sum tail
premises discharged by `MemLp`. -/
theorem
    chapter10_trimmedBootstrapVariance_tendsto_of_fourthMoment_memLp
    [Fintype k] [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ}
    {Bcoord : k → ℝ} {Bsum : k → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
        atTop (fun _ => 0))
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoord :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω => ∫ ωs, (Zstar n ω ωs a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordInt :
      ∀ n ω a, Integrable (fun ωs => (Zstar n ω ωs a) ^ 4) (Pstar n ω))
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSum :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs, (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumInt :
      ∀ n ω a c,
        Integrable
          (fun ωs => (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4)
          (Pstar n ω)) :
    TendstoInMeasure μ (trimmedBootstrapCovarianceMat Pstar Zstar τ) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_trimmedBootstrapVariance_tendsto_of_weak_distribution_uniformSquareTail
    (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z) (τ := τ)
    hPstar hτ hZmeas hZmem hZlim hweak hTailProb
    (fun a =>
      bootstrapUniformSquareTail_of_fourthMoment_tendstoInMeasure_of_memLp_limit
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a)
        (ν := ν) (Z := fun ωlim => Z ωlim a)
        (B := Bcoord a)
        (hBcoord a) (hZlim a) (hFourthCoord a)
        (fun n ω => hFourthCoordInt n ω a))
    (fun a c =>
      bootstrapUniformSquareTail_of_fourthMoment_tendstoInMeasure_of_memLp_limit
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c)
        (ν := ν) (Z := fun ωlim => Z ωlim a + Z ωlim c)
        (B := Bsum a c)
        (hBsum a c) ((hZlim a).add (hZlim c)) (hFourthSum a c)
        (fun n ω => hFourthSumInt n ω a c))

/-- Indexed Theorem 10.12 trimmed covariance from weak convergence and
uniform-square-tail controls. -/
theorem
    chapter10_indexed_trimmedBootstrapVariance_tendsto_of_weak_distribution_uniformSquareTail
    [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
        atTop (fun _ => 0))
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
    TendstoInMeasure μ (trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ)
      atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) := by
  have hweakTrim :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (trimmedBootstrapStatisticIndexed Zstar τ) ν Z :=
    hweak.trimmedBootstrapStatistic_of_tailProb hPstar hZmeas hTailProb
  have hTrimMem :
      ∀ n ω a,
        MemLp
          (fun ωs => trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a) 2
          (Pstar n ω) := by
    intro n ω a
    haveI : IsFiniteMeasure (Pstar n ω) := by
      haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      infer_instance
    exact
      memLp_trimmedBootstrapStatisticIndexed_apply_of_aestronglyMeasurable
        (P := Pstar n ω) (Zstar := Zstar) (τ := τ)
        (hτ n) ω a ((hZmeas n ω).aestronglyMeasurable)
  have hTailCoordTrim :
      ∀ a,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs =>
            trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a) ν
          (fun ωlim => Z ωlim a) :=
    fun a =>
      bootstrapUniformSquareTail_trimmedBootstrapStatisticIndexed_apply
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
        a (hTailCoord a) (fun n ω => hZmem n ω a)
  have hTailSumTrim :
      ∀ a c,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs =>
            trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a +
              trimmedBootstrapStatisticIndexed Zstar τ n ω ωs c) ν
          (fun ωlim => Z ωlim a + Z ωlim c) :=
    fun a c =>
      bootstrapUniformSquareTail_add_trimmedBootstrapStatisticIndexed_apply
        (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
        a c (hTailSum a c)
        (fun n ω => (hZmem n ω a).add (hZmem n ω c))
  simpa [trimmedBootstrapCovarianceMatIndexed] using
    chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := ν) (Pstar := Pstar)
      (Zstar := trimmedBootstrapStatisticIndexed Zstar τ) (Z := Z)
      hPstar hTrimMem hZlim hweakTrim hTailCoordTrim hTailSumTrim

/-- Indexed Hansen Theorem 10.12 trimmed covariance from weak convergence,
uniform-square-tail controls, and a second-moment Markov trimming-tail bound. -/
theorem
    chapter10_indexed_trimmedBootstrapVariance_tendsto_of_uniformSquareTail_integral_norm_sq
    [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hZmemVec : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hSecond :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Zstar n ω ωs‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => B))
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
    TendstoInMeasure μ (trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ)
      atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_trimmedBootstrapVariance_tendsto_of_weak_distribution_uniformSquareTail
    (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z) (τ := τ)
    hPstar (fun n => (hτpos n).le) hZmeas hZmem hZlim hweak
    (trimmedTailProbIndexed_tendsto_zero_of_integral_norm_sq
      (μ := μ) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
      hPstar hZmemVec hτpos hτinv hSecond)
    hTailCoord hTailSum

/-- Indexed Hansen Theorem 10.12 trimmed covariance from weak convergence and
an eventually bounded trim threshold. -/
theorem
    chapter10_indexed_trimmedBootstrapVariance_tendsto_of_eventualBound_memLp_limit
    [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ} {C : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hτBound : ∀ᶠ n in atTop, τ n ≤ C)
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ)
      atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) := by
  have hweakTrim :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (trimmedBootstrapStatisticIndexed Zstar τ) ν Z :=
    hweak.trimmedBootstrapStatistic_of_tailProb hPstar hZmeas hTailProb
  have hTrimMem :
      ∀ n ω a,
        MemLp
          (fun ωs => trimmedBootstrapStatisticIndexed Zstar τ n ω ωs a) 2
          (Pstar n ω) := by
    intro n ω a
    haveI : IsFiniteMeasure (Pstar n ω) := by
      haveI : IsProbabilityMeasure (Pstar n ω) := hPstar n ω
      infer_instance
    exact
      memLp_trimmedBootstrapStatisticIndexed_apply_of_aestronglyMeasurable
        (P := Pstar n ω) (Zstar := Zstar) (τ := τ)
        (hτ n) ω a ((hZmeas n ω).aestronglyMeasurable)
  simpa [trimmedBootstrapCovarianceMatIndexed] using
    chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := ν) (Pstar := Pstar)
      (Zstar := trimmedBootstrapStatisticIndexed Zstar τ) (Z := Z)
      hPstar hTrimMem hZlim hweakTrim
      (Ccoord := fun _ => C) (Csum := fun _ _ => 2 * C)
      (fun a => by
        filter_upwards [hτBound] with n hτC
        intro ω ωs
        exact
          (abs_trimmedBootstrapStatisticIndexed_apply_le_of_nonneg
            (Zstar := Zstar) (τ := τ) (hτ n) ω ωs a).trans hτC)
      (fun a c => by
        filter_upwards [hτBound] with n hτC
        intro ω ωs
        exact
          (abs_add_trimmedBootstrapStatisticIndexed_apply_le_two_mul_of_nonneg
            (Zstar := Zstar) (τ := τ) (hτ n) ω ωs a c).trans
            (by nlinarith))

/-- Indexed Hansen Theorem 10.12 trimmed covariance from weak convergence and
fourth-moment tail controls. -/
theorem
    chapter10_indexed_trimmedBootstrapVariance_tendsto_of_weak_distribution_fourthMoment_tails
    [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ}
    {Bcoord : k → ℝ} {Bsum : k → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
        atTop (fun _ => 0))
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoord :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω => ∫ ωs, (Zstar n ω ωs a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordInt :
      ∀ n ω a, Integrable (fun ωs => (Zstar n ω ωs a) ^ 4) (Pstar n ω))
    (hLimitTailCoord :
      ∀ a ε, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim a|}
            (fun ωlim => (Z ωlim a) ^ 2) ωlim ∂ν) ≤ ε)
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSum :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs, (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumInt :
      ∀ n ω a c,
        Integrable
          (fun ωs => (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4)
          (Pstar n ω))
    (hLimitTailSum :
      ∀ a c ε, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim a + Z ωlim c|}
            (fun ωlim => (Z ωlim a + Z ωlim c) ^ 2) ωlim ∂ν) ≤ ε) :
    TendstoInMeasure μ (trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ)
      atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_trimmedBootstrapVariance_tendsto_of_weak_distribution_uniformSquareTail
    (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z) (τ := τ)
    hPstar hτ hZmeas hZmem hZlim hweak hTailProb
    (fun a =>
      bootstrapUniformSquareTailIndexed_of_fourthMoment_tendstoInMeasure_of_eventual_limit_tail
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a)
        (ν := ν) (Z := fun ωlim => Z ωlim a)
        (B := Bcoord a)
        (hBcoord a) (hFourthCoord a)
        (fun n ω => hFourthCoordInt n ω a)
        (hLimitTailCoord a))
    (fun a c =>
      bootstrapUniformSquareTailIndexed_of_fourthMoment_tendstoInMeasure_of_eventual_limit_tail
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c)
        (ν := ν) (Z := fun ωlim => Z ωlim a + Z ωlim c)
        (B := Bsum a c)
        (hBsum a c) (hFourthSum a c)
        (fun n ω => hFourthSumInt n ω a c)
        (hLimitTailSum a c))

/-- Indexed Hansen Theorem 10.12 trimmed covariance from weak convergence and
fourth-moment convergence, with weak-limit coordinate and coordinate-sum tail
premises discharged by `MemLp`. -/
theorem
    chapter10_indexed_trimmedBootstrapVariance_tendsto_of_fourthMoment_memLp
    [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ}
    {Bcoord : k → ℝ} {Bsum : k → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
        atTop (fun _ => 0))
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoord :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω => ∫ ωs, (Zstar n ω ωs a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordInt :
      ∀ n ω a, Integrable (fun ωs => (Zstar n ω ωs a) ^ 4) (Pstar n ω))
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSum :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs, (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumInt :
      ∀ n ω a c,
        Integrable
          (fun ωs => (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4)
          (Pstar n ω)) :
    TendstoInMeasure μ (trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ)
      atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_trimmedBootstrapVariance_tendsto_of_weak_distribution_uniformSquareTail
    (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z) (τ := τ)
    hPstar hτ hZmeas hZmem hZlim hweak hTailProb
    (fun a =>
      bootstrapUniformSquareTailIndexed_of_fourthMoment_tendstoInMeasure_of_memLp_limit
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a)
        (ν := ν) (Z := fun ωlim => Z ωlim a)
        (B := Bcoord a)
        (hBcoord a) (hZlim a) (hFourthCoord a)
        (fun n ω => hFourthCoordInt n ω a))
    (fun a c =>
      bootstrapUniformSquareTailIndexed_of_fourthMoment_tendstoInMeasure_of_memLp_limit
        (μ := μ) (Pstar := Pstar)
        (Zstar := fun n ω ωs => Zstar n ω ωs a + Zstar n ω ωs c)
        (ν := ν) (Z := fun ωlim => Z ωlim a + Z ωlim c)
        (B := Bsum a c)
        (hBsum a c) ((hZlim a).add (hZlim c)) (hFourthSum a c)
        (fun n ω => hFourthSumInt n ω a c))

/-- Hansen Theorem 10.10/10.12 smooth trimmed covariance consistency from
exact derivative linearization and a norm fourth-moment premise.

The trimming-tail probability remains the model-specific input.  The smooth
Gaussian weak limit and the original coordinate/coordinate-sum square-tail
controls used by the trimmed covariance theorem are discharged from the
linearized statistic. -/
theorem chapter10_smooth_trimmedBootstrapVariance_tendsto_of_linearization_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {τ : ℕ → ℝ} {B : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hZmeas :
      ∀ n ω, Measurable (fun ωs => (thetaStar n ω ωs : r → ℝ)))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)
            {ωs | τ n < ‖(thetaStar n ω ωs : r → ℝ)‖}).toReal)
        atTop (fun _ => 0))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMat Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ)
      atTop (fun _ => G * V * Gᵀ) := by
  let S : Matrix r r ℝ := G * V * Gᵀ
  have hS : S.PosSemidef := by
    dsimp [S]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.mul_mul_conjTranspose_same G
  have hGaussianEuclidean :
      TendstoInBootstrapWeakDistribution μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z) := by
    dsimp [S]
    exact
      chapter10_bootstrap_smooth_function_gaussian_of_linearization
        (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
        (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  have hGaussian :
      TendstoInBootstrapWeakDistribution μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
    chapter10_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hGaussianEuclidean (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hTailCoord :
      ∀ a,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
          (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) := by
    intro a
    exact
      bootstrapUniformSquareTail_of_linearization_coord_normFourth
        (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (Pstar := Pstar) (Tstar := Tstar)
        (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
        (B := B) G a hB (by simpa [S] using hlimMem a)
        (fun n ω ωs => by
          simpa [matrixContinuousLinearMap_apply] using
            congrArg (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
              (hlinearization n ω ωs))
        hNormFourth hNormFourthInt
  have hTailSum :
      ∀ a c,
        BootstrapUniformSquareTail μ Pstar
          (fun n ω ωs =>
            (thetaStar n ω ωs : r → ℝ) a +
              (thetaStar n ω ωs : r → ℝ) c)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
          (fun z : EuclideanSpace ℝ r =>
            (z : r → ℝ) a + (z : r → ℝ) c) := by
    intro a c
    let H : Matrix Unit d ℝ := fun _ j => G a j + G c j
    exact
      bootstrapUniformSquareTail_of_linearization_coord_normFourth
        (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (Pstar := Pstar) (Tstar := Tstar)
        (Zstar := fun n ω ωs =>
          (thetaStar n ω ωs : r → ℝ) a +
            (thetaStar n ω ωs : r → ℝ) c)
        (Z := fun z : EuclideanSpace ℝ r =>
          (z : r → ℝ) a + (z : r → ℝ) c)
        (B := B) H () hB
        (by simpa [S] using (hlimMem a).add (hlimMem c))
        (fun n ω ωs => by
          have ha :
              (thetaStar n ω ωs : r → ℝ) a =
                (G *ᵥ (Tstar n ω ωs).ofLp) a := by
            simpa [matrixContinuousLinearMap_apply] using
              congrArg (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
                (hlinearization n ω ωs)
          have hc :
              (thetaStar n ω ωs : r → ℝ) c =
                (G *ᵥ (Tstar n ω ωs).ofLp) c := by
            simpa [matrixContinuousLinearMap_apply] using
              congrArg (fun z : EuclideanSpace ℝ r => (z : r → ℝ) c)
                (hlinearization n ω ωs)
          change (thetaStar n ω ωs : r → ℝ) a +
              (thetaStar n ω ωs : r → ℝ) c =
            (((matrixContinuousLinearMap H (Tstar n ω ωs) :
              EuclideanSpace ℝ Unit) : Unit → ℝ) ())
          rw [ha, hc]
          simp [H, matrixContinuousLinearMap_apply, Matrix.mulVec, dotProduct,
            Finset.sum_add_distrib, add_mul])
        hNormFourth hNormFourthInt
  have htrim :
      TendstoInMeasure μ
        (trimmedBootstrapCovarianceMat Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ)
        atTop
        (fun _ => fun a c =>
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a *
              ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) *
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S)) :=
    chapter10_trimmedBootstrapVariance_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ)) (τ := τ)
      hPstar hτ hZmeas hcoordMem (by simpa [S] using hlimMem)
      hGaussian hTailProb hTailCoord hTailSum
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ htrim
  exact ae_of_all μ fun _ => by
    simpa [S] using
      (multivariateGaussian_covarianceIntegralMat_eq
        (S := S) hS (by simpa [S] using hlimMem))

/-- Hansen Theorem 10.10/10.12 smooth trimmed covariance consistency from
exact derivative linearization, a norm fourth-moment premise, and a
second-moment Markov trimming-tail bound. -/
theorem chapter10_smooth_trimmedBootstrapVariance_tendsto_of_normFourth_integral_norm_sq
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {τ : ℕ → ℝ} {Bsecond Bfourth : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hZmeas :
      ∀ n ω, Measurable (fun ωs => (thetaStar n ω ωs : r → ℝ)))
    (hThetaMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ)) 2
          (Pstar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖(thetaStar n ω ωs : r → ℝ)‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => Bsecond))
    (hBfourth : 0 ≤ Bfourth)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bfourth))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMat Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ)
      atTop (fun _ => G * V * Gᵀ) :=
  chapter10_smooth_trimmedBootstrapVariance_tendsto_of_linearization_normFourth
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (thetaStar := thetaStar)
    (V := V) G hV hPstar (fun n => (hτpos n).le) hT hZmeas
    hcoordMem hlimMem hlinearization
    (trimmedTailProb_tendsto_zero_of_integral_norm_sq
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (τ := τ) hPstar hThetaMem hτpos hτinv hSecond)
    hBfourth hNormFourth hNormFourthInt

/-- Indexed counterpart of
`chapter10_smooth_trimmedBootstrapVariance_tendsto_of_linearization_normFourth`. -/
theorem
    chapter10_indexed_smooth_trimmedBootstrapVariance_tendsto_of_linearization_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {τ : ℕ → ℝ} {B : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hZmeas :
      ∀ n ω, Measurable (fun ωs => (thetaStar n ω ωs : r → ℝ)))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)
            {ωs | τ n < ‖(thetaStar n ω ωs : r → ℝ)‖}).toReal)
        atTop (fun _ => 0))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ)
      atTop (fun _ => G * V * Gᵀ) := by
  let S : Matrix r r ℝ := G * V * Gᵀ
  have hS : S.PosSemidef := by
    dsimp [S]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hV.mul_mul_conjTranspose_same G
  have hGaussianEuclidean :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar thetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => z) := by
    dsimp [S]
    exact
      chapter10_indexed_bootstrap_smooth_function_gaussian_of_linearization
        (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
        (thetaStar := thetaStar) (V := V) G hV hT hlinearization
  have hGaussian :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
        (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (fun z : EuclideanSpace ℝ r => (z : r → ℝ)) :=
    chapter10_indexed_bootstrap_continuous_mapping_distribution
      (μ := μ) (Pstar := Pstar) (Zstar := thetaStar)
      (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Z := fun z : EuclideanSpace ℝ r => z)
      (g := fun z : EuclideanSpace ℝ r => (z : r → ℝ))
      hGaussianEuclidean (PiLp.continuous_ofLp 2 (fun _ : r => ℝ))
  have hTailCoord :
      ∀ a,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
          (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) := by
    intro a
    exact
      bootstrapUniformSquareTailIndexed_of_linearization_coord_normFourth
        (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (Pstar := Pstar) (Tstar := Tstar)
        (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
        (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
        (B := B) G a hB (by simpa [S] using hlimMem a)
        (fun n ω ωs => by
          simpa [matrixContinuousLinearMap_apply] using
            congrArg (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
              (hlinearization n ω ωs))
        hNormFourth hNormFourthInt
  have hTailSum :
      ∀ a c,
        BootstrapUniformSquareTailIndexed μ Pstar
          (fun n ω ωs =>
            (thetaStar n ω ωs : r → ℝ) a +
              (thetaStar n ω ωs : r → ℝ) c)
          (multivariateGaussian (0 : EuclideanSpace ℝ r) S)
          (fun z : EuclideanSpace ℝ r =>
            (z : r → ℝ) a + (z : r → ℝ) c) := by
    intro a c
    let H : Matrix Unit d ℝ := fun _ j => G a j + G c j
    exact
      bootstrapUniformSquareTailIndexed_of_linearization_coord_normFourth
        (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
        (Pstar := Pstar) (Tstar := Tstar)
        (Zstar := fun n ω ωs =>
          (thetaStar n ω ωs : r → ℝ) a +
            (thetaStar n ω ωs : r → ℝ) c)
        (Z := fun z : EuclideanSpace ℝ r =>
          (z : r → ℝ) a + (z : r → ℝ) c)
        (B := B) H () hB
        (by simpa [S] using (hlimMem a).add (hlimMem c))
        (fun n ω ωs => by
          have ha :
              (thetaStar n ω ωs : r → ℝ) a =
                (G *ᵥ (Tstar n ω ωs).ofLp) a := by
            simpa [matrixContinuousLinearMap_apply] using
              congrArg (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a)
                (hlinearization n ω ωs)
          have hc :
              (thetaStar n ω ωs : r → ℝ) c =
                (G *ᵥ (Tstar n ω ωs).ofLp) c := by
            simpa [matrixContinuousLinearMap_apply] using
              congrArg (fun z : EuclideanSpace ℝ r => (z : r → ℝ) c)
                (hlinearization n ω ωs)
          change (thetaStar n ω ωs : r → ℝ) a +
              (thetaStar n ω ωs : r → ℝ) c =
            (((matrixContinuousLinearMap H (Tstar n ω ωs) :
              EuclideanSpace ℝ Unit) : Unit → ℝ) ())
          rw [ha, hc]
          simp [H, matrixContinuousLinearMap_apply, Matrix.mulVec, dotProduct,
            Finset.sum_add_distrib, add_mul])
        hNormFourth hNormFourthInt
  have htrim :
      TendstoInMeasure μ
        (trimmedBootstrapCovarianceMatIndexed Pstar
          (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ)
        atTop
        (fun _ => fun a c =>
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a *
              ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) -
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S) *
          (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) c
            ∂multivariateGaussian (0 : EuclideanSpace ℝ r) S)) :=
    chapter10_indexed_trimmedBootstrapVariance_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := multivariateGaussian (0 : EuclideanSpace ℝ r) S)
      (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (Z := fun z : EuclideanSpace ℝ r => (z : r → ℝ)) (τ := τ)
      hPstar hτ hZmeas hcoordMem (by simpa [S] using hlimMem)
      hGaussian hTailProb hTailCoord hTailSum
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ htrim
  exact ae_of_all μ fun _ => by
    simpa [S] using
      (multivariateGaussian_covarianceIntegralMat_eq
        (S := S) hS (by simpa [S] using hlimMem))

/-- Indexed counterpart of
`chapter10_smooth_trimmedBootstrapVariance_tendsto_of_normFourth_integral_norm_sq`. -/
theorem
    chapter10_indexed_smooth_trimmedBootstrapVariance_tendsto_of_normFourth_integral_norm_sq
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {τ : ℕ → ℝ} {Bsecond Bfourth : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hZmeas :
      ∀ n ω, Measurable (fun ωs => (thetaStar n ω ωs : r → ℝ)))
    (hThetaMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ)) 2
          (Pstar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖(thetaStar n ω ωs : r → ℝ)‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => Bsecond))
    (hBfourth : 0 ≤ Bfourth)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bfourth))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ)
      atTop (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_smooth_trimmedBootstrapVariance_tendsto_of_linearization_normFourth
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (thetaStar := thetaStar)
    (V := V) G hV hPstar (fun n => (hτpos n).le) hT hZmeas
    hcoordMem hlimMem hlinearization
    (trimmedTailProbIndexed_tendsto_zero_of_integral_norm_sq
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
      (τ := τ) hPstar hThetaMem hτpos hτinv hSecond)
    hBfourth hNormFourth hNormFourthInt

/-- Smooth exact-linearization trimmed covariance route with Gaussian-limit
coordinate `MemLp 2` premises discharged automatically. -/
theorem
    chapter10_smooth_trimmedVariance_linearization_normFourth_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {τ : ℕ → ℝ} {B : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hZmeas :
      ∀ n ω, Measurable (fun ωs => (thetaStar n ω ωs : r → ℝ)))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)
            {ωs | τ n < ‖(thetaStar n ω ωs : r → ℝ)‖}).toReal)
        atTop (fun _ => 0))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMat Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ)
      atTop (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_smooth_trimmedBootstrapVariance_tendsto_of_linearization_normFourth
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (thetaStar := thetaStar)
    (V := V) G hV hPstar hτ hT hZmeas hcoordMem
    (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
    hlinearization hTailProb hB hNormFourth hNormFourthInt

/-- Indexed smooth exact-linearization trimmed covariance route with automatic
Gaussian-limit coordinate `MemLp 2` premises. -/
theorem
    chapter10_indexed_smooth_trimmedVariance_linearization_normFourth_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {τ : ℕ → ℝ} {B : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hZmeas :
      ∀ n ω, Measurable (fun ωs => (thetaStar n ω ωs : r → ℝ)))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)
            {ωs | τ n < ‖(thetaStar n ω ωs : r → ℝ)‖}).toReal)
        atTop (fun _ => 0))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ)
      atTop (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_indexed_smooth_trimmedBootstrapVariance_tendsto_of_linearization_normFourth
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (thetaStar := thetaStar)
    (V := V) G hV hPstar hτ hT hZmeas hcoordMem
    (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
    hlinearization hTailProb hB hNormFourth hNormFourthInt

/-- Smooth trimmed covariance route with the trimming-tail probability and
Gaussian-limit coordinate `MemLp 2` premises discharged. -/
theorem
    chapter10_smooth_trimmedVariance_normFourth_integral_norm_sq_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {τ : ℕ → ℝ} {Bsecond Bfourth : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hZmeas :
      ∀ n ω, Measurable (fun ωs => (thetaStar n ω ωs : r → ℝ)))
    (hThetaMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ)) 2
          (Pstar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖(thetaStar n ω ωs : r → ℝ)‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => Bsecond))
    (hBfourth : 0 ≤ Bfourth)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bfourth))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMat Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ)
      atTop (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_smooth_trimmedBootstrapVariance_tendsto_of_normFourth_integral_norm_sq
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (thetaStar := thetaStar)
    (V := V) G hV hPstar hτpos hτinv hT hZmeas hThetaMem
    hcoordMem
    (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
    hlinearization hSecond hBfourth hNormFourth hNormFourthInt

/-- Indexed smooth trimmed covariance route with the trimming-tail probability
and Gaussian-limit coordinate `MemLp 2` premises discharged. -/
theorem
    chapter10_indexed_smooth_trimmedVariance_normFourth_integral_norm_sq_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {τ : ℕ → ℝ} {Bsecond Bfourth : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hZmeas :
      ∀ n ω, Measurable (fun ωs => (thetaStar n ω ωs : r → ℝ)))
    (hThetaMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ)) 2
          (Pstar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖(thetaStar n ω ωs : r → ℝ)‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => Bsecond))
    (hBfourth : 0 ≤ Bfourth)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bfourth))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInMeasure μ
      (trimmedBootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ)
      atTop (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_indexed_smooth_trimmedBootstrapVariance_tendsto_of_normFourth_integral_norm_sq
    (μ := μ) (Pstar := Pstar) (Tstar := Tstar) (thetaStar := thetaStar)
    (V := V) G hV hPstar hτpos hτinv hT hZmeas hThetaMem
    hcoordMem
    (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
    hlinearization hSecond hBfourth hNormFourth hNormFourthInt

end BootstrapCovariance

section SmoothFunctionBootstrapVarianceCovarianceRoutes

/-- Hansen Theorem 10.8, smooth plug-in covariance consistency from the
Theorem 10.9 covariance-matrix route.

If the plug-in Jacobian converges in ordinary probability and the underlying
bootstrap statistic satisfies weak convergence plus Hansen's coordinate and
coordinate-sum uniform-square-tail conditions, then the deterministic
conditional covariance input `Cov* Zstar` can be inserted into the smooth
functional `G'VG`. -/
theorem
    chapter10_bootstrap_smooth_variance_consistency_of_covarianceMat_uniformSquareTail
    {d r : Type*} [Fintype d] [Fintype r] [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → d → ℝ}
    {Z : Ωlim → d → ℝ}
    {Gseq : ℕ → Ω → Matrix d r ℝ} {G : Matrix d r ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
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
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gseq n ω)
          (bootstrapCovarianceMat Pstar Zstar n ω))
      (fun _ =>
        smoothFunctionVarianceFunctional G
          (fun a c =>
            (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
              (∫ ωlim, Z ωlim a ∂ν) *
                (∫ ωlim, Z ωlim c ∂ν))) :=
  chapter10_bootstrap_smooth_variance_consistency_of_tendstoInMeasure_components
    (μ := μ) (Pstar := Pstar)
    (Gseq := Gseq) (Vseq := bootstrapCovarianceMat Pstar Zstar)
    (G := G)
    (V := fun a c =>
      (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
        (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν))
    hPstar hG
    (chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z)
      hPstar hZmem hZlim hweak hTailCoord hTailSum)

/-- Hansen Theorem 10.8, smooth plug-in covariance consistency from
fourth-moment covariance premises.

This wrapper composes the fourth-moment constructor for Hansen's
uniform-square-tail covariance condition with the smooth `G'VG`
continuous-mapping bridge. -/
theorem
    chapter10_bootstrap_smooth_variance_consistency_of_covarianceMat_fourthMoment_memLp
    {d r : Type*} [Fintype d] [Fintype r] [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → d → ℝ}
    {Z : Ωlim → d → ℝ}
    {Gseq : ℕ → Ω → Matrix d r ℝ} {G : Matrix d r ℝ}
    {Bcoord : d → ℝ} {Bsum : d → d → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoord :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω => ∫ ωs, (Zstar n ω ωs a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordInt :
      ∀ n ω a, Integrable (fun ωs => (Zstar n ω ωs a) ^ 4)
        (Pstar n ω))
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSum :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs, (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumInt :
      ∀ n ω a c,
        Integrable
          (fun ωs => (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4)
          (Pstar n ω)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gseq n ω)
          (bootstrapCovarianceMat Pstar Zstar n ω))
      (fun _ =>
        smoothFunctionVarianceFunctional G
          (fun a c =>
            (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
              (∫ ωlim, Z ωlim a ∂ν) *
                (∫ ωlim, Z ωlim c ∂ν))) :=
  chapter10_bootstrap_smooth_variance_consistency_of_tendstoInMeasure_components
    (μ := μ) (Pstar := Pstar)
    (Gseq := Gseq) (Vseq := bootstrapCovarianceMat Pstar Zstar)
    (G := G)
    (V := fun a c =>
      (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
        (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν))
    hPstar hG
    (chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_fourthMoment_memLp_limit
      (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z)
      (Bcoord := Bcoord) (Bsum := Bsum)
      hPstar hZmem hZlim hweak hBcoord hFourthCoord hFourthCoordInt
      hBsum hFourthSum hFourthSumInt)

/-- Hansen Theorem 10.8, smooth plug-in covariance consistency from bounded
bootstrap statistics.

Eventual deterministic bounds for coordinates and coordinate sums discharge
the covariance matrix's uniform-square-tail premises before the smooth `G'VG`
bridge is applied. -/
theorem
    chapter10_bootstrap_smooth_variance_consistency_of_covarianceMat_eventualBound_memLp
    {d r : Type*} [Fintype d] [Fintype r] [IsFiniteMeasure ν]
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → d → ℝ}
    {Z : Ωlim → d → ℝ}
    {Gseq : ℕ → Ω → Matrix d r ℝ} {G : Matrix d r ℝ}
    {Ccoord : d → ℝ} {Csum : d → d → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs a| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |Zstar n ω ωs a + Zstar n ω ωs c| ≤ Csum a c) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gseq n ω)
          (bootstrapCovarianceMat Pstar Zstar n ω))
      (fun _ =>
        smoothFunctionVarianceFunctional G
          (fun a c =>
            (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
              (∫ ωlim, Z ωlim a ∂ν) *
                (∫ ωlim, Z ωlim c ∂ν))) :=
  chapter10_bootstrap_smooth_variance_consistency_of_tendstoInMeasure_components
    (μ := μ) (Pstar := Pstar)
    (Gseq := Gseq) (Vseq := bootstrapCovarianceMat Pstar Zstar)
    (G := G)
    (V := fun a c =>
      (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
        (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν))
    hPstar hG
    (chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z)
      (Ccoord := Ccoord) (Csum := Csum)
      hPstar hZmem hZlim hweak hboundCoord hboundSum)

/-- Indexed Hansen Theorem 10.8, smooth plug-in covariance consistency from
the indexed Theorem 10.9 covariance-matrix route. -/
theorem
    chapter10_indexed_bootstrap_smooth_variance_consistency_of_covarianceMat_uniformSquareTail
    {d r : Type*} [Fintype d] [Fintype r] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → d → ℝ}
    {Z : Ωlim → d → ℝ}
    {Gseq : ℕ → Ω → Matrix d r ℝ} {G : Matrix d r ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
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
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gseq n ω)
          (bootstrapCovarianceMatIndexed Pstar Zstar n ω))
      (fun _ =>
        smoothFunctionVarianceFunctional G
          (fun a c =>
            (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
              (∫ ωlim, Z ωlim a ∂ν) *
                (∫ ωlim, Z ωlim c ∂ν))) :=
  chapter10_indexed_bootstrap_smooth_variance_consistency_of_tendstoInMeasure_components
    (μ := μ) (Pstar := Pstar)
    (Gseq := Gseq) (Vseq := bootstrapCovarianceMatIndexed Pstar Zstar)
    (G := G)
    (V := fun a c =>
      (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
        (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν))
    hPstar hG
    (chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z)
      hPstar hZmem hZlim hweak hTailCoord hTailSum)

/-- Indexed Hansen Theorem 10.8, smooth plug-in covariance consistency from
indexed fourth-moment covariance premises. -/
theorem
    chapter10_indexed_bootstrap_smooth_variance_consistency_of_covarianceMat_fourthMoment_memLp
    {d r : Type*} [Fintype d] [Fintype r] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → d → ℝ}
    {Z : Ωlim → d → ℝ}
    {Gseq : ℕ → Ω → Matrix d r ℝ} {G : Matrix d r ℝ}
    {Bcoord : d → ℝ} {Bsum : d → d → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoord :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω => ∫ ωs, (Zstar n ω ωs a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordInt :
      ∀ n ω a, Integrable (fun ωs => (Zstar n ω ωs a) ^ 4)
        (Pstar n ω))
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSum :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs, (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumInt :
      ∀ n ω a c,
        Integrable
          (fun ωs => (Zstar n ω ωs a + Zstar n ω ωs c) ^ 4)
          (Pstar n ω)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gseq n ω)
          (bootstrapCovarianceMatIndexed Pstar Zstar n ω))
      (fun _ =>
        smoothFunctionVarianceFunctional G
          (fun a c =>
            (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
              (∫ ωlim, Z ωlim a ∂ν) *
                (∫ ωlim, Z ωlim c ∂ν))) :=
  chapter10_indexed_bootstrap_smooth_variance_consistency_of_tendstoInMeasure_components
    (μ := μ) (Pstar := Pstar)
    (Gseq := Gseq) (Vseq := bootstrapCovarianceMatIndexed Pstar Zstar)
    (G := G)
    (V := fun a c =>
      (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
        (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν))
    hPstar hG
    (chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_fourthMoment_memLp_limit
      (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z)
      (Bcoord := Bcoord) (Bsum := Bsum)
      hPstar hZmem hZlim hweak hBcoord hFourthCoord hFourthCoordInt
      hBsum hFourthSum hFourthSumInt)

/-- Indexed Hansen Theorem 10.8, smooth plug-in covariance consistency from
bounded bootstrap statistics. -/
theorem
    chapter10_indexed_bootstrap_smooth_variance_consistency_of_covarianceMat_eventualBound_memLp
    {d r : Type*} [Fintype d] [Fintype r] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → d → ℝ}
    {Z : Ωlim → d → ℝ}
    {Gseq : ℕ → Ω → Matrix d r ℝ} {G : Matrix d r ℝ}
    {Ccoord : d → ℝ} {Csum : d → d → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs a| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |Zstar n ω ωs a + Zstar n ω ωs c| ≤ Csum a c) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gseq n ω)
          (bootstrapCovarianceMatIndexed Pstar Zstar n ω))
      (fun _ =>
        smoothFunctionVarianceFunctional G
          (fun a c =>
            (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
              (∫ ωlim, Z ωlim a ∂ν) *
                (∫ ωlim, Z ωlim c ∂ν))) := by
  have hV :
      TendstoInMeasure μ (bootstrapCovarianceMatIndexed Pstar Zstar) atTop
        (fun _ => fun a c =>
          (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
            (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
    chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := ν) (Pstar := Pstar) (Zstar := Zstar) (Z := Z)
      (Ccoord := Ccoord) (Csum := Csum)
      hPstar hZmem hZlim hweak hboundCoord hboundSum
  exact
    chapter10_indexed_bootstrap_smooth_variance_consistency_of_tendstoInMeasure_components
      (μ := μ) (Pstar := Pstar)
      (Gseq := Gseq) (Vseq := bootstrapCovarianceMatIndexed Pstar Zstar)
      (G := G)
      (V := fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν))
      hPstar hG hV

/-- Hansen Theorem 10.8/10.10 compact-range quadratic smooth plug-in
covariance route.

The compact-range quadratic Theorem 10.10 covariance route supplies
`Cov* thetaStar -> Glin V Glin'`; this wrapper inserts that conditional
covariance input directly into the smooth plug-in estimator. -/
theorem chapter10_smoothVariance_smoothCov_compactRangeQuadratic
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap Glin (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap Glin (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hBθ : 0 ≤ Bθ)
    (hThetaNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖thetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bθ))
    (hThetaNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖thetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (bootstrapCovarianceMat Pstar
            (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) := by
  classical
  exact
    chapter10_bootstrap_smooth_variance_consistency_of_tendstoInMeasure_components
      (μ := μ) (Pstar := Pstar)
      (Gseq := Hseq)
      (Vseq := bootstrapCovarianceMat Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      (G := H) (V := Glin * V * Glinᵀ) hPstar hH
      (chapter10_smooth_covarianceMat_tendsto_of_compact_range_quadratic_normFourthMoment
        (μ := μ) (Pstar := Pstar)
        (Tstar := Tstar) (thetaStar := thetaStar) (ρ := ρ) (V := V)
        Glin hV hPstar hT hK hTstar hthetaStar hcoordMem
        (fun a => memLp_multivariateGaussian_coord_two (S := Glin * V * Glinᵀ) a)
        hlinearized_mem hthetaStar_mem hρsq hTNormFourth hTNormFourthInt
        hR_bound hBθ hThetaNormFourth hThetaNormFourthInt)

/-- Indexed Hansen Theorem 10.8/10.10 compact-range quadratic smooth plug-in
covariance route. -/
theorem chapter10_indexed_smoothVariance_smoothCov_compactRangeQuadratic
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hK : IsCompact K)
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
    (hlinearized_mem :
      ∀ n ω ωs, matrixContinuousLinearMap Glin (Tstar n ω ωs) ∈ K)
    (hthetaStar_mem : ∀ n ω ωs, thetaStar n ω ωs ∈ K)
    (hρsq : Tendsto (fun n => ρ n ^ 2) atTop (𝓝 0))
    (hTNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => BT))
    (hTNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hR_bound : ∀ n ω ωs,
      dist (thetaStar n ω ωs) (matrixContinuousLinearMap Glin (Tstar n ω ωs)) ≤
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hBθ : 0 ≤ Bθ)
    (hThetaNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖thetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bθ))
    (hThetaNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖thetaStar n ω ωs‖ ^ 4)
        (Pstar n ω)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (bootstrapCovarianceMatIndexed Pstar
            (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) := by
  classical
  exact
    chapter10_indexed_bootstrap_smooth_variance_consistency_of_tendstoInMeasure_components
      (μ := μ) (Pstar := Pstar)
      (Gseq := Hseq)
      (Vseq := bootstrapCovarianceMatIndexed Pstar
        (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)))
      (G := H) (V := Glin * V * Glinᵀ) hPstar hH
      (chapter10_indexed_smooth_covarianceMat_tendsto_of_compact_range_quadratic_normFourthMoment
        (μ := μ) (Pstar := Pstar)
        (Tstar := Tstar) (thetaStar := thetaStar) (ρ := ρ) (V := V)
        Glin hV hPstar hT hK hTstar hthetaStar hcoordMem
        (fun a => memLp_multivariateGaussian_coord_two (S := Glin * V * Glinᵀ) a)
        hlinearized_mem hthetaStar_mem hρsq hTNormFourth hTNormFourthInt
        hR_bound hBθ hThetaNormFourth hThetaNormFourthInt)

end SmoothFunctionBootstrapVarianceCovarianceRoutes

end HansenEconometrics
