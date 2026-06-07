import HansenEconometrics.Chapter10Bootstrap.Regression

/-!
# Chapter 10 — Finite replication estimators

Finite simulation (`B`-replication) bootstrap variance and covariance estimators
and their consistency transfers to the ideal bootstrap quantities (Hansen
Theorem 10.11). This is the chapter-facing finite-replication estimator API.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.Elementwise Function

namespace HansenEconometrics

variable {Ω Ωs Ωlim E F k : Type*}
variable {mΩ : MeasurableSpace Ω} {mΩs : MeasurableSpace Ωs}
variable {mΩlim : MeasurableSpace Ωlim}
variable {μ : Measure Ω} {ν : Measure Ωlim}

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

/-- Real `L²` simulation-error constructor.

An `O(n⁻¹)` mean-square bound for a real approximation error implies that the
error is `oₚ(1)`.  The finite-replication variance/covariance wrappers below
use this to replace abstract simulation-error convergence premises by the
mean-square bounds supplied by bounded bootstrap simulations. -/
theorem tendstoInMeasure_zero_of_integral_sq_error_le_inv
    [IsFiniteMeasure μ] {E : ℕ → Ω → ℝ} {C : ℝ}
    (hInt : ∀ n, Integrable (fun ω => ‖E n ω‖ ^ (2 : ℝ)) μ)
    (hbound :
      ∀ᶠ n in atTop,
        (∫ ω, ‖E n ω‖ ^ (2 : ℝ) ∂μ) ≤ C / (n : ℝ)) :
    TendstoInMeasure μ E atTop (fun _ => 0) := by
  refine tendstoInMeasure_of_integral_norm_sq_le_inv
    (μ := μ) (X := E) (x := 0) (C := C) ?_ ?_
  · simpa using hInt
  · simpa using hbound

/-- Matrix `L²` simulation-error constructor from coordinatewise
`O(n⁻¹)` bounds. -/
theorem tendstoInMeasure_matrix_zero_of_integral_sq_entry_error_le_inv
    [IsFiniteMeasure μ] {k : Type*} [Fintype k]
    {E : ℕ → Ω → Matrix k k ℝ} {C : k → k → ℝ}
    (hInt :
      ∀ a c n, Integrable (fun ω => ‖E n ω a c‖ ^ (2 : ℝ)) μ)
    (hbound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω, ‖E n ω a c‖ ^ (2 : ℝ) ∂μ) ≤ C a c / (n : ℝ)) :
    TendstoInMeasure μ E atTop (fun _ => 0) := by
  refine tendstoInMeasure_pi (fun a => ?_)
  refine tendstoInMeasure_pi (fun c => ?_)
  simpa using
    tendstoInMeasure_zero_of_integral_sq_error_le_inv
      (μ := μ) (E := fun n ω => E n ω a c) (C := C a c)
      (hInt a c) (hbound a c)

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

/-- Hansen Theorem 10.9/10.11 finite-replication variance from an `L²`
simulation-error bound.

This theorem-facing constructor replaces the abstract finite-replication
`oₚ(1)` premise by a concrete `O(n⁻¹)` mean-square bound for the difference
between the finite-replication variance and the conditional bootstrap
variance. -/
theorem chapter10_finiteReplicationVariance_tendsto_of_l2_simulation_error
    [IsFiniteMeasure μ]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {σ2 Cfinite : ℝ}
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ))
    (hboot :
      TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
        (fun _ => σ2)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => σ2) :=
  chapter10_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ)
    (tendstoInMeasure_zero_of_integral_sq_error_le_inv
      (μ := μ)
      (E := fun n ω =>
        finiteReplicationVarianceMomentReal Zsim n ω -
          bootstrapVarianceReal Pstar Zstar n ω)
      (C := Cfinite) hfiniteInt hfiniteBound)
    hboot

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

/-- Hansen Theorem 10.9/10.11 centered finite-replication variance from an
`L²` simulation-error bound. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_l2_simulation_error
    [IsFiniteMeasure μ]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {σ2 Cfinite : ℝ}
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ))
    (hboot :
      TendstoInMeasure μ (bootstrapVarianceReal Pstar Zstar) atTop
        (fun _ => σ2)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => σ2) :=
  chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ)
    (tendstoInMeasure_zero_of_integral_sq_error_le_inv
      (μ := μ)
      (E := fun n ω =>
        finiteReplicationVarianceCenteredReal Zsim n ω -
          bootstrapVarianceReal Pstar Zstar n ω)
      (C := Cfinite) hfiniteInt hfiniteBound)
    hboot

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

/-- Zero-mean finite-replication centered-variance wrapper for Hansen Theorem
10.11. -/
theorem chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_zero_mean_moments
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
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => σ2) := by
  simpa using
    (chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_moments
      (μ := μ) (m := 0) (m₂ := σ2)
      hPstar hZ hmean hsecond hfinite)

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

/-- Hansen Theorem 10.9/10.11 finite-replication variance from bootstrap weak
convergence and an eventual deterministic bootstrap bound.

The eventual bound discharges the uniform-square-tail premise in the
conditional variance layer; the finite-replication side remains the direct
`oₚ(1)` simulation-error premise. -/
theorem
    chapter10_finiteReplicationVariance_tendsto_of_eventualBound_memLp_limit
    [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ} {C : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs| ≤ C)
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
    (chapter10_bootstrap_variance_consistency_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hbound)

/-- Hansen Theorem 10.9/10.11 centered finite-replication variance from
bootstrap weak convergence and an eventual deterministic bootstrap bound. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_eventualBound_memLp_limit
    [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ} {C : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs| ≤ C)
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
    (chapter10_bootstrap_variance_consistency_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hbound)

/-- Hansen Theorem 10.9/10.11 finite-replication variance from bootstrap weak
convergence, a named uniform-square-tail condition, and an `L²`
simulation-error bound. -/
theorem
    chapter10_finiteReplicationVariance_tendsto_of_uniformSquareTail_l2
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ} {Cfinite : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTail μ Pstar Zstar ν Z)
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_finiteReplicationVariance_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
    hfiniteInt hfiniteBound
    (chapter10_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail)

/-- Hansen Theorem 10.9/10.11 finite-replication variance from bootstrap weak
convergence, an eventual deterministic bootstrap bound, and an `L²`
simulation-error bound. -/
theorem
    chapter10_finiteReplicationVariance_tendsto_of_eventualBound_l2
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ} {C Cfinite : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs| ≤ C)
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_finiteReplicationVariance_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
    hfiniteInt hfiniteBound
    (chapter10_bootstrap_variance_consistency_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hbound)

/-- Hansen Theorem 10.9/10.11 centered finite-replication variance from
bootstrap weak convergence, a named uniform-square-tail condition, and an `L²`
simulation-error bound. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_uniformSquareTail_l2
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ} {Cfinite : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTail μ Pstar Zstar ν Z)
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
    hfiniteInt hfiniteBound
    (chapter10_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail)

/-- Hansen Theorem 10.9/10.11 centered finite-replication variance from
bootstrap weak convergence, an eventual deterministic bootstrap bound, and an
`L²` simulation-error bound. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_eventualBound_l2
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ} {C Cfinite : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs| ≤ C)
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar Zstar n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
    hfiniteInt hfiniteBound
    (chapter10_bootstrap_variance_consistency_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hbound)

/-- Hansen Theorem 10.9/10.11 finite-replication variance from bootstrap weak
convergence and fourth-moment tail controls. -/
theorem chapter10_finiteReplicationVariance_tendsto_of_weak_distribution_fourthMoment_tail
    [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω))
    (hLimitTail :
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
            (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε)
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
    (chapter10_bootstrap_variance_consistency_of_weak_distribution_fourthMoment_tail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hB
      hFourth hFourthInt hLimitTail)

/-- Hansen Theorem 10.9/10.11 centered finite-replication variance from
bootstrap weak convergence and fourth-moment tail controls. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_fourthMoment_tail
    [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω))
    (hLimitTail :
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
            (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε)
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
    (chapter10_bootstrap_variance_consistency_of_weak_distribution_fourthMoment_tail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hB
      hFourth hFourthInt hLimitTail)

/-- Hansen Theorem 10.9/10.11 finite-replication variance from bootstrap weak
convergence and fourth-moment convergence, with the weak-limit tail premise
discharged by `MemLp Z 2 ν`. -/
theorem
    chapter10_finiteReplicationVariance_tendsto_of_fourthMoment_memLp_limit
    [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω))
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
    (chapter10_bootstrap_variance_consistency_of_weak_distribution_fourthMoment_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hB
      hFourth hFourthInt)

/-- Hansen Theorem 10.9/10.11 centered finite-replication variance from
bootstrap weak convergence and fourth-moment convergence, with the weak-limit
tail premise discharged by `MemLp Z 2 ν`. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_fourthMoment_memLp_limit
    [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → ℝ}
    {Z : Ωlim → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω))
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
    (chapter10_bootstrap_variance_consistency_of_weak_distribution_fourthMoment_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hB
      hFourth hFourthInt)

/-- Hansen Theorem 10.10/10.11 finite-replication variance for a smooth
function under exact derivative linearization and an underlying norm
fourth-moment premise.

The conditional bootstrap variance consistency is supplied by
`chapter10_smooth_bootstrap_variance_consistency_of_linearization_normFourthMoment`;
the finite-replication side remains Hansen Theorem 10.11's simulation-error
premise against that conditional bootstrap variance. -/
theorem
    chapter10_finiteReplicationVariance_tendsto_of_smooth_linearization_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
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
    (hlimMem :
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_smooth_bootstrap_variance_consistency_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hB hNormFourth hNormFourthInt)

/-- Textbook-centered finite-replication variance version of
`chapter10_finiteReplicationVariance_tendsto_of_smooth_linearization_normFourthMoment`. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_linearization_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
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
    (hlimMem :
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_smooth_bootstrap_variance_consistency_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hB hNormFourth hNormFourthInt)

/-- Hansen Theorem 10.10/10.11 finite-replication variance for a smooth
function from the compact-tail remainder route and a norm fourth-moment
premise on the nonlinear smooth statistic.

This is the finite-replication face of
`chapter10_smooth_bootstrap_variance_of_compact_tail_remainder_normFourthMoment`. -/
theorem
    chapter10_finiteReplicationVariance_tendsto_smooth_compactTail_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_smooth_bootstrap_variance_of_compact_tail_remainder_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (R := R) (V := V) G a hV hPstar hT
      hTstar hthetaStar hcoordMem hlimMem hCompactTail hR_tail hR_bound
      hB hNormFourth hNormFourthInt)

/-- Textbook-centered finite-replication variance version of
`chapter10_finiteReplicationVariance_tendsto_smooth_compactTail_normFourth`. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_smooth_compactTail_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {R : ℕ → Ω → Ωs → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_smooth_bootstrap_variance_of_compact_tail_remainder_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (R := R) (V := V) G a hV hPstar hT
      hTstar hthetaStar hcoordMem hlimMem hCompactTail hR_tail hR_bound
      hB hNormFourth hNormFourthInt)

/-- Hansen Theorem 10.10/10.11 finite-replication variance for a smooth
function from the compact-range quadratic Taylor-remainder route.

The conditional bootstrap variance consistency is supplied by the fixed compact
range, quadratic remainder envelope, and norm fourth-moment controls; the
finite-replication side remains Hansen Theorem 10.11's simulation-error premise
against that conditional bootstrap variance. -/
theorem
    chapter10_finiteReplicationVariance_tendsto_smooth_compactRange_quadratic
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT : ℝ} (a : r)
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
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_smooth_bootstrap_variance_of_compact_range_quadratic_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G a hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound hBθ
      hThetaNormFourth hThetaNormFourthInt)

/-- Textbook-centered finite-replication variance version of
`chapter10_finiteReplicationVariance_tendsto_smooth_compactRange_quadratic`. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_smooth_compactRange_quadratic
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT : ℝ} (a : r)
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
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_smooth_bootstrap_variance_of_compact_range_quadratic_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G a hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound hBθ
      hThetaNormFourth hThetaNormFourthInt)

/-- Finite-replication variance from the compact-range quadratic route with
deterministic compact-membership square-tail bounds. -/
theorem
    chapter10_finiteReplicationVariance_tendsto_smooth_compactRange_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {BT : ℝ} (a : r)
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
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_smooth_bootstrap_variance_of_compact_range_quadratic_eventualBound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G a hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound)

/-- Textbook-centered finite-replication version of
`chapter10_finiteReplicationVariance_tendsto_smooth_compactRange_bound`. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_smooth_compactRange_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {BT : ℝ} (a : r)
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
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_smooth_bootstrap_variance_of_compact_range_quadratic_eventualBound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G a hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound)

/-- `L²` simulation-error version of
`chapter10_finiteReplicationVariance_tendsto_smooth_compactRange_quadratic`. -/
theorem
    chapter10_finiteReplicationVariance_tendsto_smooth_compactRangeQuad_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT Cfinite : ℝ} (a : r)
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
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVariance_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
    hfiniteInt hfiniteBound
    (chapter10_smooth_bootstrap_variance_of_compact_range_quadratic_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G a hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound hBθ
      hThetaNormFourth hThetaNormFourthInt)

/-- Textbook-centered `L²` simulation-error version of the compact-range
quadratic scalar finite-replication variance bridge. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_smooth_compactRangeQuad_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT Cfinite : ℝ} (a : r)
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
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
    hfiniteInt hfiniteBound
    (chapter10_smooth_bootstrap_variance_of_compact_range_quadratic_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G a hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound hBθ
      hThetaNormFourth hThetaNormFourthInt)

/-- `L²` simulation-error version of
`chapter10_finiteReplicationVariance_tendsto_of_smooth_linearization_normFourthMoment`. -/
theorem
    chapter10_finiteReplicationVariance_tendsto_of_smooth_normFourth_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B Cfinite : ℝ} (a : r)
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
    (hlimMem :
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVariance_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
    hfiniteInt hfiniteBound
    (chapter10_smooth_bootstrap_variance_consistency_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hB hNormFourth hNormFourthInt)

/-- Textbook-centered `L²` simulation-error version of the smooth norm-fourth
finite-replication variance bridge. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_normFourth_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B Cfinite : ℝ} (a : r)
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
    (hlimMem :
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
    hfiniteInt hfiniteBound
    (chapter10_smooth_bootstrap_variance_consistency_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hB hNormFourth hNormFourthInt)

/-- Hansen Theorem 10.10/10.11 finite-replication variance for a smooth
function under exact derivative linearization and an eventual deterministic
coordinate bound.

The bound discharges the conditional Theorem 10.9 tail premise through
`chapter10_smooth_bootstrap_variance_consistency_of_linearization_eventualBound_memLp`;
the finite-replication side is the direct Theorem 10.11 simulation-error
transfer against that conditional bootstrap variance. -/
theorem
    chapter10_finiteReplicationVariance_tendsto_of_smooth_linearization_eventualBound_memLp
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {C : ℝ} (a : r)
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
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hbound :
      ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ C)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_smooth_bootstrap_variance_consistency_of_linearization_eventualBound_memLp
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hbound)

/-- Textbook-centered finite-replication variance version of the smooth
bounded finite-replication bridge above. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_eventualBound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {C : ℝ} (a : r)
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
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hbound :
      ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ C)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_smooth_bootstrap_variance_consistency_of_linearization_eventualBound_memLp
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hbound)

/-- `L²` simulation-error version of
`chapter10_finiteReplicationVariance_tendsto_of_smooth_linearization_eventualBound_memLp`. -/
theorem
    chapter10_finiteReplicationVariance_tendsto_of_smooth_eventualBound_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {C Cfinite : ℝ} (a : r)
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
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hbound :
      ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ C)
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVariance_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
    hfiniteInt hfiniteBound
    (chapter10_smooth_bootstrap_variance_consistency_of_linearization_eventualBound_memLp
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hbound)

/-- Textbook-centered `L²` simulation-error version of the smooth bounded
finite-replication variance bridge. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_eventualBound_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {C Cfinite : ℝ} (a : r)
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
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hbound :
      ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ C)
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
    hfiniteInt hfiniteBound
    (chapter10_smooth_bootstrap_variance_consistency_of_linearization_eventualBound_memLp
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hbound)

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

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication variance from an
`L²` simulation-error bound. -/
theorem chapter10_indexed_finiteReplicationVariance_tendsto_of_l2_simulation_error
    [IsFiniteMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {σ2 Cfinite : ℝ}
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ))
    (hboot :
      TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
        (fun _ => σ2)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => σ2) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ)
    (tendstoInMeasure_zero_of_integral_sq_error_le_inv
      (μ := μ)
      (E := fun n ω =>
        finiteReplicationVarianceMomentReal Zsim n ω -
          bootstrapVarianceRealIndexed Pstar Zstar n ω)
      (C := Cfinite) hfiniteInt hfiniteBound)
    hboot

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

/-- Indexed Hansen Theorem 10.9/10.11 centered finite-replication variance from
an `L²` simulation-error bound. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_l2_simulation_error
    [IsFiniteMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {σ2 Cfinite : ℝ}
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ))
    (hboot :
      TendstoInMeasure μ (bootstrapVarianceRealIndexed Pstar Zstar) atTop
        (fun _ => σ2)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => σ2) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ)
    (tendstoInMeasure_zero_of_integral_sq_error_le_inv
      (μ := μ)
      (E := fun n ω =>
        finiteReplicationVarianceCenteredReal Zsim n ω -
          bootstrapVarianceRealIndexed Pstar Zstar n ω)
      (C := Cfinite) hfiniteInt hfiniteBound)
    hboot

/-- Theorem 10.9/10.11 ordinary nonparametric-bootstrap finite-replication
scalar variance route for iid observations.

The conditional variance target is the normalized `Fin (n+1)` ordinary
bootstrap variance.  Coordinatewise `O(n⁻¹)` mean-square simulation error
transfers the moment-form finite-replication variance estimator to the
population variance target. -/
theorem chapter10_indexed_finiteReplicationVariance_finSucc_l2_iid
    [IsProbabilityMeasure μ]
    {Zsim : ℕ → ℕ → Ω → ℝ} {Cfinite : ℝ}
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (fun ω => Y 0 ω) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed
              (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
              (fun n _ =>
                ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
              n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed
              (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
              (fun n _ =>
                ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
              n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => Var[fun ω => Y 0 ω; μ]) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (Zstar := fun n ω ωs =>
      Real.sqrt (n + 1 : ℝ) *
        (empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω)
            (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
    (σ2 := Var[fun ω => Y 0 ω; μ]) (Cfinite := Cfinite)
    hfiniteInt hfiniteBound
    (chapter10_indexed_bootstrap_variance_finSucc_resampleMean_tendsto_of_iid
      (μ := μ) Y hYmem hindep hident)

/-- Theorem 10.9/10.11 ordinary nonparametric-bootstrap finite-replication
scalar variance route with the textbook `iIndepFun` premise. -/
theorem chapter10_indexed_finiteReplicationVariance_finSucc_l2_iIndep
    [IsProbabilityMeasure μ]
    {Zsim : ℕ → ℕ → Ω → ℝ} {Cfinite : ℝ}
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (fun ω => Y 0 ω) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed
              (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
              (fun n _ =>
                ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
              n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed
              (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
              (fun n _ =>
                ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
              n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => Var[fun ω => Y 0 ω; μ]) :=
  chapter10_indexed_finiteReplicationVariance_finSucc_l2_iid
    (μ := μ) (Zsim := Zsim) (Cfinite := Cfinite) Y hYmem
    (fun _ _ hij => hindep.indepFun hij) hident hfiniteInt hfiniteBound

/-- Theorem 10.9/10.11 ordinary nonparametric-bootstrap centered
finite-replication scalar variance route for iid observations. -/
theorem chapter10_indexed_finiteReplicationVarianceCenteredReal_finSucc_l2_iid
    [IsProbabilityMeasure μ]
    {Zsim : ℕ → ℕ → Ω → ℝ} {Cfinite : ℝ}
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (fun ω => Y 0 ω) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed
              (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
              (fun n _ =>
                ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
              n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed
              (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
              (fun n _ =>
                ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
              n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => Var[fun ω => Y 0 ω; μ]) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (Zstar := fun n ω ωs =>
      Real.sqrt (n + 1 : ℝ) *
        (empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω)
            (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
    (σ2 := Var[fun ω => Y 0 ω; μ]) (Cfinite := Cfinite)
    hfiniteInt hfiniteBound
    (chapter10_indexed_bootstrap_variance_finSucc_resampleMean_tendsto_of_iid
      (μ := μ) Y hYmem hindep hident)

/-- Theorem 10.9/10.11 ordinary nonparametric-bootstrap centered
finite-replication scalar variance route with the textbook `iIndepFun`
premise. -/
theorem chapter10_indexed_finiteReplicationVarianceCenteredReal_finSucc_l2_iIndep
    [IsProbabilityMeasure μ]
    {Zsim : ℕ → ℕ → Ω → ℝ} {Cfinite : ℝ}
    (Y : ℕ → Ω → ℝ)
    (hYmem : MemLp (fun ω => Y 0 ω) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed
              (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
              (fun n _ =>
                ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
              n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed
              (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
              (fun n _ =>
                ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
              n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => Var[fun ω => Y 0 ω; μ]) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_finSucc_l2_iid
    (μ := μ) (Zsim := Zsim) (Cfinite := Cfinite) Y hYmem
    (fun _ _ hij => hindep.indepFun hij) hident hfiniteInt hfiniteBound

/-- Theorem 10.9/10.11 ordinary nonparametric-bootstrap finite-replication
scalar variance route from Hansen's fourth-moment cumulant formula.

This combines the concrete `Fin (n+1)` cumulant route for conditional
bootstrap variance consistency with an `O(n⁻¹)` mean-square simulation-error
bound for the moment-form finite-replication variance estimator. -/
theorem
    chapter10_indexed_finiteReplicationVariance_finSucc_l2_of_weak_distribution_cumulants
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → ℝ} {Z : Ωlim → ℝ} {σ2 Cfinite : ℝ}
    (Y : ℕ → Ω → ℝ)
    (hZlim : MemLp Z 2 ν)
    (hweak :
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
        ν Z)
    (hCumulant2 :
      TendstoInMeasure μ
        (fun n ω =>
          empiricalCumulant2 (fun i : Fin (n + 1) => Y i.val ω))
        atTop (fun _ => σ2))
    (hScaledCumulant4 :
      TendstoInMeasure μ
        (fun n ω =>
          empiricalCumulant4 (fun i : Fin (n + 1) => Y i.val ω) /
            (n + 1 : ℝ))
        atTop (fun _ => 0))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed
              (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
              (fun n _ =>
                ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
              n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed
              (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
              (fun n _ =>
                ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
              n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν -
        (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (Zstar := fun n ω ωs =>
      Real.sqrt (n + 1 : ℝ) *
        (empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω)
            (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
    (Cfinite := Cfinite) hfiniteInt hfiniteBound
    (chapter10_indexed_bootstrap_variance_finSucc_resampleMean_of_weak_distribution_cumulants
      (μ := μ) (ν := ν) (Y := Y) hZlim hweak hCumulant2
      hScaledCumulant4)

set_option linter.style.longLine false in
/-- Theorem 10.9/10.11 ordinary nonparametric-bootstrap centered
finite-replication scalar variance route from Hansen's fourth-moment cumulant
formula. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_finSucc_l2_of_weak_distribution_cumulants
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → ℝ} {Z : Ωlim → ℝ} {σ2 Cfinite : ℝ}
    (Y : ℕ → Ω → ℝ)
    (hZlim : MemLp Z 2 ν)
    (hweak :
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
        ν Z)
    (hCumulant2 :
      TendstoInMeasure μ
        (fun n ω =>
          empiricalCumulant2 (fun i : Fin (n + 1) => Y i.val ω))
        atTop (fun _ => σ2))
    (hScaledCumulant4 :
      TendstoInMeasure μ
        (fun n ω =>
          empiricalCumulant4 (fun i : Fin (n + 1) => Y i.val ω) /
            (n + 1 : ℝ))
        atTop (fun _ => 0))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed
              (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
              (fun n _ =>
                ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
              n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed
              (Ωboot := fun n => Fin (n + 1) → Fin (n + 1))
              (fun n _ =>
                ProbabilityTheory.uniformOn
                  (Set.univ : Set (Fin (n + 1) → Fin (n + 1))))
              (fun n ω ωs =>
                Real.sqrt (n + 1 : ℝ) *
                  (empiricalBootstrapResampleMean
                      (fun i : Fin (n + 1) => Y i.val ω)
                      (fun ωs t => ωs t) ωs -
                    empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
              n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν -
        (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim)
    (Pstar := fun n _ =>
      (ProbabilityTheory.uniformOn
        (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
          Measure (Fin (n + 1) → Fin (n + 1))))
    (Zstar := fun n ω ωs =>
      Real.sqrt (n + 1 : ℝ) *
        (empiricalBootstrapResampleMean
            (fun i : Fin (n + 1) => Y i.val ω)
            (fun ωs t => ωs t) ωs -
          empiricalMean (fun i : Fin (n + 1) => Y i.val ω)))
    (Cfinite := Cfinite) hfiniteInt hfiniteBound
    (chapter10_indexed_bootstrap_variance_finSucc_resampleMean_of_weak_distribution_cumulants
      (μ := μ) (ν := ν) (Y := Y) hZlim hweak hCumulant2
      hScaledCumulant4)

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

/-- Indexed zero-mean finite-replication centered-variance wrapper for Hansen
Theorem 10.11. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_zero_mean_moments
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
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => σ2) := by
  simpa using
    (chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_moments
      (μ := μ) (m := 0) (m₂ := σ2)
      hPstar hZ hmean hsecond hfinite)

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

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication variance from
bootstrap weak convergence and an eventual deterministic bootstrap bound. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_of_eventualBound_memLp_limit
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ} {C : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs| ≤ C)
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
    (chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hbound)

/-- Indexed Hansen Theorem 10.9/10.11 centered finite-replication variance
from bootstrap weak convergence and an eventual deterministic bootstrap
bound. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_eventualBound_memLp_limit
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ} {C : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs| ≤ C)
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
    (chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hbound)

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication variance from
bootstrap weak convergence, a named uniform-square-tail condition, and an `L²`
simulation-error bound. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_of_uniformSquareTail_l2
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ} {Cfinite : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z)
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
    hfiniteInt hfiniteBound
    (chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail)

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication variance from
bootstrap weak convergence, an eventual deterministic bootstrap bound, and an
`L²` simulation-error bound. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_of_eventualBound_l2
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ} {C Cfinite : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs| ≤ C)
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
    hfiniteInt hfiniteBound
    (chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hbound)

/-- Indexed Hansen Theorem 10.9/10.11 centered finite-replication variance from
bootstrap weak convergence, a named uniform-square-tail condition, and an `L²`
simulation-error bound. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_uniformSquareTail_l2
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ} {Cfinite : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTail : BootstrapUniformSquareTailIndexed μ Pstar Zstar ν Z)
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
    hfiniteInt hfiniteBound
    (chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_of_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTail)

/-- Indexed Hansen Theorem 10.9/10.11 centered finite-replication variance from
bootstrap weak convergence, an eventual deterministic bootstrap bound, and an
`L²` simulation-error bound. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_eventualBound_l2
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ} {C Cfinite : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hbound : ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs| ≤ C)
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar Zstar n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ => ∫ ωlim, (Z ωlim) ^ 2 ∂ν - (∫ ωlim, Z ωlim ∂ν) ^ 2) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
    hfiniteInt hfiniteBound
    (chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hbound)

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication variance from
bootstrap weak convergence and fourth-moment tail controls. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_of_weak_distribution_fourthMoment_tail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω))
    (hLimitTail :
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
            (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε)
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
    (chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_fourthMoment_tail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hB
      hFourth hFourthInt hLimitTail)

/-- Indexed Hansen Theorem 10.9/10.11 centered finite-replication variance
from bootstrap weak convergence and fourth-moment tail controls. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_fourthMoment_tail
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω))
    (hLimitTail :
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧
        ∀ R : ℝ, R₀ ≤ R →
          (∫ ωlim, Set.indicator {ωlim | R ≤ |Z ωlim|}
            (fun ωlim => (Z ωlim) ^ 2) ωlim ∂ν) ≤ ε)
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
    (chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_fourthMoment_tail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hB
      hFourth hFourthInt hLimitTail)

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication variance from bootstrap
weak convergence and fourth-moment convergence, with the weak-limit tail premise
discharged by `MemLp Z 2 ν`. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_of_fourthMoment_memLp_limit
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω))
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
    (chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_fourthMoment_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hB
      hFourth hFourthInt)

/-- Indexed Hansen Theorem 10.9/10.11 centered finite-replication variance from
bootstrap weak convergence and fourth-moment convergence, with the weak-limit
tail premise discharged by `MemLp Z 2 ν`. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_fourthMoment_memLp_limit
    [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → ℝ}
    {Z : Ωlim → ℝ} {B : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω, MemLp (Zstar n ω) 2 (Pstar n ω))
    (hZlim : MemLp Z 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hB : 0 ≤ B)
    (hFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, (Zstar n ω ωs) ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hFourthInt :
      ∀ n ω, Integrable (fun ωs => (Zstar n ω ωs) ^ 4) (Pstar n ω))
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
    (chapter10_indexed_bootstrap_variance_consistency_of_weak_distribution_fourthMoment_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hB
      hFourth hFourthInt)

/-- Indexed Hansen Theorem 10.10/10.11 finite-replication variance for a smooth
function under exact derivative linearization and an indexed norm
fourth-moment premise on the underlying statistic. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_of_smooth_linearization_normFourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hB hNormFourth hNormFourthInt)

/-- Textbook-centered indexed finite-replication variance version of
`chapter10_indexed_finiteReplicationVariance_tendsto_of_smooth_linearization_normFourthMoment`. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hB hNormFourth hNormFourthInt)

/-- Indexed finite-replication variance from the compact-tail remainder route
and an indexed norm fourth-moment premise on the nonlinear smooth statistic. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_smooth_compactTail_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_indexed_smooth_bootstrap_variance_of_tail_remainder_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (R := R) (V := V) G a hV hPstar hT
      hTstar hthetaStar hcoordMem hlimMem hCompactTail hR_tail hR_bound
      hB hNormFourth hNormFourthInt)

/-- Textbook-centered indexed finite-replication variance version of
`chapter10_indexed_finiteReplicationVariance_tendsto_smooth_compactTail_normFourth`. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_smooth_compactTail_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {R : ∀ n, Ω → Ωboot n → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hTstar : ∀ n ω, Measurable (Tstar n ω))
    (hthetaStar : ∀ n ω, Measurable (thetaStar n ω))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_indexed_smooth_bootstrap_variance_of_tail_remainder_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (R := R) (V := V) G a hV hPstar hT
      hTstar hthetaStar hcoordMem hlimMem hCompactTail hR_tail hR_bound
      hB hNormFourth hNormFourthInt)

/-- Indexed finite-replication variance from the compact-range quadratic
Taylor-remainder route and indexed norm fourth-moment premises. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_smooth_compactRange_quadratic
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT : ℝ} (a : r)
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
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_indexed_smooth_bootstrap_variance_of_compact_range_quadratic_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G a hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound hBθ
      hThetaNormFourth hThetaNormFourthInt)

/-- Textbook-centered indexed finite-replication variance version of
`chapter10_indexed_finiteReplicationVariance_tendsto_smooth_compactRange_quadratic`. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_smooth_compactRange_quadratic
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT : ℝ} (a : r)
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
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_indexed_smooth_bootstrap_variance_of_compact_range_quadratic_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G a hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound hBθ
      hThetaNormFourth hThetaNormFourthInt)

/-- Indexed finite-replication variance from the compact-range quadratic route
with deterministic compact-membership square-tail bounds. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_smooth_compactRange_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {BT : ℝ} (a : r)
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
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_indexed_smooth_bootstrap_variance_of_compact_range_quadratic_eventualBound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G a hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound)

/-- Textbook-centered indexed finite-replication version of
`chapter10_indexed_finiteReplicationVariance_tendsto_smooth_compactRange_bound`. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_smooth_compactRange_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {BT : ℝ} (a : r)
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
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_indexed_smooth_bootstrap_variance_of_compact_range_quadratic_eventualBound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G a hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound)

/-- Indexed `L²` simulation-error version of the compact-range quadratic
scalar finite-replication variance bridge. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_smooth_compactRangeQuad_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT Cfinite : ℝ} (a : r)
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
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_bootstrap_variance_of_compact_range_quadratic_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G a hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound hBθ
      hThetaNormFourth hThetaNormFourthInt)

/-- Textbook-centered indexed `L²` simulation-error version of the
compact-range quadratic scalar finite-replication variance bridge. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_smooth_compactRangeQuad_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT Cfinite : ℝ} (a : r)
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
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_bootstrap_variance_of_compact_range_quadratic_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G a hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound hBθ
      hThetaNormFourth hThetaNormFourthInt)

/-- Indexed `L²` simulation-error version of
`chapter10_indexed_finiteReplicationVariance_tendsto_of_smooth_linearization_normFourthMoment`. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_of_smooth_normFourth_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B Cfinite : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hB hNormFourth hNormFourthInt)

/-- Textbook-centered indexed `L²` simulation-error version of the smooth
norm-fourth finite-replication variance bridge. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_normFourth_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B Cfinite : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hB hNormFourth hNormFourthInt)

/-- Hansen Theorem 10.10/10.11 finite-replication variance for a smooth
function under exact derivative linearization and a linearized coordinate
fourth-moment premise.

The conditional bootstrap variance consistency is supplied by the scalar
fourth-moment route for Hansen Theorem 10.10, and the finite-replication side
is Hansen Theorem 10.11's direct simulation-error transfer. -/
theorem
    chapter10_finiteReplicationVariance_tendsto_of_smooth_linearization_fourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
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
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_smooth_bootstrap_variance_consistency_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hB hFourthLinear hFourthLinearInt)

/-- Textbook-centered finite-replication variance version of
`chapter10_finiteReplicationVariance_tendsto_of_smooth_linearization_fourthMoment`. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_linearization_fourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
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
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_smooth_bootstrap_variance_consistency_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hB hFourthLinear hFourthLinearInt)

/-- `L²` simulation-error version of the smooth coordinate fourth-moment
finite-replication variance bridge. -/
theorem
    chapter10_finiteReplicationVariance_tendsto_of_smooth_fourthMoment_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B Cfinite : ℝ} (a : r)
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
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVariance_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
    hfiniteInt hfiniteBound
    (chapter10_smooth_bootstrap_variance_consistency_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hB hFourthLinear hFourthLinearInt)

/-- Textbook-centered `L²` simulation-error version of the smooth coordinate
fourth-moment finite-replication variance bridge. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_fourthMoment_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B Cfinite : ℝ} (a : r)
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
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
    hfiniteInt hfiniteBound
    (chapter10_smooth_bootstrap_variance_consistency_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hB hFourthLinear hFourthLinearInt)

/-- Indexed Hansen Theorem 10.10/10.11 finite-replication variance for a
smooth function under exact derivative linearization and an indexed linearized
coordinate fourth-moment premise. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_of_smooth_linearization_fourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
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
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hB hFourthLinear hFourthLinearInt)

/-- Textbook-centered indexed finite-replication variance version of the
indexed smooth linearized fourth-moment bridge. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_fourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
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
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hB hFourthLinear hFourthLinearInt)

/-- Indexed `L²` simulation-error version of the smooth coordinate
fourth-moment finite-replication variance bridge. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_of_smooth_fourthMoment_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B Cfinite : ℝ} (a : r)
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
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hB hFourthLinear hFourthLinearInt)

/-- Textbook-centered indexed `L²` simulation-error version of the smooth
coordinate fourth-moment finite-replication variance bridge. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_fourthMoment_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B Cfinite : ℝ} (a : r)
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
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hB hFourthLinear hFourthLinearInt)

/-- Smooth scalar finite-replication variance bridge with the automatic
Gaussian-limit coordinate `MemLp 2` premise discharged. -/
theorem
    chapter10_finiteReplicationVariance_smooth_normFourth_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_finiteReplicationVariance_tendsto_of_smooth_linearization_normFourthMoment
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G a hV
      hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt hfinite

/-- Textbook-centered smooth scalar finite-replication variance bridge with
the automatic Gaussian-limit coordinate `MemLp 2` premise discharged. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_smooth_normFourth_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_linearization_normFourthMoment
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G a hV
      hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt hfinite

/-- `L²` simulation-error version of the smooth scalar finite-replication
variance bridge with the Gaussian-limit coordinate `MemLp 2` premise
discharged. -/
theorem
    chapter10_finiteReplicationVariance_smooth_normFourth_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {B Cfinite : ℝ} (a : r)
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_finiteReplicationVariance_tendsto_of_smooth_normFourth_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G a hV
      hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt hfiniteInt hfiniteBound

/-- Textbook-centered `L²` simulation-error version of the smooth scalar
finite-replication variance bridge with the Gaussian-limit coordinate
`MemLp 2` premise discharged. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_smooth_normFourth_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {B Cfinite : ℝ} (a : r)
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_normFourth_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G a hV
      hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt hfiniteInt hfiniteBound

/-- Indexed smooth scalar finite-replication variance bridge with the
automatic Gaussian-limit coordinate `MemLp 2` premise discharged. -/
theorem
    chapter10_indexed_finiteReplicationVariance_smooth_normFourth_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_indexed_finiteReplicationVariance_tendsto_of_smooth_linearization_normFourthMoment
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G a hV
      hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt hfinite

/-- Textbook-centered indexed smooth scalar finite-replication variance bridge
with the automatic Gaussian-limit coordinate `MemLp 2` premise discharged. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_smooth_normFourth_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_normFourth
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G a hV
      hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt hfinite

/-- Indexed `L²` simulation-error version of the smooth scalar
finite-replication variance bridge with the Gaussian-limit coordinate
`MemLp 2` premise discharged. -/
theorem
    chapter10_indexed_finiteReplicationVariance_smooth_normFourth_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {B Cfinite : ℝ} (a : r)
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_indexed_finiteReplicationVariance_tendsto_of_smooth_normFourth_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G a hV
      hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt hfiniteInt hfiniteBound

/-- Textbook-centered indexed `L²` simulation-error version of the smooth
scalar finite-replication variance bridge with the Gaussian-limit coordinate
`MemLp 2` premise discharged. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_smooth_normFourth_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {B Cfinite : ℝ} (a : r)
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_normFourth_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G a hV
      hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt hfiniteInt hfiniteBound

/-- Smooth scalar finite-replication variance bridge from the linearized
coordinate fourth-moment route, with the automatic Gaussian-limit coordinate
`MemLp 2` premise discharged. -/
theorem
    chapter10_finiteReplicationVariance_smooth_fourthMoment_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_finiteReplicationVariance_tendsto_of_smooth_linearization_fourthMoment
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G a hV
      hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hFourthLinear hFourthLinearInt hfinite

/-- Textbook-centered smooth scalar finite-replication variance bridge from
the linearized coordinate fourth-moment route, with the automatic
Gaussian-limit coordinate `MemLp 2` premise discharged. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_smooth_fourthMoment_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_linearization_fourthMoment
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G a hV
      hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hFourthLinear hFourthLinearInt hfinite

/-- `L²` simulation-error version of the smooth scalar finite-replication
variance bridge from the linearized coordinate fourth-moment route, with the
Gaussian-limit coordinate `MemLp 2` premise discharged. -/
theorem
    chapter10_finiteReplicationVariance_smooth_fourthMoment_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {B Cfinite : ℝ} (a : r)
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_finiteReplicationVariance_tendsto_of_smooth_fourthMoment_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G a hV
      hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hFourthLinear hFourthLinearInt hfiniteInt hfiniteBound

/-- Textbook-centered `L²` simulation-error version of the smooth scalar
finite-replication variance bridge from the linearized coordinate
fourth-moment route, with the Gaussian-limit coordinate `MemLp 2` premise
discharged. -/
theorem
    chapter10_finiteReplicationVarianceCenteredReal_smooth_fourthMoment_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {B Cfinite : ℝ} (a : r)
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceReal Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_fourthMoment_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G a hV
      hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hFourthLinear hFourthLinearInt hfiniteInt hfiniteBound

/-- Indexed smooth scalar finite-replication variance bridge from the
linearized coordinate fourth-moment route, with the automatic Gaussian-limit
coordinate `MemLp 2` premise discharged. -/
theorem
    chapter10_indexed_finiteReplicationVariance_smooth_fourthMoment_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_indexed_finiteReplicationVariance_tendsto_of_smooth_linearization_fourthMoment
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G a hV
      hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hFourthLinear hFourthLinearInt hfinite

/-- Textbook-centered indexed smooth scalar finite-replication variance bridge
from the linearized coordinate fourth-moment route, with the automatic
Gaussian-limit coordinate `MemLp 2` premise discharged. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_smooth_fourthMoment_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_fourthMoment
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G a hV
      hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hFourthLinear hFourthLinearInt hfinite

/-- Indexed `L²` simulation-error version of the smooth scalar
finite-replication variance bridge from the linearized coordinate
fourth-moment route, with the Gaussian-limit coordinate `MemLp 2` premise
discharged. -/
theorem
    chapter10_indexed_finiteReplicationVariance_smooth_fourthMoment_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {B Cfinite : ℝ} (a : r)
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_indexed_finiteReplicationVariance_tendsto_of_smooth_fourthMoment_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G a hV
      hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hFourthLinear hFourthLinearInt hfiniteInt hfiniteBound

/-- Textbook-centered indexed `L²` simulation-error version of the smooth
scalar finite-replication variance bridge from the linearized coordinate
fourth-moment route, with the Gaussian-limit coordinate `MemLp 2` premise
discharged. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_smooth_fourthMoment_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    {B Cfinite : ℝ} (a : r)
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) := by
  classical
  exact
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_fourthMoment_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G a hV
      hPstar hT hcoordMem
      (memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hFourthLinear hFourthLinearInt hfiniteInt hfiniteBound

/-- Indexed Hansen Theorem 10.10/10.11 finite-replication variance for a
smooth function under exact derivative linearization and an eventual
deterministic coordinate bound. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_of_smooth_linearization_eventualBound_memLp
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {C : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hbound :
      ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ C)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_eventualBound_memLp
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hbound)

/-- Textbook-centered indexed finite-replication variance version of the
smooth bounded finite-replication bridge above. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_eventualBound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {C : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hbound :
      ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ C)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_bootstrap_variance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) hfinite
    (chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_eventualBound_memLp
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hbound)

/-- Indexed `L²` simulation-error version of the smooth bounded
finite-replication variance bridge. -/
theorem
    chapter10_indexed_finiteReplicationVariance_tendsto_of_smooth_eventualBound_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {C Cfinite : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hbound :
      ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ C)
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceMomentReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceMomentReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVariance_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_eventualBound_memLp
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hbound)

/-- Textbook-centered indexed `L²` simulation-error version of the smooth
bounded finite-replication variance bridge. -/
theorem
    chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_smooth_eventualBound_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {C Cfinite : ℝ} (a : r)
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar Tstar
        (multivariateGaussian (0 : EuclideanSpace ℝ d) V)
        (fun z : EuclideanSpace ℝ d => z))
    (hcoordMem :
      ∀ n ω,
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a) 2
          (Pstar n ω))
    (hlimMem :
      MemLp (fun z : EuclideanSpace ℝ r => (z : r → ℝ) a) 2
        (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)))
    (hlinearization :
      ∀ n ω ωs, thetaStar n ω ωs =
        matrixContinuousLinearMap G (Tstar n ω ωs))
    (hbound :
      ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ C)
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationVarianceCenteredReal Zsim n ω -
            bootstrapVarianceRealIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a) n ω‖ ^
              (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationVarianceCenteredReal Zsim) atTop
      (fun _ =>
        ∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a ^ 2
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ) -
        (∫ z, ((z : EuclideanSpace ℝ r) : r → ℝ) a
          ∂multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ)) ^ 2) :=
  chapter10_indexed_finiteReplicationVarianceCenteredReal_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ) a)
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_bootstrap_variance_consistency_of_linearization_eventualBound_memLp
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G a hV hPstar hT hcoordMem
      hlimMem hlinearization hbound)

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

/-- Hansen Theorem 10.9/10.11 finite-replication covariance matrix from
coordinatewise `L²` simulation-error bounds. -/
theorem chapter10_finiteReplicationCovarianceMat_tendsto_of_l2_simulation_error
    [IsFiniteMeasure μ] {k : Type*} [Fintype k]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {V : Matrix k k ℝ} {Cfinite : k → k → ℝ}
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMat Pstar Zstar n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMat Pstar Zstar n ω) a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ))
    (hboot :
      TendstoInMeasure μ (bootstrapCovarianceMat Pstar Zstar) atTop
        (fun _ => V)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => V) :=
  chapter10_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ)
    (tendstoInMeasure_matrix_zero_of_integral_sq_entry_error_le_inv
      (μ := μ)
      (E := fun n ω =>
        finiteReplicationCovarianceMomentMat Zsim n ω -
          bootstrapCovarianceMat Pstar Zstar n ω)
      (C := Cfinite) hfiniteInt hfiniteBound)
    hboot

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

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication covariance matrix from
coordinatewise `L²` simulation-error bounds. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_l2_simulation_error
    [IsFiniteMeasure μ] {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {V : Matrix k k ℝ} {Cfinite : k → k → ℝ}
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar Zstar n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar Zstar n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ))
    (hboot :
      TendstoInMeasure μ (bootstrapCovarianceMatIndexed Pstar Zstar) atTop
        (fun _ => V)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => V) :=
  chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ)
    (tendstoInMeasure_matrix_zero_of_integral_sq_entry_error_le_inv
      (μ := μ)
      (E := fun n ω =>
        finiteReplicationCovarianceMomentMat Zsim n ω -
          bootstrapCovarianceMatIndexed Pstar Zstar n ω)
      (C := Cfinite) hfiniteInt hfiniteBound)
    hboot

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

/-- Hansen Theorem 10.9/10.11 finite-replication covariance matrix from
bootstrap weak convergence and eventual deterministic coordinate and
coordinate-sum bounds. -/
theorem
    chapter10_finiteReplicationCovarianceMat_tendsto_of_eventualBound_memLp_limit
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
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
        |Zstar n ω ωs a + Zstar n ω ωs c| ≤ Csum a c)
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
    (chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
      hboundCoord hboundSum)

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication covariance matrix
from bootstrap weak convergence and eventual deterministic coordinate and
coordinate-sum bounds. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_eventualBound_memLp_limit
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
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
        |Zstar n ω ωs a + Zstar n ω ωs c| ≤ Csum a c)
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
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
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
          (C := Csum a c) ((hZlim a).add (hZlim c)) (hboundSum a c)))

/-- Hansen Theorem 10.9/10.11 finite-replication covariance matrix from
bootstrap weak convergence, uniform-square-tail controls, and coordinatewise
`L²` simulation-error bounds. -/
theorem
    chapter10_finiteReplicationCovarianceMat_tendsto_of_uniformSquareTail_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ} {Cfinite : k → k → ℝ}
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
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMat Pstar Zstar n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMat Pstar Zstar n ω) a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_finiteReplicationCovarianceMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
    hfiniteInt hfiniteBound
    (chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailCoord hTailSum)

/-- Hansen Theorem 10.9/10.11 finite-replication covariance matrix from
bootstrap weak convergence, eventual deterministic coordinate and
coordinate-sum bounds, and coordinatewise `L²` simulation-error bounds. -/
theorem
    chapter10_finiteReplicationCovarianceMat_tendsto_of_eventualBound_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ}
    {Ccoord : k → ℝ} {Csum : k → k → ℝ} {Cfinite : k → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs a| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |Zstar n ω ωs a + Zstar n ω ωs c| ≤ Csum a c)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMat Pstar Zstar n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMat Pstar Zstar n ω) a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_finiteReplicationCovarianceMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
    hfiniteInt hfiniteBound
    (chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
      hboundCoord hboundSum)

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication covariance matrix from
bootstrap weak convergence, indexed uniform-square-tail controls, and
coordinatewise `L²` simulation-error bounds. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_uniformSquareTail_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ} {Cfinite : k → k → ℝ}
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
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar Zstar n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar Zstar n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
    hfiniteInt hfiniteBound
    (chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailCoord hTailSum)

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication covariance matrix
from bootstrap weak convergence, eventual deterministic coordinate and
coordinate-sum bounds, and coordinatewise `L²` simulation-error bounds. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_eventualBound_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ}
    {Ccoord : k → ℝ} {Csum : k → k → ℝ} {Cfinite : k → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs a| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |Zstar n ω ωs a + Zstar n ω ωs c| ≤ Csum a c)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar Zstar n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar Zstar n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
    hfiniteInt hfiniteBound
    (chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
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
          (C := Csum a c) ((hZlim a).add (hZlim c)) (hboundSum a c)))

/-- Hansen Theorem 10.9/10.11 finite-replication covariance matrix from
bootstrap weak convergence and fourth-moment tail controls. -/
theorem chapter10_finiteReplicationCovarianceMat_tendsto_of_fourthMoment_tails
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
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
            (fun ωlim => (Z ωlim a + Z ωlim c) ^ 2) ωlim ∂ν) ≤ ε)
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
    (chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_fourthMoment_tails
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
      hBcoord hFourthCoord hFourthCoordInt hLimitTailCoord
      hBsum hFourthSum hFourthSumInt hLimitTailSum)

/-- Hansen Theorem 10.9/10.11 finite-replication covariance matrix from
bootstrap weak convergence and fourth-moment convergence, with weak-limit
coordinate and coordinate-sum tail premises discharged by `MemLp`. -/
theorem
    chapter10_finiteReplicationCovarianceMat_tendsto_of_fourthMoment_memLp_limit
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
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
          (Pstar n ω))
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
    (chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_fourthMoment_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
      hBcoord hFourthCoord hFourthCoordInt
      hBsum hFourthSum hFourthSumInt)

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication covariance matrix
from bootstrap weak convergence and fourth-moment tail controls. -/
theorem chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_fourthMoment_tails
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
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
            (fun ωlim => (Z ωlim a + Z ωlim c) ^ 2) ωlim ∂ν) ≤ ε)
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
    (chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_fourthMoment_tails
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
      hBcoord hFourthCoord hFourthCoordInt hLimitTailCoord
      hBsum hFourthSum hFourthSumInt hLimitTailSum)

/-- Indexed Hansen Theorem 10.9/10.11 finite-replication covariance matrix from
bootstrap weak convergence and fourth-moment convergence, with weak-limit
coordinate and coordinate-sum tail premises discharged by `MemLp`. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_fourthMoment_memLp_limit
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
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
          (Pstar n ω))
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
    (chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_fourthMoment_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
      hBcoord hFourthCoord hFourthCoordInt
      hBsum hFourthSum hFourthSumInt)

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

/-- Hansen Theorem 10.9/10.11 centered finite-replication covariance matrix
from coordinatewise `L²` simulation-error bounds. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
    [IsFiniteMeasure μ] {k : Type*} [Fintype k]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {V : Matrix k k ℝ} {Cfinite : k → k → ℝ}
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMat Pstar Zstar n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMat Pstar Zstar n ω) a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ))
    (hboot :
      TendstoInMeasure μ (bootstrapCovarianceMat Pstar Zstar) atTop
        (fun _ => V)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => V) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ)
    (tendstoInMeasure_matrix_zero_of_integral_sq_entry_error_le_inv
      (μ := μ)
      (E := fun n ω =>
        finiteReplicationCovarianceCenteredMat Zsim n ω -
          bootstrapCovarianceMat Pstar Zstar n ω)
      (C := Cfinite) hfiniteInt hfiniteBound)
    hboot

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

/-- Indexed Hansen Theorem 10.9/10.11 centered finite-replication covariance
matrix from coordinatewise `L²` simulation-error bounds. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
    [IsFiniteMeasure μ] {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {V : Matrix k k ℝ} {Cfinite : k → k → ℝ}
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar Zstar n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar Zstar n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ))
    (hboot :
      TendstoInMeasure μ (bootstrapCovarianceMatIndexed Pstar Zstar) atTop
        (fun _ => V)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => V) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ)
    (tendstoInMeasure_matrix_zero_of_integral_sq_entry_error_le_inv
      (μ := μ)
      (E := fun n ω =>
        finiteReplicationCovarianceCenteredMat Zsim n ω -
          bootstrapCovarianceMatIndexed Pstar Zstar n ω)
      (C := Cfinite) hfiniteInt hfiniteBound)
    hboot

/-- Theorem 10.11 ordinary nonparametric-bootstrap finite-replication
moment-form covariance route for iid finite-dimensional observations.

The conditional covariance target is the normalized `Fin (n+1)` ordinary
bootstrap covariance from Theorem 10.4; coordinatewise `O(n⁻¹)` mean-square
simulation error transfers the moment-form finite-replication covariance
estimator to the same population covariance target. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_finSucc_l2_iid
    [IsProbabilityMeasure μ] {k : Type*} [Fintype k]
    {Zsim : ℕ → ℕ → Ω → k → ℝ} {Cfinite : k → k → ℝ}
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
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
                n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
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
                  n ω) a c‖ ^ (2 : ℝ) ∂μ) ≤
              Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => covMat μ (Y 0)) :=
  chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim)
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
    (V := covMat μ (Y 0)) (Cfinite := Cfinite)
    hfiniteInt hfiniteBound
    (bootstrapCovarianceMatIndexed_normalized_finSucc_tendsto_of_iid
      (μ := μ) Y hYmem hindep hident)

/-- Theorem 10.11 ordinary nonparametric-bootstrap finite-replication
moment-form covariance route with the textbook `iIndepFun` premise. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_finSucc_l2_iIndep
    [IsProbabilityMeasure μ] {k : Type*} [Fintype k]
    {Zsim : ℕ → ℕ → Ω → k → ℝ} {Cfinite : k → k → ℝ}
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
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
                n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
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
                  n ω) a c‖ ^ (2 : ℝ) ∂μ) ≤
              Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => covMat μ (Y 0)) :=
  chapter10_indexed_finiteReplicationCovarianceMat_finSucc_l2_iid
    (μ := μ) (Zsim := Zsim) (Cfinite := Cfinite) Y hYmem
    (fun _ _ hij => hindep.indepFun hij) hident hfiniteInt hfiniteBound

/-- Theorem 10.11 ordinary nonparametric-bootstrap finite-replication
covariance route for iid finite-dimensional observations.

The conditional covariance target is the normalized `Fin (n+1)` ordinary
bootstrap covariance from Theorem 10.4; coordinatewise `O(n⁻¹)` mean-square
simulation error transfers Hansen's centered finite-replication covariance
estimator to the same population covariance target. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_finSucc_l2_iid
    [IsProbabilityMeasure μ] {k : Type*} [Fintype k]
    {Zsim : ℕ → ℕ → Ω → k → ℝ} {Cfinite : k → k → ℝ}
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
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
                n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
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
                  n ω) a c‖ ^ (2 : ℝ) ∂μ) ≤
              Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => covMat μ (Y 0)) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim)
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
    (V := covMat μ (Y 0)) (Cfinite := Cfinite)
    hfiniteInt hfiniteBound
    (bootstrapCovarianceMatIndexed_normalized_finSucc_tendsto_of_iid
      (μ := μ) Y hYmem hindep hident)

/-- Theorem 10.11 ordinary nonparametric-bootstrap finite-replication
covariance route with the textbook `iIndepFun` premise. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_finSucc_l2_iIndep
    [IsProbabilityMeasure μ] {k : Type*} [Fintype k]
    {Zsim : ℕ → ℕ → Ω → k → ℝ} {Cfinite : k → k → ℝ}
    (Y : ℕ → Ω → k → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
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
                n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
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
                  n ω) a c‖ ^ (2 : ℝ) ∂μ) ≤
              Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => covMat μ (Y 0)) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_finSucc_l2_iid
    (μ := μ) (Zsim := Zsim) (Cfinite := Cfinite) Y hYmem
    (fun _ _ hij => hindep.indepFun hij) hident hfiniteInt hfiniteBound

/-- Hansen Theorem 10.10/10.11 finite-replication covariance matrix for a
smooth function under exact derivative linearization and an underlying norm
fourth-moment premise. -/
theorem
    chapter10_finiteReplicationCovarianceMat_tendsto_of_smooth_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hB hNormFourth hNormFourthInt)

/-- Hansen Theorem 10.10/10.11 finite-replication covariance matrix for a
smooth function under exact derivative linearization and coordinate plus
coordinate-sum fourth-moment premises. -/
theorem
    chapter10_finiteReplicationCovarianceMat_tendsto_of_smooth_fourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hBcoord hFourthCoordLinear
      hFourthCoordLinearInt hBsum hFourthSumLinear hFourthSumLinearInt)

/-- Textbook-centered finite-replication covariance version of the smooth
norm-fourth finite-replication covariance bridge. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hB hNormFourth hNormFourthInt)

/-- Textbook-centered finite-replication covariance version of the smooth
coordinate-fourth-moment finite-replication covariance bridge. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_fourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hBcoord hFourthCoordLinear
      hFourthCoordLinearInt hBsum hFourthSumLinear hFourthSumLinearInt)

/-- Hansen Theorem 10.10/10.11 finite-replication covariance matrix from the
compact-tail remainder route and a norm fourth-moment premise on the nonlinear
smooth statistic. -/
theorem
    chapter10_finiteReplicationCovarianceMat_tendsto_smooth_compactTail_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_smooth_covarianceMat_tendsto_of_compact_tail_remainder_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (R := R) (V := V) G hV hPstar hT
      hTstar hthetaStar hcoordMem hlimMem hCompactTail hR_tail hR_bound
      hB hNormFourth hNormFourthInt)

/-- Textbook-centered finite-replication covariance version of
`chapter10_finiteReplicationCovarianceMat_tendsto_smooth_compactTail_normFourth`. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_smooth_compactTail_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_smooth_covarianceMat_tendsto_of_compact_tail_remainder_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (R := R) (V := V) G hV hPstar hT
      hTstar hthetaStar hcoordMem hlimMem hCompactTail hR_tail hR_bound
      hB hNormFourth hNormFourthInt)

/-- Hansen Theorem 10.10/10.11 finite-replication covariance matrix from the
compact-range quadratic Taylor-remainder route and norm fourth-moment
premises. -/
theorem
    chapter10_finiteReplicationCovarianceMat_tendsto_smooth_compactRange_quadratic
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_smooth_covarianceMat_tendsto_of_compact_range_quadratic_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound hBθ
      hThetaNormFourth hThetaNormFourthInt)

/-- Textbook-centered finite-replication covariance version of
`chapter10_finiteReplicationCovarianceMat_tendsto_smooth_compactRange_quadratic`. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_smooth_compactRange_quadratic
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_smooth_covarianceMat_tendsto_of_compact_range_quadratic_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound hBθ
      hThetaNormFourth hThetaNormFourthInt)

/-- Finite-replication covariance matrix from the compact-range quadratic
route with deterministic compact-membership coordinate and coordinate-sum
square-tail bounds. -/
theorem
    chapter10_finiteReplicationCovarianceMat_tendsto_smooth_compactRange_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_smooth_covarianceMat_tendsto_of_compact_range_quadratic_eventualBound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound)

/-- Textbook-centered finite-replication covariance version of
`chapter10_finiteReplicationCovarianceMat_tendsto_smooth_compactRange_bound`. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_smooth_compactRange_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_smooth_covarianceMat_tendsto_of_compact_range_quadratic_eventualBound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound)

/-- `L²` simulation-error version of
`chapter10_finiteReplicationCovarianceMat_tendsto_smooth_compactRange_quadratic`. -/
theorem
    chapter10_finiteReplicationCovarianceMat_tendsto_smooth_compactRangeQuad_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
    hfiniteInt hfiniteBound
    (chapter10_smooth_covarianceMat_tendsto_of_compact_range_quadratic_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound hBθ
      hThetaNormFourth hThetaNormFourthInt)

/-- Textbook-centered `L²` simulation-error version of the compact-range
quadratic finite-replication covariance matrix bridge. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_smooth_compactRangeQuad_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
    hfiniteInt hfiniteBound
    (chapter10_smooth_covarianceMat_tendsto_of_compact_range_quadratic_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound hBθ
      hThetaNormFourth hThetaNormFourthInt)

/-- `L²` simulation-error version of the smooth finite-replication covariance
matrix bridge. -/
theorem
    chapter10_finiteReplicationCovarianceMat_tendsto_of_smooth_normFourth_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
    hfiniteInt hfiniteBound
    (chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hB hNormFourth hNormFourthInt)

/-- `L²` simulation-error version of the smooth coordinate-fourth-moment
finite-replication covariance matrix bridge. -/
theorem
    chapter10_finiteReplicationCovarianceMat_tendsto_of_smooth_fourthMoment_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Bcoord : r → ℝ} {Bsum : r → r → ℝ} {Cfinite : r → r → ℝ}
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
    hfiniteInt hfiniteBound
    (chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hBcoord hFourthCoordLinear
      hFourthCoordLinearInt hBsum hFourthSumLinear hFourthSumLinearInt)

/-- Textbook-centered `L²` simulation-error version of the smooth
finite-replication covariance bridge. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_normFourth_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
    hfiniteInt hfiniteBound
    (chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hB hNormFourth hNormFourthInt)

/-- Textbook-centered `L²` simulation-error version of the smooth
coordinate-fourth-moment finite-replication covariance bridge. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_fourthMoment_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Bcoord : r → ℝ} {Bsum : r → r → ℝ} {Cfinite : r → r → ℝ}
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
    hfiniteInt hfiniteBound
    (chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hBcoord hFourthCoordLinear
      hFourthCoordLinearInt hBsum hFourthSumLinear hFourthSumLinearInt)

/-- Hansen Theorem 10.10/10.11 finite-replication covariance matrix for a
smooth function under exact derivative linearization and eventual
deterministic coordinate and coordinate-sum bounds. -/
theorem
    chapter10_finiteReplicationCovarianceMat_tendsto_of_smooth_eventualBound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
          (thetaStar n ω ωs : r → ℝ) c)| ≤ Csum a c)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_eventualBound_memLp
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hboundCoord hboundSum)

/-- Textbook-centered finite-replication covariance version of the smooth
bounded finite-replication covariance bridge. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_eventualBound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
          (thetaStar n ω ωs : r → ℝ) c)| ≤ Csum a c)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_eventualBound_memLp
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hboundCoord hboundSum)

/-- `L²` simulation-error version of the smooth bounded finite-replication
covariance matrix bridge. -/
theorem
    chapter10_finiteReplicationCovarianceMat_tendsto_of_smooth_eventualBound_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Ccoord : r → ℝ} {Csum : r → r → ℝ} {Cfinite : r → r → ℝ}
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
          (thetaStar n ω ωs : r → ℝ) c)| ≤ Csum a c)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
    hfiniteInt hfiniteBound
    (chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_eventualBound_memLp
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hboundCoord hboundSum)

/-- Textbook-centered `L²` simulation-error version of the smooth bounded
finite-replication covariance bridge. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_eventualBound_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Ccoord : r → ℝ} {Csum : r → r → ℝ} {Cfinite : r → r → ℝ}
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
          (thetaStar n ω ωs : r → ℝ) c)| ≤ Csum a c)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
    hfiniteInt hfiniteBound
    (chapter10_smooth_bootstrap_covarianceMat_tendsto_of_linearization_eventualBound_memLp
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hboundCoord hboundSum)

/-- Indexed smooth finite-replication covariance matrix bridge under exact
derivative linearization and an underlying norm fourth-moment premise. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_smooth_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hB hNormFourth hNormFourthInt)

/-- Indexed finite-replication covariance matrix for a smooth function under
exact derivative linearization and coordinate plus coordinate-sum fourth-moment
premises. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_smooth_fourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hBcoord hFourthCoordLinear
      hFourthCoordLinearInt hBsum hFourthSumLinear hFourthSumLinearInt)

/-- Indexed textbook-centered smooth finite-replication covariance bridge. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hB hNormFourth hNormFourthInt)

/-- Indexed textbook-centered finite-replication covariance version of the
smooth coordinate-fourth-moment finite-replication covariance bridge. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_fourthMoment
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hBcoord hFourthCoordLinear
      hFourthCoordLinearInt hBsum hFourthSumLinear hFourthSumLinearInt)

/-- Indexed finite-replication covariance matrix from the compact-tail
remainder route and an indexed norm fourth-moment premise on the nonlinear
smooth statistic. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_smooth_compactTail_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_indexed_smooth_covarianceMat_tendsto_of_tail_remainder_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (R := R) (V := V) G hV hPstar hT
      hTstar hthetaStar hcoordMem hlimMem hCompactTail hR_tail hR_bound
      hB hNormFourth hNormFourthInt)

/-- Textbook-centered indexed finite-replication covariance version of
`chapter10_indexed_finiteReplicationCovarianceMat_tendsto_smooth_compactTail_normFourth`. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_smooth_compactTail_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_indexed_smooth_covarianceMat_tendsto_of_tail_remainder_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (R := R) (V := V) G hV hPstar hT
      hTstar hthetaStar hcoordMem hlimMem hCompactTail hR_tail hR_bound
      hB hNormFourth hNormFourthInt)

/-- Indexed finite-replication covariance matrix from the compact-range
quadratic Taylor-remainder route and indexed norm fourth-moment premises. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_smooth_compactRange_quadratic
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_indexed_smooth_covarianceMat_tendsto_of_compact_range_quadratic_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound hBθ
      hThetaNormFourth hThetaNormFourthInt)

/-- Textbook-centered indexed finite-replication covariance version of
`chapter10_indexed_finiteReplicationCovarianceMat_tendsto_smooth_compactRange_quadratic`. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_smooth_compactRange_quadratic
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_indexed_smooth_covarianceMat_tendsto_of_compact_range_quadratic_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound hBθ
      hThetaNormFourth hThetaNormFourthInt)

/-- Indexed finite-replication covariance matrix from the compact-range
quadratic route with deterministic compact-membership coordinate and
coordinate-sum square-tail bounds. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_smooth_compactRange_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_indexed_smooth_covarianceMat_tendsto_of_compact_range_quadratic_eventualBound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound)

/-- Textbook-centered indexed finite-replication covariance version of
`chapter10_indexed_finiteReplicationCovarianceMat_tendsto_smooth_compactRange_bound`. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_compactRange_bound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        ρ n * ‖Tstar n ω ωs‖ ^ 2)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_indexed_smooth_covarianceMat_tendsto_of_compact_range_quadratic_eventualBound
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound)

/-- Indexed `L²` simulation-error version of the compact-range quadratic
finite-replication covariance matrix bridge. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_smooth_compactRangeQuad_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_covarianceMat_tendsto_of_compact_range_quadratic_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound hBθ
      hThetaNormFourth hThetaNormFourthInt)

/-- Textbook-centered indexed `L²` simulation-error version of the
compact-range quadratic finite-replication covariance matrix bridge. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_smooth_compactRangeQuad_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_covarianceMat_tendsto_of_compact_range_quadratic_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (ρ := ρ) (V := V) G hV hPstar hT
      hK hTstar hthetaStar hcoordMem hlimMem hlinearized_mem
      hthetaStar_mem hρsq hTNormFourth hTNormFourthInt hR_bound hBθ
      hThetaNormFourth hThetaNormFourthInt)

/-- Indexed `L²` simulation-error version of the smooth finite-replication
covariance matrix bridge. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_smooth_normFourth_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hB hNormFourth hNormFourthInt)

/-- Indexed `L²` simulation-error version of the smooth
coordinate-fourth-moment finite-replication covariance matrix bridge. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_smooth_fourthMoment_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Bcoord : r → ℝ} {Bsum : r → r → ℝ} {Cfinite : r → r → ℝ}
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hBcoord hFourthCoordLinear
      hFourthCoordLinearInt hBsum hFourthSumLinear hFourthSumLinearInt)

/-- Indexed textbook-centered `L²` simulation-error version of the smooth
finite-replication covariance bridge. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_normFourth_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_normFourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hB hNormFourth hNormFourthInt)

/-- Indexed textbook-centered `L²` simulation-error version of the smooth
coordinate-fourth-moment finite-replication covariance bridge. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_fourthMoment_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Bcoord : r → ℝ} {Bsum : r → r → ℝ} {Cfinite : r → r → ℝ}
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_fourthMoment
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hBcoord hFourthCoordLinear
      hFourthCoordLinearInt hBsum hFourthSumLinear hFourthSumLinearInt)

/-- Indexed smooth finite-replication covariance matrix bridge under exact
derivative linearization and eventual deterministic coordinate and
coordinate-sum bounds. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_smooth_eventualBound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
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
          (thetaStar n ω ωs : r → ℝ) c)| ≤ Csum a c)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_eventualBound_memLp
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hboundCoord hboundSum)

/-- Indexed textbook-centered smooth finite-replication covariance bridge
from eventual deterministic coordinate and coordinate-sum bounds. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_eventualBound
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        MemLp (fun ωs => (thetaStar n ω ωs : r → ℝ) a)
          2 (Pstar n ω))
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
          (thetaStar n ω ωs : r → ℝ) c)| ≤ Csum a c)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_bootstrap_covariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) hfinite
    (chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_eventualBound_memLp
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hboundCoord hboundSum)

/-- Indexed `L²` simulation-error version of the smooth bounded
finite-replication covariance bridge. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_smooth_eventualBound_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Ccoord : r → ℝ} {Csum : r → r → ℝ} {Cfinite : r → r → ℝ}
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
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a +
          (thetaStar n ω ωs : r → ℝ) c)| ≤ Csum a c)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_eventualBound_memLp
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hboundCoord hboundSum)

/-- Indexed textbook-centered `L²` simulation-error version of the smooth
bounded finite-replication covariance bridge. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_eventualBound_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Ccoord : r → ℝ} {Csum : r → r → ℝ} {Cfinite : r → r → ℝ}
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
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a +
          (thetaStar n ω ωs : r → ℝ) c)| ≤ Csum a c)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ))
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_bootstrap_covarianceMat_tendsto_of_linearization_eventualBound_memLp
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hT hcoordMem
      hlimMem hlinearization hboundCoord hboundSum)

/-- Smooth finite-replication covariance matrix bridge with Gaussian-limit
coordinate `MemLp 2` premises discharged automatically. -/
theorem
    chapter10_finiteReplicationCovarianceMat_smooth_normFourth_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_finiteReplicationCovarianceMat_tendsto_of_smooth_normFourth
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt hfinite

/-- Textbook-centered smooth finite-replication covariance bridge with
Gaussian-limit coordinate `MemLp 2` premises discharged automatically. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_smooth_normFourth_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_normFourth
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt hfinite

/-- `L²` simulation-error smooth finite-replication covariance bridge with
Gaussian-limit coordinate `MemLp 2` premises discharged automatically. -/
theorem
    chapter10_finiteReplicationCovarianceMat_smooth_normFourth_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_finiteReplicationCovarianceMat_tendsto_of_smooth_normFourth_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt hfiniteInt hfiniteBound

/-- Textbook-centered `L²` simulation-error smooth finite-replication
covariance bridge with Gaussian-limit coordinate `MemLp 2` premises
discharged automatically. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_smooth_normFourth_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_normFourth_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt hfiniteInt hfiniteBound

/-- Indexed smooth finite-replication covariance matrix bridge with
Gaussian-limit coordinate `MemLp 2` premises discharged automatically. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_smooth_normFourth_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_smooth_normFourth
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt hfinite

/-- Indexed textbook-centered smooth finite-replication covariance bridge with
Gaussian-limit coordinate `MemLp 2` premises discharged automatically. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_smooth_normFourth_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_normFourth
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt hfinite

/-- Indexed `L²` simulation-error smooth finite-replication covariance bridge
with Gaussian-limit coordinate `MemLp 2` premises discharged automatically. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_smooth_normFourth_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_smooth_normFourth_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt hfiniteInt hfiniteBound

/-- Indexed textbook-centered `L²` simulation-error smooth finite-replication
covariance bridge with Gaussian-limit coordinate `MemLp 2` premises
discharged automatically. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_smooth_normFourth_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {B : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_normFourth_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hB hNormFourth hNormFourthInt hfiniteInt hfiniteBound

/-- Smooth coordinate-fourth-moment finite-replication covariance bridge with
Gaussian-limit coordinate `MemLp 2` premises discharged automatically. -/
theorem
    chapter10_finiteReplicationCovarianceMat_smooth_fourthMoment_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_finiteReplicationCovarianceMat_tendsto_of_smooth_fourthMoment
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hBcoord hFourthCoordLinear hFourthCoordLinearInt
      hBsum hFourthSumLinear hFourthSumLinearInt hfinite

/-- Textbook-centered smooth coordinate-fourth-moment finite-replication
covariance bridge with Gaussian-limit coordinate `MemLp 2` premises discharged
automatically. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_smooth_fourthMoment_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_fourthMoment
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hBcoord hFourthCoordLinear hFourthCoordLinearInt
      hBsum hFourthSumLinear hFourthSumLinearInt hfinite

/-- `L²` simulation-error smooth coordinate-fourth-moment finite-replication
covariance bridge with Gaussian-limit coordinate `MemLp 2` premises discharged
automatically. -/
theorem
    chapter10_finiteReplicationCovarianceMat_smooth_fourthMoment_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Bcoord : r → ℝ} {Bsum : r → r → ℝ} {Cfinite : r → r → ℝ}
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_finiteReplicationCovarianceMat_tendsto_of_smooth_fourthMoment_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hBcoord hFourthCoordLinear hFourthCoordLinearInt
      hBsum hFourthSumLinear hFourthSumLinearInt hfiniteInt hfiniteBound

/-- Textbook-centered `L²` simulation-error smooth coordinate-fourth-moment
finite-replication covariance bridge with Gaussian-limit coordinate `MemLp 2`
premises discharged automatically. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_smooth_fourthMoment_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Bcoord : r → ℝ} {Bsum : r → r → ℝ} {Cfinite : r → r → ℝ}
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_fourthMoment_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hBcoord hFourthCoordLinear hFourthCoordLinearInt
      hBsum hFourthSumLinear hFourthSumLinearInt hfiniteInt hfiniteBound

/-- Indexed smooth coordinate-fourth-moment finite-replication covariance
bridge with Gaussian-limit coordinate `MemLp 2` premises discharged
automatically. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_smooth_fourthMoment_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceMomentMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_smooth_fourthMoment
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hBcoord hFourthCoordLinear hFourthCoordLinearInt
      hBsum hFourthSumLinear hFourthSumLinearInt hfinite

/-- Indexed textbook-centered smooth coordinate-fourth-moment finite-replication
covariance bridge with Gaussian-limit coordinate `MemLp 2` premises discharged
automatically. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_smooth_fourthMoment_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_fourthMoment
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hBcoord hFourthCoordLinear hFourthCoordLinearInt
      hBsum hFourthSumLinear hFourthSumLinearInt hfinite

/-- Indexed `L²` simulation-error smooth coordinate-fourth-moment
finite-replication covariance bridge with Gaussian-limit coordinate `MemLp 2`
premises discharged automatically. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceMat_smooth_fourthMoment_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Bcoord : r → ℝ} {Bsum : r → r → ℝ} {Cfinite : r → r → ℝ}
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceMomentMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_indexed_finiteReplicationCovarianceMat_tendsto_of_smooth_fourthMoment_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hBcoord hFourthCoordLinear hFourthCoordLinearInt
      hBsum hFourthSumLinear hFourthSumLinearInt hfiniteInt hfiniteBound

/-- Indexed textbook-centered `L²` simulation-error smooth
coordinate-fourth-moment finite-replication covariance bridge with
Gaussian-limit coordinate `MemLp 2` premises discharged automatically. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_smooth_fourthMoment_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {Bcoord : r → ℝ} {Bsum : r → r → ℝ} {Cfinite : r → r → ℝ}
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_fourthMoment_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hT hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hBcoord hFourthCoordLinear hFourthCoordLinearInt
      hBsum hFourthSumLinear hFourthSumLinearInt hfiniteInt hfiniteBound

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

/-- Hansen Theorem 10.9/10.11 centered finite-replication covariance from
bootstrap weak convergence and eventual deterministic coordinate and
coordinate-sum bounds. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_eventualBound_memLp_limit
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
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
        |Zstar n ω ωs a + Zstar n ω ωs c| ≤ Csum a c)
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
    (chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
      hboundCoord hboundSum)

/-- Indexed Hansen Theorem 10.9/10.11 centered finite-replication covariance
from bootstrap weak convergence and eventual deterministic coordinate and
coordinate-sum bounds. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_eventualBound_memLp_limit
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
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
        |Zstar n ω ωs a + Zstar n ω ωs c| ≤ Csum a c)
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
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
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
          (C := Csum a c) ((hZlim a).add (hZlim c)) (hboundSum a c)))

/-- Hansen Theorem 10.9/10.11 centered finite-replication covariance matrix
from bootstrap weak convergence, uniform-square-tail controls, and
coordinatewise `L²` simulation-error bounds. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_uniformSquareTail_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ} {Cfinite : k → k → ℝ}
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
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMat Pstar Zstar n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMat Pstar Zstar n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
    hfiniteInt hfiniteBound
    (chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailCoord hTailSum)

/-- Hansen Theorem 10.9/10.11 centered finite-replication covariance matrix
from bootstrap weak convergence, eventual deterministic coordinate and
coordinate-sum bounds, and coordinatewise `L²` simulation-error bounds. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_eventualBound_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ}
    {Ccoord : k → ℝ} {Csum : k → k → ℝ} {Cfinite : k → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs a| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |Zstar n ω ωs a + Zstar n ω ωs c| ≤ Csum a c)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMat Pstar Zstar n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMat Pstar Zstar n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
    hfiniteInt hfiniteBound
    (chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_eventualBound_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
      hboundCoord hboundSum)

/-- Indexed Hansen Theorem 10.9/10.11 centered finite-replication covariance
matrix from bootstrap weak convergence, indexed uniform-square-tail controls,
and coordinatewise `L²` simulation-error bounds. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_uniformSquareTail_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ} {Cfinite : k → k → ℝ}
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
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar Zstar n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar Zstar n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
    hfiniteInt hfiniteBound
    (chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak hTailCoord hTailSum)

/-- Indexed Hansen Theorem 10.9/10.11 centered finite-replication covariance
matrix from bootstrap weak convergence, eventual deterministic coordinate and
coordinate-sum bounds, and coordinatewise `L²` simulation-error bounds. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_eventualBound_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ}
    {Ccoord : k → ℝ} {Csum : k → k → ℝ} {Cfinite : k → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hZmem : ∀ n ω a, MemLp (fun ωs => Zstar n ω ωs a) 2 (Pstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs, |Zstar n ω ωs a| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |Zstar n ω ωs a + Zstar n ω ωs c| ≤ Csum a c)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar Zstar n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar Zstar n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
    hfiniteInt hfiniteBound
    (chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
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
          (C := Csum a c) ((hZlim a).add (hZlim c)) (hboundSum a c)))

/-- Hansen Theorem 10.9/10.11 centered finite-replication covariance from
bootstrap weak convergence and fourth-moment tail controls. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_fourthMoment_tails
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
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
            (fun ωlim => (Z ωlim a + Z ωlim c) ^ 2) ωlim ∂ν) ≤ ε)
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
    (chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_fourthMoment_tails
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
      hBcoord hFourthCoord hFourthCoordInt hLimitTailCoord
      hBsum hFourthSum hFourthSumInt hLimitTailSum)

/-- Hansen Theorem 10.9/10.11 centered finite-replication covariance from
bootstrap weak convergence and fourth-moment convergence, with weak-limit
coordinate and coordinate-sum tail premises discharged by `MemLp`. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_fourthMoment_memLp_limit
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
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
          (Pstar n ω))
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
    (chapter10_bootstrap_covarianceMat_tendsto_of_weak_distribution_fourthMoment_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
      hBcoord hFourthCoord hFourthCoordInt
      hBsum hFourthSum hFourthSumInt)

/-- Indexed Hansen Theorem 10.9/10.11 centered finite-replication covariance
from bootstrap weak convergence and fourth-moment tail controls. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_fourthMoment_tails
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
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
            (fun ωlim => (Z ωlim a + Z ωlim c) ^ 2) ωlim ∂ν) ≤ ε)
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
    (chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_fourthMoment_tails
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
      hBcoord hFourthCoord hFourthCoordInt hLimitTailCoord
      hBsum hFourthSum hFourthSumInt hLimitTailSum)

/-- Indexed Hansen Theorem 10.9/10.11 centered finite-replication covariance
from bootstrap weak convergence and fourth-moment convergence, with weak-limit
coordinate and coordinate-sum tail premises discharged by `MemLp`. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_fourthMoment_memLp_limit
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
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
          (Pstar n ω))
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
    (chapter10_indexed_bootstrap_covarianceMat_tendsto_of_weak_distribution_fourthMoment_memLp_limit
      (μ := μ) (ν := ν) hPstar hZmem hZlim hweak
      hBcoord hFourthCoord hFourthCoordInt
      hBsum hFourthSum hFourthSumInt)

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
from an `L²` simulation-error bound.

This discharges the direct `oₚ(1)` simulation-error premise of
`chapter10_finiteReplicationCovarianceCenteredReal_tendsto_of_bootstrap_covariance`
from an `O(n⁻¹)` mean-square bound. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredReal_tendsto_of_l2_simulation_error
    [IsFiniteMeasure μ]
    {Xsim Ysim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Xstar Ystar : ℕ → Ω → Ωs → ℝ}
    {v Cfinite : ℝ}
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationCovarianceCenteredReal Xsim Ysim n ω -
            bootstrapCovarianceReal Pstar Xstar Ystar n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationCovarianceCenteredReal Xsim Ysim n ω -
            bootstrapCovarianceReal Pstar Xstar Ystar n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ))
    (hboot :
      TendstoInMeasure μ (bootstrapCovarianceReal Pstar Xstar Ystar) atTop
        (fun _ => v)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredReal Xsim Ysim)
      atTop (fun _ => v) := by
  have hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredReal Xsim Ysim n ω -
            bootstrapCovarianceReal Pstar Xstar Ystar n ω)
        atTop (fun _ => 0) :=
    tendstoInMeasure_zero_of_integral_sq_error_le_inv
      (μ := μ)
      (E := fun n ω =>
        finiteReplicationCovarianceCenteredReal Xsim Ysim n ω -
          bootstrapCovarianceReal Pstar Xstar Ystar n ω)
      (C := Cfinite) hfiniteInt hfiniteBound
  exact
    chapter10_finiteReplicationCovarianceCenteredReal_tendsto_of_bootstrap_covariance
      (μ := μ)
      (by simpa [bootstrapCovarianceReal] using hfinite)
      (by simpa [bootstrapCovarianceReal] using hboot)

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

/-- Indexed Hansen Theorem 10.9/10.11 scalar centered finite-replication
covariance from conditional bootstrap covariance consistency.

This is the sample-size-dependent bootstrap-space counterpart of
`chapter10_finiteReplicationCovarianceCenteredReal_tendsto_of_bootstrap_covariance`. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredReal_tendsto_of_bootstrap_covariance
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Xsim Ysim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ}
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

/-- Indexed Hansen Theorem 10.9/10.11 scalar centered finite-replication
covariance from an `L²` simulation-error bound. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredReal_tendsto_of_l2_simulation_error
    [IsFiniteMeasure μ]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Xsim Ysim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ}
    {v Cfinite : ℝ}
    (hfiniteInt :
      ∀ n, Integrable
        (fun ω =>
          ‖finiteReplicationCovarianceCenteredReal Xsim Ysim n ω -
            bootstrapCovarianceRealIndexed Pstar Xstar Ystar n ω‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ᶠ n in atTop,
        (∫ ω,
          ‖finiteReplicationCovarianceCenteredReal Xsim Ysim n ω -
            bootstrapCovarianceRealIndexed Pstar Xstar Ystar n ω‖ ^ (2 : ℝ) ∂μ) ≤
          Cfinite / (n : ℝ))
    (hboot :
      TendstoInMeasure μ
        (bootstrapCovarianceRealIndexed Pstar Xstar Ystar) atTop
        (fun _ => v)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredReal Xsim Ysim)
      atTop (fun _ => v) := by
  have hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredReal Xsim Ysim n ω -
            bootstrapCovarianceRealIndexed Pstar Xstar Ystar n ω)
        atTop (fun _ => 0) :=
    tendstoInMeasure_zero_of_integral_sq_error_le_inv
      (μ := μ)
      (E := fun n ω =>
        finiteReplicationCovarianceCenteredReal Xsim Ysim n ω -
          bootstrapCovarianceRealIndexed Pstar Xstar Ystar n ω)
      (C := Cfinite) hfiniteInt hfiniteBound
  exact
    chapter10_indexed_finiteReplicationCovarianceCenteredReal_tendsto_of_bootstrap_covariance
      (μ := μ)
      (by simpa [bootstrapCovarianceRealIndexed] using hfinite)
      (by simpa [bootstrapCovarianceRealIndexed] using hboot)

/-- Indexed Hansen Theorem 10.9/10.11 scalar centered finite-replication
covariance from conditional bootstrap moment convergence. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredReal_tendsto_of_bootstrap_moments
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Xsim Ysim : ℕ → ℕ → Ω → ℝ}
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
  chapter10_indexed_finiteReplicationCovarianceCenteredReal_tendsto_of_bootstrap_covariance
    (μ := μ) hfinite
    (chapter10_indexed_bootstrap_covarianceReal_tendsto_of_moments
      (μ := μ) hmeanX hmeanY hcross)

/-- Indexed zero-mean scalar finite-replication covariance wrapper for Hansen
Theorem 10.11. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredReal_tendsto_of_bootstrap_zero_mean_moments
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Xsim Ysim : ℕ → ℕ → Ω → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Xstar Ystar : ∀ n, Ω → Ωboot n → ℝ}
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
    (chapter10_indexed_finiteReplicationCovarianceCenteredReal_tendsto_of_bootstrap_moments
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

/-- Hansen Theorem 10.11/10.12 finite-replication trimmed covariance from
coordinatewise `L²` simulation-error bounds. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    [IsFiniteMeasure μ] {k : Type*} [Fintype k]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs} {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {τ : ℕ → ℝ} {V : Matrix k k ℝ} {Cfinite : k → k → ℝ}
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar Zstar τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar Zstar τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ))
    (htrim :
      TendstoInMeasure μ (trimmedBootstrapCovarianceMat Pstar Zstar τ)
        atTop (fun _ => V)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => V) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmedBootstrapVariance
    (μ := μ)
    (tendstoInMeasure_matrix_zero_of_integral_sq_entry_error_le_inv
      (μ := μ)
      (E := fun n ω =>
        finiteReplicationCovarianceCenteredMat Zsim n ω -
          trimmedBootstrapCovarianceMat Pstar Zstar τ n ω)
      (C := Cfinite) hfiniteInt hfiniteBound)
    htrim

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

/-- Indexed Hansen Theorem 10.11/10.12 finite-replication trimmed covariance
from coordinatewise `L²` simulation-error bounds. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    [IsFiniteMeasure μ] {k : Type*} [Fintype k]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {τ : ℕ → ℝ} {V : Matrix k k ℝ} {Cfinite : k → k → ℝ}
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ))
    (htrim :
      TendstoInMeasure μ (trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ)
        atTop (fun _ => V)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => V) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmedBootstrapVariance
    (μ := μ)
    (tendstoInMeasure_matrix_zero_of_integral_sq_entry_error_le_inv
      (μ := μ)
      (E := fun n ω =>
        finiteReplicationCovarianceCenteredMat Zsim n ω -
          trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω)
      (C := Cfinite) hfiniteInt hfiniteBound)
    htrim

/-- Hansen Theorems 10.11 and 10.19 for finite-replication regression
trimmed variance.

For a transformed regression statistic, trimmed conditional moment convergence
to `R' Vβ R` plus coordinatewise `L²` simulation-error bounds for Hansen's
centered finite-replication covariance estimator imply finite-replication
covariance consistency for `R' Vβ R`. -/
theorem chapter10_regression_finiteReplicationTrimmedVariance_l2
    [IsFiniteMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q]
    {Zsim : ℕ → ℕ → Ω → q → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {ZthetaStar : ℕ → Ω → Ωs → q → ℝ}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    {Cfinite : q → q → ℝ}
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
        (bootstrapCrossMomentMat Pstar
          (trimmedBootstrapStatistic ZthetaStar τ))
        atTop (fun _ => smoothFunctionVarianceFunctional R Vβ))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar ZthetaStar τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar ZthetaStar τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => smoothFunctionVarianceFunctional R Vβ) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := ZthetaStar) (τ := τ) hfiniteInt hfiniteBound
    (chapter10_bootstrap_regression_trimmedVariance_tendsto
      (μ := μ) (Pstar := Pstar) (ZthetaStar := ZthetaStar)
      (τ := τ) (Vβ := Vβ) R hPstar hZ hmean hcross)

/-- Indexed finite-replication version of Hansen Theorem 10.19 for
sample-size-dependent bootstrap spaces. -/
theorem chapter10_indexed_regression_finiteReplicationTrimmedVariance_l2
    [IsFiniteMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → q → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {ZthetaStar : ∀ n, Ω → Ωboot n → q → ℝ}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    {Cfinite : q → q → ℝ}
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
        atTop (fun _ => smoothFunctionVarianceFunctional R Vβ))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar ZthetaStar τ n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar ZthetaStar τ n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => smoothFunctionVarianceFunctional R Vβ) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := ZthetaStar) (τ := τ) hfiniteInt hfiniteBound
    (chapter10_indexed_bootstrap_regression_trimmedVariance_tendsto
      (μ := μ) (Pstar := Pstar) (ZthetaStar := ZthetaStar)
      (τ := τ) (Vβ := Vβ) R hPstar hZ hmean hcross)

/-- Hansen Theorem 10.19 finite-replication regression trimmed covariance
route from coefficient-level Gaussian bootstrap convergence, norm-fourth
control, and coordinatewise `L²` simulation-error bounds. -/
theorem
    chapter10_regression_finiteReplicationTrimmedVariance_l2_of_linearization_normFourth
    [IsFiniteMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Zsim : ℕ → ℕ → Ω → q → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * Vβ * (Rᵀ)ᵀ))]
    {B : ℝ} {Cfinite : q → q → ℝ}
    (hVβ : Vβ.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ q => (z : q → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * Vβ * (Rᵀ)ᵀ)))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)
            {ωs |
              τ n <
                ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)‖}).toReal)
        atTop (fun _ => 0))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar
                (fun n ω ωs =>
                  ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar
                  (fun n ω ωs =>
                    ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                      EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => smoothFunctionVarianceFunctional R Vβ) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs =>
      ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
        EuclideanSpace ℝ q) : q → ℝ))
    (τ := τ) hfiniteInt hfiniteBound
    (chapter10_bootstrap_regression_trimmedVariance_tendsto_of_linearization_normFourth
      (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
      (τ := τ) (Vβ := Vβ) R hVβ hPstar hτ hT hTbetaMeas
      hcoordMem hlimMem hTailProb hB hNormFourth hNormFourthInt)

/-- Indexed finite-replication version of
`chapter10_regression_finiteReplicationTrimmedVariance_l2_of_linearization_normFourth`. -/
theorem
    chapter10_indexed_regression_finiteReplicationTrimmedVariance_l2_of_linearization_normFourth
    [IsFiniteMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → q → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * Vβ * (Rᵀ)ᵀ))]
    {B : ℝ} {Cfinite : q → q → ℝ}
    (hVβ : Vβ.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ q => (z : q → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * Vβ * (Rᵀ)ᵀ)))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)
            {ωs |
              τ n <
                ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)‖}).toReal)
        atTop (fun _ => 0))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs =>
                  ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs =>
                    ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                      EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => smoothFunctionVarianceFunctional R Vβ) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs =>
      ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
        EuclideanSpace ℝ q) : q → ℝ))
    (τ := τ) hfiniteInt hfiniteBound
    (chapter10_indexed_bootstrap_regression_trimmedVariance_tendsto_of_linearization_normFourth
      (μ := μ) (Pstar := Pstar) (TbetaStar := TbetaStar)
      (τ := τ) (Vβ := Vβ) R hVβ hPstar hτ hT hTbetaMeas
      hcoordMem hlimMem hTailProb hB hNormFourth hNormFourthInt)

/-- Hansen Theorem 10.19 finite-replication regression trimmed covariance
route with trimming-tail negligibility discharged by conditional second
moments and a diverging threshold. -/
theorem
    chapter10_regression_finiteReplicationTrimmedVariance_l2_of_linearization_secondMoment
    [IsFiniteMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Zsim : ℕ → ℕ → Ω → q → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * Vβ * (Rᵀ)ᵀ))]
    {Bsecond Bfourth : ℝ} {Cfinite : q → q → ℝ}
    (hVβ : Vβ.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hThetaMem :
      ∀ n ω,
        MemLp
          (fun ωs =>
            ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ))
          2 (Pstar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ q => (z : q → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * Vβ * (Rᵀ)ᵀ)))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ)‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => Bsecond))
    (hBfourth : 0 ≤ Bfourth)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bfourth))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar
                (fun n ω ωs =>
                  ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar
                  (fun n ω ωs =>
                    ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                      EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => smoothFunctionVarianceFunctional R Vβ) :=
  chapter10_regression_finiteReplicationTrimmedVariance_l2_of_linearization_normFourth
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (TbetaStar := TbetaStar) (τ := τ) (Vβ := Vβ) R hVβ hPstar
    (fun n => (hτpos n).le) hT hTbetaMeas hcoordMem hlimMem
    (trimmedTailProb_tendsto_zero_of_integral_norm_sq
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (τ := τ) hPstar hThetaMem hτpos hτinv hSecond)
    hBfourth hNormFourth hNormFourthInt hfiniteInt hfiniteBound

/-- Indexed finite-replication version of
`chapter10_regression_finiteReplicationTrimmedVariance_l2_of_linearization_secondMoment`. -/
theorem
    chapter10_indexed_regression_finiteReplicationTrimmedVariance_l2_of_linearization_secondMoment
    [IsFiniteMeasure μ]
    {k q : Type*} [Fintype k] [Fintype q] [DecidableEq k] [DecidableEq q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → q → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ q)
        (Rᵀ * Vβ * (Rᵀ)ᵀ))]
    {Bsecond Bfourth : ℝ} {Cfinite : q → q → ℝ}
    (hVβ : Vβ.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hThetaMem :
      ∀ n ω,
        MemLp
          (fun ωs =>
            ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ))
          2 (Pstar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hlimMem :
      ∀ a,
        MemLp (fun z : EuclideanSpace ℝ q => (z : q → ℝ) a) 2
          (multivariateGaussian (0 : EuclideanSpace ℝ q)
            (Rᵀ * Vβ * (Rᵀ)ᵀ)))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ)‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => Bsecond))
    (hBfourth : 0 ≤ Bfourth)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bfourth))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs =>
                  ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs =>
                    ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                      EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => smoothFunctionVarianceFunctional R Vβ) :=
  chapter10_indexed_regression_finiteReplicationTrimmedVariance_l2_of_linearization_normFourth
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (TbetaStar := TbetaStar) (τ := τ) (Vβ := Vβ) R hVβ hPstar
    (fun n => (hτpos n).le) hT hTbetaMeas hcoordMem hlimMem
    (trimmedTailProbIndexed_tendsto_zero_of_integral_norm_sq
      (μ := μ) (Pstar := Pstar)
      (Zstar := fun n ω ωs =>
        ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
          EuclideanSpace ℝ q) : q → ℝ))
      (τ := τ) hPstar hThetaMem hτpos hτinv hSecond)
    hBfourth hNormFourth hNormFourthInt hfiniteInt hfiniteBound

/-- Finite-replication Theorem 10.19 norm-fourth route with automatic
Gaussian-limit coordinate `MemLp 2` premises. -/
theorem
    chapter10_regression_finiteReplicationTrimmedVariance_normFourth_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {k q : Type*} [Fintype k] [DecidableEq k] [Fintype q]
    {Zsim : ℕ → ℕ → Ω → q → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    {B : ℝ} {Cfinite : q → q → ℝ}
    (hVβ : Vβ.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)
            {ωs |
              τ n <
                ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)‖}).toReal)
        atTop (fun _ => 0))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar
                (fun n ω ωs =>
                  ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar
                  (fun n ω ωs =>
                    ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                      EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => smoothFunctionVarianceFunctional R Vβ) := by
  classical
  exact
    chapter10_regression_finiteReplicationTrimmedVariance_l2_of_linearization_normFourth
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (TbetaStar := TbetaStar) (τ := τ) (Vβ := Vβ) R hVβ hPstar
      hτ hT hTbetaMeas hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two a) hTailProb hB
      hNormFourth hNormFourthInt hfiniteInt hfiniteBound

/-- Indexed finite-replication Theorem 10.19 norm-fourth route with automatic
Gaussian-limit coordinate `MemLp 2` premises. -/
theorem
    chapter10_indexed_regression_finiteReplicationTrimmedVariance_normFourth_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {k q : Type*} [Fintype k] [DecidableEq k] [Fintype q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → q → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    {B : ℝ} {Cfinite : q → q → ℝ}
    (hVβ : Vβ.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)
            {ωs |
              τ n <
                ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)‖}).toReal)
        atTop (fun _ => 0))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs =>
                  ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs =>
                    ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                      EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => smoothFunctionVarianceFunctional R Vβ) := by
  classical
  exact
    chapter10_indexed_regression_finiteReplicationTrimmedVariance_l2_of_linearization_normFourth
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (TbetaStar := TbetaStar) (τ := τ) (Vβ := Vβ) R hVβ hPstar
      hτ hT hTbetaMeas hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two a) hTailProb hB
      hNormFourth hNormFourthInt hfiniteInt hfiniteBound

/-- Finite-replication Theorem 10.19 second-moment/diverging-threshold route
with automatic Gaussian-limit coordinate `MemLp 2` premises. -/
theorem
    chapter10_regression_finiteReplicationTrimmedVariance_secondMoment_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {k q : Type*} [Fintype k] [DecidableEq k] [Fintype q]
    {Zsim : ℕ → ℕ → Ω → q → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    {Bsecond Bfourth : ℝ} {Cfinite : q → q → ℝ}
    (hVβ : Vβ.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hThetaMem :
      ∀ n ω,
        MemLp
          (fun ωs =>
            ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ))
          2 (Pstar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ)‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => Bsecond))
    (hBfourth : 0 ≤ Bfourth)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bfourth))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar
                (fun n ω ωs =>
                  ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar
                  (fun n ω ωs =>
                    ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                      EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => smoothFunctionVarianceFunctional R Vβ) := by
  classical
  exact
    chapter10_regression_finiteReplicationTrimmedVariance_l2_of_linearization_secondMoment
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (TbetaStar := TbetaStar) (τ := τ) (Vβ := Vβ) R hVβ hPstar
      hτpos hτinv hT hTbetaMeas hThetaMem hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two a) hSecond hBfourth
      hNormFourth hNormFourthInt hfiniteInt hfiniteBound

/-- Indexed finite-replication Theorem 10.19
second-moment/diverging-threshold route with automatic Gaussian-limit
coordinate `MemLp 2` premises. -/
theorem
    chapter10_indexed_regression_finiteReplicationTrimmedVariance_secondMoment_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {k q : Type*} [Fintype k] [DecidableEq k] [Fintype q]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → q → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} {Vβ : Matrix k k ℝ} (R : Matrix k q ℝ)
    {Bsecond Bfourth : ℝ} {Cfinite : q → q → ℝ}
    (hVβ : Vβ.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k) Vβ)
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hThetaMem :
      ∀ n ω,
        MemLp
          (fun ωs =>
            ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ))
          2 (Pstar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ)‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => Bsecond))
    (hBfourth : 0 ≤ Bfourth)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bfourth))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs =>
                  ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs =>
                    ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                      EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => smoothFunctionVarianceFunctional R Vβ) := by
  classical
  exact
    chapter10_indexed_regression_finiteReplicationTrimmedVariance_l2_of_linearization_secondMoment
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (TbetaStar := TbetaStar) (τ := τ) (Vβ := Vβ) R hVβ hPstar
      hτpos hτinv hT hTbetaMeas hThetaMem hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two a) hSecond hBfourth
      hNormFourth hNormFourthInt hfiniteInt hfiniteBound

set_option linter.style.longLine false

/-- Robust-feasible HC specialization of the finite-replication Theorem 10.19
norm-fourth route.

This fixes `Vβ = heteroAsymCov μ X e` in the centered finite-replication
trimmed covariance estimator and discharges covariance positive semidefiniteness
from the Chapter 7 robust feasible HC condition package. -/
theorem
chapter10_regression_finiteReplicationTrimmedVariance_normFourth_gaussianLimit_l2_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [DecidableEq k] [Fintype q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Zsim : ℕ → ℕ → Ω → q → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} (β : k → ℝ) (R : Matrix k q ℝ)
    {B : ℝ} {Cfinite : q → q → ℝ}
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (heteroAsymCov μ X e))
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)
            {ωs |
              τ n <
                ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)‖}).toReal)
        atTop (fun _ => 0))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar
                (fun n ω ωs =>
                  ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar
                  (fun n ω ωs =>
                    ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                      EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ =>
        smoothFunctionVarianceFunctional R (heteroAsymCov μ X e)) :=
  chapter10_regression_finiteReplicationTrimmedVariance_normFourth_gaussianLimit_l2
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (TbetaStar := TbetaStar) (τ := τ)
    (Vβ := heteroAsymCov μ X e) R
    (heteroAsymCov_posSemidef_of_scoreCLTConditions
      (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions)
    hPstar hτ hT hTbetaMeas hcoordMem hTailProb hB hNormFourth
    hNormFourthInt hfiniteInt hfiniteBound

/-- Indexed robust-feasible HC specialization of the finite-replication
Theorem 10.19 norm-fourth route. -/
theorem
chapter10_indexed_regression_finiteReplicationTrimmedVariance_normFourth_gaussianLimit_l2_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [DecidableEq k] [Fintype q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → q → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} (β : k → ℝ) (R : Matrix k q ℝ)
    {B : ℝ} {Cfinite : q → q → ℝ}
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (heteroAsymCov μ X e))
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω)
            {ωs |
              τ n <
                ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)‖}).toReal)
        atTop (fun _ => 0))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs =>
                  ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs =>
                    ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                      EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ =>
        smoothFunctionVarianceFunctional R (heteroAsymCov μ X e)) :=
  chapter10_indexed_regression_finiteReplicationTrimmedVariance_normFourth_gaussianLimit_l2
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (TbetaStar := TbetaStar) (τ := τ)
    (Vβ := heteroAsymCov μ X e) R
    (heteroAsymCov_posSemidef_of_scoreCLTConditions
      (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions)
    hPstar hτ hT hTbetaMeas hcoordMem hTailProb hB hNormFourth
    hNormFourthInt hfiniteInt hfiniteBound

/-- Robust-feasible HC specialization of the finite-replication Theorem 10.19
second-moment/diverging-threshold route.

The coefficient-level bootstrap weak convergence, conditional second-moment,
norm-fourth, and coordinatewise finite-replication `L²` simulation-error
premises remain explicit. -/
theorem
chapter10_regression_finiteReplicationTrimmedVariance_secondMoment_gaussianLimit_l2_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [DecidableEq k] [Fintype q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Zsim : ℕ → ℕ → Ω → q → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {TbetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} (β : k → ℝ) (R : Matrix k q ℝ)
    {Bsecond Bfourth : ℝ} {Cfinite : q → q → ℝ}
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hT :
      TendstoInBootstrapWeakDistribution μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (heteroAsymCov μ X e))
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hThetaMem :
      ∀ n ω,
        MemLp
          (fun ωs =>
            ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ))
          2 (Pstar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ)‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => Bsecond))
    (hBfourth : 0 ≤ Bfourth)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bfourth))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar
                (fun n ω ωs =>
                  ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar
                  (fun n ω ωs =>
                    ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                      EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ =>
        smoothFunctionVarianceFunctional R (heteroAsymCov μ X e)) :=
  chapter10_regression_finiteReplicationTrimmedVariance_secondMoment_gaussianLimit_l2
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (TbetaStar := TbetaStar) (τ := τ)
    (Vβ := heteroAsymCov μ X e) R
    (heteroAsymCov_posSemidef_of_scoreCLTConditions
      (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions)
    hPstar hτpos hτinv hT hTbetaMeas hThetaMem hcoordMem hSecond
    hBfourth hNormFourth hNormFourthInt hfiniteInt hfiniteBound

/-- Indexed robust-feasible HC specialization of the finite-replication
Theorem 10.19 second-moment/diverging-threshold route. -/
theorem
chapter10_indexed_regression_finiteReplicationTrimmedVariance_secondMoment_gaussianLimit_l2_of_robustFeasibleHCMomentConditions
    [IsProbabilityMeasure μ]
    {k q : Type*} [Fintype k] [DecidableEq k] [Fintype q]
    {X : ℕ → Ω → (k → ℝ)} {e y : ℕ → Ω → ℝ}
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → q → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {TbetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ k}
    {τ : ℕ → ℝ} (β : k → ℝ) (R : Matrix k q ℝ)
    {Bsecond Bfourth : ℝ} {Cfinite : q → q → ℝ}
    (hm : RobustFeasibleHCMomentConditions μ X e y β)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hT :
      TendstoInBootstrapWeakDistributionIndexed μ Pstar TbetaStar
        (multivariateGaussian (0 : EuclideanSpace ℝ k)
          (heteroAsymCov μ X e))
        (fun z : EuclideanSpace ℝ k => z))
    (hTbetaMeas : ∀ n ω, Measurable (TbetaStar n ω))
    (hThetaMem :
      ∀ n ω,
        MemLp
          (fun ωs =>
            ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ))
          2 (Pstar n ω))
    (hcoordMem :
      ∀ n ω a,
        MemLp
          (fun ωs =>
            (((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                EuclideanSpace ℝ q) : q → ℝ) a))
          2 (Pstar n ω))
    (hSecond :
      TendstoInMeasure μ
        (fun n ω =>
          ∫ ωs,
            ‖((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
              EuclideanSpace ℝ q) : q → ℝ)‖ ^ 2 ∂Pstar n ω)
        atTop (fun _ => Bsecond))
    (hBfourth : 0 ≤ Bfourth)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖TbetaStar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => Bfourth))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖TbetaStar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs =>
                  ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                    EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs =>
                    ((matrixContinuousLinearMap Rᵀ (TbetaStar n ω ωs) :
                      EuclideanSpace ℝ q) : q → ℝ)) τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ =>
        smoothFunctionVarianceFunctional R (heteroAsymCov μ X e)) :=
  chapter10_indexed_regression_finiteReplicationTrimmedVariance_secondMoment_gaussianLimit_l2
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (TbetaStar := TbetaStar) (τ := τ)
    (Vβ := heteroAsymCov μ X e) R
    (heteroAsymCov_posSemidef_of_scoreCLTConditions
      (μ := μ) (X := X) (e := e) hm.toScoreCLTConditions)
    hPstar hτpos hτinv hT hTbetaMeas hThetaMem hcoordMem hSecond
    hBfourth hNormFourth hNormFourthInt hfiniteInt hfiniteBound

set_option linter.style.longLine true

/-- Hansen Theorem 10.11/10.12 smooth finite-replication trimmed covariance
bridge from exact linearization and an underlying norm fourth moment.

The finite-replication estimator is compared to the trimmed conditional
covariance by an explicit `oₚ(1)` simulation-error premise. -/
theorem chapter10_finiteReplicationCenteredTrimmedCovariance_tendsto_of_smooth_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmedBootstrapVariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) (τ := τ)
    hfinite
    (chapter10_smooth_trimmedBootstrapVariance_tendsto_of_linearization_normFourth
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hτ hT hZmeas
      hcoordMem hlimMem hlinearization hTailProb hB hNormFourth
      hNormFourthInt)

/-- `L²` simulation-error version of the smooth finite-replication trimmed
covariance bridge. -/
theorem
    chapter10_finiteReplicationCenteredTrimmedCovariance_tendsto_of_smooth_normFourth_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {τ : ℕ → ℝ} {B : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) (τ := τ)
    hfiniteInt hfiniteBound
    (chapter10_smooth_trimmedBootstrapVariance_tendsto_of_linearization_normFourth
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hτ hT hZmeas
      hcoordMem hlimMem hlinearization hTailProb hB hNormFourth
      hNormFourthInt)

/-- `L²` simulation-error version of the smooth finite-replication trimmed
covariance bridge, with trimming-tail negligibility discharged by conditional
second-moment convergence and a diverging threshold. -/
theorem
    chapter10_finiteReplicationCenteredTrimmedCovariance_tendsto_of_smooth_secondMoment_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {τ : ℕ → ℝ} {Bsecond Bfourth : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) (τ := τ)
    hfiniteInt hfiniteBound
    (chapter10_smooth_trimmedBootstrapVariance_tendsto_of_normFourth_integral_norm_sq
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hτpos hτinv hT
      hZmeas hThetaMem hcoordMem hlimMem hlinearization hSecond
      hBfourth hNormFourth hNormFourthInt)

/-- Indexed smooth finite-replication trimmed covariance bridge from exact
linearization and an underlying norm fourth moment. -/
theorem
    chapter10_indexed_finiteReplicationCenteredTrimmedCovariance_tendsto_of_smooth_normFourth
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmedBootstrapVariance
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) (τ := τ)
    hfinite
    (chapter10_indexed_smooth_trimmedBootstrapVariance_tendsto_of_linearization_normFourth
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hτ hT hZmeas
      hcoordMem hlimMem hlinearization hTailProb hB hNormFourth
      hNormFourthInt)

/-- Indexed `L²` simulation-error version of the smooth finite-replication
trimmed covariance bridge. -/
theorem
    chapter10_indexed_finiteReplicationCenteredTrimmedCovariance_tendsto_of_smooth_normFourth_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {τ : ℕ → ℝ} {B : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) (τ := τ)
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_trimmedBootstrapVariance_tendsto_of_linearization_normFourth
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hτ hT hZmeas
      hcoordMem hlimMem hlinearization hTailProb hB hNormFourth
      hNormFourthInt)

/-- Indexed `L²` simulation-error version of the smooth finite-replication
trimmed covariance bridge, with trimming-tail negligibility discharged by
conditional second-moment convergence and a diverging threshold. -/
theorem
    chapter10_indexed_finiteReplicationCenteredTrimmedCovariance_tendsto_of_smooth_secondMoment_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {τ : ℕ → ℝ} {Bsecond Bfourth : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
    (Zstar := fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) (τ := τ)
    hfiniteInt hfiniteBound
    (chapter10_indexed_smooth_trimmedBootstrapVariance_tendsto_of_normFourth_integral_norm_sq
      (μ := μ) (Pstar := Pstar) (Tstar := Tstar)
      (thetaStar := thetaStar) (V := V) G hV hPstar hτpos hτinv hT
      hZmeas hThetaMem hcoordMem hlimMem hlinearization hSecond
      hBfourth hNormFourth hNormFourthInt)

/-- Smooth finite-replication trimmed covariance bridge with Gaussian-limit
coordinate `MemLp 2` premises discharged automatically. -/
theorem
    chapter10_finiteReplicationTrimmedCovariance_smooth_normFourth_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_finiteReplicationCenteredTrimmedCovariance_tendsto_of_smooth_normFourth
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hτ hT hZmeas hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hTailProb hB hNormFourth hNormFourthInt hfinite

/-- `L²` simulation-error version of the smooth finite-replication trimmed
covariance bridge with Gaussian-limit coordinate `MemLp 2` premises discharged
automatically. -/
theorem
    chapter10_finiteReplicationTrimmedCovariance_smooth_normFourth_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {τ : ℕ → ℝ} {B : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_finiteReplicationCenteredTrimmedCovariance_tendsto_of_smooth_normFourth_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hτ hT hZmeas hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hTailProb hB hNormFourth hNormFourthInt
      hfiniteInt hfiniteBound

/-- Smooth finite-replication trimmed covariance bridge with trimming-tail
negligibility and Gaussian-limit coordinate `MemLp 2` premises discharged. -/
theorem
    chapter10_finiteReplicationTrimmedCovariance_smooth_secondMoment_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {τ : ℕ → ℝ} {Bsecond Bfourth : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_finiteReplicationCenteredTrimmedCovariance_tendsto_of_smooth_secondMoment_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hτpos hτinv hT hZmeas hThetaMem hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hSecond hBfourth hNormFourth hNormFourthInt
      hfiniteInt hfiniteBound

/-- Indexed smooth finite-replication trimmed covariance bridge with
Gaussian-limit coordinate `MemLp 2` premises discharged automatically. -/
theorem
    chapter10_indexed_finiteReplicationTrimmedCovariance_smooth_normFourth_gaussianLimit
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_indexed_finiteReplicationCenteredTrimmedCovariance_tendsto_of_smooth_normFourth
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hτ hT hZmeas hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hTailProb hB hNormFourth hNormFourthInt hfinite

/-- Indexed `L²` simulation-error version of the smooth finite-replication
trimmed covariance bridge with Gaussian-limit coordinate `MemLp 2` premises
discharged automatically. -/
theorem
    chapter10_indexed_finiteReplicationTrimmedCovariance_smooth_normFourth_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {τ : ℕ → ℝ} {B : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_indexed_finiteReplicationCenteredTrimmedCovariance_tendsto_of_smooth_normFourth_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hτ hT hZmeas hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hTailProb hB hNormFourth hNormFourthInt
      hfiniteInt hfiniteBound

/-- Indexed smooth finite-replication trimmed covariance bridge with
trimming-tail negligibility and Gaussian-limit coordinate `MemLp 2` premises
discharged. -/
theorem
    chapter10_indexed_finiteReplicationTrimmedCovariance_smooth_secondMoment_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r] [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (G : Matrix r d ℝ)
    [IsFiniteMeasure (multivariateGaussian (0 : EuclideanSpace ℝ r) (G * V * Gᵀ))]
    {τ : ℕ → ℝ} {Bsecond Bfourth : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => G * V * Gᵀ) := by
  classical
  exact
    chapter10_indexed_finiteReplicationCenteredTrimmedCovariance_tendsto_of_smooth_secondMoment_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) G
      hV hPstar hτpos hτinv hT hZmeas hThetaMem hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := G * V * Gᵀ) a)
      hlinearization hSecond hBfourth hNormFourth hNormFourthInt
      hfiniteInt hfiniteBound

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

/-- Hansen Theorem 10.11/10.12 finite-replication trimmed covariance from
weak convergence, uniform-square-tail controls, and coordinatewise `L²`
simulation-error bounds. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_uniformSquareTail_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ} {Cfinite : k → k → ℝ}
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
          (fun ωlim => Z ωlim a + Z ωlim c))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar Zstar τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar Zstar τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
    hfiniteInt hfiniteBound
    (chapter10_trimmedBootstrapVariance_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hτ hZmeas hZmem hZlim hweak hTailProb
      hTailCoord hTailSum)

/-- Hansen Theorem 10.11/10.12 finite-replication trimmed covariance from
weak convergence, uniform-square-tail controls, a second-moment trimming-tail
bound, and coordinatewise `L²` simulation-error bounds. -/
theorem
    chapter10_finiteReplicationCenteredTrimmedCovariance_tendsto_of_integral_norm_sq_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ} {B : ℝ}
    {Cfinite : k → k → ℝ}
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
          (fun ωlim => Z ωlim a + Z ωlim c))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar Zstar τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar Zstar τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
    hfiniteInt hfiniteBound
    (chapter10_trimmedBootstrapVariance_tendsto_of_uniformSquareTail_integral_norm_sq
      (μ := μ) (ν := ν) hPstar hτpos hτinv hZmeas hZmemVec hZmem
      hZlim hweak hSecond hTailCoord hTailSum)

/-- Hansen Theorem 10.11/10.12 finite-replication trimmed covariance from
weak convergence, an eventually bounded trim threshold, and coordinatewise `L²`
simulation-error bounds. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_eventualBound_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ} {Cτ : ℝ}
    {Cfinite : k → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hτBound : ∀ᶠ n in atTop, τ n ≤ Cτ)
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
        atTop (fun _ => 0))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar Zstar τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar Zstar τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
    hfiniteInt hfiniteBound
    (chapter10_trimmedBootstrapVariance_tendsto_of_eventualBound_memLp_limit
      (μ := μ) (ν := ν) hPstar hτ hτBound hZmeas hZlim hweak hTailProb)

/-- Hansen Theorem 10.11/10.12 finite-replication trimmed covariance from
bootstrap weak convergence, fourth-moment tail controls, and coordinatewise
`L²` simulation-error bounds. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_fourthMoment_tails_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ}
    {Bcoord : k → ℝ} {Bsum : k → k → ℝ}
    {Cfinite : k → k → ℝ}
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
            (fun ωlim => (Z ωlim a + Z ωlim c) ^ 2) ωlim ∂ν) ≤ ε)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar Zstar τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar Zstar τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
    hfiniteInt hfiniteBound
    (chapter10_trimmedBootstrapVariance_tendsto_of_weak_distribution_fourthMoment_tails
      (μ := μ) (ν := ν) hPstar hτ hZmeas hZmem hZlim hweak hTailProb
      hBcoord hFourthCoord hFourthCoordInt hLimitTailCoord
      hBsum hFourthSum hFourthSumInt hLimitTailSum)

/-- Hansen Theorem 10.11/10.12 finite-replication trimmed covariance from
bootstrap weak convergence and fourth-moment convergence, with weak-limit
coordinate and coordinate-sum tail premises discharged by `MemLp` and
finite-replication error discharged by coordinatewise `L²` bounds. -/
theorem
    chapter10_finiteReplicationCenteredTrimmedCovariance_tendsto_of_fourthMoment_memLp_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ}
    {Bcoord : k → ℝ} {Bsum : k → k → ℝ}
    {Cfinite : k → k → ℝ}
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar Zstar τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar Zstar τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
    hfiniteInt hfiniteBound
    (chapter10_trimmedBootstrapVariance_tendsto_of_fourthMoment_memLp
      (μ := μ) (ν := ν) hPstar hτ hZmeas hZmem hZlim hweak hTailProb
      hBcoord hFourthCoord hFourthCoordInt
      hBsum hFourthSum hFourthSumInt)

/-- Indexed Hansen Theorem 10.11/10.12 finite-replication trimmed covariance
from weak convergence, uniform-square-tail controls, and coordinatewise `L²`
simulation-error bounds. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_uniformSquareTail_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ} {Cfinite : k → k → ℝ}
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
          (fun ωlim => Z ωlim a + Z ωlim c))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
    hfiniteInt hfiniteBound
    (chapter10_indexed_trimmedBootstrapVariance_tendsto_of_weak_distribution_uniformSquareTail
      (μ := μ) (ν := ν) hPstar hτ hZmeas hZmem hZlim hweak hTailProb
      hTailCoord hTailSum)

/-- Indexed Hansen Theorem 10.11/10.12 finite-replication trimmed covariance
from weak convergence, uniform-square-tail controls, a second-moment
trimming-tail bound, and coordinatewise `L²` simulation-error bounds. -/
theorem
    chapter10_indexed_finiteReplicationCenteredTrimmedCovariance_tendsto_of_integral_norm_sq_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ} {B : ℝ}
    {Cfinite : k → k → ℝ}
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
          (fun ωlim => Z ωlim a + Z ωlim c))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
    hfiniteInt hfiniteBound
    (chapter10_indexed_trimmedBootstrapVariance_tendsto_of_uniformSquareTail_integral_norm_sq
      (μ := μ) (ν := ν) hPstar hτpos hτinv hZmeas hZmemVec hZmem
      hZlim hweak hSecond hTailCoord hTailSum)

/-- Indexed Hansen Theorem 10.11/10.12 finite-replication trimmed covariance
from weak convergence, an eventually bounded trim threshold, and coordinatewise
`L²` simulation-error bounds. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_eventualBound_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ} {Cτ : ℝ}
    {Cfinite : k → k → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hτBound : ∀ᶠ n in atTop, τ n ≤ Cτ)
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
        atTop (fun _ => 0))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
    hfiniteInt hfiniteBound
    (chapter10_indexed_trimmedBootstrapVariance_tendsto_of_eventualBound_memLp_limit
      (μ := μ) (ν := ν) hPstar hτ hτBound hZmeas hZlim hweak hTailProb)

/-- Indexed Hansen Theorem 10.11/10.12 finite-replication trimmed covariance
from bootstrap weak convergence, fourth-moment tail controls, and
coordinatewise `L²` simulation-error bounds. -/
theorem
    chapter10_indexed_finiteReplicationTrimmedCovariance_tendsto_of_fourthMoment_tails_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ}
    {Bcoord : k → ℝ} {Bsum : k → k → ℝ}
    {Cfinite : k → k → ℝ}
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
            (fun ωlim => (Z ωlim a + Z ωlim c) ^ 2) ωlim ∂ν) ≤ ε)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
    hfiniteInt hfiniteBound
    (chapter10_indexed_trimmedBootstrapVariance_tendsto_of_weak_distribution_fourthMoment_tails
      (μ := μ) (ν := ν) hPstar hτ hZmeas hZmem hZlim hweak hTailProb
      hBcoord hFourthCoord hFourthCoordInt hLimitTailCoord
      hBsum hFourthSum hFourthSumInt hLimitTailSum)

/-- Indexed Hansen Theorem 10.11/10.12 finite-replication trimmed covariance
from bootstrap weak convergence and fourth-moment convergence, with weak-limit
coordinate and coordinate-sum tail premises discharged by `MemLp` and
finite-replication error discharged by coordinatewise `L²` bounds. -/
theorem
    chapter10_indexed_finiteReplicationCenteredTrimmedCovariance_tendsto_of_fourthMoment_memLp_l2
    [IsFiniteMeasure μ] {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ}
    {Bcoord : k → ℝ} {Bsum : k → k → ℝ}
    {Cfinite : k → k → ℝ}
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
          (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
    (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar) (τ := τ)
    hfiniteInt hfiniteBound
    (chapter10_indexed_trimmedBootstrapVariance_tendsto_of_fourthMoment_memLp
      (μ := μ) (ν := ν) hPstar hτ hZmeas hZmem hZlim hweak hTailProb
      hBcoord hFourthCoord hFourthCoordInt
      hBsum hFourthSum hFourthSumInt)

/-- Hansen Theorem 10.11/10.12 finite-replication trimmed covariance from
weak convergence and an eventually bounded trim threshold.

This is the direct `oₚ(1)` simulation-error version of the bounded-threshold
trimmed covariance route. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_eventualBound_memLp
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zstar : ℕ → Ω → Ωs → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ} {Cτ : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hτBound : ∀ᶠ n in atTop, τ n ≤ Cτ)
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistribution μ Pstar Zstar ν Z)
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
        atTop (fun _ => 0))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMat Pstar Zstar τ n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmedBootstrapVariance
    (μ := μ) hfinite
    (chapter10_trimmedBootstrapVariance_tendsto_of_eventualBound_memLp_limit
      (μ := μ) (ν := ν) hPstar hτ hτBound hZmeas hZlim hweak hTailProb)

/-- Indexed Hansen Theorem 10.11/10.12 finite-replication trimmed covariance
from weak convergence and an eventually bounded trim threshold.

This is the sample-size-indexed direct `oₚ(1)` simulation-error version of the
bounded-threshold trimmed covariance route. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_eventualBound_memLp
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zstar : ∀ n, Ω → Ωboot n → k → ℝ}
    {Z : Ωlim → k → ℝ} {τ : ℕ → ℝ} {Cτ : ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hτBound : ∀ᶠ n in atTop, τ n ≤ Cτ)
    (hZmeas : ∀ n ω, Measurable (Zstar n ω))
    (hZlim : ∀ a, MemLp (fun ωlim => Z ωlim a) 2 ν)
    (hweak : TendstoInBootstrapWeakDistributionIndexed μ Pstar Zstar ν Z)
    (hTailProb :
      TendstoInMeasure μ
        (fun n ω =>
          ((Pstar n ω) {ωs | τ n < ‖Zstar n ω ωs‖}).toReal)
        atTop (fun _ => 0))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmedBootstrapVariance
    (μ := μ) hfinite
    (chapter10_indexed_trimmedBootstrapVariance_tendsto_of_eventualBound_memLp_limit
      (μ := μ) (ν := ν) hPstar hτ hτBound hZmeas hZlim hweak hTailProb)

/-- Hansen Theorem 10.11/10.12 finite-replication trimmed covariance from
bootstrap weak convergence and fourth-moment tail controls. -/
theorem
    chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_fourthMoment_tails
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
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
            (fun ωlim => (Z ωlim a + Z ωlim c) ^ 2) ωlim ∂ν) ≤ ε)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMat Pstar Zstar τ n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmedBootstrapVariance
    (μ := μ) hfinite
    (chapter10_trimmedBootstrapVariance_tendsto_of_weak_distribution_fourthMoment_tails
      (μ := μ) (ν := ν) hPstar hτ hZmeas hZmem hZlim hweak hTailProb
      hBcoord hFourthCoord hFourthCoordInt hLimitTailCoord
      hBsum hFourthSum hFourthSumInt hLimitTailSum)

/-- Hansen Theorem 10.11/10.12 finite-replication trimmed covariance from
bootstrap weak convergence and fourth-moment convergence, with weak-limit
coordinate and coordinate-sum tail premises discharged by `MemLp`. -/
theorem
    chapter10_finiteReplicationCenteredTrimmedCovariance_tendsto_of_fourthMoment_memLp
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMat Pstar Zstar τ n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmedBootstrapVariance
    (μ := μ) hfinite
    (chapter10_trimmedBootstrapVariance_tendsto_of_fourthMoment_memLp
      (μ := μ) (ν := ν) hPstar hτ hZmeas hZmem hZlim hweak hTailProb
      hBcoord hFourthCoord hFourthCoordInt
      hBsum hFourthSum hFourthSumInt)

/-- Indexed Hansen Theorem 10.11/10.12 finite-replication trimmed covariance
from bootstrap weak convergence and fourth-moment tail controls. -/
theorem
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_fourthMoment_tails
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
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
            (fun ωlim => (Z ωlim a + Z ωlim c) ^ 2) ωlim ∂ν) ≤ ε)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmedBootstrapVariance
    (μ := μ) hfinite
    (chapter10_indexed_trimmedBootstrapVariance_tendsto_of_weak_distribution_fourthMoment_tails
      (μ := μ) (ν := ν) hPstar hτ hZmeas hZmem hZlim hweak hTailProb
      hBcoord hFourthCoord hFourthCoordInt hLimitTailCoord
      hBsum hFourthSum hFourthSumInt hLimitTailSum)

/-- Indexed Hansen Theorem 10.11/10.12 finite-replication trimmed covariance
from bootstrap weak convergence and fourth-moment convergence, with weak-limit
coordinate and coordinate-sum tail premises discharged by `MemLp`. -/
theorem
    chapter10_indexed_finiteReplicationCenteredTrimmedCovariance_tendsto_of_fourthMoment_memLp
    {k : Type*} [Fintype k] [IsFiniteMeasure ν]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → k → ℝ}
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
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω)
        atTop (fun _ => 0)) :
    TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
      (fun _ => fun a c =>
        (∫ ωlim, Z ωlim a * Z ωlim c ∂ν) -
          (∫ ωlim, Z ωlim a ∂ν) * (∫ ωlim, Z ωlim c ∂ν)) :=
  chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmedBootstrapVariance
    (μ := μ) hfinite
    (chapter10_indexed_trimmedBootstrapVariance_tendsto_of_fourthMoment_memLp
      (μ := μ) (ν := ν) hPstar hτ hZmeas hZmem hZlim hweak hTailProb
      hBcoord hFourthCoord hFourthCoordInt
      hBsum hFourthSum hFourthSumInt)

end FiniteReplicationVariance

section SmoothFunctionFiniteReplicationCovariance

/-- Hansen Theorem 10.8/10.11 bridge for smooth plug-in covariance estimators
using finite bootstrap replications.

If the finite-replication covariance matrix converges in ordinary probability
to `V`, and the plug-in Jacobian converges to `G`, then the deterministic
finite-replication plug-in estimator `G_n' V_B G_n` converges in bootstrap
probability to `G'VG`.  The concrete Theorem 10.11 routes supply `hV`. -/
theorem chapter10_bootstrap_smooth_variance_of_finiteReplicationCovarianceMat
    {d r : Type*} [Fintype d] [Fintype r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zsim : ℕ → ℕ → Ω → d → ℝ}
    {Gseq : ℕ → Ω → Matrix d r ℝ} {G : Matrix d r ℝ}
    {V : Matrix d d ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hV :
      TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
        (fun _ => V)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gseq n ω)
          (finiteReplicationCovarianceMomentMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_bootstrap_smooth_variance_consistency_of_tendstoInMeasure_components
    (μ := μ) (Pstar := Pstar)
    (Gseq := Gseq) (Vseq := finiteReplicationCovarianceMomentMat Zsim)
    (G := G) (V := V) hPstar hG hV

/-- Hansen Theorem 10.8/10.11 bridge for smooth plug-in covariance estimators
using Hansen's centered finite-replication covariance matrix. -/
theorem
    chapter10_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    {d r : Type*} [Fintype d] [Fintype r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zsim : ℕ → ℕ → Ω → d → ℝ}
    {Gseq : ℕ → Ω → Matrix d r ℝ} {G : Matrix d r ℝ}
    {V : Matrix d d ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hV :
      TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
        (fun _ => V)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_bootstrap_smooth_variance_consistency_of_tendstoInMeasure_components
    (μ := μ) (Pstar := Pstar)
    (Gseq := Gseq) (Vseq := finiteReplicationCovarianceCenteredMat Zsim)
    (G := G) (V := V) hPstar hG hV

/-- Indexed Hansen Theorem 10.8/10.11 bridge for smooth plug-in covariance
estimators using finite bootstrap replications. -/
theorem
    chapter10_indexed_bootstrap_smooth_variance_of_finiteReplicationCovarianceMat
    {d r : Type*} [Fintype d] [Fintype r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zsim : ℕ → ℕ → Ω → d → ℝ}
    {Gseq : ℕ → Ω → Matrix d r ℝ} {G : Matrix d r ℝ}
    {V : Matrix d d ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hV :
      TendstoInMeasure μ (finiteReplicationCovarianceMomentMat Zsim) atTop
        (fun _ => V)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gseq n ω)
          (finiteReplicationCovarianceMomentMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_indexed_bootstrap_smooth_variance_consistency_of_tendstoInMeasure_components
    (μ := μ) (Pstar := Pstar)
    (Gseq := Gseq) (Vseq := finiteReplicationCovarianceMomentMat Zsim)
    (G := G) (V := V) hPstar hG hV

/-- Indexed Hansen Theorem 10.8/10.11 bridge for smooth plug-in covariance
estimators using Hansen's centered finite-replication covariance matrix. -/
theorem
    chapter10_indexed_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    {d r : Type*} [Fintype d] [Fintype r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zsim : ℕ → ℕ → Ω → d → ℝ}
    {Gseq : ℕ → Ω → Matrix d r ℝ} {G : Matrix d r ℝ}
    {V : Matrix d d ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hV :
      TendstoInMeasure μ (finiteReplicationCovarianceCenteredMat Zsim) atTop
        (fun _ => V)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_indexed_bootstrap_smooth_variance_consistency_of_tendstoInMeasure_components
    (μ := μ) (Pstar := Pstar)
    (Gseq := Gseq) (Vseq := finiteReplicationCovarianceCenteredMat Zsim)
    (G := G) (V := V) hPstar hG hV

/-- Hansen Theorem 10.8/10.11 plug-in covariance estimator from bounded
finite-replication `L²` WLLN bounds.

This theorem inserts Hansen's centered finite-replication covariance estimator
directly into `G_n' V_B G_n` once the finite-replication mean and cross-moment
errors are `O(B⁻¹)` in mean square. -/
theorem chapter10_smoothVariance_finiteReplicationCentered_l2Bounds
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Z : ℕ → ℕ → Ω → d → ℝ}
    {Gseq : ℕ → Ω → Matrix d r ℝ} {G : Matrix d r ℝ}
    {m : d → ℝ} {M₂ : Matrix d d ℝ}
    {Cmean : d → ℝ} {Ccross : d → d → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hmeanInt :
      ∀ a B, Integrable
        (fun ω => ‖finiteReplicationMeanVec Z B ω a - m a‖ ^
          (2 : ℝ)) μ)
    (hmeanBound :
      ∀ a,
        ∀ᶠ B in atTop,
          (∫ ω, ‖finiteReplicationMeanVec Z B ω a - m a‖ ^
              (2 : ℝ) ∂μ) ≤
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
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gseq n ω)
          (finiteReplicationCovarianceCenteredMat Z n ω))
      (fun _ =>
        smoothFunctionVarianceFunctional G
          (fun a c => M₂ a c - m a * m c)) :=
  chapter10_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) hPstar hG
    (chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_error_bounds
      (μ := μ) (Z := Z) (m := m) (M₂ := M₂)
      (Cmean := Cmean) (Ccross := Ccross)
      hmeanInt hmeanBound hcrossInt hcrossBound)

/-- Indexed Hansen Theorem 10.8/10.11 plug-in covariance estimator from
bounded finite-replication `L²` WLLN bounds. -/
theorem chapter10_indexed_smoothVariance_finiteReplicationCentered_l2Bounds
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Z : ℕ → ℕ → Ω → d → ℝ}
    {Gseq : ℕ → Ω → Matrix d r ℝ} {G : Matrix d r ℝ}
    {m : d → ℝ} {M₂ : Matrix d d ℝ}
    {Cmean : d → ℝ} {Ccross : d → d → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hmeanInt :
      ∀ a B, Integrable
        (fun ω => ‖finiteReplicationMeanVec Z B ω a - m a‖ ^
          (2 : ℝ)) μ)
    (hmeanBound :
      ∀ a,
        ∀ᶠ B in atTop,
          (∫ ω, ‖finiteReplicationMeanVec Z B ω a - m a‖ ^
              (2 : ℝ) ∂μ) ≤
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
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gseq n ω)
          (finiteReplicationCovarianceCenteredMat Z n ω))
      (fun _ =>
        smoothFunctionVarianceFunctional G
          (fun a c => M₂ a c - m a * m c)) :=
  chapter10_indexed_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) hPstar hG
    (chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_error_bounds
      (μ := μ) (Z := Z) (m := m) (M₂ := M₂)
      (Cmean := Cmean) (Ccross := Ccross)
      hmeanInt hmeanBound hcrossInt hcrossBound)

/-- Hansen Theorem 10.8/10.11 plug-in covariance estimator from conditional
covariance consistency and finite-replication `L²` simulation error.

This is the smooth plug-in version of the centered finite-replication
simulation-error transfer against the ordinary conditional bootstrap covariance
matrix. -/
theorem chapter10_smoothVariance_finiteReplicationCentered_l2Simulation
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zsim : ℕ → ℕ → Ω → d → ℝ}
    {Zstar : ℕ → Ω → Ωs → d → ℝ}
    {Gseq : ℕ → Ω → Matrix d r ℝ} {G : Matrix d r ℝ}
    {V : Matrix d d ℝ} {Cfinite : d → d → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMat Pstar Zstar n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMat Pstar Zstar n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ))
    (hboot :
      TendstoInMeasure μ (bootstrapCovarianceMat Pstar Zstar) atTop
        (fun _ => V)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) hPstar hG
    (chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
      hfiniteInt hfiniteBound hboot)

/-- Indexed Hansen Theorem 10.8/10.11 plug-in covariance estimator from
conditional covariance consistency and finite-replication `L²` simulation
error. -/
theorem chapter10_indexed_smoothVariance_finiteReplicationCentered_l2Simulation
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zsim : ℕ → ℕ → Ω → d → ℝ}
    {Zstar : ∀ n, Ω → Ωboot n → d → ℝ}
    {Gseq : ℕ → Ω → Matrix d r ℝ} {G : Matrix d r ℝ}
    {V : Matrix d d ℝ} {Cfinite : d → d → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar Zstar n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar Zstar n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ))
    (hboot :
      TendstoInMeasure μ (bootstrapCovarianceMatIndexed Pstar Zstar) atTop
        (fun _ => V)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_indexed_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) hPstar hG
    (chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_l2_simulation_error
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
      hfiniteInt hfiniteBound hboot)

/-- Theorem 10.8/10.11 ordinary-bootstrap finite-replication smooth plug-in
route with a deterministic Jacobian source and iid observations.

The normalized `Fin (n+1)` ordinary bootstrap covariance supplies the target
conditional covariance; coordinatewise `O(n⁻¹)` simulation error transfers
Hansen's centered finite-replication covariance estimator to that target before
the smooth plug-in covariance CMT is applied. -/
theorem
    chapter10_indexed_smoothVariance_detJacobian_finSuccFiniteReplicationCovariance_l2_iid
    [IsProbabilityMeasure μ] [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Useq : ℕ → Ω → A} {u : A} {Gfun : A → Matrix d r ℝ}
    {Zsim : ℕ → ℕ → Ω → d → ℝ} {Cfinite : d → d → ℝ}
    (Y : ℕ → Ω → d → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on Y))
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hU : TendstoInMeasure μ Useq atTop (fun _ => u))
    (hG : ContinuousAt Gfun u)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
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
                n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
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
                  n ω) a c‖ ^ (2 : ℝ) ∂μ) ≤
              Cfinite a c / (n : ℝ)) :
    TendstoInBootstrapProbabilityIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gfun (Useq n ω))
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
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
      (Vseq := finiteReplicationCovarianceCenteredMat Zsim)
      (V := covMat μ (Y 0)) hPstar hU hG
      (chapter10_indexed_finiteReplicationCovarianceCenteredMat_finSucc_l2_iid
        (μ := μ) (Zsim := Zsim) (Cfinite := Cfinite) Y hYmem
        hindep hident hfiniteInt hfiniteBound)

/-- Theorem 10.8/10.11 ordinary-bootstrap finite-replication smooth plug-in
route with a deterministic Jacobian source and the textbook `iIndepFun`
premise. -/
theorem
    chapter10_indexed_smoothVariance_detJacobian_finSuccFiniteReplicationCovariance_l2_iIndep
    [IsProbabilityMeasure μ] [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Useq : ℕ → Ω → A} {u : A} {Gfun : A → Matrix d r ℝ}
    {Zsim : ℕ → ℕ → Ω → d → ℝ} {Cfinite : d → d → ℝ}
    (Y : ℕ → Ω → d → ℝ)
    (hYmem : ∀ a, MemLp (fun ω => Y 0 ω a) 2 μ)
    (hindep : iIndepFun Y μ)
    (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hU : TendstoInMeasure μ Useq atTop (fun _ => u))
    (hG : ContinuousAt Gfun u)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
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
                n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
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
                  n ω) a c‖ ^ (2 : ℝ) ∂μ) ≤
              Cfinite a c / (n : ℝ)) :
    TendstoInBootstrapProbabilityIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gfun (Useq n ω))
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional (Gfun u) (covMat μ (Y 0))) :=
  chapter10_indexed_smoothVariance_detJacobian_finSuccFiniteReplicationCovariance_l2_iid
    (μ := μ) (Useq := Useq) (u := u) (Gfun := Gfun)
    (Zsim := Zsim) (Cfinite := Cfinite) Y hYmem
    (fun _ _ hij => hindep.indepFun hij) hident hU hG
    hfiniteInt hfiniteBound

/-- Theorem 10.8/10.11 ordinary-bootstrap finite-replication smooth plug-in
route with a stochastic continuous Jacobian source and iid observations. -/
theorem
    chapter10_indexed_smoothVariance_contJacobian_finSuccFiniteReplicationCovariance_l2_iid
    [IsProbabilityMeasure μ] [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Ustar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → A}
    {u : A} {Gfun : A → Matrix d r ℝ}
    {Zsim : ℕ → ℕ → Ω → d → ℝ} {Cfinite : d → d → ℝ}
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
    (hG : ContinuousAt Gfun u)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
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
                n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
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
                  n ω) a c‖ ^ (2 : ℝ) ∂μ) ≤
              Cfinite a c / (n : ℝ)) :
    TendstoInBootstrapProbabilityIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gfun (Ustar n ω ωs))
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
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
      (Vstar := fun n ω _ => finiteReplicationCovarianceCenteredMat Zsim n ω)
      (V := covMat μ (Y 0)) hPstar hU hG
      (tendstoInBootstrapProbabilityIndexed_of_tendstoInMeasure
        (μ := μ)
        (Pstar := fun n _ =>
          (ProbabilityTheory.uniformOn
            (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
              Measure (Fin (n + 1) → Fin (n + 1))))
        hPstar
        (chapter10_indexed_finiteReplicationCovarianceCenteredMat_finSucc_l2_iid
          (μ := μ) (Zsim := Zsim) (Cfinite := Cfinite) Y hYmem
          hindep hident hfiniteInt hfiniteBound))

/-- Theorem 10.8/10.11 ordinary-bootstrap finite-replication smooth plug-in
route with a stochastic continuous Jacobian source and the textbook
`iIndepFun` premise. -/
theorem
    chapter10_indexed_smoothVariance_contJacobian_finSuccFiniteReplicationCovariance_l2_iIndep
    [IsProbabilityMeasure μ] [Fintype d] [Fintype r] [PseudoMetricSpace A]
    {Ustar : ∀ n, Ω → (Fin (n + 1) → Fin (n + 1)) → A}
    {u : A} {Gfun : A → Matrix d r ℝ}
    {Zsim : ℕ → ℕ → Ω → d → ℝ} {Cfinite : d → d → ℝ}
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
    (hG : ContinuousAt Gfun u)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
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
                n ω) a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
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
                  n ω) a c‖ ^ (2 : ℝ) ∂μ) ≤
              Cfinite a c / (n : ℝ)) :
    TendstoInBootstrapProbabilityIndexed μ
      (fun n _ =>
        (ProbabilityTheory.uniformOn
          (Set.univ : Set (Fin (n + 1) → Fin (n + 1))) :
            Measure (Fin (n + 1) → Fin (n + 1))))
      (fun n ω ωs =>
        smoothFunctionVarianceFunctional (Gfun (Ustar n ω ωs))
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional (Gfun u) (covMat μ (Y 0))) :=
  chapter10_indexed_smoothVariance_contJacobian_finSuccFiniteReplicationCovariance_l2_iid
    (μ := μ) (Ustar := Ustar) (u := u) (Gfun := Gfun)
    (Zsim := Zsim) (Cfinite := Cfinite) Y hYmem
    (fun _ _ hij => hindep.indepFun hij) hident hU hG
    hfiniteInt hfiniteBound

/-- Hansen Theorem 10.8/10.11/10.12 plug-in covariance estimator from trimmed
conditional covariance consistency and finite-replication `L²` simulation
error.

This composes the trimmed Theorem 10.12 covariance target with the centered
finite-replication simulation-error transfer, then inserts the result into the
smooth plug-in covariance estimator. -/
theorem chapter10_smoothVariance_finiteReplicationCentered_trimmedL2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r]
    {Pstar : ℕ → Ω → Measure Ωs}
    {Zsim : ℕ → ℕ → Ω → d → ℝ}
    {Zstar : ℕ → Ω → Ωs → d → ℝ}
    {τ : ℕ → ℝ}
    {Gseq : ℕ → Ω → Matrix d r ℝ} {G : Matrix d r ℝ}
    {V : Matrix d d ℝ} {Cfinite : d → d → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar Zstar τ n ω) a c‖ ^
            (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar Zstar τ n ω) a c‖ ^
              (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ))
    (htrim :
      TendstoInMeasure μ (trimmedBootstrapCovarianceMat Pstar Zstar τ)
        atTop (fun _ => V)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) hPstar hG
    (chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
      (τ := τ) hfiniteInt hfiniteBound htrim)

/-- Indexed Hansen Theorem 10.8/10.11/10.12 plug-in covariance estimator from
trimmed conditional covariance consistency and finite-replication `L²`
simulation error. -/
theorem chapter10_indexed_smoothVariance_finiteReplicationCentered_trimmedL2
    [IsFiniteMeasure μ]
    {d r : Type*} [Fintype d] [Fintype r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Zsim : ℕ → ℕ → Ω → d → ℝ}
    {Zstar : ∀ n, Ω → Ωboot n → d → ℝ}
    {τ : ℕ → ℝ}
    {Gseq : ℕ → Ω → Matrix d r ℝ} {G : Matrix d r ℝ}
    {V : Matrix d d ℝ} {Cfinite : d → d → ℝ}
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hG : TendstoInMeasure μ Gseq atTop (fun _ => G))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ))
    (htrim :
      TendstoInMeasure μ (trimmedBootstrapCovarianceMatIndexed Pstar Zstar τ)
        atTop (fun _ => V)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Gseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional G V) :=
  chapter10_indexed_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) hPstar hG
    (chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_trimmed_l2_simulation_error
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar) (Zstar := Zstar)
      (τ := τ) hfiniteInt hfiniteBound htrim)

/-- Smooth plug-in covariance estimator from the smooth exact-linearization
finite-replication covariance route, with Gaussian-limit coordinate `MemLp 2`
premises discharged automatically. -/
theorem
    chapter10_smoothVariance_finiteReplication_smoothCov_gaussianLimit
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {B : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) :=
  chapter10_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
    (G := H) (V := Glin * V * Glinᵀ) hPstar hH
    (chapter10_finiteReplicationCovarianceCenteredMat_smooth_normFourth_gaussianLimit
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
      hV hPstar hT hcoordMem hlinearization hB hNormFourth
      hNormFourthInt hfinite)

/-- `L²` simulation-error version of
`chapter10_smoothVariance_finiteReplication_smoothCov_gaussianLimit`. -/
theorem
    chapter10_smoothVariance_finiteReplication_smoothCov_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {B : ℝ} {Cfinite : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) :=
  chapter10_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
    (G := H) (V := Glin * V * Glinᵀ) hPstar hH
    (chapter10_finiteReplicationCovarianceCenteredMat_smooth_normFourth_gaussianLimit_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
      hV hPstar hT hcoordMem hlinearization hB hNormFourth
      hNormFourthInt hfiniteInt hfiniteBound)

/-- Indexed smooth plug-in covariance estimator from the smooth
exact-linearization finite-replication covariance route, with Gaussian-limit
coordinate `MemLp 2` premises discharged automatically. -/
theorem
    chapter10_indexed_smoothVariance_finiteReplication_smoothCov_gaussianLimit
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {B : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) :=
  chapter10_indexed_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
    (G := H) (V := Glin * V * Glinᵀ) hPstar hH
    (chapter10_indexed_finiteReplicationCovarianceCenteredMat_smooth_normFourth_gaussianLimit
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
      hV hPstar hT hcoordMem hlinearization hB hNormFourth
      hNormFourthInt hfinite)

/-- Indexed `L²` simulation-error version of
`chapter10_indexed_smoothVariance_finiteReplication_smoothCov_gaussianLimit`. -/
theorem
    chapter10_indexed_smoothVariance_finiteReplication_smoothCov_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {B : ℝ} {Cfinite : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
    (hB : 0 ≤ B)
    (hNormFourth :
      TendstoInMeasure μ
        (fun n ω => ∫ ωs, ‖Tstar n ω ωs‖ ^ 4 ∂Pstar n ω)
        atTop (fun _ => B))
    (hNormFourthInt :
      ∀ n ω, Integrable (fun ωs => ‖Tstar n ω ωs‖ ^ 4)
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) :=
  chapter10_indexed_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
    (G := H) (V := Glin * V * Glinᵀ) hPstar hH
    (chapter10_indexed_finiteReplicationCovarianceCenteredMat_smooth_normFourth_gaussianLimit_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
      hV hPstar hT hcoordMem hlinearization hB hNormFourth
      hNormFourthInt hfiniteInt hfiniteBound)

/-- Smooth plug-in covariance estimator from the smooth coordinate-fourth-moment
finite-replication covariance route, with Gaussian-limit coordinate `MemLp 2`
premises discharged automatically. -/
theorem
    chapter10_smoothVariance_finiteReplication_smoothCov_fourthMoment_gaussianLimit
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {Bcoord : r → ℝ} {Bsum : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoordLinear :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              (((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordLinearInt :
      ∀ n ω a,
        Integrable
          (fun ωs =>
            (((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4)
          (Pstar n ω))
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSumLinear :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              ((((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) a) +
                (((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
                  EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumLinearInt :
      ∀ n ω a c,
        Integrable
          (fun ωs =>
            ((((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) +
              (((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4)
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) :=
  chapter10_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
    (G := H) (V := Glin * V * Glinᵀ) hPstar hH
    (chapter10_finiteReplicationCovarianceCenteredMat_smooth_fourthMoment_gaussianLimit
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
      hV hPstar hT hcoordMem hlinearization
      hBcoord hFourthCoordLinear hFourthCoordLinearInt
      hBsum hFourthSumLinear hFourthSumLinearInt hfinite)

/-- `L²` simulation-error version of
`chapter10_smoothVariance_finiteReplication_smoothCov_fourthMoment_gaussianLimit`. -/
theorem
    chapter10_smoothVariance_finiteReplication_smoothCov_fourthMoment_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {Bcoord : r → ℝ} {Bsum : r → r → ℝ} {Cfinite : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoordLinear :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              (((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordLinearInt :
      ∀ n ω a,
        Integrable
          (fun ωs =>
            (((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4)
          (Pstar n ω))
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSumLinear :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              ((((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) a) +
                (((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
                  EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumLinearInt :
      ∀ n ω a c,
        Integrable
          (fun ωs =>
            ((((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) +
              (((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4)
          (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) :=
  chapter10_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
    (G := H) (V := Glin * V * Glinᵀ) hPstar hH
    (chapter10_finiteReplicationCovarianceCenteredMat_smooth_fourthMoment_gaussianLimit_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
      hV hPstar hT hcoordMem hlinearization
      hBcoord hFourthCoordLinear hFourthCoordLinearInt
      hBsum hFourthSumLinear hFourthSumLinearInt hfiniteInt hfiniteBound)

/-- Indexed smooth plug-in covariance estimator from the smooth
coordinate-fourth-moment finite-replication covariance route, with
Gaussian-limit coordinate `MemLp 2` premises discharged automatically. -/
theorem
    chapter10_indexed_smoothVariance_finiteReplication_smoothCov_fourthMoment_gaussianLimit
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {Bcoord : r → ℝ} {Bsum : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoordLinear :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              (((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordLinearInt :
      ∀ n ω a,
        Integrable
          (fun ωs =>
            (((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4)
          (Pstar n ω))
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSumLinear :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              ((((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) a) +
                (((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
                  EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumLinearInt :
      ∀ n ω a c,
        Integrable
          (fun ωs =>
            ((((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) +
              (((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4)
          (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) :=
  chapter10_indexed_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
    (G := H) (V := Glin * V * Glinᵀ) hPstar hH
    (chapter10_indexed_finiteReplicationCovarianceCenteredMat_smooth_fourthMoment_gaussianLimit
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
      hV hPstar hT hcoordMem hlinearization
      hBcoord hFourthCoordLinear hFourthCoordLinearInt
      hBsum hFourthSumLinear hFourthSumLinearInt hfinite)

/-- Indexed `L²` simulation-error version of
`chapter10_indexed_smoothVariance_finiteReplication_smoothCov_fourthMoment_gaussianLimit`. -/
theorem
    chapter10_indexed_smoothVariance_finiteReplication_smoothCov_fourthMoment_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {Bcoord : r → ℝ} {Bsum : r → r → ℝ} {Cfinite : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
    (hBcoord : ∀ a, 0 ≤ Bcoord a)
    (hFourthCoordLinear :
      ∀ a,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              (((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) a) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bcoord a))
    (hFourthCoordLinearInt :
      ∀ n ω a,
        Integrable
          (fun ωs =>
            (((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) ^ 4)
          (Pstar n ω))
    (hBsum : ∀ a c, 0 ≤ Bsum a c)
    (hFourthSumLinear :
      ∀ a c,
        TendstoInMeasure μ
          (fun n ω =>
            ∫ ωs,
              ((((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) a) +
                (((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
                  EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4 ∂Pstar n ω)
          atTop (fun _ => Bsum a c))
    (hFourthSumLinearInt :
      ∀ n ω a c,
        Integrable
          (fun ωs =>
            ((((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
              EuclideanSpace ℝ r) : r → ℝ) a) +
              (((matrixContinuousLinearMap Glin (Tstar n ω ωs) :
                EuclideanSpace ℝ r) : r → ℝ) c)) ^ 4)
          (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) :=
  chapter10_indexed_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
    (G := H) (V := Glin * V * Glinᵀ) hPstar hH
    (chapter10_indexed_finiteReplicationCovarianceCenteredMat_smooth_fourthMoment_gaussianLimit_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
      hV hPstar hT hcoordMem hlinearization
      hBcoord hFourthCoordLinear hFourthCoordLinearInt
      hBsum hFourthSumLinear hFourthSumLinearInt hfiniteInt hfiniteBound)

/-- Smooth plug-in covariance estimator from the compact-range quadratic
finite-replication covariance route, with Gaussian-limit coordinate `MemLp 2`
premises discharged automatically. -/
theorem
    chapter10_smoothVariance_finiteReplication_smoothCov_compactRangeQuadratic
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) := by
  classical
  exact
    chapter10_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
      (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
      (G := H) (V := Glin * V * Glinᵀ) hPstar hH
      (chapter10_finiteReplicationCovarianceCenteredMat_tendsto_smooth_compactRange_quadratic
        (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
        (Tstar := Tstar) (thetaStar := thetaStar) (ρ := ρ) (V := V)
        Glin hV hPstar hT hK hTstar hthetaStar hcoordMem
        (fun a => memLp_multivariateGaussian_coord_two (S := Glin * V * Glinᵀ) a)
        hlinearized_mem hthetaStar_mem hρsq hTNormFourth hTNormFourthInt
        hR_bound hBθ hThetaNormFourth hThetaNormFourthInt hfinite)

/-- `L²` simulation-error version of
`chapter10_smoothVariance_finiteReplication_smoothCov_compactRangeQuadratic`. -/
theorem
    chapter10_smoothVariance_finiteReplication_smoothCov_compactRangeQuad_l2
    [IsFiniteMeasure μ]
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) := by
  classical
  exact
    chapter10_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
      (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
      (G := H) (V := Glin * V * Glinᵀ) hPstar hH
      (chapter10_finiteReplicationCovarianceCenteredMat_tendsto_smooth_compactRangeQuad_l2
        (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
        (Tstar := Tstar) (thetaStar := thetaStar) (ρ := ρ) (V := V)
        Glin hV hPstar hT hK hTstar hthetaStar hcoordMem
        (fun a => memLp_multivariateGaussian_coord_two (S := Glin * V * Glinᵀ) a)
        hlinearized_mem hthetaStar_mem hρsq hTNormFourth hTNormFourthInt
        hR_bound hBθ hThetaNormFourth hThetaNormFourthInt
        hfiniteInt hfiniteBound)

/-- Indexed smooth plug-in covariance estimator from the compact-range
quadratic finite-replication covariance route, with Gaussian-limit coordinate
`MemLp 2` premises discharged automatically. -/
theorem
    chapter10_indexed_smoothVariance_finiteReplication_smoothCov_compactRangeQuadratic
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) := by
  classical
  have hcov :=
    chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_smooth_compactRange_quadratic
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (ρ := ρ) (V := V)
      Glin hV hPstar hT hK hTstar hthetaStar hcoordMem
      (fun a => memLp_multivariateGaussian_coord_two (S := Glin * V * Glinᵀ) a)
      hlinearized_mem hthetaStar_mem hρsq hTNormFourth hTNormFourthInt
      hR_bound hBθ hThetaNormFourth hThetaNormFourthInt hfinite
  exact
    chapter10_indexed_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
      (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
      (G := H) (V := Glin * V * Glinᵀ) hPstar hH hcov

/-- Indexed `L²` simulation-error version of the compact-range quadratic
finite-replication smooth plug-in covariance route. -/
theorem
    chapter10_indexed_smoothVariance_finiteReplication_smoothCov_compactRangeQuad_l2
    [IsFiniteMeasure μ]
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {ρ : ℕ → ℝ}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {K : Set (EuclideanSpace ℝ r)}
    {Bθ BT : ℝ} {Cfinite : r → r → ℝ}
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) := by
  classical
  exact
    chapter10_indexed_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
      (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
      (G := H) (V := Glin * V * Glinᵀ) hPstar hH
      (chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_smooth_compactRangeQuad_l2
        (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
        (Tstar := Tstar) (thetaStar := thetaStar) (ρ := ρ) (V := V)
        Glin hV hPstar hT hK hTstar hthetaStar hcoordMem
        (fun a => memLp_multivariateGaussian_coord_two (S := Glin * V * Glinᵀ) a)
        hlinearized_mem hthetaStar_mem hρsq hTNormFourth hTNormFourthInt
        hR_bound hBθ hThetaNormFourth hThetaNormFourthInt
        hfiniteInt hfiniteBound)

/-- Smooth plug-in covariance estimator from the bounded smooth
finite-replication covariance route, with Gaussian-limit coordinate `MemLp 2`
premises discharged automatically. -/
theorem
    chapter10_smoothVariance_finiteReplication_smoothCov_eventualBound
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {Ccoord : r → ℝ} {Csum : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a +
          (thetaStar n ω ωs : r → ℝ) c)| ≤ Csum a c)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) := by
  classical
  exact
    chapter10_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
      (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
      (G := H) (V := Glin * V * Glinᵀ) hPstar hH
      (chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_eventualBound
        (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
        (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
        hV hPstar hT hcoordMem
        (fun a => memLp_multivariateGaussian_coord_two (S := Glin * V * Glinᵀ) a)
        hlinearization hboundCoord hboundSum hfinite)

/-- `L²` simulation-error version of
`chapter10_smoothVariance_finiteReplication_smoothCov_eventualBound`. -/
theorem
    chapter10_smoothVariance_finiteReplication_smoothCov_eventualBound_l2
    [IsFiniteMeasure μ]
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {Ccoord : r → ℝ} {Csum : r → r → ℝ} {Cfinite : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a +
          (thetaStar n ω ωs : r → ℝ) c)| ≤ Csum a c)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) := by
  classical
  exact
    chapter10_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
      (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
      (G := H) (V := Glin * V * Glinᵀ) hPstar hH
      (chapter10_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_eventualBound_l2
        (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
        (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
        hV hPstar hT hcoordMem
        (fun a => memLp_multivariateGaussian_coord_two (S := Glin * V * Glinᵀ) a)
        hlinearization hboundCoord hboundSum hfiniteInt hfiniteBound)

/-- Indexed smooth plug-in covariance estimator from the bounded smooth
finite-replication covariance route, with Gaussian-limit coordinate `MemLp 2`
premises discharged automatically. -/
theorem
    chapter10_indexed_smoothVariance_finiteReplication_smoothCov_eventualBound
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {Ccoord : r → ℝ} {Csum : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a +
          (thetaStar n ω ωs : r → ℝ) c)| ≤ Csum a c)
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            bootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
        atTop (fun _ => 0)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) := by
  classical
  exact
    chapter10_indexed_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
      (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
      (G := H) (V := Glin * V * Glinᵀ) hPstar hH
      (chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_eventualBound
        (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
        (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
        hV hPstar hT hcoordMem
        (fun a => memLp_multivariateGaussian_coord_two (S := Glin * V * Glinᵀ) a)
        hlinearization hboundCoord hboundSum hfinite)

/-- Indexed `L²` simulation-error version of
`chapter10_indexed_smoothVariance_finiteReplication_smoothCov_eventualBound`. -/
theorem
    chapter10_indexed_smoothVariance_finiteReplication_smoothCov_eventualBound_l2
    [IsFiniteMeasure μ]
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {Ccoord : r → ℝ} {Csum : r → r → ℝ} {Cfinite : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
    (hboundCoord :
      ∀ a, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a)| ≤ Ccoord a)
    (hboundSum :
      ∀ a c, ∀ᶠ n in atTop, ∀ ω ωs,
        |((thetaStar n ω ωs : r → ℝ) a +
          (thetaStar n ω ωs : r → ℝ) c)| ≤ Csum a c)
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              bootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                bootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) := by
  classical
  exact
    chapter10_indexed_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
      (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
      (G := H) (V := Glin * V * Glinᵀ) hPstar hH
      (chapter10_indexed_finiteReplicationCovarianceCenteredMat_tendsto_of_smooth_eventualBound_l2
        (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
        (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
        hV hPstar hT hcoordMem
        (fun a => memLp_multivariateGaussian_coord_two (S := Glin * V * Glinᵀ) a)
        hlinearization hboundCoord hboundSum hfiniteInt hfiniteBound)

/-- Smooth plug-in covariance estimator from the smooth trimmed
finite-replication covariance route, with Gaussian-limit coordinate `MemLp 2`
premises discharged automatically. -/
theorem
    chapter10_smoothVariance_finiteReplication_smoothTrimmed_gaussianLimit
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {τ : ℕ → ℝ}
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {B : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMat Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
        atTop (fun _ => 0)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) :=
  chapter10_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
    (G := H) (V := Glin * V * Glinᵀ) hPstar hH
    (chapter10_finiteReplicationTrimmedCovariance_smooth_normFourth_gaussianLimit
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
      hV hPstar hτ hT hZmeas hcoordMem hlinearization hTailProb
      hB hNormFourth hNormFourthInt hfinite)

/-- `L²` simulation-error version of
`chapter10_smoothVariance_finiteReplication_smoothTrimmed_gaussianLimit`. -/
theorem
    chapter10_smoothVariance_finiteReplication_smoothTrimmed_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {τ : ℕ → ℝ}
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {B : ℝ} {Cfinite : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) :=
  chapter10_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
    (G := H) (V := Glin * V * Glinᵀ) hPstar hH
    (chapter10_finiteReplicationTrimmedCovariance_smooth_normFourth_gaussianLimit_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
      hV hPstar hτ hT hZmeas hcoordMem hlinearization hTailProb
      hB hNormFourth hNormFourthInt hfiniteInt hfiniteBound)

/-- Smooth plug-in covariance estimator from the smooth trimmed
finite-replication covariance route, with trimming-tail negligibility and
Gaussian-limit coordinate `MemLp 2` premises discharged. -/
theorem
    chapter10_smoothVariance_finiteReplication_smoothTrimmed_secondMoment_l2
    [IsFiniteMeasure μ]
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ℕ → Ω → Measure Ωs}
    {Tstar : ℕ → Ω → Ωs → EuclideanSpace ℝ d}
    {thetaStar : ℕ → Ω → Ωs → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {τ : ℕ → ℝ}
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {Bsecond Bfourth : ℝ} {Cfinite : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMat Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMat Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInBootstrapProbability μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) :=
  chapter10_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
    (G := H) (V := Glin * V * Glinᵀ) hPstar hH
    (chapter10_finiteReplicationTrimmedCovariance_smooth_secondMoment_gaussianLimit_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
      hV hPstar hτpos hτinv hT hZmeas hThetaMem hcoordMem
      hlinearization hSecond hBfourth hNormFourth hNormFourthInt
      hfiniteInt hfiniteBound)

/-- Indexed smooth plug-in covariance estimator from the smooth trimmed
finite-replication covariance route, with Gaussian-limit coordinate `MemLp 2`
premises discharged automatically. -/
theorem
    chapter10_indexed_smoothVariance_finiteReplication_smoothTrimmed_gaussianLimit
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {τ : ℕ → ℝ}
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {B : ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
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
        (Pstar n ω))
    (hfinite :
      TendstoInMeasure μ
        (fun n ω =>
          finiteReplicationCovarianceCenteredMat Zsim n ω -
            trimmedBootstrapCovarianceMatIndexed Pstar
              (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
        atTop (fun _ => 0)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) :=
  chapter10_indexed_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
    (G := H) (V := Glin * V * Glinᵀ) hPstar hH
    (chapter10_indexed_finiteReplicationTrimmedCovariance_smooth_normFourth_gaussianLimit
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
      hV hPstar hτ hT hZmeas hcoordMem hlinearization hTailProb
      hB hNormFourth hNormFourthInt hfinite)

/-- Indexed `L²` simulation-error version of
`chapter10_indexed_smoothVariance_finiteReplication_smoothTrimmed_gaussianLimit`. -/
theorem
    chapter10_indexed_smoothVariance_finiteReplication_smoothTrimmed_gaussianLimit_l2
    [IsFiniteMeasure μ]
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {τ : ℕ → ℝ}
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {B : ℝ} {Cfinite : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτ : ∀ n, 0 ≤ τ n)
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) :=
  chapter10_indexed_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
    (G := H) (V := Glin * V * Glinᵀ) hPstar hH
    (chapter10_indexed_finiteReplicationTrimmedCovariance_smooth_normFourth_gaussianLimit_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
      hV hPstar hτ hT hZmeas hcoordMem hlinearization hTailProb
      hB hNormFourth hNormFourthInt hfiniteInt hfiniteBound)

/-- Indexed smooth plug-in covariance estimator from the smooth trimmed
finite-replication covariance route, with trimming-tail negligibility and
Gaussian-limit coordinate `MemLp 2` premises discharged. -/
theorem
    chapter10_indexed_smoothVariance_finiteReplication_smoothTrimmed_secondMoment_l2
    [IsFiniteMeasure μ]
    {d r q : Type*} [Fintype d] [Fintype r] [Fintype q]
    [DecidableEq d] [DecidableEq r]
    {Ωboot : ℕ → Type*} [∀ n, MeasurableSpace (Ωboot n)]
    {Zsim : ℕ → ℕ → Ω → r → ℝ}
    {Pstar : ∀ n, Ω → Measure (Ωboot n)}
    {Tstar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ d}
    {thetaStar : ∀ n, Ω → Ωboot n → EuclideanSpace ℝ r}
    {V : Matrix d d ℝ} (Glin : Matrix r d ℝ)
    [IsFiniteMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ r) (Glin * V * Glinᵀ))]
    {τ : ℕ → ℝ}
    {Hseq : ℕ → Ω → Matrix r q ℝ} {H : Matrix r q ℝ}
    {Bsecond Bfourth : ℝ} {Cfinite : r → r → ℝ}
    (hV : V.PosSemidef)
    (hPstar : ∀ n ω, IsProbabilityMeasure (Pstar n ω))
    (hτpos : ∀ n, 0 < τ n)
    (hτinv : Tendsto (fun n => ((τ n) ^ 2)⁻¹) atTop (𝓝 0))
    (hH : TendstoInMeasure μ Hseq atTop (fun _ => H))
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
        matrixContinuousLinearMap Glin (Tstar n ω ωs))
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
        (Pstar n ω))
    (hfiniteInt :
      ∀ a c n, Integrable
        (fun ω =>
          ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
              trimmedBootstrapCovarianceMatIndexed Pstar
                (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
              a c‖ ^ (2 : ℝ)) μ)
    (hfiniteBound :
      ∀ a c,
        ∀ᶠ n in atTop,
          (∫ ω,
            ‖(finiteReplicationCovarianceCenteredMat Zsim n ω -
                trimmedBootstrapCovarianceMatIndexed Pstar
                  (fun n ω ωs => (thetaStar n ω ωs : r → ℝ)) τ n ω)
                a c‖ ^ (2 : ℝ) ∂μ) ≤
            Cfinite a c / (n : ℝ)) :
    TendstoInBootstrapProbabilityIndexed μ Pstar
      (fun n ω _ =>
        smoothFunctionVarianceFunctional (Hseq n ω)
          (finiteReplicationCovarianceCenteredMat Zsim n ω))
      (fun _ => smoothFunctionVarianceFunctional H (Glin * V * Glinᵀ)) :=
  chapter10_indexed_bootstrap_smooth_variance_of_finiteReplicationCovarianceCenteredMat
    (μ := μ) (Pstar := Pstar) (Zsim := Zsim) (Gseq := Hseq)
    (G := H) (V := Glin * V * Glinᵀ) hPstar hH
    (chapter10_indexed_finiteReplicationTrimmedCovariance_smooth_secondMoment_gaussianLimit_l2
      (μ := μ) (Zsim := Zsim) (Pstar := Pstar)
      (Tstar := Tstar) (thetaStar := thetaStar) (V := V) Glin
      hV hPstar hτpos hτinv hT hZmeas hThetaMem hcoordMem
      hlinearization hSecond hBfourth hNormFourth hNormFourthInt
      hfiniteInt hfiniteBound)

end SmoothFunctionFiniteReplicationCovariance

end HansenEconometrics
