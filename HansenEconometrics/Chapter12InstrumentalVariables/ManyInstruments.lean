import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.Chapter11MultivariateRegression.ReducedRank
import HansenEconometrics.Chapter7Asymptotics.Consistency
import HansenEconometrics.Chapter12InstrumentalVariables.Asymptotics
import HansenEconometrics.Chapter12InstrumentalVariables.LIML
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Conditional

/-!
# Chapter 12 — many instruments

This file contains the theorem surface for Hansen Theorem 12.19.  The
instrument index type is allowed to depend on the sample size, so the statement
can express the Bekker-style sequence `ℓ_n / n -> α` rather than fixing the
instrument dimension.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Function Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

open Matrix

variable {k : Type*} [Fintype k] [DecidableEq k]
variable {ι : ℕ → Type*} [∀ m, Fintype (ι m)] [∀ m, DecidableEq (ι m)]

/-- Signal component `Z Γ` in Hansen's many-instrument reduced form
`X = Γ'Z + u₂`, written in row-matrix convention. -/
noncomputable def manyInstrumentSignal
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ) : Matrix n k ℝ :=
  Z * Gamma

/-- Sample signal Gram matrix `n^{-1} Γ'Z'ZΓ` from Hansen (12.77). -/
noncomputable def manyInstrumentSignalGram
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ) : Matrix k k ℝ :=
  sampleGram (manyInstrumentSignal Z Gamma)

/-- OLS reduced-form Gram cross term
`n^{-1}((ZΓ)'u₂ + u₂'(ZΓ))` from Hansen's many-instrument decomposition. -/
noncomputable def manyInstrumentReducedFormCrossGram
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ) (u2 : Matrix n k ℝ) :
    Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ((manyInstrumentSignal Z Gamma)ᵀ * u2 +
      u2ᵀ * manyInstrumentSignal Z Gamma)

omit [Fintype k] [DecidableEq k] in
/-- The signal Gram `n⁻¹Γ'Z'ZΓ` is the primitive instrument Gram
`Q̂_ZZ` pre- and post-multiplied by `Γ`. -/
theorem manyInstrumentSignalGram_eq_Gamma_transpose_sampleQZZ_mul_Gamma
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ) :
    manyInstrumentSignalGram Z Gamma =
      Gammaᵀ * sampleQZZ Z * Gamma := by
  rw [manyInstrumentSignalGram, manyInstrumentSignal, sampleQZZ]
  unfold sampleGram
  rw [Matrix.transpose_mul]
  simp [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul]

omit [Fintype k] [DecidableEq k] in
/-- The signal/reduced-form-error cross Gram is the symmetrized primitive
instrument-error cross moment `Q̂_Zu₂`, transformed by `Γ`. -/
theorem manyInstrumentReducedFormCrossGram_eq_Gamma_transpose_sampleQZX
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ) (u2 : Matrix n k ℝ) :
    manyInstrumentReducedFormCrossGram Z Gamma u2 =
      Gammaᵀ * sampleQZX Z u2 + (Gammaᵀ * sampleQZX Z u2)ᵀ := by
  simp [manyInstrumentReducedFormCrossGram, manyInstrumentSignal, sampleQZX,
    Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_smul, smul_add]

omit [Fintype k] [DecidableEq k] in
/-- The signal score `n⁻¹Γ'Z'e` is `Γ'` times the primitive instrument score. -/
theorem sampleCrossMoment_manyInstrumentSignal_eq_Gamma_transpose_sampleCrossMoment
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ) (e : n → ℝ) :
    sampleCrossMoment (manyInstrumentSignal Z Gamma) e =
      Gammaᵀ *ᵥ sampleCrossMoment Z e := by
  simp [manyInstrumentSignal, sampleCrossMoment, Matrix.transpose_mul,
    Matrix.mulVec_mulVec, Matrix.mulVec_smul]

omit [Fintype k] [DecidableEq k] in
/-- Projected signal Gram matrix for the 2SLS face of Hansen's many-instrument
decomposition.  This is the exact Star-projection version of the signal bread
component. -/
noncomputable def manyInstrumentProjectedSignalGram
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ) : Matrix k k ℝ :=
  sampleGram (instrumentProjectionStar Z * manyInstrumentSignal Z Gamma)

omit [Fintype k] [DecidableEq k] in
/-- Projected signal/error cross-Gram term for the 2SLS bread decomposition. -/
noncomputable def manyInstrumentProjectedReducedFormCrossGram
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ) (u2 : Matrix n k ℝ) :
    Matrix k k ℝ :=
  (Fintype.card n : ℝ)⁻¹ •
    ((instrumentProjectionStar Z * manyInstrumentSignal Z Gamma)ᵀ *
        (instrumentProjectionStar Z * u2) +
      (instrumentProjectionStar Z * u2)ᵀ *
        (instrumentProjectionStar Z * manyInstrumentSignal Z Gamma))

omit [Fintype k] [DecidableEq k] in
/-- Projected signal score component for the 2SLS score decomposition. -/
noncomputable def manyInstrumentProjectedSignalScore
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ) (e : n → ℝ) : k → ℝ :=
  sampleCrossMoment (instrumentProjectionStar Z * manyInstrumentSignal Z Gamma) e

omit [Fintype k] [DecidableEq k] in
/-- Projected reduced-form error Gram matrix `n^{-1} u₂' P_Z u₂`.
Under Hansen's many-instrument homoskedasticity and fourth-moment assumptions
this is the matrix whose probability limit is `α Σ₂₂`. -/
noncomputable def manyInstrumentProjectedErrorGram
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (u2 : Matrix n k ℝ) : Matrix k k ℝ :=
  sampleGram (instrumentProjectionStar Z * u2)

omit [Fintype k] [DecidableEq k] in
/-- Projected reduced-form error cross moment `n^{-1} u₂' P_Z e`.
Under Hansen's many-instrument homoskedasticity and fourth-moment assumptions
this has probability limit `α Σ₂e`. -/
noncomputable def manyInstrumentProjectedErrorCross
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (u2 : Matrix n k ℝ) (e : n → ℝ) : k → ℝ :=
  sampleCrossMoment (instrumentProjectionStar Z * u2) e

omit [Fintype k] [DecidableEq k] in
/-- Projection trace ratio `n^{-1}tr(P_Z*)` used in Hansen's many-instrument
homoskedastic projection moment calculations.  On nonsingular instrument Gram
matrices this is the instrument-count ratio `ℓ_n/n`. -/
noncomputable def manyInstrumentProjectionTraceRatio
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq l]
    (Z : Matrix n l ℝ) : ℝ :=
  (Fintype.card n : ℝ)⁻¹ * Matrix.trace (instrumentProjectionStar Z)

omit [Fintype k] [DecidableEq k] in
/-- On the ordinary nonsingular projection branch, `n^{-1}tr(P_Z)` equals the
instrument-count ratio.  This reuses the Chapter 3 hat-matrix trace theorem
rather than reproving the projection-rank argument locally. -/
theorem manyInstrumentProjectionTraceRatio_eq_card_ratio_of_nonsingular
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq l]
    (Z : Matrix n l ℝ) [Invertible (Zᵀ * Z)] :
    manyInstrumentProjectionTraceRatio Z =
      (Fintype.card l : ℝ) / (Fintype.card n : ℝ) := by
  simp [manyInstrumentProjectionTraceRatio, instrumentProjectionStar_eq_projection,
    instrumentProjection, hatMatrix_trace, div_eq_mul_inv, mul_comm]

/-- If every realized instrument Gram is nonsingular and Hansen's instrument
count ratio `ℓ_n / n` converges to `α`, then the projection trace ratio
`n^{-1} tr(P_Z*)` converges to `α` in probability.

This is the deterministic trace step in the many-instrument projection
calculation; the remaining work in Hansen's theorem is the homoskedastic
moment/remainder argument, not the trace identity itself. -/
theorem manyInstrumentProjectionTraceRatio_tendstoInMeasure_of_card_ratio_nonsingular
    {ι : ℕ → Type*} [∀ m, Fintype (ι m)] [∀ m, DecidableEq (ι m)]
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {alpha : ℝ}
    (hcard : Tendsto
      (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ)) atTop (𝓝 alpha))
    (hnonsing : ∀ (m : ℕ) (ω : Ω),
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω))) :
    TendstoInMeasure μ
      (fun m ω => manyInstrumentProjectionTraceRatio (Z m ω))
      atTop (fun _ => alpha) := by
  have hconst : TendstoInMeasure μ
      (fun m (_ : Ω) => (Fintype.card (ι m) : ℝ) / (m : ℝ))
      atTop (fun _ => alpha) :=
    tendstoInMeasure_const_real (μ := μ) hcard
  refine TendstoInMeasure.congr (fun m => ?_) EventuallyEq.rfl hconst
  exact ae_of_all μ fun ω => by
    rcases hnonsing m ω with ⟨inst⟩
    letI : Invertible ((Z m ω)ᵀ * Z m ω) := inst
    simpa using
      (manyInstrumentProjectionTraceRatio_eq_card_ratio_of_nonsingular
        (Z m ω)
      ).symm

/-- Eventual-a.e. version of
`manyInstrumentProjectionTraceRatio_tendstoInMeasure_of_card_ratio_nonsingular`.

This is the form used by the many-instrument theorem: the projection trace
ratio is identified with `ℓ_n / n` on the high-probability nonsingular branch,
not necessarily for every sample size and realization. -/
theorem manyInstrumentProjectionTraceRatio_tendstoInMeasure_of_eventually_ae_card_ratio_nonsingular
    {ι : ℕ → Type*} [∀ m, Fintype (ι m)] [∀ m, DecidableEq (ι m)]
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {alpha : ℝ}
    (hcard : Tendsto
      (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ)) atTop (𝓝 alpha))
    (hnonsing : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω))) :
    TendstoInMeasure μ
      (fun m ω => manyInstrumentProjectionTraceRatio (Z m ω))
      atTop (fun _ => alpha) := by
  have hconst : TendstoInMeasure μ
      (fun m (_ : Ω) => (Fintype.card (ι m) : ℝ) / (m : ℝ))
      atTop (fun _ => alpha) :=
    tendstoInMeasure_const_real (μ := μ) hcard
  refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hconst
  filter_upwards [hnonsing] with m hm
  filter_upwards [hm] with ω hω
  rcases hω with ⟨inst⟩
  letI : Invertible ((Z m ω)ᵀ * Z m ω) := inst
  simpa using
    (manyInstrumentProjectionTraceRatio_eq_card_ratio_of_nonsingular
      (Z m ω)
    ).symm

omit [Fintype k] [DecidableEq k] in
/-- On an a.e. nonsingular instrument branch, the projection trace ratio is
a.e. equal to the deterministic instrument-count ratio, hence measurable.

This is the measurability companion to
`manyInstrumentProjectionTraceRatio_tendstoInMeasure_of_eventually_ae_card_ratio_nonsingular`;
it lets theorem-facing constructors derive the trace-ratio measurability field
instead of carrying it as a separate homoskedastic projection-remainder input. -/
theorem manyInstrumentProjectionTraceRatio_aestronglyMeasurable_of_ae_nonsingular
    {Ω : Type*} [MeasurableSpace Ω]
    {m : ℕ} {Z : Ω → Matrix (Fin m) (ι m) ℝ} {μ : Measure Ω}
    (hnonsing : ∀ᵐ ω ∂μ, Nonempty (Invertible ((Z ω)ᵀ * Z ω))) :
    AEStronglyMeasurable (fun ω => manyInstrumentProjectionTraceRatio (Z ω)) μ := by
  have hconst : AEStronglyMeasurable
      (fun _ : Ω => (Fintype.card (ι m) : ℝ) / (Fintype.card (Fin m) : ℝ)) μ :=
    aestronglyMeasurable_const
  refine hconst.congr ?_
  filter_upwards [hnonsing] with ω hω
  rcases hω with ⟨inst⟩
  letI : Invertible ((Z ω)ᵀ * Z ω) := inst
  exact (manyInstrumentProjectionTraceRatio_eq_card_ratio_of_nonsingular (Z ω)).symm

omit [Fintype k] [DecidableEq k] in
private theorem instrumentProjectionStar_transpose
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq l]
    (Z : Matrix n l ℝ) :
    (instrumentProjectionStar Z)ᵀ = instrumentProjectionStar Z := by
  simp [instrumentProjectionStar, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    Matrix.mul_assoc]

omit [Fintype k] [DecidableEq k] in
private theorem instrumentProjectionStar_idempotent
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq l]
    (Z : Matrix n l ℝ) :
    instrumentProjectionStar Z * instrumentProjectionStar Z =
      instrumentProjectionStar Z := by
  by_cases hunit : IsUnit (Zᵀ * Z).det
  · letI : Invertible (Zᵀ * Z) := Matrix.invertibleOfIsUnitDet (A := Zᵀ * Z) hunit
    exact instrumentProjectionStar_idempotent_of_nonsingular Z
  · rw [instrumentProjectionStar, Matrix.nonsing_inv_apply_not_isUnit _ hunit]
    simp

omit [Fintype k] [DecidableEq k] in
/-- On the nonsingular instrument branch, projecting the first-stage signal
`ZΓ` leaves its sample Gram unchanged. -/
theorem manyInstrumentProjectedSignalGram_eq_signalGram_of_nonsingular
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ) [Invertible (Zᵀ * Z)] :
    manyInstrumentProjectedSignalGram Z Gamma =
      manyInstrumentSignalGram Z Gamma := by
  rw [manyInstrumentProjectedSignalGram, manyInstrumentSignalGram]
  congr 1
  rw [manyInstrumentSignal, ← Matrix.mul_assoc,
    instrumentProjectionStar_mul_Z_of_nonsingular]

omit [Fintype k] [DecidableEq k] in
/-- On the nonsingular instrument branch, projecting the first-stage signal
`ZΓ` leaves its score against any outcome/error vector unchanged. -/
theorem manyInstrumentProjectedSignalScore_eq_signalScore_of_nonsingular
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ) (e : n → ℝ)
    [Invertible (Zᵀ * Z)] :
    manyInstrumentProjectedSignalScore Z Gamma e =
      sampleCrossMoment (manyInstrumentSignal Z Gamma) e := by
  rw [manyInstrumentProjectedSignalScore]
  congr 1
  rw [manyInstrumentSignal, ← Matrix.mul_assoc,
    instrumentProjectionStar_mul_Z_of_nonsingular]

omit [Fintype k] [DecidableEq k] in
/-- On the nonsingular instrument branch, the projected signal/error cross-Gram
equals the unprojected reduced-form cross-Gram because `P_Z ZΓ = ZΓ`. -/
theorem manyInstrumentProjectedReducedFormCrossGram_eq_crossGram_of_nonsingular
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ) (u2 : Matrix n k ℝ)
    [Invertible (Zᵀ * Z)] :
    manyInstrumentProjectedReducedFormCrossGram Z Gamma u2 =
      manyInstrumentReducedFormCrossGram Z Gamma u2 := by
  let P : Matrix n n ℝ := instrumentProjectionStar Z
  let S : Matrix n k ℝ := manyInstrumentSignal Z Gamma
  have hPS : P * S = S := by
    dsimp [P, S, manyInstrumentSignal]
    rw [← Matrix.mul_assoc, instrumentProjectionStar_mul_Z_of_nonsingular]
  have hPT : Pᵀ = P := by
    simpa [P] using instrumentProjectionStar_transpose_of_nonsingular (Z := Z)
  have hSP : Sᵀ * P = Sᵀ := by
    have h := congrArg Matrix.transpose hPS
    simpa [Matrix.transpose_mul, hPT] using h
  have hleft : (P * S)ᵀ * (P * u2) = Sᵀ * u2 := by
    calc
      (P * S)ᵀ * (P * u2) = Sᵀ * (P * u2) := by rw [hPS]
      _ = (Sᵀ * P) * u2 := by rw [Matrix.mul_assoc]
      _ = Sᵀ * u2 := by rw [hSP]
  have hright : (P * u2)ᵀ * (P * S) = u2ᵀ * S := by
    calc
      (P * u2)ᵀ * (P * S) = (P * u2)ᵀ * S := by rw [hPS]
      _ = (u2ᵀ * Pᵀ) * S := by rw [Matrix.transpose_mul]
      _ = u2ᵀ * (P * S) := by rw [hPT, Matrix.mul_assoc]
      _ = u2ᵀ * S := by rw [hPS]
  change
    (Fintype.card n : ℝ)⁻¹ • ((P * S)ᵀ * (P * u2) + (P * u2)ᵀ * (P * S)) =
      (Fintype.card n : ℝ)⁻¹ • (Sᵀ * u2 + u2ᵀ * S)
  rw [hleft, hright]

omit [Fintype k] [DecidableEq k] in
private theorem limlNormalizedMomentMatrixStar_zero_eq_sampleGram_projected
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) :
    limlNormalizedMomentMatrixStar Z X 0 =
      sampleGram (instrumentProjectionStar Z * X) := by
  let P : Matrix n n ℝ := instrumentProjectionStar Z
  simp only [limlNormalizedMomentMatrixStar, limlMomentMatrixStar, sampleGram]
  rw [limlWeightMatrixStar_zero]
  change (Fintype.card n : ℝ)⁻¹ • (Xᵀ * P * X) =
    (Fintype.card n : ℝ)⁻¹ • ((P * X)ᵀ * (P * X))
  rw [Matrix.transpose_mul]
  change (Fintype.card n : ℝ)⁻¹ • (Xᵀ * P * X) =
    (Fintype.card n : ℝ)⁻¹ • (Xᵀ * Pᵀ * (P * X))
  rw [show Pᵀ = P by simpa [P] using instrumentProjectionStar_transpose Z]
  congr 1
  rw [Matrix.mul_assoc (Xᵀ) P X]
  rw [Matrix.mul_assoc (Xᵀ) P (P * X)]
  rw [← Matrix.mul_assoc P P X,
    show P * P = P by simpa [P] using instrumentProjectionStar_idempotent Z]

omit [Fintype k] [DecidableEq k] in
private theorem limlNormalizedMomentVectorStar_zero_eq_sampleCrossMoment_projected
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (e : n → ℝ) :
    limlNormalizedMomentVectorStar Z X e 0 =
      sampleCrossMoment (instrumentProjectionStar Z * X) e := by
  simp [limlNormalizedMomentVectorStar, limlMomentVectorStar, sampleCrossMoment,
    Matrix.transpose_mul, instrumentProjectionStar_transpose]

omit [Fintype k] [DecidableEq k] in
private theorem limlNormalizedMomentMatrixStar_eq_zero_sub_mu_residual
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (muHat : ℝ) :
    limlNormalizedMomentMatrixStar Z X muHat =
      limlNormalizedMomentMatrixStar Z X 0 -
        muHat • (sampleGram X - limlNormalizedMomentMatrixStar Z X 0) := by
  ext a b
  simp [limlNormalizedMomentMatrixStar, limlMomentMatrixStar, limlWeightMatrixStar,
    sampleGram, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  ring

omit [Fintype k] [DecidableEq k] in
private theorem limlNormalizedMomentVectorStar_eq_zero_sub_mu_residual
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (e : n → ℝ) (muHat : ℝ) :
    limlNormalizedMomentVectorStar Z X e muHat =
      limlNormalizedMomentVectorStar Z X e 0 -
        muHat • (sampleCrossMoment X e - limlNormalizedMomentVectorStar Z X e 0) := by
  ext a
  simp [limlNormalizedMomentVectorStar, limlMomentVectorStar, limlWeightMatrixStar,
    sampleCrossMoment, Matrix.mul_sub, Matrix.sub_mulVec, Matrix.smul_mulVec]
  ring_nf

/-- OLS many-instrument probability-limit drift `(H + Σ₂₂)^{-1} Σ₂e`. -/
noncomputable def manyInstrumentsOLSBias
    (H Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) : k → ℝ :=
  (H + Sigma22)⁻¹ *ᵥ Sigma2e

/-- 2SLS many-instrument probability-limit drift
`(H + αΣ₂₂)^{-1} αΣ₂e`. -/
noncomputable def manyInstrumentsTwoSLSBias
    (H Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) (alpha : ℝ) : k → ℝ :=
  (H + alpha • Sigma22)⁻¹ *ᵥ (alpha • Sigma2e)

/-- OLS limit bread nonsingularity in Hansen Theorem 12.19 follows from a
positive-definite signal limit and positive-semidefinite reduced-form error
covariance. -/
theorem manyInstruments_ols_limit_matrix_nonsingular_of_posSemidef
    {H Sigma22 : Matrix k k ℝ}
    (hH : H.PosDef) (hSigma22 : Sigma22.PosSemidef) :
    IsUnit (H + Sigma22).det := by
  exact (Matrix.isUnit_iff_isUnit_det _).mp (hH.add_posSemidef hSigma22).isUnit

/-- 2SLS limit bread nonsingularity in Hansen Theorem 12.19 follows from a
positive-definite signal limit, positive-semidefinite reduced-form error
covariance, and nonnegative instrument-ratio limit. -/
theorem manyInstruments_twoSLS_limit_matrix_nonsingular_of_posSemidef
    {H Sigma22 : Matrix k k ℝ} {alpha : ℝ}
    (hH : H.PosDef) (hSigma22 : Sigma22.PosSemidef) (halpha : 0 ≤ alpha) :
    IsUnit (H + alpha • Sigma22).det := by
  have hscaled : (alpha • Sigma22).PosSemidef := hSigma22.smul halpha
  exact (Matrix.isUnit_iff_isUnit_det _).mp (hH.add_posSemidef hscaled).isUnit

omit [Fintype k] [DecidableEq k] in
/-- OLS sample Gram under Hansen's many-instrument reduced form
`X = ZΓ + u₂`.

This deterministic identity is the algebraic bridge used before proving the
many-instrument OLS bread limit from the signal, reduced-form error, and
cross-term moment limits. -/
theorem manyInstrumentReducedForm_sampleGram
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ) (u2 : Matrix n k ℝ) :
    sampleGram (manyInstrumentSignal Z Gamma + u2) =
      manyInstrumentSignalGram Z Gamma + sampleGram u2 +
        manyInstrumentReducedFormCrossGram Z Gamma u2 := by
  ext a b
  simp [manyInstrumentSignalGram, manyInstrumentReducedFormCrossGram,
    sampleGram, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, add_assoc]
  ring

omit [Fintype k] [DecidableEq k] in
/-- OLS sample score under Hansen's many-instrument reduced form
`X = ZΓ + u₂`. -/
theorem manyInstrumentReducedForm_sampleCrossMoment
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ)
    (u2 : Matrix n k ℝ) (e : n → ℝ) :
    sampleCrossMoment (manyInstrumentSignal Z Gamma + u2) e =
      sampleCrossMoment (manyInstrumentSignal Z Gamma) e +
        sampleCrossMoment u2 e := by
  ext a
  simp [sampleCrossMoment, Matrix.transpose_add, Matrix.add_mulVec]
  ring

omit [Fintype k] [DecidableEq k] in
/-- Normalized 2SLS bread under Hansen's many-instrument reduced form
`X = ZΓ + u₂`, decomposed into projected signal, projected reduced-form-error,
and projected cross-Gram terms. -/
theorem manyInstrumentProjectedReducedForm_normalizedMomentMatrix_zero
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ) (u2 : Matrix n k ℝ) :
    limlNormalizedMomentMatrixStar Z (manyInstrumentSignal Z Gamma + u2) 0 =
      manyInstrumentProjectedSignalGram Z Gamma +
        manyInstrumentProjectedErrorGram Z u2 +
          manyInstrumentProjectedReducedFormCrossGram Z Gamma u2 := by
  rw [limlNormalizedMomentMatrixStar_zero_eq_sampleGram_projected]
  ext a b
  simp [manyInstrumentProjectedSignalGram, manyInstrumentProjectedErrorGram,
    manyInstrumentProjectedReducedFormCrossGram, sampleGram, Matrix.mul_add,
    Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, add_assoc]
  ring

omit [Fintype k] [DecidableEq k] in
/-- Normalized 2SLS score under Hansen's many-instrument reduced form
`X = ZΓ + u₂`, decomposed into projected signal and reduced-form-error scores. -/
theorem manyInstrumentProjectedReducedForm_normalizedMomentVector_zero
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ)
    (u2 : Matrix n k ℝ) (e : n → ℝ) :
    limlNormalizedMomentVectorStar Z (manyInstrumentSignal Z Gamma + u2) e 0 =
      manyInstrumentProjectedSignalScore Z Gamma e +
        manyInstrumentProjectedErrorCross Z u2 e := by
  rw [limlNormalizedMomentVectorStar_zero_eq_sampleCrossMoment_projected]
  ext a
  simp [manyInstrumentProjectedSignalScore, manyInstrumentProjectedErrorCross,
    sampleCrossMoment, Matrix.mul_add, Matrix.transpose_add, Matrix.add_mulVec]
  ring

section Asymptotics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq k] in
@[reducible]
private noncomputable def manyInstrumentsMatrixBorelMeasurableSpaceInst :
    MeasurableSpace (Matrix k k ℝ) :=
  matrixBorelMeasurableSpace k k

attribute [local instance] manyInstrumentsMatrixBorelMeasurableSpaceInst

omit [DecidableEq k] in
private lemma manyInstrumentsMatrixBorelSpaceInst :
    BorelSpace (Matrix k k ℝ) :=
  matrixBorelSpace k k

attribute [local instance] manyInstrumentsMatrixBorelSpaceInst

omit [Fintype k] [DecidableEq k] [IsProbabilityMeasure μ] in
/-- On an a.e. nonsingular instrument branch, projected signal-Gram
measurability follows from the unprojected signal-Gram measurability and the
identity `P_Z ZΓ = ZΓ`. -/
theorem manyInstrumentProjectedSignalGram_aestronglyMeasurable_of_ae_nonsingular
    {m : ℕ} {Z : Ω → Matrix (Fin m) (ι m) ℝ}
    {Gamma : Matrix (ι m) k ℝ}
    (hnonsing : ∀ᵐ ω ∂μ, Nonempty (Invertible ((Z ω)ᵀ * Z ω)))
    (hsignal : AEStronglyMeasurable
      (fun ω => manyInstrumentSignalGram (Z ω) Gamma) μ) :
    AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z ω) Gamma) μ := by
  refine hsignal.congr ?_
  filter_upwards [hnonsing] with ω hω
  rcases hω with ⟨inst⟩
  letI : Invertible ((Z ω)ᵀ * Z ω) := inst
  exact
    (manyInstrumentProjectedSignalGram_eq_signalGram_of_nonsingular
      (Z ω) Gamma).symm

omit [Fintype k] [DecidableEq k] [IsProbabilityMeasure μ] in
/-- On an a.e. nonsingular instrument branch, projected signal/error cross-Gram
measurability follows from the unprojected cross-Gram measurability. -/
theorem
manyInstrumentProjectedReducedFormCrossGram_aestronglyMeasurable_of_ae_nonsingular
    {m : ℕ} {Z : Ω → Matrix (Fin m) (ι m) ℝ}
    {Gamma : Matrix (ι m) k ℝ} {u2 : Ω → Matrix (Fin m) k ℝ}
    (hnonsing : ∀ᵐ ω ∂μ, Nonempty (Invertible ((Z ω)ᵀ * Z ω)))
    (hcross : AEStronglyMeasurable
      (fun ω => manyInstrumentReducedFormCrossGram (Z ω) Gamma (u2 ω)) μ) :
    AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedReducedFormCrossGram (Z ω) Gamma (u2 ω)) μ := by
  refine hcross.congr ?_
  filter_upwards [hnonsing] with ω hω
  rcases hω with ⟨inst⟩
  letI : Invertible ((Z ω)ᵀ * Z ω) := inst
  exact
    (manyInstrumentProjectedReducedFormCrossGram_eq_crossGram_of_nonsingular
      (Z ω) Gamma (u2 ω)).symm

omit [Fintype k] [DecidableEq k] [IsProbabilityMeasure μ] in
/-- On an a.e. nonsingular instrument branch, projected signal-score
measurability follows from the unprojected signal-score measurability. -/
theorem manyInstrumentProjectedSignalScore_aestronglyMeasurable_of_ae_nonsingular
    {m : ℕ} {Z : Ω → Matrix (Fin m) (ι m) ℝ}
    {Gamma : Matrix (ι m) k ℝ} {e : Ω → Fin m → ℝ}
    (hnonsing : ∀ᵐ ω ∂μ, Nonempty (Invertible ((Z ω)ᵀ * Z ω)))
    (hscore : AEStronglyMeasurable
      (fun ω => sampleCrossMoment (manyInstrumentSignal (Z ω) Gamma) (e ω)) μ) :
    AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z ω) Gamma (e ω)) μ := by
  refine hscore.congr ?_
  filter_upwards [hnonsing] with ω hω
  rcases hω with ⟨inst⟩
  letI : Invertible ((Z ω)ᵀ * Z ω) := inst
  exact
    (manyInstrumentProjectedSignalScore_eq_signalScore_of_nonsingular
      (Z ω) Gamma (e ω)).symm

set_option linter.unusedFintypeInType false in
omit [Fintype k] [DecidableEq k] [IsProbabilityMeasure μ] in
private theorem manyInstrumentVector_aestronglyMeasurable_of_entries
    {r : Type*} [Fintype r] {v : Ω → r → ℝ}
    (hv : ∀ i, AEStronglyMeasurable (fun ω => v ω i) μ) :
    AEStronglyMeasurable v μ := by
  rw [aestronglyMeasurable_iff_aemeasurable]
  rw [aemeasurable_pi_iff]
  intro i
  exact (hv i).aemeasurable

omit [Fintype k] [DecidableEq k] [IsProbabilityMeasure μ] in
/-- Finite-sample measurability of the totalized instrument projection
`P_Z*` from measurability of the realized instrument matrix. -/
theorem manyInstrumentProjectionStar_aestronglyMeasurable
    {m : ℕ} {Zmat : Ω → Matrix (Fin m) (ι m) ℝ}
    (hZmat : AEStronglyMeasurable Zmat μ) :
    AEStronglyMeasurable
      (fun ω => instrumentProjectionStar (Zmat ω)) μ := by
  have hZt : AEStronglyMeasurable (fun ω => (Zmat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hZmat
  have hZZ : AEStronglyMeasurable (fun ω => (Zmat ω)ᵀ * Zmat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hZt.prodMk hZmat)
  have hZZinv : AEStronglyMeasurable
      (fun ω => ((Zmat ω)ᵀ * Zmat ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hZZ
  have hleft : AEStronglyMeasurable
      (fun ω => Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hZmat.prodMk hZZinv)
  have hproj : AEStronglyMeasurable
      (fun ω => Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹ * (Zmat ω)ᵀ) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hleft.prodMk hZt)
  simpa [instrumentProjectionStar, Matrix.mul_assoc] using hproj

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
omit [IsProbabilityMeasure μ] in
/-- Projected reduced-form error Gram measurability from finite-sample matrix
measurability of `Z` and `u₂`. -/
theorem manyInstrumentProjectedErrorGram_aestronglyMeasurable
    {m : ℕ} {Zmat : Ω → Matrix (Fin m) (ι m) ℝ}
    {Umat : Ω → Matrix (Fin m) k ℝ}
    (hZmat : AEStronglyMeasurable Zmat μ)
    (hUmat : AEStronglyMeasurable Umat μ) :
    AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorGram (Zmat ω) (Umat ω)) μ := by
  have hP : AEStronglyMeasurable
      (fun ω => instrumentProjectionStar (Zmat ω)) μ :=
    manyInstrumentProjectionStar_aestronglyMeasurable (μ := μ) hZmat
  have hPU : AEStronglyMeasurable
      (fun ω => instrumentProjectionStar (Zmat ω) * Umat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hP.prodMk hUmat)
  have hPUt : AEStronglyMeasurable
      (fun ω => (instrumentProjectionStar (Zmat ω) * Umat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hPU
  have hraw : AEStronglyMeasurable
      (fun ω =>
        (Fintype.card (Fin m) : ℝ)⁻¹ •
          ((instrumentProjectionStar (Zmat ω) * Umat ω)ᵀ *
            (instrumentProjectionStar (Zmat ω) * Umat ω))) μ :=
    ((Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hPUt.prodMk hPU)).const_smul (Fintype.card (Fin m) : ℝ)⁻¹
  simpa [manyInstrumentProjectedErrorGram, sampleGram] using hraw

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
omit [IsProbabilityMeasure μ] in
/-- Projected reduced-form error score measurability from finite-sample matrix
measurability of `Z`, `u₂`, and the structural error vector. -/
theorem manyInstrumentProjectedErrorCross_aestronglyMeasurable
    {m : ℕ} {Zmat : Ω → Matrix (Fin m) (ι m) ℝ}
    {Umat : Ω → Matrix (Fin m) k ℝ} {evec : Ω → Fin m → ℝ}
    (hZmat : AEStronglyMeasurable Zmat μ)
    (hUmat : AEStronglyMeasurable Umat μ)
    (hevec : AEStronglyMeasurable evec μ) :
    AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorCross (Zmat ω) (Umat ω) (evec ω)) μ := by
  have hP : AEStronglyMeasurable
      (fun ω => instrumentProjectionStar (Zmat ω)) μ :=
    manyInstrumentProjectionStar_aestronglyMeasurable (μ := μ) hZmat
  have hPU : AEStronglyMeasurable
      (fun ω => instrumentProjectionStar (Zmat ω) * Umat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hP.prodMk hUmat)
  have hPUt : AEStronglyMeasurable
      (fun ω => (instrumentProjectionStar (Zmat ω) * Umat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hPU
  have hraw : AEStronglyMeasurable
      (fun ω =>
        (Fintype.card (Fin m) : ℝ)⁻¹ •
          ((instrumentProjectionStar (Zmat ω) * Umat ω)ᵀ *ᵥ evec ω)) μ :=
    ((Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hPUt.prodMk hevec)).const_smul (Fintype.card (Fin m) : ℝ)⁻¹
  simpa [manyInstrumentProjectedErrorCross, sampleCrossMoment] using hraw

omit [IsProbabilityMeasure μ] in
/-- Finite-sample measurability of totalized OLS from matrix-valued
regressor and outcome measurability. -/
theorem manyInstruments_olsBetaStar_aestronglyMeasurable
    {m : ℕ} {Xmat : Ω → Matrix (Fin m) k ℝ} {Yvec : Ω → Fin m → ℝ}
    (hXmat : AEStronglyMeasurable Xmat μ)
    (hYvec : AEStronglyMeasurable Yvec μ) :
    AEStronglyMeasurable (fun ω => olsBetaStar (Xmat ω) (Yvec ω)) μ := by
  have hXt : AEStronglyMeasurable (fun ω => (Xmat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hXmat
  have hGram : AEStronglyMeasurable (fun ω => (Xmat ω)ᵀ * Xmat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXt.prodMk hXmat)
  have hInv : AEStronglyMeasurable
      (fun ω => ((Xmat ω)ᵀ * Xmat ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hGram
  have hCross : AEStronglyMeasurable (fun ω => (Xmat ω)ᵀ *ᵥ Yvec ω) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXt.prodMk hYvec)
  have hbeta : AEStronglyMeasurable
      (fun ω => ((Xmat ω)ᵀ * Xmat ω)⁻¹ *ᵥ ((Xmat ω)ᵀ *ᵥ Yvec ω)) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hInv.prodMk hCross)
  simpa [olsBetaStar] using hbeta

set_option linter.unusedFintypeInType false in
omit [IsProbabilityMeasure μ] in
/-- Finite-sample measurability of totalized 2SLS from matrix-valued
instrument, regressor, and outcome measurability. -/
theorem manyInstruments_twoSLSBetaStar_aestronglyMeasurable
    {m : ℕ} {Zmat : Ω → Matrix (Fin m) (ι m) ℝ}
    {Xmat : Ω → Matrix (Fin m) k ℝ} {Yvec : Ω → Fin m → ℝ}
    (hZmat : AEStronglyMeasurable Zmat μ)
    (hXmat : AEStronglyMeasurable Xmat μ)
    (hYvec : AEStronglyMeasurable Yvec μ) :
    AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Zmat ω) (Xmat ω) (Yvec ω)) μ := by
  have hP : AEStronglyMeasurable
      (fun ω => instrumentProjectionStar (Zmat ω)) μ :=
    manyInstrumentProjectionStar_aestronglyMeasurable (μ := μ) hZmat
  have hXt : AEStronglyMeasurable (fun ω => (Xmat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hXmat
  have hXtP : AEStronglyMeasurable
      (fun ω => (Xmat ω)ᵀ * instrumentProjectionStar (Zmat ω)) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXt.prodMk hP)
  have hM : AEStronglyMeasurable
      (fun ω => (Xmat ω)ᵀ * instrumentProjectionStar (Zmat ω) * Xmat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXtP.prodMk hXmat)
  have hMinv : AEStronglyMeasurable
      (fun ω => ((Xmat ω)ᵀ * instrumentProjectionStar (Zmat ω) * Xmat ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hM
  have hV : AEStronglyMeasurable
      (fun ω => ((Xmat ω)ᵀ * instrumentProjectionStar (Zmat ω)) *ᵥ Yvec ω) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXtP.prodMk hYvec)
  have hbeta : AEStronglyMeasurable
      (fun ω =>
        ((Xmat ω)ᵀ * instrumentProjectionStar (Zmat ω) * Xmat ω)⁻¹ *ᵥ
          (((Xmat ω)ᵀ * instrumentProjectionStar (Zmat ω)) *ᵥ Yvec ω)) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hMinv.prodMk hV)
  simpa [twoSLSBetaStar, twoSLSMomentMatrixStar, twoSLSMomentVectorStar,
    Matrix.mul_assoc] using hbeta

set_option linter.unusedFintypeInType false in
omit [Fintype k] [DecidableEq k] [IsProbabilityMeasure μ] in
private theorem manyInstruments_limlWeightMatrixStar_aestronglyMeasurable
    {m : ℕ} {Zmat : Ω → Matrix (Fin m) (ι m) ℝ}
    {muHat : Ω → ℝ}
    (hZmat : AEStronglyMeasurable Zmat μ)
    (hmu : AEStronglyMeasurable muHat μ) :
    AEStronglyMeasurable
      (fun ω => limlWeightMatrixStar (Zmat ω) (muHat ω)) μ := by
  have hP : AEStronglyMeasurable
      (fun ω => instrumentProjectionStar (Zmat ω)) μ :=
    manyInstrumentProjectionStar_aestronglyMeasurable (μ := μ) hZmat
  have hResid : AEStronglyMeasurable
      (fun ω => (1 : Matrix (Fin m) (Fin m) ℝ) -
        instrumentProjectionStar (Zmat ω)) μ :=
    aestronglyMeasurable_const.sub hP
  exact hP.sub (hmu.smul hResid)

set_option linter.unusedFintypeInType false in
omit [IsProbabilityMeasure μ] in
/-- Finite-sample measurability of totalized LIML from matrix-valued
instrument, regressor, outcome, and eigenvalue-adjustment measurability. -/
theorem manyInstruments_limlBetaStar_aestronglyMeasurable
    {m : ℕ} {Zmat : Ω → Matrix (Fin m) (ι m) ℝ}
    {Xmat : Ω → Matrix (Fin m) k ℝ} {Yvec : Ω → Fin m → ℝ}
    {muHat : Ω → ℝ}
    (hZmat : AEStronglyMeasurable Zmat μ)
    (hXmat : AEStronglyMeasurable Xmat μ)
    (hYvec : AEStronglyMeasurable Yvec μ)
    (hmu : AEStronglyMeasurable muHat μ) :
    AEStronglyMeasurable
      (fun ω => limlBetaStar (Zmat ω) (Xmat ω) (Yvec ω) (muHat ω)) μ := by
  have hW :=
    manyInstruments_limlWeightMatrixStar_aestronglyMeasurable
      (μ := μ) (Zmat := Zmat) hZmat hmu
  have hXt : AEStronglyMeasurable (fun ω => (Xmat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hXmat
  have hXtW : AEStronglyMeasurable
      (fun ω => (Xmat ω)ᵀ * limlWeightMatrixStar (Zmat ω) (muHat ω)) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXt.prodMk hW)
  have hM : AEStronglyMeasurable
      (fun ω => (Xmat ω)ᵀ * limlWeightMatrixStar (Zmat ω) (muHat ω) * Xmat ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXtW.prodMk hXmat)
  have hMinv : AEStronglyMeasurable
      (fun ω =>
        ((Xmat ω)ᵀ * limlWeightMatrixStar (Zmat ω) (muHat ω) * Xmat ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hM
  have hV : AEStronglyMeasurable
      (fun ω => ((Xmat ω)ᵀ * limlWeightMatrixStar (Zmat ω) (muHat ω)) *ᵥ
        Yvec ω) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXtW.prodMk hYvec)
  have hbeta : AEStronglyMeasurable
      (fun ω =>
        ((Xmat ω)ᵀ * limlWeightMatrixStar (Zmat ω) (muHat ω) * Xmat ω)⁻¹ *ᵥ
          (((Xmat ω)ᵀ * limlWeightMatrixStar (Zmat ω) (muHat ω)) *ᵥ
            Yvec ω)) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hMinv.prodMk hV)
  simpa [limlBetaStar, limlMomentMatrixStar, limlMomentVectorStar] using hbeta

set_option linter.unusedFintypeInType false in
omit [IsProbabilityMeasure μ] in
/-- Estimator measurability for Hansen Theorem 12.19 from reduced-form matrix
measurability and the structural equation. -/
theorem manyInstruments_estimator_measurability_of_reduced_form
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ}
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) + u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hmu_meas : ∀ m, AEStronglyMeasurable (limlMuHat m) μ) :
    (∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ) ∧
    (∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ) ∧
    (∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) := by
  have hX_meas : ∀ m, AEStronglyMeasurable (X m) μ := by
    intro m
    have hsignal : AEStronglyMeasurable
        (fun ω => manyInstrumentSignal (Z m ω) (Gamma m)) μ := by
      simpa [manyInstrumentSignal] using
        (Continuous.matrix_mul continuous_id continuous_const).comp_aestronglyMeasurable
          (hZ_meas m)
    exact (hsignal.add (hu2_meas m)).congr
      (ae_of_all μ fun ω => (hreduced m ω).symm)
  have hY_meas : ∀ m, AEStronglyMeasurable (Y m) μ := by
    intro m
    have hfit : AEStronglyMeasurable (fun ω => X m ω *ᵥ β) μ :=
      (Continuous.matrix_mulVec continuous_id continuous_const).comp_aestronglyMeasurable
        (hX_meas m)
    exact (hfit.add (he_meas m)).congr
      (ae_of_all μ fun ω => (hstruct m ω).symm)
  refine ⟨?_, ?_, ?_⟩
  · intro m
    exact manyInstruments_olsBetaStar_aestronglyMeasurable
      (μ := μ) (hX_meas m) (hY_meas m)
  · intro m
    exact manyInstruments_twoSLSBetaStar_aestronglyMeasurable
      (hZ_meas m) (hX_meas m) (hY_meas m)
  · intro m
    exact manyInstruments_limlBetaStar_aestronglyMeasurable
      (hZ_meas m) (hX_meas m) (hY_meas m) (hmu_meas m)

set_option maxHeartbeats 600000 in
-- Product-space synthesis for scalar/matrix smul CMT is expensive.
private theorem tendstoInMeasure_smul_matrix
    {κ : Type*} [Fintype κ]
    {r : ℕ → Ω → ℝ} {A : ℕ → Ω → Matrix κ κ ℝ}
    {c : ℝ} {M : Matrix κ κ ℝ}
    (hr_meas : ∀ m, AEStronglyMeasurable (r m) μ)
    (hA_meas : ∀ m, AEStronglyMeasurable (A m) μ)
    (hr : TendstoInMeasure μ r atTop (fun _ => c))
    (hA : TendstoInMeasure μ A atTop (fun _ => M)) :
    TendstoInMeasure μ (fun m ω => r m ω • A m ω) atTop (fun _ => c • M) := by
  have hprod_meas : ∀ m, AEStronglyMeasurable
      (fun ω => (r m ω, A m ω)) μ :=
    fun m => (hr_meas m).prodMk (hA_meas m)
  have hprod : TendstoInMeasure μ
      (fun m ω => (r m ω, A m ω)) atTop (fun _ => (c, M)) :=
    tendstoInMeasure_prodMk hr hA
  have hcont : Continuous (fun p : ℝ × Matrix κ κ ℝ => p.1 • p.2) :=
    continuous_fst.smul continuous_snd
  exact tendstoInMeasure_continuous_comp hprod_meas hprod hcont

set_option maxHeartbeats 600000 in
-- Product-space synthesis for scalar/vector smul CMT is expensive.
private theorem tendstoInMeasure_smul_vector
    {κ : Type*} [Fintype κ]
    {r : ℕ → Ω → ℝ} {v : ℕ → Ω → κ → ℝ}
    {c : ℝ} {g : κ → ℝ}
    (hr_meas : ∀ m, AEStronglyMeasurable (r m) μ)
    (hv_meas : ∀ m, AEStronglyMeasurable (v m) μ)
    (hr : TendstoInMeasure μ r atTop (fun _ => c))
    (hv : TendstoInMeasure μ v atTop (fun _ => g)) :
    TendstoInMeasure μ (fun m ω => r m ω • v m ω) atTop (fun _ => c • g) := by
  have hprod_meas : ∀ m, AEStronglyMeasurable
      (fun ω => (r m ω, v m ω)) μ :=
    fun m => (hr_meas m).prodMk (hv_meas m)
  have hprod : TendstoInMeasure μ
      (fun m ω => (r m ω, v m ω)) atTop (fun _ => (c, g)) :=
    tendstoInMeasure_prodMk hr hv
  have hcont : Continuous (fun p : ℝ × (κ → ℝ) => p.1 • p.2) :=
    continuous_fst.smul continuous_snd
  exact tendstoInMeasure_continuous_comp hprod_meas hprod hcont

omit [Fintype k] [DecidableEq k] in
private theorem manyInstruments_liml_matrix_limit_cancel
    {H Sigma22 : Matrix k k ℝ} {alpha : ℝ}
    (halpha_lt_one : alpha < 1) :
    (H + alpha • Sigma22) -
        (alpha / (1 - alpha)) • ((H + Sigma22) - (H + alpha • Sigma22)) =
      H := by
  have hden : 1 - alpha ≠ 0 := by linarith
  ext i j
  simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
  field_simp [hden]
  ring

omit [Fintype k] [DecidableEq k] in
private theorem manyInstruments_liml_score_limit_cancel
    {Sigma2e : k → ℝ} {alpha : ℝ}
    (halpha_lt_one : alpha < 1) :
    alpha • Sigma2e -
        (alpha / (1 - alpha)) • (Sigma2e - alpha • Sigma2e) =
      (0 : k → ℝ) := by
  have hden : 1 - alpha ≠ 0 := by linarith
  ext i
  simp [Pi.sub_apply, Pi.smul_apply]
  field_simp [hden]
  ring

/-- Moment-level LIML consistency package for Hansen Theorem 12.19.

The fields are Hansen's normalized LIML bread and structural-error score
convergences.  This package is deliberately below the theorem-facing
many-instrument package: it proves the LIML estimator limit from moment
convergence instead of assuming that final limit directly. -/
structure ManyInstrumentsLIMLMomentConsistencyConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (H : Matrix k k ℝ) : Prop where
  moment_meas : ∀ m, AEStronglyMeasurable
    (fun ω => limlNormalizedMomentMatrixStar (Z m ω) (X m ω) (limlMuHat m ω)) μ
  score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => limlNormalizedMomentVectorStar
      (Z m ω) (X m ω) (e m ω) (limlMuHat m ω)) μ
  moment_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      limlNormalizedMomentMatrixStar (Z m ω) (X m ω) (limlMuHat m ω))
    atTop (fun _ => H)
  score_tendsto_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      limlNormalizedMomentVectorStar (Z m ω) (X m ω) (e m ω) (limlMuHat m ω))
    atTop (fun _ => (0 : k → ℝ))
  limit_nonsing : IsUnit H.det

set_option maxHeartbeats 900000 in
-- Product-space synthesis for the inverse/product/mulVec CMT chain is expensive.
/-- LIML consistency from normalized bread and structural-error score
convergence.

This is the CMT proof engine for the LIML face of Hansen Theorem 12.19.  It
uses totalized matrix inverses throughout, so finite-sample singular designs do
not require a separate high-probability nonsingularity premise. -/
theorem limlBetaStar_tendstoInMeasure_beta_of_normalized_moments
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    (h : ManyInstrumentsLIMLMomentConsistencyConditions μ Z X e limlMuHat H)
    (hmodel : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) := by
  let A : ℕ → Ω → Matrix k k ℝ := fun m ω =>
    limlNormalizedMomentMatrixStar (Z m ω) (X m ω) (limlMuHat m ω)
  let s : ℕ → Ω → k → ℝ := fun m ω =>
    limlNormalizedMomentVectorStar (Z m ω) (X m ω) (e m ω) (limlMuHat m ω)
  have hA_meas : ∀ m, AEStronglyMeasurable (A m) μ := by
    intro m
    simpa [A] using h.moment_meas m
  have hs_meas : ∀ m, AEStronglyMeasurable (s m) μ := by
    intro m
    simpa [s] using h.score_meas m
  have hA : TendstoInMeasure μ A atTop (fun _ => H) := by
    simpa [A] using h.moment_tendsto
  have hs : TendstoInMeasure μ s atTop (fun _ => (0 : k → ℝ)) := by
    simpa [s] using h.score_tendsto_zero
  have hAinv_meas : ∀ m, AEStronglyMeasurable (fun ω => (A m ω)⁻¹) μ :=
    fun m => aestronglyMeasurable_matrix_inv (hA_meas m)
  have hAinv : TendstoInMeasure μ
      (fun m ω => (A m ω)⁻¹) atTop (fun _ => H⁻¹) :=
    tendstoInMeasure_matrix_inv (μ := μ) hA_meas hA (fun _ => h.limit_nonsing)
  have hAinvA_meas : ∀ m, AEStronglyMeasurable
      (fun ω => (A m ω)⁻¹ * A m ω) μ := by
    intro m
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hAinv_meas m).prodMk (hA_meas m))
  have hAinvA : TendstoInMeasure μ
      (fun m ω => (A m ω)⁻¹ * A m ω) atTop (fun _ => H⁻¹ * H) :=
    tendstoInMeasure_matrix_mul hAinv_meas hA_meas hAinv hA
  have hAinvAβ_meas : ∀ m, AEStronglyMeasurable
      (fun ω => ((A m ω)⁻¹ * A m ω) *ᵥ β) μ := by
    intro m
    exact (Continuous.matrix_mulVec continuous_id continuous_const).comp_aestronglyMeasurable
      (hAinvA_meas m)
  have hAinvAβ : TendstoInMeasure μ
      (fun m ω => ((A m ω)⁻¹ * A m ω) *ᵥ β) atTop (fun _ => β) := by
    have hcont : Continuous (fun M : Matrix k k ℝ => M *ᵥ β) :=
      Continuous.matrix_mulVec continuous_id continuous_const
    have hraw := tendstoInMeasure_continuous_comp hAinvA_meas hAinvA hcont
    refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hraw
    exact ae_of_all μ (fun _ => by
      rw [Matrix.nonsing_inv_mul H h.limit_nonsing]
      simp)
  have hAinvs_meas : ∀ m, AEStronglyMeasurable
      (fun ω => (A m ω)⁻¹ *ᵥ s m ω) μ := by
    intro m
    exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hAinv_meas m).prodMk (hs_meas m))
  have hAinvs : TendstoInMeasure μ
      (fun m ω => (A m ω)⁻¹ *ᵥ s m ω) atTop (fun _ => (0 : k → ℝ)) := by
    have hraw := tendstoInMeasure_mulVec hAinv_meas hs_meas hAinv hs
    refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hraw
    exact ae_of_all μ (fun _ => by simp)
  have hsum := tendstoInMeasure_add hAinvAβ_meas hAinvs_meas hAinvAβ hAinvs
  simp only [add_zero] at hsum
  refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hsum
  filter_upwards [eventually_gt_atTop 0] with m hm
  exact ae_of_all μ (fun ω => by
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hY : Y m ω = X m ω *ᵥ β + e m ω := hmodel m ω
    change ((A m ω)⁻¹ * A m ω) *ᵥ β + (A m ω)⁻¹ *ᵥ s m ω =
      limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)
    rw [hY, limlBetaStar_eq_normalized_moments,
      limlNormalizedMomentVectorStar_linear_model]
    simp [A, s, Matrix.mulVec_add, Matrix.mulVec_mulVec])

/-- Moment-level LIML package with a nonzero structural-error score limit.

This generic CMT layer is used for the 2SLS face of Hansen Theorem 12.19 by
setting the LIML adjustment to zero. -/
structure ManyInstrumentsLIMLMomentLimitConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (Q : Matrix k k ℝ) (g : k → ℝ) : Prop where
  moment_meas : ∀ m, AEStronglyMeasurable
    (fun ω => limlNormalizedMomentMatrixStar (Z m ω) (X m ω) (limlMuHat m ω)) μ
  score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => limlNormalizedMomentVectorStar
      (Z m ω) (X m ω) (e m ω) (limlMuHat m ω)) μ
  moment_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      limlNormalizedMomentMatrixStar (Z m ω) (X m ω) (limlMuHat m ω))
    atTop (fun _ => Q)
  score_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      limlNormalizedMomentVectorStar (Z m ω) (X m ω) (e m ω) (limlMuHat m ω))
    atTop (fun _ => g)
  limit_nonsing : IsUnit Q.det

/-- Convert the nonzero-score LIML moment package to the zero-score consistency
package when the score limit is `0`. -/
theorem ManyInstrumentsLIMLMomentConsistencyConditions.of_moment_limit_zero_score
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {H : Matrix k k ℝ}
    (h : ManyInstrumentsLIMLMomentLimitConditions
      μ Z X e limlMuHat H (0 : k → ℝ)) :
    ManyInstrumentsLIMLMomentConsistencyConditions μ Z X e limlMuHat H :=
  { moment_meas := h.moment_meas
    score_meas := h.score_meas
    moment_tendsto := h.moment_tendsto
    score_tendsto_zero := h.score_tendsto
    limit_nonsing := h.limit_nonsing }

set_option maxHeartbeats 900000 in
-- Product-space synthesis for the inverse/product/mulVec CMT chain is expensive.
/-- LIML/k-class estimator convergence from normalized bread and score limits.

The limit is `β + Q^{-1}g`; the LIML consistency theorem above is the special
case `g = 0`. -/
theorem limlBetaStar_tendstoInMeasure_of_normalized_moment_limits
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β g : k → ℝ} {Q : Matrix k k ℝ}
    (h : ManyInstrumentsLIMLMomentLimitConditions μ Z X e limlMuHat Q g)
    (hmodel : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β + Q⁻¹ *ᵥ g) := by
  let A : ℕ → Ω → Matrix k k ℝ := fun m ω =>
    limlNormalizedMomentMatrixStar (Z m ω) (X m ω) (limlMuHat m ω)
  let s : ℕ → Ω → k → ℝ := fun m ω =>
    limlNormalizedMomentVectorStar (Z m ω) (X m ω) (e m ω) (limlMuHat m ω)
  have hA_meas : ∀ m, AEStronglyMeasurable (A m) μ := by
    intro m
    simpa [A] using h.moment_meas m
  have hs_meas : ∀ m, AEStronglyMeasurable (s m) μ := by
    intro m
    simpa [s] using h.score_meas m
  have hA : TendstoInMeasure μ A atTop (fun _ => Q) := by
    simpa [A] using h.moment_tendsto
  have hs : TendstoInMeasure μ s atTop (fun _ => g) := by
    simpa [s] using h.score_tendsto
  have hAinv_meas : ∀ m, AEStronglyMeasurable (fun ω => (A m ω)⁻¹) μ :=
    fun m => aestronglyMeasurable_matrix_inv (hA_meas m)
  have hAinv : TendstoInMeasure μ
      (fun m ω => (A m ω)⁻¹) atTop (fun _ => Q⁻¹) :=
    tendstoInMeasure_matrix_inv (μ := μ) hA_meas hA (fun _ => h.limit_nonsing)
  have hAinvA_meas : ∀ m, AEStronglyMeasurable
      (fun ω => (A m ω)⁻¹ * A m ω) μ := by
    intro m
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hAinv_meas m).prodMk (hA_meas m))
  have hAinvA : TendstoInMeasure μ
      (fun m ω => (A m ω)⁻¹ * A m ω) atTop (fun _ => Q⁻¹ * Q) :=
    tendstoInMeasure_matrix_mul hAinv_meas hA_meas hAinv hA
  have hAinvAβ_meas : ∀ m, AEStronglyMeasurable
      (fun ω => ((A m ω)⁻¹ * A m ω) *ᵥ β) μ := by
    intro m
    exact (Continuous.matrix_mulVec continuous_id continuous_const).comp_aestronglyMeasurable
      (hAinvA_meas m)
  have hAinvAβ : TendstoInMeasure μ
      (fun m ω => ((A m ω)⁻¹ * A m ω) *ᵥ β) atTop (fun _ => β) := by
    have hcont : Continuous (fun M : Matrix k k ℝ => M *ᵥ β) :=
      Continuous.matrix_mulVec continuous_id continuous_const
    have hraw := tendstoInMeasure_continuous_comp hAinvA_meas hAinvA hcont
    refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hraw
    exact ae_of_all μ (fun _ => by
      rw [Matrix.nonsing_inv_mul Q h.limit_nonsing]
      simp)
  have hAinvs_meas : ∀ m, AEStronglyMeasurable
      (fun ω => (A m ω)⁻¹ *ᵥ s m ω) μ := by
    intro m
    exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hAinv_meas m).prodMk (hs_meas m))
  have hAinvs : TendstoInMeasure μ
      (fun m ω => (A m ω)⁻¹ *ᵥ s m ω) atTop (fun _ => Q⁻¹ *ᵥ g) :=
    tendstoInMeasure_mulVec hAinv_meas hs_meas hAinv hs
  have hsum := tendstoInMeasure_add hAinvAβ_meas hAinvs_meas hAinvAβ hAinvs
  refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hsum
  filter_upwards [eventually_gt_atTop 0] with m hm
  exact ae_of_all μ (fun ω => by
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hY : Y m ω = X m ω *ᵥ β + e m ω := hmodel m ω
    change ((A m ω)⁻¹ * A m ω) *ᵥ β + (A m ω)⁻¹ *ᵥ s m ω =
      limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)
    rw [hY, limlBetaStar_eq_normalized_moments,
      limlNormalizedMomentVectorStar_linear_model]
    simp [A, s, Matrix.mulVec_add, Matrix.mulVec_mulVec])

/-- Moment-level OLS package for the many-instrument theorem. -/
structure ManyInstrumentsOLSMomentLimitConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (Q : Matrix k k ℝ) (g : k → ℝ) : Prop where
  gram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ
  score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => sampleCrossMoment (X m ω) (e m ω)) μ
  gram_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω => sampleGram (X m ω)) atTop (fun _ => Q)
  score_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω => sampleCrossMoment (X m ω) (e m ω)) atTop (fun _ => g)
  limit_nonsing : IsUnit Q.det

set_option maxHeartbeats 900000 in
-- Product-space synthesis for the three-input LIML cancellation maps is expensive.
/-- Build Hansen's many-instrument LIML zero-score moment package from the OLS
and projected 2SLS moment limits plus the LIML eigenvalue adjustment limit
`μ̂ -> α / (1 - α)`.

This is the local formal version of Hansen's cancellation in the proof of
Theorem 12.19:
`(H + αΣ₂₂) - (α/(1-α))((H + Σ₂₂) - (H + αΣ₂₂)) = H` and
`αΣ₂e - (α/(1-α))(Σ₂e - αΣ₂e) = 0`. -/
theorem ManyInstrumentsLIMLMomentConsistencyConditions.of_ols_twoSLS_moments_mu_tendsto
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ} {alpha : ℝ}
    (hOLS : ManyInstrumentsOLSMomentLimitConditions μ X e (H + Sigma22) Sigma2e)
    (h2SLS : ManyInstrumentsLIMLMomentLimitConditions
      μ Z X e (fun _ _ => 0) (H + alpha • Sigma22) (alpha • Sigma2e))
    (hmu_meas : ∀ m, AEStronglyMeasurable (limlMuHat m) μ)
    (hmu_tendsto : TendstoInMeasure μ limlMuHat atTop
      (fun _ => alpha / (1 - alpha)))
    (halpha_lt_one : alpha < 1)
    (hH_nonsing : IsUnit H.det) :
    ManyInstrumentsLIMLMomentConsistencyConditions μ Z X e limlMuHat H := by
  let mu0 : ℝ := alpha / (1 - alpha)
  let Pmat : ℕ → Ω → Matrix k k ℝ := fun m ω =>
    limlNormalizedMomentMatrixStar (Z m ω) (X m ω) 0
  let Gmat : ℕ → Ω → Matrix k k ℝ := fun m ω => sampleGram (X m ω)
  let Pscore : ℕ → Ω → k → ℝ := fun m ω =>
    limlNormalizedMomentVectorStar (Z m ω) (X m ω) (e m ω) 0
  let Gscore : ℕ → Ω → k → ℝ := fun m ω =>
    sampleCrossMoment (X m ω) (e m ω)
  have hPmat_meas : ∀ m, AEStronglyMeasurable (Pmat m) μ := by
    intro m
    simpa [Pmat] using h2SLS.moment_meas m
  have hGmat_meas : ∀ m, AEStronglyMeasurable (Gmat m) μ := by
    intro m
    simpa [Gmat] using hOLS.gram_meas m
  have hPscore_meas : ∀ m, AEStronglyMeasurable (Pscore m) μ := by
    intro m
    simpa [Pscore] using h2SLS.score_meas m
  have hGscore_meas : ∀ m, AEStronglyMeasurable (Gscore m) μ := by
    intro m
    simpa [Gscore] using hOLS.score_meas m
  have hPmat_tendsto : TendstoInMeasure μ Pmat atTop
      (fun _ => H + alpha • Sigma22) := by
    simpa [Pmat] using h2SLS.moment_tendsto
  have hGmat_tendsto : TendstoInMeasure μ Gmat atTop
      (fun _ => H + Sigma22) := by
    simpa [Gmat] using hOLS.gram_tendsto
  have hPscore_tendsto : TendstoInMeasure μ Pscore atTop
      (fun _ => alpha • Sigma2e) := by
    simpa [Pscore] using h2SLS.score_tendsto
  have hGscore_tendsto : TendstoInMeasure μ Gscore atTop
      (fun _ => Sigma2e) := by
    simpa [Gscore] using hOLS.score_tendsto
  have hmat_prod_meas : ∀ m, AEStronglyMeasurable
      (fun ω => (limlMuHat m ω, (Pmat m ω, Gmat m ω))) μ := by
    intro m
    exact (hmu_meas m).prodMk ((hPmat_meas m).prodMk (hGmat_meas m))
  have hmat_prod_tendsto : TendstoInMeasure μ
      (fun m ω => (limlMuHat m ω, (Pmat m ω, Gmat m ω))) atTop
      (fun _ => (mu0, (H + alpha • Sigma22, H + Sigma22))) := by
    exact tendstoInMeasure_prodMk hmu_tendsto
      (tendstoInMeasure_prodMk hPmat_tendsto hGmat_tendsto)
  have hmat_cont : Continuous
      (fun p : ℝ × (Matrix k k ℝ × Matrix k k ℝ) =>
        p.2.1 - p.1 • (p.2.2 - p.2.1)) := by
    have hP : Continuous
        (fun p : ℝ × (Matrix k k ℝ × Matrix k k ℝ) => p.2.1) :=
      continuous_fst.comp continuous_snd
    have hG : Continuous
        (fun p : ℝ × (Matrix k k ℝ × Matrix k k ℝ) => p.2.2) :=
      continuous_snd.comp continuous_snd
    exact hP.sub (continuous_fst.smul (hG.sub hP))
  have hliml_mat_raw : TendstoInMeasure μ
      (fun m ω => Pmat m ω - limlMuHat m ω • (Gmat m ω - Pmat m ω))
      atTop
      (fun _ =>
        (H + alpha • Sigma22) -
          (alpha / (1 - alpha)) • ((H + Sigma22) - (H + alpha • Sigma22))) := by
    simpa [mu0] using
      tendstoInMeasure_continuous_comp hmat_prod_meas hmat_prod_tendsto hmat_cont
  have hliml_mat : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlNormalizedMomentMatrixStar (Z m ω) (X m ω) (limlMuHat m ω))
      atTop (fun _ => H) := by
    refine TendstoInMeasure.congr' ?_ ?_ hliml_mat_raw
    · exact Eventually.of_forall fun m => ae_of_all μ fun ω => by
        simpa [Pmat, Gmat] using
          (limlNormalizedMomentMatrixStar_eq_zero_sub_mu_residual
            (Z m ω) (X m ω) (limlMuHat m ω)).symm
    · exact ae_of_all μ fun _ => by
        simpa using
          (manyInstruments_liml_matrix_limit_cancel
            (H := H) (Sigma22 := Sigma22) (alpha := alpha) halpha_lt_one)
  have hscore_prod_meas : ∀ m, AEStronglyMeasurable
      (fun ω => (limlMuHat m ω, (Pscore m ω, Gscore m ω))) μ := by
    intro m
    exact (hmu_meas m).prodMk ((hPscore_meas m).prodMk (hGscore_meas m))
  have hscore_prod_tendsto : TendstoInMeasure μ
      (fun m ω => (limlMuHat m ω, (Pscore m ω, Gscore m ω))) atTop
      (fun _ => (mu0, (alpha • Sigma2e, Sigma2e))) := by
    exact tendstoInMeasure_prodMk hmu_tendsto
      (tendstoInMeasure_prodMk hPscore_tendsto hGscore_tendsto)
  have hscore_cont : Continuous
      (fun p : ℝ × ((k → ℝ) × (k → ℝ)) =>
        p.2.1 - p.1 • (p.2.2 - p.2.1)) := by
    have hP : Continuous
        (fun p : ℝ × ((k → ℝ) × (k → ℝ)) => p.2.1) :=
      continuous_fst.comp continuous_snd
    have hG : Continuous
        (fun p : ℝ × ((k → ℝ) × (k → ℝ)) => p.2.2) :=
      continuous_snd.comp continuous_snd
    exact hP.sub (continuous_fst.smul (hG.sub hP))
  have hliml_score_raw : TendstoInMeasure μ
      (fun m ω => Pscore m ω - limlMuHat m ω • (Gscore m ω - Pscore m ω))
      atTop
      (fun _ =>
        alpha • Sigma2e -
          (alpha / (1 - alpha)) • (Sigma2e - alpha • Sigma2e)) := by
    simpa [mu0] using
      tendstoInMeasure_continuous_comp
        hscore_prod_meas hscore_prod_tendsto hscore_cont
  have hliml_score : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlNormalizedMomentVectorStar
          (Z m ω) (X m ω) (e m ω) (limlMuHat m ω))
      atTop (fun _ => (0 : k → ℝ)) := by
    refine TendstoInMeasure.congr' ?_ ?_ hliml_score_raw
    · exact Eventually.of_forall fun m => ae_of_all μ fun ω => by
        simpa [Pscore, Gscore] using
          (limlNormalizedMomentVectorStar_eq_zero_sub_mu_residual
            (Z m ω) (X m ω) (e m ω) (limlMuHat m ω)).symm
    · exact ae_of_all μ fun _ => by
        simpa using
          (manyInstruments_liml_score_limit_cancel
            (Sigma2e := Sigma2e) (alpha := alpha) halpha_lt_one)
  refine
    { moment_meas := ?_
      score_meas := ?_
      moment_tendsto := hliml_mat
      score_tendsto_zero := hliml_score
      limit_nonsing := hH_nonsing }
  · intro m
    have hformula : AEStronglyMeasurable
        (fun ω => Pmat m ω - limlMuHat m ω • (Gmat m ω - Pmat m ω)) μ :=
      (hPmat_meas m).sub ((hmu_meas m).smul ((hGmat_meas m).sub (hPmat_meas m)))
    refine hformula.congr (ae_of_all μ fun ω => ?_)
    simpa [Pmat, Gmat] using
      (limlNormalizedMomentMatrixStar_eq_zero_sub_mu_residual
        (Z m ω) (X m ω) (limlMuHat m ω)).symm
  · intro m
    have hformula : AEStronglyMeasurable
        (fun ω => Pscore m ω - limlMuHat m ω • (Gscore m ω - Pscore m ω)) μ :=
      (hPscore_meas m).sub
        ((hmu_meas m).smul ((hGscore_meas m).sub (hPscore_meas m)))
    refine hformula.congr (ae_of_all μ fun ω => ?_)
    simpa [Pscore, Gscore] using
      (limlNormalizedMomentVectorStar_eq_zero_sub_mu_residual
        (Z m ω) (X m ω) (e m ω) (limlMuHat m ω)).symm

/-- Positive-definite specialization of
`ManyInstrumentsLIMLMomentConsistencyConditions.of_ols_twoSLS_moments_mu_tendsto`,
matching Hansen's signal limit assumption `H > 0`. -/
theorem ManyInstrumentsLIMLMomentConsistencyConditions.of_ols_twoSLS_moments_mu_tendsto_posDef
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ} {alpha : ℝ}
    (hOLS : ManyInstrumentsOLSMomentLimitConditions μ X e (H + Sigma22) Sigma2e)
    (h2SLS : ManyInstrumentsLIMLMomentLimitConditions
      μ Z X e (fun _ _ => 0) (H + alpha • Sigma22) (alpha • Sigma2e))
    (hmu_meas : ∀ m, AEStronglyMeasurable (limlMuHat m) μ)
    (hmu_tendsto : TendstoInMeasure μ limlMuHat atTop
      (fun _ => alpha / (1 - alpha)))
    (halpha_lt_one : alpha < 1)
    (hH : H.PosDef) :
    ManyInstrumentsLIMLMomentConsistencyConditions μ Z X e limlMuHat H :=
  ManyInstrumentsLIMLMomentConsistencyConditions.of_ols_twoSLS_moments_mu_tendsto
    (μ := μ) (Z := Z) (X := X) (e := e) (limlMuHat := limlMuHat)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    hOLS h2SLS hmu_meas hmu_tendsto halpha_lt_one
    ((Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit)

/-- Current many-instrument interface for the sample LIML eigenvalue adjustment.

The imported LIML layer already supplies Rayleigh-minimum notation, but this
module still has no finite-sample many-instrument eigenvalue statistic whose
limit can be linked to Hansen's `μ̂`.  This package names exactly the output
needed by Theorem 12.19 until that sample eigenvalue bridge is added. -/
structure ManyInstrumentsLIMLEigenvalueLimitConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (limlMuHat : ℕ → Ω → ℝ) (alpha : ℝ) : Prop where
  meas : ∀ m, AEStronglyMeasurable (limlMuHat m) μ
  tendsto : TendstoInMeasure μ limlMuHat atTop
    (fun _ => alpha / (1 - alpha))

/-- Deterministic many-instrument LIML eigenvalue benchmark
`(ℓ_n/n)/(1 - ℓ_n/n)`.

Hansen's Theorem 12.19 sends `ℓ_n/n -> α`; this is the deterministic scalar
that the sample LIML adjustment must track before the cancellation API can use
the limit `α/(1-α)`. -/
noncomputable def manyInstrumentsLIMLEigenvalueCardRatioAdjustment
    (m : ℕ) : ℝ :=
  let r := (Fintype.card (ι m) : ℝ) / (m : ℝ)
  r / (1 - r)

omit [∀ m, DecidableEq (ι m)] in
/-- If the instrument-count ratio converges to `α < 1`, Hansen's deterministic
LIML eigenvalue benchmark converges to `α/(1-α)`. -/
theorem manyInstrumentsLIMLEigenvalueCardRatioAdjustment_tendsto
    {alpha : ℝ}
    (hratio : Tendsto
      (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ)) atTop (𝓝 alpha))
    (halpha_lt_one : alpha < 1) :
    Tendsto
      (fun m : ℕ =>
        manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m)
      atTop (𝓝 (alpha / (1 - alpha))) := by
  have hcont : ContinuousAt (fun r : ℝ => r / (1 - r)) alpha := by
    have hden : 1 - alpha ≠ 0 := by linarith
    exact continuousAt_id.div (continuousAt_const.sub continuousAt_id) hden
  simpa [manyInstrumentsLIMLEigenvalueCardRatioAdjustment] using
    hcont.tendsto.comp hratio

omit [Fintype k] [DecidableEq k] [∀ m, DecidableEq (ι m)] in
/-- The many-instrument ratio limit is automatically nonnegative.

Hansen assumes `ℓ_n / n -> α`; since each finite-sample ratio is nonnegative,
the limit side condition `0 ≤ α` used by the matrix nonsingularity wrappers is
not a separate primitive. -/
theorem manyInstruments_alpha_nonneg_of_card_ratio_tendsto
    {alpha : ℝ}
    (hratio : Tendsto
      (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ)) atTop (𝓝 alpha)) :
    0 ≤ alpha :=
  le_of_tendsto_of_tendsto tendsto_const_nhds hratio
    (Eventually.of_forall fun _ =>
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Sample LIML eigenvalue-problem output for Hansen Theorem 12.19.

The substantive spectral/WLLN work is isolated in the centered gap:
`μ̂_n - (ℓ_n/n)/(1 - ℓ_n/n) ->p 0`.  Combined with `ℓ_n/n -> α`, this derives
the existing theorem-facing limit package `μ̂_n ->p α/(1-α)`. -/
structure ManyInstrumentsLIMLSampleEigenvalueProblemConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (limlMuHat : ℕ → Ω → ℝ) : Prop where
  meas : ∀ m, AEStronglyMeasurable (limlMuHat m) μ
  adjustment_gap_tendsto_zero : TendstoInMeasure μ
    (fun m ω =>
      limlMuHat m ω -
        manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m)
    atTop (fun _ => 0)

omit [∀ m, DecidableEq (ι m)] in
/-- Convert the sample LIML eigenvalue-problem gap into Hansen's
`μ̂_n ->p α/(1-α)` limit package. -/
theorem
    ManyInstrumentsLIMLSampleEigenvalueProblemConditions.toLIMLEigenvalueLimitConditions
    {limlMuHat : ℕ → Ω → ℝ} {alpha : ℝ}
    (h : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat)
    (hratio : Tendsto
      (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ)) atTop (𝓝 alpha))
    (halpha_lt_one : alpha < 1) :
    ManyInstrumentsLIMLEigenvalueLimitConditions μ limlMuHat alpha where
  meas := h.meas
  tendsto := by
    have hbenchmark : TendstoInMeasure μ
        (fun m (_ : Ω) =>
          manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m)
        atTop (fun _ => alpha / (1 - alpha)) :=
      tendstoInMeasure_const_real (μ := μ)
        (manyInstrumentsLIMLEigenvalueCardRatioAdjustment_tendsto
          (ι := ι) hratio halpha_lt_one)
    exact TendstoInMeasure.of_sub_tendsto_zero_real
      h.adjustment_gap_tendsto_zero hbenchmark

omit [∀ m, DecidableEq (ι m)] in
/-- Direct convergence form of the sample LIML eigenvalue-problem bridge:
`μ̂_n ->p α/(1-α)`. -/
theorem manyInstruments_limlMuHat_tendsto_alpha_over_one_minus_alpha_of_sample_eigenvalue_problem
    {limlMuHat : ℕ → Ω → ℝ} {alpha : ℝ}
    (h : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat)
    (hratio : Tendsto
      (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ)) atTop (𝓝 alpha))
    (halpha_lt_one : alpha < 1) :
    TendstoInMeasure μ limlMuHat atTop
      (fun _ => alpha / (1 - alpha)) :=
  (h.toLIMLEigenvalueLimitConditions
    (ι := ι) (μ := μ) hratio halpha_lt_one).tendsto

/-- Sharply named certificate for the remaining many-instrument LIML
eigenvalue input in Hansen Theorem 12.19: the sample LIML adjustment must
converge to `α / (1 - α)`.

This is an alias of `ManyInstrumentsLIMLEigenvalueLimitConditions`; it names
the exact remaining theorem input until the finite-sample LIML eigenvalue
statistic is connected to the many-instrument Rayleigh/eigenvalue argument. -/
abbrev ManyInstrumentsLIMLEigenvalueAlphaOverOneMinusAlphaCertificate
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (limlMuHat : ℕ → Ω → ℝ) (alpha : ℝ) : Prop :=
  ManyInstrumentsLIMLEigenvalueLimitConditions μ limlMuHat alpha

/-- The sharply named Theorem 12.19 LIML eigenvalue certificate is exactly the
existing many-instrument eigenvalue limit-condition package. -/
theorem manyInstrumentsLIMLEigenvalueAlphaOverOneMinusAlphaCertificate_iff_limitConditions
    {limlMuHat : ℕ → Ω → ℝ} {alpha : ℝ} :
    ManyInstrumentsLIMLEigenvalueAlphaOverOneMinusAlphaCertificate
        μ limlMuHat alpha ↔
      ManyInstrumentsLIMLEigenvalueLimitConditions μ limlMuHat alpha :=
  Iff.rfl

/-- Convert the many-instrument LIML eigenvalue-adjustment limit package into
the LIML zero-score moment package, once the OLS and projected-2SLS moment
limits are available.

This is a named bridge from the theorem-facing eigenvalue certificate to the
existing LIML cancellation theorem. -/
theorem ManyInstrumentsLIMLEigenvalueLimitConditions.toLIMLMomentConsistencyConditions_posDef
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ} {alpha : ℝ}
    (hmu : ManyInstrumentsLIMLEigenvalueLimitConditions μ limlMuHat alpha)
    (hOLS : ManyInstrumentsOLSMomentLimitConditions μ X e (H + Sigma22) Sigma2e)
    (h2SLS : ManyInstrumentsLIMLMomentLimitConditions
      μ Z X e (fun _ _ => 0) (H + alpha • Sigma22) (alpha • Sigma2e))
    (halpha_lt_one : alpha < 1) (hH : H.PosDef) :
    ManyInstrumentsLIMLMomentConsistencyConditions μ Z X e limlMuHat H :=
  ManyInstrumentsLIMLMomentConsistencyConditions.of_ols_twoSLS_moments_mu_tendsto_posDef
    (μ := μ) (Z := Z) (X := X) (e := e) (limlMuHat := limlMuHat)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    hOLS h2SLS hmu.meas hmu.tendsto halpha_lt_one hH

/-- Reduced-form moment components sufficient to assemble the OLS moment package
used in Hansen Theorem 12.19.

This keeps the theorem-facing many-instrument assumptions closer to Hansen's
decomposition `X = ZΓ + u₂`: signal Gram, reduced-form error Gram, their
cross-Gram, and the two score components are primitive moment limits; the OLS
bread/score package is then derived. -/
structure ManyInstrumentsOLSMomentAssemblyConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Gamma : (m : ℕ) → Matrix (ι m) k ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (H Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) : Prop where
  reduced_form : ∀ (m : ℕ) (ω : Ω),
    X m ω = manyInstrumentSignal (Z m ω) (Gamma m) + u2 m ω
  gram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ
  score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => sampleCrossMoment (X m ω) (e m ω)) μ
  signal_gram_meas : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentSignalGram (Z m ω) (Gamma m)) μ
  reduced_error_gram_meas : ∀ m, AEStronglyMeasurable
    (fun ω => sampleGram (u2 m ω)) μ
  cross_gram_meas : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω)) μ
  signal_score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m)) (e m ω)) μ
  reduced_error_score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => sampleCrossMoment (u2 m ω) (e m ω)) μ
  signal_gram_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω => manyInstrumentSignalGram (Z m ω) (Gamma m))
    atTop (fun _ => H)
  reduced_error_gram_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω => sampleGram (u2 m ω))
    atTop (fun _ => Sigma22)
  cross_gram_tendsto_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω => manyInstrumentReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
    atTop (fun _ => (0 : Matrix k k ℝ))
  signal_score_tendsto_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m)) (e m ω))
    atTop (fun _ => (0 : k → ℝ))
  reduced_error_score_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω => sampleCrossMoment (u2 m ω) (e m ω))
    atTop (fun _ => Sigma2e)
  limit_nonsing : IsUnit (H + Sigma22).det

/-- Build the OLS reduced-form assembly package with the OLS limit
nonsingularity discharged from Hansen's positive-definite signal limit and
positive-semidefinite reduced-form error covariance. -/
theorem ManyInstrumentsOLSMomentAssemblyConditions.of_components_posSemidef
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) + u2 m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (e m ω)) μ)
    (hsignal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentSignalGram (Z m ω) (Gamma m)) μ)
    (hreduced_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleGram (u2 m ω)) μ)
    (hcross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hsignal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m)) (e m ω)) μ)
    (hreduced_error_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (u2 m ω) (e m ω)) μ)
    (hsignal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hreduced_error_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => sampleGram (u2 m ω))
      atTop (fun _ => Sigma22))
    (hcross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hsignal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m)) (e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hreduced_error_score_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => sampleCrossMoment (u2 m ω) (e m ω))
      atTop (fun _ => Sigma2e))
    (hH : H.PosDef) (hSigma22 : Sigma22.PosSemidef) :
    ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e where
  reduced_form := hreduced
  gram_meas := hgram_meas
  score_meas := hscore_meas
  signal_gram_meas := hsignal_gram_meas
  reduced_error_gram_meas := hreduced_error_gram_meas
  cross_gram_meas := hcross_gram_meas
  signal_score_meas := hsignal_score_meas
  reduced_error_score_meas := hreduced_error_score_meas
  signal_gram_tendsto := hsignal_gram_tendsto
  reduced_error_gram_tendsto := hreduced_error_gram_tendsto
  cross_gram_tendsto_zero := hcross_gram_tendsto_zero
  signal_score_tendsto_zero := hsignal_score_tendsto_zero
  reduced_error_score_tendsto := hreduced_error_score_tendsto
  limit_nonsing :=
    manyInstruments_ols_limit_matrix_nonsingular_of_posSemidef hH hSigma22

/-- Named WLLN output for Hansen's OLS reduced-form decomposition in
Theorem 12.19.

This is the smallest current enforceable reduced-form package: it contains the
five component probability limits generated by `X = ZΓ + u₂`, the associated
measurability fields, and the positivity facts needed to derive OLS
nonsingularity.  Conditional homoskedasticity and fourth-moment hypotheses
should target this package rather than the downstream estimator limit. -/
structure ManyInstrumentsReducedFormWLLNConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Gamma : (m : ℕ) → Matrix (ι m) k ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (H Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) : Prop where
  reduced_form : ∀ (m : ℕ) (ω : Ω),
    X m ω = manyInstrumentSignal (Z m ω) (Gamma m) + u2 m ω
  gram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ
  score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => sampleCrossMoment (X m ω) (e m ω)) μ
  signal_gram_meas : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentSignalGram (Z m ω) (Gamma m)) μ
  reduced_error_gram_meas : ∀ m, AEStronglyMeasurable
    (fun ω => sampleGram (u2 m ω)) μ
  cross_gram_meas : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω)) μ
  signal_score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m)) (e m ω)) μ
  reduced_error_score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => sampleCrossMoment (u2 m ω) (e m ω)) μ
  signal_gram_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω => manyInstrumentSignalGram (Z m ω) (Gamma m))
    atTop (fun _ => H)
  reduced_error_gram_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω => sampleGram (u2 m ω))
    atTop (fun _ => Sigma22)
  cross_gram_tendsto_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω => manyInstrumentReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
    atTop (fun _ => (0 : Matrix k k ℝ))
  signal_score_tendsto_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m)) (e m ω))
    atTop (fun _ => (0 : k → ℝ))
  reduced_error_score_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω => sampleCrossMoment (u2 m ω) (e m ω))
    atTop (fun _ => Sigma2e)
  signal_limit_posDef : H.PosDef
  reduced_error_limit_posSemidef : Sigma22.PosSemidef

/-- Turn the named OLS reduced-form WLLN package into the existing assembly
package used by the 12.19 estimator constructors. -/
theorem ManyInstrumentsReducedFormWLLNConditions.toOLSMomentAssemblyConditions
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e) :
    ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e :=
  ManyInstrumentsOLSMomentAssemblyConditions.of_components_posSemidef
    (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    h.reduced_form h.gram_meas h.score_meas h.signal_gram_meas
    h.reduced_error_gram_meas h.cross_gram_meas h.signal_score_meas
    h.reduced_error_score_meas h.signal_gram_tendsto
    h.reduced_error_gram_tendsto h.cross_gram_tendsto_zero
    h.signal_score_tendsto_zero h.reduced_error_score_tendsto
    h.signal_limit_posDef h.reduced_error_limit_posSemidef

omit [DecidableEq k] in
/-- Construct the reduced-form WLLN package when the reduced-form errors and
structural error are ordinary stacked iid row sequences.

This discharges the two unprojected reduced-form WLLNs in Hansen Theorem 12.19
from the Chapter 7 WLLN layer. The signal Gram, signal-score, and signal-error
cross-Gram limits remain explicit because they involve the sample-size-dependent
instrument space and first-stage coefficient sequence. -/
theorem ManyInstrumentsReducedFormWLLNConditions.of_stacked_error_wlln
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hsignal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentSignalGram (Z m ω) (Gamma m)) μ)
    (hcross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentReducedFormCrossGram
        (Z m ω) (Gamma m) (stackRegressors u2 m ω)) μ)
    (hsignal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m))
          (stackErrors e m ω)) μ)
    (hsignal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hcross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentReducedFormCrossGram
          (Z m ω) (Gamma m) (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hsignal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m))
          (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hint_outer : Integrable (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hindep_outer :
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))))
    (hident_outer : ∀ i,
      IdentDistrib
        (fun ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))
        (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hint_cross : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hindep_cross :
      Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • u2 i ω)))
    (hident_cross : ∀ i,
      IdentDistrib
        (fun ω => e i ω • u2 i ω)
        (fun ω => e 0 ω • u2 0 ω) μ μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef) :
    ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H Sigma22 Sigma2e where
  reduced_form := hreduced
  gram_meas := hgram_meas
  score_meas := hscore_meas
  signal_gram_meas := hsignal_gram_meas
  reduced_error_gram_meas :=
    fun m => sampleGram_stackRegressors_aestronglyMeasurable_of_wlln
      (μ := μ) (X := u2) ⟨hindep_outer, hident_outer, hint_outer⟩ m
  cross_gram_meas := hcross_gram_meas
  signal_score_meas := hsignal_score_meas
  reduced_error_score_meas :=
    fun m => sampleCrossMoment_stack_aestronglyMeasurable_of_wlln
      (μ := μ) (X := u2) (e := e) hint_cross hident_cross m
  signal_gram_tendsto := hsignal_gram_tendsto
  reduced_error_gram_tendsto := by
    simpa [hSigma22] using
      sampleGram_stackRegressors_tendstoInMeasure_popGram_of_wlln
        (μ := μ) (X := u2) ⟨hindep_outer, hident_outer, hint_outer⟩
  cross_gram_tendsto_zero := hcross_gram_tendsto_zero
  signal_score_tendsto_zero := hsignal_score_tendsto_zero
  reduced_error_score_tendsto := by
    simpa [hSigma2e] using
      sampleCrossMoment_stack_tendstoInMeasure_integral
        (μ := μ) (X := u2) (e := e) hint_cross hindep_cross hident_cross
  signal_limit_posDef := hH
  reduced_error_limit_posSemidef := hSigma22_psd

omit [DecidableEq k] in
/-- Primitive instrument-side WLLN inputs for Hansen Theorem 12.19.

Because the instrument index type `ι m` changes with the sample size, raw
objects such as `Q̂_ZZ : Matrix (ι m) (ι m) ℝ` do not have a fixed codomain in
which to state convergence.  Hansen's proof only needs the fixed-dimensional
transforms `Γ'Q̂_ZZΓ`, the symmetrized `Γ'Q̂_Zu₂`, and `Γ'(n⁻¹Z'e)`, so this
package names exactly those primitive instrument-moment WLLNs instead of the
downstream composite signal WLLNs. -/
structure ManyInstrumentsPrimitiveInstrumentMomentWLLNConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (Gamma : (m : ℕ) → Matrix (ι m) k ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (H : Matrix k k ℝ) : Prop where
  qzz_signal_gram_meas : ∀ m, AEStronglyMeasurable
    (fun ω => (Gamma m)ᵀ * sampleQZZ (Z m ω) * Gamma m) μ
  qzu2_cross_gram_meas : ∀ m, AEStronglyMeasurable
    (fun ω =>
      (Gamma m)ᵀ * sampleQZX (Z m ω) (u2 m ω) +
        ((Gamma m)ᵀ * sampleQZX (Z m ω) (u2 m ω))ᵀ) μ
  ze_signal_score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => (Gamma m)ᵀ *ᵥ sampleCrossMoment (Z m ω) (e m ω)) μ
  qzz_signal_gram_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω => (Gamma m)ᵀ * sampleQZZ (Z m ω) * Gamma m)
    atTop (fun _ => H)
  qzu2_cross_gram_tendsto_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      (Gamma m)ᵀ * sampleQZX (Z m ω) (u2 m ω) +
        ((Gamma m)ᵀ * sampleQZX (Z m ω) (u2 m ω))ᵀ)
    atTop (fun _ => (0 : Matrix k k ℝ))
  ze_signal_score_tendsto_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω => (Gamma m)ᵀ *ᵥ sampleCrossMoment (Z m ω) (e m ω))
    atTop (fun _ => (0 : k → ℝ))

omit [Fintype k] [DecidableEq k] in
/-- Symmetrized row cross product `x u' + u x'` used in the many-instrument
cross-Gram WLLN. -/
noncomputable def manyInstrumentSymCrossRow (x u : k → ℝ) : Matrix k k ℝ :=
  Matrix.vecMulVec x u + (Matrix.vecMulVec x u)ᵀ

omit [DecidableEq k] in
private lemma measurable_manyInstrumentSymCrossRow_joint :
    Measurable
      (fun z : ((k → ℝ) × (k → ℝ)) × ℝ =>
        manyInstrumentSymCrossRow z.1.1 z.1.2) := by
  have hx : Continuous
      (fun z : ((k → ℝ) × (k → ℝ)) × ℝ => z.1.1) :=
    continuous_fst.comp continuous_fst
  have hu : Continuous
      (fun z : ((k → ℝ) × (k → ℝ)) × ℝ => z.1.2) :=
    continuous_snd.comp continuous_fst
  have houter : Continuous
      (fun z : ((k → ℝ) × (k → ℝ)) × ℝ =>
        Matrix.vecMulVec z.1.1 z.1.2) :=
    Continuous.matrix_vecMulVec hx hu
  have htranspose : Continuous
      (fun z : ((k → ℝ) × (k → ℝ)) × ℝ =>
        (Matrix.vecMulVec z.1.1 z.1.2)ᵀ) :=
    houter.matrix_transpose
  simpa [manyInstrumentSymCrossRow] using
    (houter.add htranspose).measurable

omit [Fintype k] [DecidableEq k] in
private lemma measurable_manyInstrumentCompressedSignal_joint :
    Measurable
      (fun z : ((k → ℝ) × (k → ℝ)) × ℝ => z.1.1) :=
  measurable_fst.comp measurable_fst

omit [Fintype k] [DecidableEq k] in
private lemma measurable_manyInstrumentSignalScore_joint :
    Measurable
      (fun z : ((k → ℝ) × (k → ℝ)) × ℝ => z.2 • z.1.1) := by
  rw [measurable_pi_iff]
  intro a
  have he : Measurable (fun z : ((k → ℝ) × (k → ℝ)) × ℝ => z.2) :=
    measurable_snd
  have hxa : Measurable
      (fun z : ((k → ℝ) × (k → ℝ)) × ℝ => z.1.1 a) :=
    ((measurable_pi_apply a).comp measurable_fst).comp measurable_fst
  simpa [Pi.smul_apply] using he.mul hxa

omit [DecidableEq k] in
private lemma measurable_manyInstrumentReducedErrorOuter_joint :
    Measurable
      (fun z : ((k → ℝ) × (k → ℝ)) × ℝ =>
        Matrix.vecMulVec z.1.2 z.1.2) := by
  have hu : Continuous
      (fun z : ((k → ℝ) × (k → ℝ)) × ℝ => z.1.2) :=
    continuous_snd.comp continuous_fst
  exact (Continuous.matrix_vecMulVec hu hu).measurable

omit [Fintype k] [DecidableEq k] in
private lemma measurable_manyInstrumentReducedErrorScore_joint :
    Measurable
      (fun z : ((k → ℝ) × (k → ℝ)) × ℝ => z.2 • z.1.2) := by
  rw [measurable_pi_iff]
  intro a
  have he : Measurable (fun z : ((k → ℝ) × (k → ℝ)) × ℝ => z.2) :=
    measurable_snd
  have hua : Measurable
      (fun z : ((k → ℝ) × (k → ℝ)) × ℝ => z.1.2 a) :=
    ((measurable_pi_apply a).comp measurable_snd).comp measurable_fst
  simpa [Pi.smul_apply] using he.mul hua

omit [Fintype k] [DecidableEq k] in
private theorem manyInstrumentReducedFormCrossGram_core_eq_avg_symCross
    {n : Type*} [Fintype n]
    (S U : Matrix n k ℝ) :
    (Fintype.card n : ℝ)⁻¹ • (Sᵀ * U + Uᵀ * S) =
      (Fintype.card n : ℝ)⁻¹ •
        ∑ i : n, manyInstrumentSymCrossRow (S i) (U i) := by
  have hsum : Sᵀ * U + Uᵀ * S =
      ∑ i : n, manyInstrumentSymCrossRow (S i) (U i) := by
    ext a b
    simp [manyInstrumentSymCrossRow, Matrix.mul_apply, Matrix.add_apply,
      Matrix.sum_apply, Matrix.vecMulVec_apply, Finset.sum_add_distrib, mul_comm]
  rw [hsum]

omit [Fintype k] [DecidableEq k] in
private theorem manyInstrumentReducedFormCrossGram_eq_avg_symCross_of_signal
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq l]
    (Z : Matrix n l ℝ) (Gamma : Matrix l k ℝ) (U S : Matrix n k ℝ)
    (hS : manyInstrumentSignal Z Gamma = S) :
    manyInstrumentReducedFormCrossGram Z Gamma U =
      (Fintype.card n : ℝ)⁻¹ •
        ∑ i : n, manyInstrumentSymCrossRow (S i) (U i) := by
  rw [manyInstrumentReducedFormCrossGram, hS]
  exact manyInstrumentReducedFormCrossGram_core_eq_avg_symCross S U

omit [DecidableEq k] in
/-- Fixed-codomain compressed-signal WLLN inputs for Hansen Theorem 12.19.

The raw instrument dimension `ι m` varies with `m`, so Chapter 7's ordinary
WLLN cannot directly apply to `Q̂_ZZ`.  When the theorem user has already
identified the compressed signal `ZΓ` with a fixed `k`-dimensional stacked row
sequence, this package derives the transformed primitive instrument WLLNs from
ordinary Chapter 7 WLLNs for that compressed signal, its cross product with
`u₂`, and its score against `e`. -/
structure ManyInstrumentsCompressedSignalWLLNConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (Gamma : (m : ℕ) → Matrix (ι m) k ℝ)
    (signal : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ)
    (u2 : ℕ → Ω → k → ℝ)
    (H : Matrix k k ℝ) : Prop where
  compressed_signal : ∀ (m : ℕ) (ω : Ω),
    manyInstrumentSignal (Z m ω) (Gamma m) = stackRegressors signal m ω
  signal_gram_wlln : SampleGramWLLNConditions μ signal
  signal_gram_limit : H = popGram μ signal
  sym_cross_integrable : Integrable
    (fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)) μ
  sym_cross_indep :
    Pairwise ((· ⟂ᵢ[μ] ·) on
      (fun i ω => manyInstrumentSymCrossRow (signal i ω) (u2 i ω)))
  sym_cross_ident : ∀ i,
    IdentDistrib
      (fun ω => manyInstrumentSymCrossRow (signal i ω) (u2 i ω))
      (fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)) μ μ
  sym_cross_mean_zero :
    μ[fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)] = 0
  signal_score_integrable : Integrable (fun ω => e 0 ω • signal 0 ω) μ
  signal_score_indep :
    Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • signal i ω))
  signal_score_ident : ∀ i,
    IdentDistrib
      (fun ω => e i ω • signal i ω)
      (fun ω => e 0 ω • signal 0 ω) μ μ
  signal_score_mean_zero : μ[fun ω => e 0 ω • signal 0 ω] = 0

omit [DecidableEq k] in
/-- IID fixed-codomain compressed rows supply the compressed-signal WLLN package
used in Hansen Theorem 12.19.

This constructor reduces the transformed-instrument WLLN input to one ordinary
joint iid row process `((ZΓ)_i, u₂ᵢ, eᵢ)`.  Chapter 7's finite-second WLLN
constructs the compressed signal Gram, while independence and identical
distribution for the symmetrized signal-error cross row and signal score are
obtained by measurable composition from the same joint iid primitive. -/
theorem ManyInstrumentsCompressedSignalWLLNConditions.of_iid_compressed_signal
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {signal : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {H : Matrix k k ℝ}
    (hcompressed : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentSignal (Z m ω) (Gamma m) = stackRegressors signal m ω)
    (hsignal_meas : ∀ i, AEStronglyMeasurable (signal i) μ)
    (hjoint_indep : iIndepFun
      (fun i ω => ((signal i ω, u2 i ω), e i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => ((signal i ω, u2 i ω), e i ω))
        (fun ω => ((signal 0 ω, u2 0 ω), e 0 ω)) μ μ)
    (hsignal_norm_sq : Integrable (fun ω => ‖signal 0 ω‖ ^ 2) μ)
    (hsignal_gram_limit : H = popGram μ signal)
    (hsym_cross_integrable : Integrable
      (fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)) μ)
    (hsym_cross_mean_zero :
      μ[fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)] = 0)
    (hsignal_score_integrable : Integrable (fun ω => e 0 ω • signal 0 ω) μ)
    (hsignal_score_mean_zero : μ[fun ω => e 0 ω • signal 0 ω] = 0) :
    ManyInstrumentsCompressedSignalWLLNConditions
      μ Z Gamma signal e u2 H where
  compressed_signal := hcompressed
  signal_gram_wlln := by
    refine SampleGramWLLNConditions.of_iid_finite_second
      (μ := μ) (X := signal) hsignal_meas ?_ ?_ hsignal_norm_sq
    · simpa [Function.comp] using
        hjoint_indep.comp
          (fun (_ : ℕ) (z : ((k → ℝ) × (k → ℝ)) × ℝ) => z.1.1)
          (fun (_ : ℕ) => measurable_manyInstrumentCompressedSignal_joint)
    · intro i
      simpa [Function.comp] using
        (hjoint_ident i).comp measurable_manyInstrumentCompressedSignal_joint
  signal_gram_limit := hsignal_gram_limit
  sym_cross_integrable := hsym_cross_integrable
  sym_cross_indep := by
    have hindep : iIndepFun
        (fun i ω => manyInstrumentSymCrossRow (signal i ω) (u2 i ω)) μ := by
      simpa [Function.comp] using
        hjoint_indep.comp
          (fun (_ : ℕ) (z : ((k → ℝ) × (k → ℝ)) × ℝ) =>
            manyInstrumentSymCrossRow z.1.1 z.1.2)
          (fun (_ : ℕ) => measurable_manyInstrumentSymCrossRow_joint)
    intro i j hij
    exact hindep.indepFun hij
  sym_cross_ident := by
    intro i
    simpa [Function.comp] using
      (hjoint_ident i).comp measurable_manyInstrumentSymCrossRow_joint
  sym_cross_mean_zero := hsym_cross_mean_zero
  signal_score_integrable := hsignal_score_integrable
  signal_score_indep := by
    have hindep : iIndepFun (fun i ω => e i ω • signal i ω) μ := by
      simpa [Function.comp] using
        hjoint_indep.comp
          (fun (_ : ℕ) (z : ((k → ℝ) × (k → ℝ)) × ℝ) => z.2 • z.1.1)
          (fun (_ : ℕ) => measurable_manyInstrumentSignalScore_joint)
    intro i j hij
    exact hindep.indepFun hij
  signal_score_ident := by
    intro i
    simpa [Function.comp] using
      (hjoint_ident i).comp measurable_manyInstrumentSignalScore_joint
  signal_score_mean_zero := hsignal_score_mean_zero

omit [DecidableEq k] in
theorem
    ManyInstrumentsCompressedSignalWLLNConditions.toPrimitiveInstrumentMomentWLLNConditions
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {signal : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {H : Matrix k k ℝ}
    (h : ManyInstrumentsCompressedSignalWLLNConditions
      μ Z Gamma signal e u2 H) :
    ManyInstrumentsPrimitiveInstrumentMomentWLLNConditions
      μ Z Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H := by
  let C : ℕ → Ω → Matrix k k ℝ := fun i ω =>
    manyInstrumentSymCrossRow (signal i ω) (u2 i ω)
  have hcross_meas_avg : ∀ m : ℕ, AEStronglyMeasurable
      (fun ω => (m : ℝ)⁻¹ • ∑ i : Fin m, C i.val ω) μ := by
    intro m
    refine AEStronglyMeasurable.const_smul ?_ ((m : ℝ)⁻¹)
    refine Finset.aestronglyMeasurable_fun_sum _ (fun i _ => ?_)
    exact ((h.sym_cross_ident i.val).integrable_iff.mpr
      h.sym_cross_integrable).aestronglyMeasurable
  have hcross_wlln_range : TendstoInMeasure μ
      (fun (m : ℕ) ω => (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, C i ω)
      atTop (fun _ => (0 : Matrix k k ℝ)) := by
    have hraw := tendstoInMeasure_wlln
      (μ := μ) C h.sym_cross_integrable h.sym_cross_indep h.sym_cross_ident
    simpa [C, h.sym_cross_mean_zero] using hraw
  have hcross_wlln_fin : TendstoInMeasure μ
      (fun (m : ℕ) ω => (m : ℝ)⁻¹ • ∑ i : Fin m, C i.val ω)
      atTop (fun _ => (0 : Matrix k k ℝ)) := by
    refine TendstoInMeasure.congr (fun m => ?_) EventuallyEq.rfl hcross_wlln_range
    exact ae_of_all μ fun ω => by
      simpa using congrArg (fun M : Matrix k k ℝ => (m : ℝ)⁻¹ • M)
        ((Fin.sum_univ_eq_sum_range (fun i => C i ω) m).symm)
  refine
    { qzz_signal_gram_meas := ?_
      qzu2_cross_gram_meas := ?_
      ze_signal_score_meas := ?_
      qzz_signal_gram_tendsto := ?_
      qzu2_cross_gram_tendsto_zero := ?_
      ze_signal_score_tendsto_zero := ?_ }
  · intro m
    have hstack := sampleGram_stackRegressors_aestronglyMeasurable_of_wlln
      (μ := μ) (X := signal) h.signal_gram_wlln m
    exact hstack.congr (ae_of_all μ fun ω => by
      calc
        sampleGram (stackRegressors signal m ω) =
            manyInstrumentSignalGram (Z m ω) (Gamma m) := by
          simp [manyInstrumentSignalGram, h.compressed_signal m ω]
        _ = (Gamma m)ᵀ * sampleQZZ (Z m ω) * Gamma m := by
          exact manyInstrumentSignalGram_eq_Gamma_transpose_sampleQZZ_mul_Gamma
            (Z m ω) (Gamma m))
  · intro m
    exact (hcross_meas_avg m).congr (ae_of_all μ fun ω => by
      calc
        (m : ℝ)⁻¹ • ∑ i : Fin m, C i.val ω =
            manyInstrumentReducedFormCrossGram
              (Z m ω) (Gamma m) (stackRegressors u2 m ω) := by
          rw [manyInstrumentReducedFormCrossGram_eq_avg_symCross_of_signal
            (Z m ω) (Gamma m) (stackRegressors u2 m ω)
            (stackRegressors signal m ω) (h.compressed_signal m ω)]
          rw [Fintype.card_fin]
          apply congrArg (fun M : Matrix k k ℝ => (m : ℝ)⁻¹ • M)
          refine Finset.sum_congr rfl ?_
          intro i _
          ext a b
          simp [C, manyInstrumentSymCrossRow, stackRegressors,
            Matrix.vecMulVec_apply]
        _ = (Gamma m)ᵀ * sampleQZX (Z m ω) (stackRegressors u2 m ω) +
            ((Gamma m)ᵀ * sampleQZX (Z m ω) (stackRegressors u2 m ω))ᵀ := by
          exact manyInstrumentReducedFormCrossGram_eq_Gamma_transpose_sampleQZX
            (Z m ω) (Gamma m) (stackRegressors u2 m ω))
  · intro m
    have hstack := sampleCrossMoment_stack_aestronglyMeasurable_of_wlln
      (μ := μ) (X := signal) (e := e)
      h.signal_score_integrable h.signal_score_ident m
    exact hstack.congr (ae_of_all μ fun ω => by
      calc
        sampleCrossMoment (stackRegressors signal m ω) (stackErrors e m ω) =
            sampleCrossMoment
              (manyInstrumentSignal (Z m ω) (Gamma m)) (stackErrors e m ω) := by
          simp [h.compressed_signal m ω]
        _ = (Gamma m)ᵀ *ᵥ sampleCrossMoment (Z m ω) (stackErrors e m ω) := by
          exact sampleCrossMoment_manyInstrumentSignal_eq_Gamma_transpose_sampleCrossMoment
            (Z m ω) (Gamma m) (stackErrors e m ω))
  · have hstack : TendstoInMeasure μ
        (fun m ω => sampleGram (stackRegressors signal m ω))
        atTop (fun _ => H) := by
      simpa [h.signal_gram_limit] using
        sampleGram_stackRegressors_tendstoInMeasure_popGram_of_wlln
          (μ := μ) (X := signal) h.signal_gram_wlln
    refine TendstoInMeasure.congr (fun m => ?_) EventuallyEq.rfl hstack
    exact ae_of_all μ fun ω => by
      calc
        sampleGram (stackRegressors signal m ω) =
            manyInstrumentSignalGram (Z m ω) (Gamma m) := by
          simp [manyInstrumentSignalGram, h.compressed_signal m ω]
        _ = (Gamma m)ᵀ * sampleQZZ (Z m ω) * Gamma m := by
          exact manyInstrumentSignalGram_eq_Gamma_transpose_sampleQZZ_mul_Gamma
            (Z m ω) (Gamma m)
  · refine TendstoInMeasure.congr (fun m => ?_) EventuallyEq.rfl hcross_wlln_fin
    exact ae_of_all μ fun ω => by
      calc
        (m : ℝ)⁻¹ • ∑ i : Fin m, C i.val ω =
            manyInstrumentReducedFormCrossGram
              (Z m ω) (Gamma m) (stackRegressors u2 m ω) := by
          rw [manyInstrumentReducedFormCrossGram_eq_avg_symCross_of_signal
            (Z m ω) (Gamma m) (stackRegressors u2 m ω)
            (stackRegressors signal m ω) (h.compressed_signal m ω)]
          rw [Fintype.card_fin]
          apply congrArg (fun M : Matrix k k ℝ => (m : ℝ)⁻¹ • M)
          refine Finset.sum_congr rfl ?_
          intro i _
          ext a b
          simp [C, manyInstrumentSymCrossRow, stackRegressors,
            Matrix.vecMulVec_apply]
        _ = (Gamma m)ᵀ * sampleQZX (Z m ω) (stackRegressors u2 m ω) +
            ((Gamma m)ᵀ * sampleQZX (Z m ω) (stackRegressors u2 m ω))ᵀ := by
          exact manyInstrumentReducedFormCrossGram_eq_Gamma_transpose_sampleQZX
            (Z m ω) (Gamma m) (stackRegressors u2 m ω)
  · have hscore : TendstoInMeasure μ
        (fun m ω => sampleCrossMoment (stackRegressors signal m ω) (stackErrors e m ω))
        atTop (fun _ => (0 : k → ℝ)) := by
      have hraw := sampleCrossMoment_stack_tendstoInMeasure_integral
        (μ := μ) (X := signal) (e := e)
        h.signal_score_integrable h.signal_score_indep h.signal_score_ident
      simpa [h.signal_score_mean_zero] using hraw
    refine TendstoInMeasure.congr (fun m => ?_) EventuallyEq.rfl hscore
    exact ae_of_all μ fun ω => by
      calc
        sampleCrossMoment (stackRegressors signal m ω) (stackErrors e m ω) =
            sampleCrossMoment
              (manyInstrumentSignal (Z m ω) (Gamma m)) (stackErrors e m ω) := by
          simp [h.compressed_signal m ω]
        _ = (Gamma m)ᵀ *ᵥ sampleCrossMoment (Z m ω) (stackErrors e m ω) := by
          exact sampleCrossMoment_manyInstrumentSignal_eq_Gamma_transpose_sampleCrossMoment
            (Z m ω) (Gamma m) (stackErrors e m ω)

omit [DecidableEq k] in
/-- Primitive transformed-instrument WLLNs from a fixed-dimensional iid
compressed row process.

This is the direct theorem-facing form of
`ManyInstrumentsCompressedSignalWLLNConditions.of_iid_compressed_signal`
followed by
`ManyInstrumentsCompressedSignalWLLNConditions.toPrimitiveInstrumentMomentWLLNConditions`.
It replaces the varying-dimension primitive moment package by enforceable
fixed-codomain iid assumptions on `(ZΓ, u₂, e)`. -/
theorem
ManyInstrumentsPrimitiveInstrumentMomentWLLNConditions.of_iid_compressed_signal
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {signal : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {H : Matrix k k ℝ}
    (hcompressed : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentSignal (Z m ω) (Gamma m) = stackRegressors signal m ω)
    (hsignal_meas : ∀ i, AEStronglyMeasurable (signal i) μ)
    (hjoint_indep : iIndepFun
      (fun i ω => ((signal i ω, u2 i ω), e i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => ((signal i ω, u2 i ω), e i ω))
        (fun ω => ((signal 0 ω, u2 0 ω), e 0 ω)) μ μ)
    (hsignal_norm_sq : Integrable (fun ω => ‖signal 0 ω‖ ^ 2) μ)
    (hsignal_gram_limit : H = popGram μ signal)
    (hsym_cross_integrable : Integrable
      (fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)) μ)
    (hsym_cross_mean_zero :
      μ[fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)] = 0)
    (hsignal_score_integrable : Integrable (fun ω => e 0 ω • signal 0 ω) μ)
    (hsignal_score_mean_zero : μ[fun ω => e 0 ω • signal 0 ω] = 0) :
    ManyInstrumentsPrimitiveInstrumentMomentWLLNConditions
      μ Z Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H :=
  (ManyInstrumentsCompressedSignalWLLNConditions.of_iid_compressed_signal
    (μ := μ) (Z := Z) (Gamma := Gamma) (signal := signal) (e := e)
    (u2 := u2) (H := H)
    hcompressed hsignal_meas hjoint_indep hjoint_ident hsignal_norm_sq
    hsignal_gram_limit hsym_cross_integrable hsym_cross_mean_zero
    hsignal_score_integrable
    hsignal_score_mean_zero).toPrimitiveInstrumentMomentWLLNConditions

omit [DecidableEq k] in
/-- Construct the reduced-form WLLN package from primitive instrument-moment
WLLNs plus the Chapter 7 stacked-row WLLNs for the reduced-form errors.

Compared with `ManyInstrumentsReducedFormWLLNConditions.of_stacked_error_wlln`,
this constructor does not ask for WLLNs of the composite signal objects
`ZΓ` directly.  It derives them from the deterministic bridges
`n⁻¹Γ'Z'ZΓ = Γ'Q̂_ZZΓ`, the symmetrized `Γ'Q̂_Zu₂`, and
`n⁻¹Γ'Z'e = Γ'(n⁻¹Z'e)`. -/
theorem ManyInstrumentsReducedFormWLLNConditions.of_stacked_error_instrument_moment_wlln
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hinstrument_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => (Gamma m)ᵀ * sampleQZZ (Z m ω) * Gamma m) μ)
    (hinstrument_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        (Gamma m)ᵀ * sampleQZX (Z m ω) (stackRegressors u2 m ω) +
          ((Gamma m)ᵀ * sampleQZX (Z m ω) (stackRegressors u2 m ω))ᵀ) μ)
    (hinstrument_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        (Gamma m)ᵀ *ᵥ sampleCrossMoment (Z m ω) (stackErrors e m ω)) μ)
    (hinstrument_signal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => (Gamma m)ᵀ * sampleQZZ (Z m ω) * Gamma m)
      atTop (fun _ => H))
    (hinstrument_cross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        (Gamma m)ᵀ * sampleQZX (Z m ω) (stackRegressors u2 m ω) +
          ((Gamma m)ᵀ * sampleQZX (Z m ω) (stackRegressors u2 m ω))ᵀ)
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hinstrument_signal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        (Gamma m)ᵀ *ᵥ sampleCrossMoment (Z m ω) (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hint_outer : Integrable (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hindep_outer :
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))))
    (hident_outer : ∀ i,
      IdentDistrib
        (fun ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))
        (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hint_cross : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hindep_cross :
      Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • u2 i ω)))
    (hident_cross : ∀ i,
      IdentDistrib
        (fun ω => e i ω • u2 i ω)
        (fun ω => e 0 ω • u2 0 ω) μ μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef) :
    ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H Sigma22 Sigma2e := by
  let hsignal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentSignalGram (Z m ω) (Gamma m)) μ := by
    intro m
    exact (hinstrument_signal_gram_meas m).congr
      (ae_of_all μ fun ω =>
        (manyInstrumentSignalGram_eq_Gamma_transpose_sampleQZZ_mul_Gamma
          (Z m ω) (Gamma m)).symm)
  let hcross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentReducedFormCrossGram
          (Z m ω) (Gamma m) (stackRegressors u2 m ω)) μ := by
    intro m
    exact (hinstrument_cross_gram_meas m).congr
      (ae_of_all μ fun ω =>
        (manyInstrumentReducedFormCrossGram_eq_Gamma_transpose_sampleQZX
          (Z m ω) (Gamma m) (stackRegressors u2 m ω)).symm)
  let hsignal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m))
          (stackErrors e m ω)) μ := by
    intro m
    exact (hinstrument_signal_score_meas m).congr
      (ae_of_all μ fun ω =>
        (sampleCrossMoment_manyInstrumentSignal_eq_Gamma_transpose_sampleCrossMoment
          (Z m ω) (Gamma m) (stackErrors e m ω)).symm)
  let hsignal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H) :=
    TendstoInMeasure.congr
      (fun m => ae_of_all μ fun ω =>
        (manyInstrumentSignalGram_eq_Gamma_transpose_sampleQZZ_mul_Gamma
          (Z m ω) (Gamma m)).symm)
      EventuallyEq.rfl hinstrument_signal_gram_tendsto
  let hcross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentReducedFormCrossGram
          (Z m ω) (Gamma m) (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)) :=
    TendstoInMeasure.congr
      (fun m => ae_of_all μ fun ω =>
        (manyInstrumentReducedFormCrossGram_eq_Gamma_transpose_sampleQZX
          (Z m ω) (Gamma m) (stackRegressors u2 m ω)).symm)
      EventuallyEq.rfl hinstrument_cross_gram_tendsto_zero
  let hsignal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m))
          (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)) :=
    TendstoInMeasure.congr
      (fun m => ae_of_all μ fun ω =>
        (sampleCrossMoment_manyInstrumentSignal_eq_Gamma_transpose_sampleCrossMoment
          (Z m ω) (Gamma m) (stackErrors e m ω)).symm)
      EventuallyEq.rfl hinstrument_signal_score_tendsto_zero
  exact
    ManyInstrumentsReducedFormWLLNConditions.of_stacked_error_wlln
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      hreduced hgram_meas hscore_meas hsignal_gram_meas hcross_gram_meas
      hsignal_score_meas hsignal_gram_tendsto hcross_gram_tendsto_zero
      hsignal_score_tendsto_zero hint_outer hindep_outer hident_outer hSigma22
      hint_cross hindep_cross hident_cross hSigma2e hH hSigma22_psd

omit [DecidableEq k] in
/-- Construct the reduced-form WLLN package from the named primitive
instrument-side WLLN package plus Chapter 7 stacked-row WLLNs for the
reduced-form errors.

This is the preferred theorem-facing bridge for Hansen's `Q̂_ZZ`, `Q̂_Zu₂`,
and `n⁻¹Z'e` inputs: the varying instrument dimension is confined to
`ManyInstrumentsPrimitiveInstrumentMomentWLLNConditions`, while the resulting
reduced-form package has the fixed `k × k` and `k` limits used by the estimator
proofs. -/
theorem
ManyInstrumentsReducedFormWLLNConditions.of_stacked_error_primitive_instrument_moment_wlln
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hinst : ManyInstrumentsPrimitiveInstrumentMomentWLLNConditions
      μ Z Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H)
    (hint_outer : Integrable (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hindep_outer :
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))))
    (hident_outer : ∀ i,
      IdentDistrib
        (fun ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))
        (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hint_cross : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hindep_cross :
      Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • u2 i ω)))
    (hident_cross : ∀ i,
      IdentDistrib
        (fun ω => e i ω • u2 i ω)
        (fun ω => e 0 ω • u2 0 ω) μ μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef) :
    ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H Sigma22 Sigma2e :=
  ManyInstrumentsReducedFormWLLNConditions.of_stacked_error_instrument_moment_wlln
    (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    hreduced hgram_meas hscore_meas
    hinst.qzz_signal_gram_meas hinst.qzu2_cross_gram_meas
    hinst.ze_signal_score_meas hinst.qzz_signal_gram_tendsto
    hinst.qzu2_cross_gram_tendsto_zero hinst.ze_signal_score_tendsto_zero
    hint_outer hindep_outer hident_outer hSigma22 hint_cross hindep_cross
    hident_cross hSigma2e hH hSigma22_psd

/-- Assemble the OLS moment-limit package from Hansen's many-instrument
reduced-form moment components. -/
theorem ManyInstrumentsOLSMomentLimitConditions.of_reduced_form_components
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e) :
    ManyInstrumentsOLSMomentLimitConditions μ X e (H + Sigma22) Sigma2e := by
  refine
    { gram_meas := h.gram_meas
      score_meas := h.score_meas
      gram_tendsto := ?_
      score_tendsto := ?_
      limit_nonsing := h.limit_nonsing }
  · have hsignal_plus_error : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          manyInstrumentSignalGram (Z m ω) (Gamma m) + sampleGram (u2 m ω))
        atTop (fun _ => H + Sigma22) :=
      tendstoInMeasure_add h.signal_gram_meas h.reduced_error_gram_meas
        h.signal_gram_tendsto h.reduced_error_gram_tendsto
    have htotal : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          manyInstrumentSignalGram (Z m ω) (Gamma m) + sampleGram (u2 m ω) +
            manyInstrumentReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
        atTop (fun _ => H + Sigma22 + (0 : Matrix k k ℝ)) :=
      tendstoInMeasure_add
        (fun m => (h.signal_gram_meas m).add (h.reduced_error_gram_meas m))
        h.cross_gram_meas hsignal_plus_error h.cross_gram_tendsto_zero
    refine TendstoInMeasure.congr' ?_ ?_ htotal
    · filter_upwards [eventually_gt_atTop 0] with m hm
      exact ae_of_all μ (fun ω => by
        haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
        change
          manyInstrumentSignalGram (Z m ω) (Gamma m) + sampleGram (u2 m ω) +
              manyInstrumentReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω) =
            sampleGram (X m ω)
        rw [h.reduced_form m ω, manyInstrumentReducedForm_sampleGram])
    · exact ae_of_all μ (fun _ => by simp)
  · have hscore_sum : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m)) (e m ω) +
            sampleCrossMoment (u2 m ω) (e m ω))
        atTop (fun _ => (0 : k → ℝ) + Sigma2e) :=
      tendstoInMeasure_add h.signal_score_meas h.reduced_error_score_meas
        h.signal_score_tendsto_zero h.reduced_error_score_tendsto
    refine TendstoInMeasure.congr' ?_ ?_ hscore_sum
    · filter_upwards [eventually_gt_atTop 0] with m hm
      exact ae_of_all μ (fun ω => by
        haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
        change
          sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m)) (e m ω) +
              sampleCrossMoment (u2 m ω) (e m ω) =
            sampleCrossMoment (X m ω) (e m ω)
        rw [h.reduced_form m ω, manyInstrumentReducedForm_sampleCrossMoment])
    · exact ae_of_all μ (fun _ => by simp)

/-- Projected reduced-form moment components sufficient to assemble the 2SLS
moment package used in Hansen Theorem 12.19.

This is the `μ = 0` LIML/k-class face.  The primitive limits are the projected
signal Gram, projected reduced-form-error Gram, projected cross-Gram, projected
signal score, and projected reduced-form-error score; the normalized 2SLS
bread/score package is then derived. -/
structure ManyInstrumentsTwoSLSMomentAssemblyConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Gamma : (m : ℕ) → Matrix (ι m) k ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (H Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) (alpha : ℝ) : Prop where
  reduced_form : ∀ (m : ℕ) (ω : Ω),
    X m ω = manyInstrumentSignal (Z m ω) (Gamma m) + u2 m ω
  moment_meas : ∀ m, AEStronglyMeasurable
    (fun ω => limlNormalizedMomentMatrixStar (Z m ω) (X m ω) 0) μ
  score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => limlNormalizedMomentVectorStar (Z m ω) (X m ω) (e m ω) 0) μ
  projected_signal_gram_meas : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ
  projected_error_gram_meas : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω)) μ
  projected_cross_gram_meas : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentProjectedReducedFormCrossGram
      (Z m ω) (Gamma m) (u2 m ω)) μ
  projected_signal_score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ
  projected_error_score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω)) μ
  projected_signal_gram_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m))
    atTop (fun _ => H)
  projected_error_gram_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω => manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω))
    atTop (fun _ => alpha • Sigma22)
  projected_cross_gram_tendsto_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      manyInstrumentProjectedReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
    atTop (fun _ => (0 : Matrix k k ℝ))
  projected_signal_score_tendsto_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω))
    atTop (fun _ => (0 : k → ℝ))
  projected_error_score_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω => manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω))
    atTop (fun _ => alpha • Sigma2e)
  limit_nonsing : IsUnit (H + alpha • Sigma22).det

/-- Lower-level projection-trace layer for the many-instrument 2SLS
projected-error moment consequences.

The primitive assumptions mirror Hansen's homoskedastic many-instrument
calculation: the projected error Gram/cross moments equal the projection trace
ratio times the unprojected reduced-form moments up to `o_p(1)` remainders,
and `n^{-1}tr(P_Z*) -> α`.  The theorem below turns these lower-level
projection-trace consequences into the projected-error fields required by the
existing 2SLS assembly package. -/
structure ManyInstrumentsProjectedTraceMomentConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) (alpha : ℝ) : Prop where
  trace_ratio_meas : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentProjectionTraceRatio (Z m ω)) μ
  reduced_error_gram_meas : ∀ m, AEStronglyMeasurable
    (fun ω => sampleGram (u2 m ω)) μ
  reduced_error_cross_meas : ∀ m, AEStronglyMeasurable
    (fun ω => sampleCrossMoment (u2 m ω) (e m ω)) μ
  projected_error_gram_meas : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω)) μ
  projected_error_cross_meas : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω)) μ
  trace_ratio_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω => manyInstrumentProjectionTraceRatio (Z m ω))
    atTop (fun _ => alpha)
  reduced_error_gram_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω => sampleGram (u2 m ω))
    atTop (fun _ => Sigma22)
  reduced_error_cross_tendsto : TendstoInMeasure μ
    (fun (m : ℕ) ω => sampleCrossMoment (u2 m ω) (e m ω))
    atTop (fun _ => Sigma2e)
  projected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω) -
        manyInstrumentProjectionTraceRatio (Z m ω) • sampleGram (u2 m ω))
    atTop (fun _ => (0 : Matrix k k ℝ))
  projected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω) -
        manyInstrumentProjectionTraceRatio (Z m ω) •
          sampleCrossMoment (u2 m ω) (e m ω))
    atTop (fun _ => (0 : k → ℝ))

/-- Homoskedastic projection-trace remainders left after the reduced-form WLLNs
and instrument trace ratio have been separated out.

Under Hansen's conditional homoskedasticity and bounded fourth moments, these
are the two projected-error remainder WLLNs that still require a triangular
array/projection proof in the current repo. -/
structure ManyInstrumentsHomoskedasticProjectionRemainderConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ) : Prop where
  trace_ratio_meas : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentProjectionTraceRatio (Z m ω)) μ
  projected_error_gram_meas : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω)) μ
  projected_error_cross_meas : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω)) μ
  projected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω) -
        manyInstrumentProjectionTraceRatio (Z m ω) • sampleGram (u2 m ω))
    atTop (fun _ => (0 : Matrix k k ℝ))
  projected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω) -
        manyInstrumentProjectionTraceRatio (Z m ω) •
          sampleCrossMoment (u2 m ω) (e m ω))
    atTop (fun _ => (0 : k → ℝ))

omit [Fintype k] [DecidableEq k] in
/-- Matrix-valued projected-error trace remainder in Hansen's many-instrument
homoskedastic calculation. -/
noncomputable def manyInstrumentProjectedErrorGramTraceRemainder
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (u2 : Matrix n k ℝ) : Matrix k k ℝ :=
  manyInstrumentProjectedErrorGram Z u2 -
    manyInstrumentProjectionTraceRatio Z • sampleGram u2

omit [Fintype k] [DecidableEq k] in
/-- Vector-valued projected-error score trace remainder in Hansen's
many-instrument homoskedastic calculation. -/
noncomputable def manyInstrumentProjectedErrorCrossTraceRemainder
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (u2 : Matrix n k ℝ) (e : n → ℝ) : k → ℝ :=
  manyInstrumentProjectedErrorCross Z u2 e -
    manyInstrumentProjectionTraceRatio Z • sampleCrossMoment u2 e

omit [Fintype k] [DecidableEq k] in
private theorem sampleGram_eq_average_vecMulVec
    {n : Type*} [Fintype n] (X : Matrix n k ℝ) :
    sampleGram X =
      (Fintype.card n : ℝ)⁻¹ • ∑ i : n, Matrix.vecMulVec (X i) (X i) := by
  ext a b
  by_cases hn : Fintype.card n = 0
  · simp [sampleGram, Matrix.smul_apply, hn]
  · simp [sampleGram, Matrix.mul_apply, Matrix.vecMulVec, Matrix.sum_apply,
      Matrix.smul_apply]

omit [Fintype k] [DecidableEq k] in
private theorem sampleCrossMoment_eq_average_rows
    {n : Type*} [Fintype n] (X : Matrix n k ℝ) (e : n → ℝ) :
    sampleCrossMoment X e =
      (Fintype.card n : ℝ)⁻¹ • ∑ i : n, e i • X i := by
  ext a
  by_cases hn : Fintype.card n = 0
  · simp [sampleCrossMoment, Pi.smul_apply, hn]
  · simp [sampleCrossMoment, Matrix.mulVec, dotProduct, Pi.smul_apply, mul_comm]

omit [Fintype k] [DecidableEq k] in
/-- Canonical matrix row contribution for the projected-error trace remainder.

This is the exact finite-sample row summand whose average is
`manyInstrumentProjectedErrorGramTraceRemainder`.  It separates the algebraic
row-identity step from the remaining homoskedastic triangular-array WLLN. -/
noncomputable def manyInstrumentProjectedErrorGramTraceRemainderCanonicalRow
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (u2 : Matrix n k ℝ) (i : n) : Matrix k k ℝ :=
  Matrix.vecMulVec ((instrumentProjectionStar Z * u2) i)
      ((instrumentProjectionStar Z * u2) i) -
    manyInstrumentProjectionTraceRatio Z • Matrix.vecMulVec (u2 i) (u2 i)

omit [Fintype k] [DecidableEq k] in
/-- Canonical vector row contribution for the projected-error score trace
remainder. -/
noncomputable def manyInstrumentProjectedErrorCrossTraceRemainderCanonicalRow
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (u2 : Matrix n k ℝ) (e : n → ℝ) (i : n) : k → ℝ :=
  e i • ((instrumentProjectionStar Z * u2) i) -
    manyInstrumentProjectionTraceRatio Z • (e i • u2 i)

omit [Fintype k] [DecidableEq k] in
/-- The projected-error Gram trace remainder is exactly the average of its
canonical finite-sample row contributions. -/
theorem manyInstrumentProjectedErrorGramTraceRemainder_eq_average_canonicalRow
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (u2 : Matrix n k ℝ) :
    manyInstrumentProjectedErrorGramTraceRemainder Z u2 =
      (Fintype.card n : ℝ)⁻¹ •
        ∑ i : n,
          manyInstrumentProjectedErrorGramTraceRemainderCanonicalRow Z u2 i := by
  rw [manyInstrumentProjectedErrorGramTraceRemainder,
    manyInstrumentProjectedErrorGram]
  rw [sampleGram_eq_average_vecMulVec (instrumentProjectionStar Z * u2),
    sampleGram_eq_average_vecMulVec u2]
  simp [manyInstrumentProjectedErrorGramTraceRemainderCanonicalRow,
    Finset.sum_sub_distrib, Finset.smul_sum, smul_sub, smul_smul, mul_comm]

omit [Fintype k] [DecidableEq k] in
/-- The projected-error score trace remainder is exactly the average of its
canonical finite-sample row contributions. -/
theorem manyInstrumentProjectedErrorCrossTraceRemainder_eq_average_canonicalRow
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (u2 : Matrix n k ℝ) (e : n → ℝ) :
    manyInstrumentProjectedErrorCrossTraceRemainder Z u2 e =
      (Fintype.card n : ℝ)⁻¹ •
        ∑ i : n,
          manyInstrumentProjectedErrorCrossTraceRemainderCanonicalRow Z u2 e i := by
  rw [manyInstrumentProjectedErrorCrossTraceRemainder,
    manyInstrumentProjectedErrorCross]
  rw [sampleCrossMoment_eq_average_rows (instrumentProjectionStar Z * u2) e,
    sampleCrossMoment_eq_average_rows u2 e]
  simp [manyInstrumentProjectedErrorCrossTraceRemainderCanonicalRow,
    Finset.sum_sub_distrib, Finset.smul_sum, smul_sub, smul_smul,
    mul_assoc, mul_left_comm, mul_comm]

omit [DecidableEq k] in
/-- Canonical row-average convergence inputs for Hansen's projected-error
trace remainders.

Unlike the more abstract scalar/row WLLN packages below, these fields use the
exact finite-sample row summands defined from `P_Z*`, `u₂`, and `e`.  The
remaining work is therefore the probabilistic homoskedastic projection WLLN for
these canonical averages, not an additional algebraic identification step. -/
structure ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ) : Prop where
  gram_average_tendsto_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      (Fintype.card (Fin m) : ℝ)⁻¹ •
        ∑ i : Fin m,
          manyInstrumentProjectedErrorGramTraceRemainderCanonicalRow
            (Z m ω) (u2 m ω) i)
    atTop (fun _ => (0 : Matrix k k ℝ))
  cross_average_tendsto_zero : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      (Fintype.card (Fin m) : ℝ)⁻¹ •
        ∑ i : Fin m,
          manyInstrumentProjectedErrorCrossTraceRemainderCanonicalRow
            (Z m ω) (u2 m ω) (e m ω) i)
    atTop (fun _ => (0 : k → ℝ))

omit [DecidableEq k] in
/-- Entrywise scalar WLLN certificates for the two projected-error trace
remainders.

This is a narrower proof target than the matrix/vector remainder fields in
`ManyInstrumentsHomoskedasticProjectionRemainderConditions`: each matrix entry
and vector coordinate can be proved as a scalar `o_p(1)` statement, and the
finite-dimensional assembly below supplies the full Hansen remainder package. -/
structure ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ) : Prop where
  gram_entry_tendsto_zero : ∀ a b : k, TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) a b)
    atTop (fun _ => 0)
  cross_entry_tendsto_zero : ∀ a : k, TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) a)
    atTop (fun _ => 0)

namespace ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions

omit [DecidableEq k] in
/-- Entrywise scalar projected-error trace WLLNs imply the matrix-valued Gram
remainder WLLN. -/
theorem gram_tendsto_zero
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    (h : ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
      μ Z e u2) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) • sampleGram (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)) := by
  refine tendstoInMeasure_pi (μ := μ) (fun a => ?_)
  refine tendstoInMeasure_pi (μ := μ) (fun b => ?_)
  simpa [manyInstrumentProjectedErrorGramTraceRemainder] using
    h.gram_entry_tendsto_zero a b

omit [DecidableEq k] in
/-- Entrywise scalar projected-error trace WLLNs imply the vector-valued score
remainder WLLN. -/
theorem cross_tendsto_zero
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    (h : ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
      μ Z e u2) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (u2 m ω) (e m ω))
      atTop (fun _ => (0 : k → ℝ)) := by
  refine tendstoInMeasure_pi (μ := μ) (fun a => ?_)
  simpa [manyInstrumentProjectedErrorCrossTraceRemainder] using
    h.cross_entry_tendsto_zero a

end ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions

namespace ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions

omit [DecidableEq k] in
/-- Canonical row-average convergence supplies the entrywise projected-error
trace-remainder WLLN package. -/
theorem toEntryWLLNConditions
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    (h : ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions
      μ Z e u2) :
    ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
      μ Z e u2 where
  gram_entry_tendsto_zero := by
    intro a b
    have hgram : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω))
        atTop (fun _ => (0 : Matrix k k ℝ)) := by
      refine TendstoInMeasure.congr (fun m => ?_) EventuallyEq.rfl
        h.gram_average_tendsto_zero
      exact ae_of_all μ fun ω =>
        (manyInstrumentProjectedErrorGramTraceRemainder_eq_average_canonicalRow
          (Z m ω) (u2 m ω)).symm
    exact TendstoInMeasure.pi_apply (TendstoInMeasure.pi_apply hgram a) b
  cross_entry_tendsto_zero := by
    intro a
    have hcross : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          manyInstrumentProjectedErrorCrossTraceRemainder
            (Z m ω) (u2 m ω) (e m ω))
        atTop (fun _ => (0 : k → ℝ)) := by
      refine TendstoInMeasure.congr (fun m => ?_) EventuallyEq.rfl
        h.cross_average_tendsto_zero
      exact ae_of_all μ fun ω =>
        (manyInstrumentProjectedErrorCrossTraceRemainder_eq_average_canonicalRow
          (Z m ω) (u2 m ω) (e m ω)).symm
    exact TendstoInMeasure.pi_apply hcross a

end ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions

omit [DecidableEq k] in
/-- Compatibility-only matrix/vector row WLLN inputs for projected remainders.

This generic implication is valid if such iid additive rows are independently
constructed. Hansen's projected quadratic forms do not supply them because
`P_Z` couples all observations. New theorem-facing work must use
`ManyInstrumentsProjectionQuadraticMeanSquareConditions`. -/
structure ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (gram_row : ℕ → Ω → Matrix k k ℝ)
    (cross_row : ℕ → Ω → k → ℝ) : Prop where
  gram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
    manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
      (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gram_row i ω
  cross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
    manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
      (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, cross_row i ω
  gram_integrable : Integrable (gram_row 0) μ
  gram_indep : Pairwise ((· ⟂ᵢ[μ] ·) on gram_row)
  gram_ident : ∀ i, IdentDistrib (gram_row i) (gram_row 0) μ μ
  gram_mean_zero : μ[gram_row 0] = 0
  cross_integrable : Integrable (cross_row 0) μ
  cross_indep : Pairwise ((· ⟂ᵢ[μ] ·) on cross_row)
  cross_ident : ∀ i, IdentDistrib (cross_row i) (cross_row 0) μ μ
  cross_mean_zero : μ[cross_row 0] = 0

namespace ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions

omit [DecidableEq k] in
/-- Joint-row constructor for the projected-error trace-remainder WLLN package.

This is the Hansen-facing form when the homoskedastic projection argument
produces one iid row process containing both the matrix Gram remainder row and
the vector score remainder row.  The separate independence and identical-law
fields in `ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions` are
then derived by measurable projection from that joint row process. -/
theorem of_joint_wlln
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gram_row i ω)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, cross_row i ω)
    (hgram_integrable : Integrable (gram_row 0) μ)
    (hcross_integrable : Integrable (cross_row 0) μ)
    (hjoint_indep : iIndepFun (fun i ω => (gram_row i ω, cross_row i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => (gram_row i ω, cross_row i ω))
        (fun ω => (gram_row 0 ω, cross_row 0 ω)) μ μ)
    (hgram_mean_zero : μ[gram_row 0] = 0)
    (hcross_mean_zero : μ[cross_row 0] = 0) :
    ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
      μ Z e u2 gram_row cross_row where
  gram_remainder_eq_avg := hgram_remainder_eq_avg
  cross_remainder_eq_avg := hcross_remainder_eq_avg
  gram_integrable := hgram_integrable
  gram_indep := by
    have hindep : iIndepFun gram_row μ := by
      simpa [Function.comp] using
        hjoint_indep.comp
          (fun (_ : ℕ) (z : Matrix k k ℝ × (k → ℝ)) => z.1)
          (fun (_ : ℕ) => measurable_fst)
    intro i j hij
    exact hindep.indepFun hij
  gram_ident := by
    intro i
    simpa [Function.comp] using (hjoint_ident i).comp measurable_fst
  gram_mean_zero := hgram_mean_zero
  cross_integrable := hcross_integrable
  cross_indep := by
    have hindep : iIndepFun cross_row μ := by
      simpa [Function.comp] using
        hjoint_indep.comp
          (fun (_ : ℕ) (z : Matrix k k ℝ × (k → ℝ)) => z.2)
          (fun (_ : ℕ) => measurable_snd)
    intro i j hij
    exact hindep.indepFun hij
  cross_ident := by
    intro i
    simpa [Function.comp] using (hjoint_ident i).comp measurable_snd
  cross_mean_zero := hcross_mean_zero

set_option linter.style.longLine false in
omit [DecidableEq k] in
/-- Canonical-row constructor for the projected-error trace-remainder WLLN
package.

This strengthens the row-process boundary from aggregate sample-average
identities to pointwise identifications with the canonical finite-sample row
summands `manyInstrumentProjectedErrorGramTraceRemainderCanonicalRow` and
`manyInstrumentProjectedErrorCrossTraceRemainderCanonicalRow`.  The remaining
probabilistic work is still exactly the iid zero-mean row WLLN. -/
theorem of_canonical_rows_joint_wlln
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    (hgram_canonical_eq_row : ∀ (m : ℕ) (ω : Ω) (i : Fin m),
      manyInstrumentProjectedErrorGramTraceRemainderCanonicalRow
        (Z m ω) (u2 m ω) i = gram_row i.val ω)
    (hcross_canonical_eq_row : ∀ (m : ℕ) (ω : Ω) (i : Fin m),
      manyInstrumentProjectedErrorCrossTraceRemainderCanonicalRow
        (Z m ω) (u2 m ω) (e m ω) i = cross_row i.val ω)
    (hgram_integrable : Integrable (gram_row 0) μ)
    (hcross_integrable : Integrable (cross_row 0) μ)
    (hjoint_indep : iIndepFun (fun i ω => (gram_row i ω, cross_row i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => (gram_row i ω, cross_row i ω))
        (fun ω => (gram_row 0 ω, cross_row 0 ω)) μ μ)
    (hgram_mean_zero : μ[gram_row 0] = 0)
    (hcross_mean_zero : μ[cross_row 0] = 0) :
    ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
      μ Z e u2 gram_row cross_row :=
  ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions.of_joint_wlln
    (μ := μ) (Z := Z) (e := e) (u2 := u2)
    (gram_row := gram_row) (cross_row := cross_row)
    (by
      intro m ω
      calc
        manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
            (Fintype.card (Fin m) : ℝ)⁻¹ •
              ∑ i : Fin m,
                manyInstrumentProjectedErrorGramTraceRemainderCanonicalRow
                  (Z m ω) (u2 m ω) i := by
          exact manyInstrumentProjectedErrorGramTraceRemainder_eq_average_canonicalRow
            (Z m ω) (u2 m ω)
        _ = (m : ℝ)⁻¹ • ∑ i : Fin m, gram_row i.val ω := by
          rw [Fintype.card_fin]
          apply congrArg (fun M : Matrix k k ℝ => (m : ℝ)⁻¹ • M)
          refine Finset.sum_congr rfl ?_
          intro i _
          exact hgram_canonical_eq_row m ω i
        _ = (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gram_row i ω := by
          exact congrArg (fun M : Matrix k k ℝ => (m : ℝ)⁻¹ • M)
            (Fin.sum_univ_eq_sum_range (fun i => gram_row i ω) m))
    (by
      intro m ω
      calc
        manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
            (Fintype.card (Fin m) : ℝ)⁻¹ •
              ∑ i : Fin m,
                manyInstrumentProjectedErrorCrossTraceRemainderCanonicalRow
                  (Z m ω) (u2 m ω) (e m ω) i := by
          exact manyInstrumentProjectedErrorCrossTraceRemainder_eq_average_canonicalRow
            (Z m ω) (u2 m ω) (e m ω)
        _ = (m : ℝ)⁻¹ • ∑ i : Fin m, cross_row i.val ω := by
          rw [Fintype.card_fin]
          apply congrArg (fun v : k → ℝ => (m : ℝ)⁻¹ • v)
          refine Finset.sum_congr rfl ?_
          intro i _
          exact hcross_canonical_eq_row m ω i
        _ = (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, cross_row i ω := by
          exact congrArg (fun v : k → ℝ => (m : ℝ)⁻¹ • v)
            (Fin.sum_univ_eq_sum_range (fun i => cross_row i ω) m))
    hgram_integrable hcross_integrable hjoint_indep hjoint_ident
    hgram_mean_zero hcross_mean_zero

omit [DecidableEq k] in
/-- Matrix/vector row WLLNs imply the entrywise projected-error trace-remainder
package used by the theorem-facing constructors. -/
theorem toEntryWLLNConditions
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    (h : ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
      μ Z e u2 gram_row cross_row) :
    ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
      μ Z e u2 where
  gram_entry_tendsto_zero := by
    intro a b
    have hraw : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gram_row i ω)
        atTop (fun _ => (0 : Matrix k k ℝ)) := by
      have hw := tendstoInMeasure_wlln
        (μ := μ) gram_row h.gram_integrable h.gram_indep h.gram_ident
      simpa [h.gram_mean_zero] using hw
    have hentry : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          ((m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gram_row i ω) a b)
        atTop (fun _ => 0) := by
      simpa using TendstoInMeasure.pi_apply
        (TendstoInMeasure.pi_apply hraw a) b
    refine TendstoInMeasure.congr (fun m => ?_) EventuallyEq.rfl hentry
    exact ae_of_all μ fun ω => by
      have hcoord := congrArg (fun M : Matrix k k ℝ => M a b)
        (h.gram_remainder_eq_avg m ω)
      simpa using hcoord.symm
  cross_entry_tendsto_zero := by
    intro a
    have hraw : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, cross_row i ω)
        atTop (fun _ => (0 : k → ℝ)) := by
      have hw := tendstoInMeasure_wlln
        (μ := μ) cross_row h.cross_integrable h.cross_indep h.cross_ident
      simpa [h.cross_mean_zero] using hw
    have hentry : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          ((m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, cross_row i ω) a)
        atTop (fun _ => 0) := by
      simpa using TendstoInMeasure.pi_apply hraw a
    refine TendstoInMeasure.congr (fun m => ?_) EventuallyEq.rfl hentry
    exact ae_of_all μ fun ω => by
      have hcoord := congrArg (fun v : k → ℝ => v a)
        (h.cross_remainder_eq_avg m ω)
      simpa using hcoord.symm

omit [DecidableEq k] in
/-- Matrix/vector row WLLNs imply the canonical row-average convergence package.

This bridge replaces the direct canonical-average primitive whenever the
projection proof has already produced an enforceable row-WLLN package.  The
canonical averages are identified with the same finite-sample remainders by the
exact row identities above; no extra stochastic argument is introduced here. -/
theorem toCanonicalRowAverageConditions
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    (h : ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
      μ Z e u2 gram_row cross_row) :
    ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions
      μ Z e u2 where
  gram_average_tendsto_zero := by
    have hgram : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω))
        atTop (fun _ => (0 : Matrix k k ℝ)) :=
      (h.toEntryWLLNConditions).gram_tendsto_zero
    refine TendstoInMeasure.congr (fun m => ?_) EventuallyEq.rfl hgram
    exact ae_of_all μ fun ω =>
      manyInstrumentProjectedErrorGramTraceRemainder_eq_average_canonicalRow
        (Z m ω) (u2 m ω)
  cross_average_tendsto_zero := by
    have hcross : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          manyInstrumentProjectedErrorCrossTraceRemainder
            (Z m ω) (u2 m ω) (e m ω))
        atTop (fun _ => (0 : k → ℝ)) :=
      (h.toEntryWLLNConditions).cross_tendsto_zero
    refine TendstoInMeasure.congr (fun m => ?_) EventuallyEq.rfl hcross
    exact ae_of_all μ fun ω =>
      manyInstrumentProjectedErrorCrossTraceRemainder_eq_average_canonicalRow
        (Z m ω) (u2 m ω) (e m ω)

end ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions

omit [DecidableEq k] in
/-- Compatibility-only scalar row-average inputs for projected remainders.

This package does not follow from Hansen's iid errors because projection makes
the canonical summands dependent. It is retained only for callers that have
an independent additive representation from a separate argument. -/
structure ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (gram_row : k → k → ℕ → Ω → ℝ)
    (cross_row : k → ℕ → Ω → ℝ) : Prop where
  gram_entry_eq_avg : ∀ (a b : k) (m : ℕ) (ω : Ω),
    manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) a b =
      (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gram_row a b i ω
  cross_entry_eq_avg : ∀ (a : k) (m : ℕ) (ω : Ω),
    manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) a =
      (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, cross_row a i ω
  gram_integrable : ∀ a b : k, Integrable (gram_row a b 0) μ
  gram_indep : ∀ a b : k, Pairwise ((· ⟂ᵢ[μ] ·) on gram_row a b)
  gram_ident : ∀ a b : k, ∀ i,
    IdentDistrib (gram_row a b i) (gram_row a b 0) μ μ
  gram_mean_zero : ∀ a b : k, μ[gram_row a b 0] = 0
  cross_integrable : ∀ a : k, Integrable (cross_row a 0) μ
  cross_indep : ∀ a : k, Pairwise ((· ⟂ᵢ[μ] ·) on cross_row a)
  cross_ident : ∀ a : k, ∀ i,
    IdentDistrib (cross_row a i) (cross_row a 0) μ μ
  cross_mean_zero : ∀ a : k, μ[cross_row a 0] = 0

namespace ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions

omit [Fintype k] [DecidableEq k] in
/-- Scalar row WLLNs imply the entrywise projected-error trace-remainder WLLN
package. -/
theorem toEntryWLLNConditions
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {gram_row : k → k → ℕ → Ω → ℝ}
    {cross_row : k → ℕ → Ω → ℝ}
    (h : ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions
      μ Z e u2 gram_row cross_row) :
    ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
      μ Z e u2 where
  gram_entry_tendsto_zero := by
    intro a b
    have hraw : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gram_row a b i ω)
        atTop (fun _ => 0) := by
      have hw := tendstoInMeasure_wlln
        (μ := μ) (gram_row a b)
        (h.gram_integrable a b) (h.gram_indep a b) (h.gram_ident a b)
      simpa [h.gram_mean_zero a b] using hw
    refine TendstoInMeasure.congr (fun m => ?_) EventuallyEq.rfl hraw
    exact ae_of_all μ fun ω => (h.gram_entry_eq_avg a b m ω).symm
  cross_entry_tendsto_zero := by
    intro a
    have hraw : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, cross_row a i ω)
        atTop (fun _ => 0) := by
      have hw := tendstoInMeasure_wlln
        (μ := μ) (cross_row a)
        (h.cross_integrable a) (h.cross_indep a) (h.cross_ident a)
      simpa [h.cross_mean_zero a] using hw
    refine TendstoInMeasure.congr (fun m => ?_) EventuallyEq.rfl hraw
    exact ae_of_all μ fun ω => (h.cross_entry_eq_avg a m ω).symm

omit [DecidableEq k] in
/-- A matrix/vector projected-error row WLLN package supplies the scalar
entrywise package by coordinate projection.

This records that scalar entry certificates are not a separate mathematical
input once the stronger row-average identities and row WLLNs have been proved. -/
theorem of_row_wlln
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    (h : ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
      μ Z e u2 gram_row cross_row) :
    ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions
      μ Z e u2
        (fun a b i ω => gram_row i ω a b)
        (fun a i ω => cross_row i ω a) where
  gram_entry_eq_avg := by
    intro a b m ω
    have hcoord := congrArg (fun M : Matrix k k ℝ => M a b)
      (h.gram_remainder_eq_avg m ω)
    simpa [Matrix.smul_apply, Matrix.sum_apply] using hcoord
  cross_entry_eq_avg := by
    intro a m ω
    have hcoord := congrArg (fun v : k → ℝ => v a)
      (h.cross_remainder_eq_avg m ω)
    simpa [Pi.smul_apply, Finset.sum_apply] using hcoord
  gram_integrable := by
    intro a b
    let L : Matrix k k ℝ →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) b).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => k → ℝ) a)
    simpa [L] using L.integrable_comp h.gram_integrable
  gram_indep := by
    intro a b i j hij
    have hrow_cont : Continuous (fun M : Matrix k k ℝ => M a) :=
      continuous_apply a
    have hcoord_meas : Measurable (fun M : Matrix k k ℝ => M a b) :=
      ((continuous_apply b).comp hrow_cont).measurable
    simpa [Function.comp] using
      IndepFun.comp (h.gram_indep hij) hcoord_meas hcoord_meas
  gram_ident := by
    intro a b i
    have hrow_cont : Continuous (fun M : Matrix k k ℝ => M a) :=
      continuous_apply a
    have hcoord_meas : Measurable (fun M : Matrix k k ℝ => M a b) :=
      ((continuous_apply b).comp hrow_cont).measurable
    simpa [Function.comp] using (h.gram_ident i).comp hcoord_meas
  gram_mean_zero := by
    intro a b
    let L : Matrix k k ℝ →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) b).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => k → ℝ) a)
    have hcoord := congrArg L h.gram_mean_zero
    have hL := L.integral_comp_comm h.gram_integrable
    rw [← hL] at hcoord
    simpa using hcoord
  cross_integrable := by
    intro a
    let L : (k → ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) a
    simpa [L] using L.integrable_comp h.cross_integrable
  cross_indep := by
    intro a i j hij
    simpa [Function.comp] using
      IndepFun.comp (h.cross_indep hij)
        (measurable_pi_apply a) (measurable_pi_apply a)
  cross_ident := by
    intro a i
    simpa [Function.comp] using
      (h.cross_ident i).comp (measurable_pi_apply a)
  cross_mean_zero := by
    intro a
    let L : (k → ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : k => ℝ) a
    have hcoord := congrArg L h.cross_mean_zero
    have hL := L.integral_comp_comm h.cross_integrable
    rw [← hL] at hcoord
    simpa using hcoord

omit [DecidableEq k] in
/-- Direct scalar projected-error trace-remainder package from one joint
matrix/vector row process.

This composes the row-level joint WLLN constructor with `of_row_wlln`, so a
caller proving Hansen's homoskedastic projection remainder as matrix/vector
row averages automatically gets the scalar entrywise package as well. -/
theorem of_joint_row_wlln
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gram_row i ω)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, cross_row i ω)
    (hgram_integrable : Integrable (gram_row 0) μ)
    (hcross_integrable : Integrable (cross_row 0) μ)
    (hjoint_indep : iIndepFun (fun i ω => (gram_row i ω, cross_row i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => (gram_row i ω, cross_row i ω))
        (fun ω => (gram_row 0 ω, cross_row 0 ω)) μ μ)
    (hgram_mean_zero : μ[gram_row 0] = 0)
    (hcross_mean_zero : μ[cross_row 0] = 0) :
    ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions
      μ Z e u2
        (fun a b i ω => gram_row i ω a b)
        (fun a i ω => cross_row i ω a) :=
  of_row_wlln
    (μ := μ) (Z := Z) (e := e) (u2 := u2)
    (gram_row := gram_row) (cross_row := cross_row)
    (ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions.of_joint_wlln
      (μ := μ) (Z := Z) (e := e) (u2 := u2)
      (gram_row := gram_row) (cross_row := cross_row)
      hgram_remainder_eq_avg hcross_remainder_eq_avg hgram_integrable
      hcross_integrable hjoint_indep hjoint_ident hgram_mean_zero
      hcross_mean_zero)

end ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions

omit [∀ m, DecidableEq (ι m)] in
/-- Compatibility-only scalar row-average inputs for the LIML gap.

The implication from the stated additive representation is valid, but a LIML
generalized eigenvalue is not itself an additive row statistic. Hansen's raw
model therefore does not construct this package; use normalized-pencil
convergence and a generalized-eigenvalue selector instead. -/
structure ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (limlMuHat : ℕ → Ω → ℝ)
    (gap_row : ℕ → Ω → ℝ) : Prop where
  meas : ∀ m, AEStronglyMeasurable (limlMuHat m) μ
  adjustment_gap_eq_avg : ∀ (m : ℕ) (ω : Ω),
    limlMuHat m ω -
        manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m =
      (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gap_row i ω
  integrable : Integrable (gap_row 0) μ
  indep : Pairwise ((· ⟂ᵢ[μ] ·) on gap_row)
  ident : ∀ i, IdentDistrib (gap_row i) (gap_row 0) μ μ
  mean_zero : μ[gap_row 0] = 0

namespace ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions

omit [∀ m, DecidableEq (ι m)] in
/-- Build the scalar sample-average LIML eigenvalue-gap WLLN package from the
average identity and ordinary Chapter 7 scalar WLLN inputs.

The measurability of `limlMuHat` is derived from the row-process measurability
implied by integrability/identical distribution and the deterministic
adjustment-gap identity, so callers do not need to supply it separately. -/
theorem of_average
    {limlMuHat : ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    (hadjust : ∀ (m : ℕ) (ω : Ω),
      limlMuHat m ω -
          manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gap_row i ω)
    (hintegrable : Integrable (gap_row 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on gap_row))
    (hident : ∀ i, IdentDistrib (gap_row i) (gap_row 0) μ μ)
    (hmean_zero : μ[gap_row 0] = 0) :
    ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
      (ι := ι) μ limlMuHat gap_row where
  meas := by
    intro m
    have hrow_meas : ∀ i, AEStronglyMeasurable (gap_row i) μ :=
      fun i => ((hident i).integrable_iff.mpr hintegrable).aestronglyMeasurable
    have havg_meas : AEStronglyMeasurable
        (fun ω => (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gap_row i ω) μ := by
      have hsum : AEStronglyMeasurable (∑ i ∈ Finset.range m, gap_row i) μ :=
        Finset.aestronglyMeasurable_sum (Finset.range m)
          (fun i _ => hrow_meas i)
      have hscaled := hsum.const_smul ((m : ℝ)⁻¹)
      have heq : (fun ω => (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gap_row i ω) =
          ((m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gap_row i) := by
        funext ω
        simp [Finset.sum_apply]
      rw [heq]
      exact hscaled
    have hmu_meas : AEStronglyMeasurable
        (fun ω =>
          (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gap_row i ω +
            manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m) μ :=
      havg_meas.add aestronglyMeasurable_const
    exact hmu_meas.congr (ae_of_all μ fun ω => by
      have h := hadjust m ω
      linarith)
  adjustment_gap_eq_avg := hadjust
  integrable := hintegrable
  indep := hindep
  ident := hident
  mean_zero := hmean_zero

omit [∀ m, DecidableEq (ι m)] in
/-- Scalar row WLLNs imply the sample LIML eigenvalue adjustment-gap package. -/
theorem toSampleEigenvalueProblemConditions
    {limlMuHat : ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    (h : ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
      (ι := ι) μ limlMuHat gap_row) :
    ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat where
  meas := h.meas
  adjustment_gap_tendsto_zero := by
    have hraw : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gap_row i ω)
        atTop (fun _ => 0) := by
      have hw := tendstoInMeasure_wlln
        (μ := μ) gap_row h.integrable h.indep h.ident
      simpa [h.mean_zero] using hw
    refine TendstoInMeasure.congr (fun m => ?_) EventuallyEq.rfl hraw
    exact ae_of_all μ fun ω => (h.adjustment_gap_eq_avg m ω).symm

end ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions

omit [∀ m, DecidableEq (ι m)] in
/-- Direct constructor for the sample LIML eigenvalue-problem package from a
scalar sample-average WLLN for the centered adjustment gap.

This composes `ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions.of_average`
with `toSampleEigenvalueProblemConditions`; it is the theorem-facing bridge
when the remaining spectral argument has already produced a scalar row
representation for
`μ̂_n - (ℓ_n/n)/(1 - ℓ_n/n)`. -/
theorem ManyInstrumentsLIMLSampleEigenvalueProblemConditions.of_adjustment_gap_average_wlln
    {limlMuHat : ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    (hadjust : ∀ (m : ℕ) (ω : Ω),
      limlMuHat m ω -
          manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gap_row i ω)
    (hintegrable : Integrable (gap_row 0) μ)
    (hindep : Pairwise ((· ⟂ᵢ[μ] ·) on gap_row))
    (hident : ∀ i, IdentDistrib (gap_row i) (gap_row 0) μ μ)
    (hmean_zero : μ[gap_row 0] = 0) :
    ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat :=
  (ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions.of_average
    (ι := ι) (μ := μ) (limlMuHat := limlMuHat) (gap_row := gap_row)
    hadjust hintegrable hindep hident hmean_zero).toSampleEigenvalueProblemConditions

omit [∀ m, DecidableEq (ι m)] in
/-- Joint outcome/regressor matrix `[Y X]` for the finite-sample LIML
Rayleigh problem.

The left column is indexed by `Unit`, and the regressor block by `k`, matching
the reduced-form Rayleigh surface used in the weak-IV file. -/
noncomputable def manyInstrumentsLIMLSampleRayleighData
    {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n k ℝ) (Y : n → ℝ) : Matrix n (Sum Unit k) ℝ :=
  Matrix.fromCols (fun i (_ : Unit) => Y i) X

omit [∀ m, DecidableEq (ι m)] in
/-- Numerator matrix for Hansen's finite-sample many-instrument LIML
Rayleigh quotient, `[Y X]'P_Z[Y X]`. -/
  noncomputable def manyInstrumentsLIMLSampleRayleighNumerator
      {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
      (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) :
      Matrix (Sum Unit k) (Sum Unit k) ℝ :=
    let W : Matrix n (Sum Unit k) ℝ :=
      Matrix.fromCols (fun i (_ : Unit) => Y i) X
    Wᵀ * instrumentProjectionStar Z * W

omit [∀ m, DecidableEq (ι m)] in
/-- Denominator matrix for Hansen's finite-sample many-instrument LIML
Rayleigh quotient, `[Y X]'M_Z[Y X]` with `M_Z = I - P_Z`. -/
  noncomputable def manyInstrumentsLIMLSampleRayleighDenominator
      {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
      (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) :
      Matrix (Sum Unit k) (Sum Unit k) ℝ :=
    let W : Matrix n (Sum Unit k) ℝ :=
      Matrix.fromCols (fun i (_ : Unit) => Y i) X
    Wᵀ * ((1 : Matrix n n ℝ) - instrumentProjectionStar Z) * W

/-- Compatibility finite-sample Rayleigh/eigenvalue adjustment-gap input.

The Rayleigh audit field is genuine, but the separate iid row decomposition of
the selected eigenvalue gap is not supplied by Hansen's assumptions. The
canonical replacement is
`ManyInstrumentsLIMLGeneralizedEigenvalueSelectorCertificate`. -/
structure ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Y : (m : ℕ) → Ω → Fin m → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (gap_row : ℕ → Ω → ℝ) : Prop where
  finite_sample_rayleigh_minimizer : ∀ m ω,
    LIMLRayleighMinimizer
      (manyInstrumentsLIMLSampleRayleighNumerator (Z m ω) (X m ω) (Y m ω))
      (manyInstrumentsLIMLSampleRayleighDenominator (Z m ω) (X m ω) (Y m ω))
      (limlMuHat m ω)
  adjustment_gap_eq_avg : ∀ (m : ℕ) (ω : Ω),
    limlMuHat m ω -
        manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m =
      (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gap_row i ω
  integrable : Integrable (gap_row 0) μ
  indep : Pairwise ((· ⟂ᵢ[μ] ·) on gap_row)
  ident : ∀ i, IdentDistrib (gap_row i) (gap_row 0) μ μ
  mean_zero : μ[gap_row 0] = 0

namespace ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions

omit [DecidableEq k] in
/-- Forget the finite-sample Rayleigh minimizer audit field after it has been
recorded, recovering the existing scalar adjustment-gap WLLN package consumed
by the 12.19 estimator constructors. -/
theorem toAdjustmentGapWLLNConditions
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    (h : ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions
      (ι := ι) μ Z X Y limlMuHat gap_row) :
    ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
      (ι := ι) μ limlMuHat gap_row :=
  ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions.of_average
    (ι := ι) (μ := μ) h.adjustment_gap_eq_avg h.integrable h.indep h.ident
    h.mean_zero

omit [DecidableEq k] in
/-- Finite-sample Rayleigh adjustment-gap WLLNs imply the sample eigenvalue
problem package `μ̂_n - (ℓ_n/n)/(1-ℓ_n/n) ->p 0`. -/
theorem toSampleEigenvalueProblemConditions
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    (h : ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions
      (ι := ι) μ Z X Y limlMuHat gap_row) :
    ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat :=
  h.toAdjustmentGapWLLNConditions.toSampleEigenvalueProblemConditions

end ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions

omit [DecidableEq k] in
/-- Compatibility-only joint row package for projected and eigenvalue gaps.

Neither a projected quadratic form nor a selected generalized eigenvalue has
this iid additive structure in Hansen's model. The package remains only as a
generic compatibility implication and is deprecated below. -/
structure ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Y : (m : ℕ) → Ω → Fin m → ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (gram_row : ℕ → Ω → Matrix k k ℝ)
    (cross_row : ℕ → Ω → k → ℝ)
    (gap_row : ℕ → Ω → ℝ) : Prop where
  finite_sample_rayleigh_minimizer : ∀ m ω,
    LIMLRayleighMinimizer
      (manyInstrumentsLIMLSampleRayleighNumerator (Z m ω) (X m ω) (Y m ω))
      (manyInstrumentsLIMLSampleRayleighDenominator (Z m ω) (X m ω) (Y m ω))
      (limlMuHat m ω)
  gram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
    manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
      (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gram_row i ω
  cross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
    manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
      (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, cross_row i ω
  adjustment_gap_eq_avg : ∀ (m : ℕ) (ω : Ω),
    limlMuHat m ω -
        manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m =
      (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gap_row i ω
  gram_integrable : Integrable (gram_row 0) μ
  cross_integrable : Integrable (cross_row 0) μ
  gap_integrable : Integrable (gap_row 0) μ
  joint_indep :
    iIndepFun (fun i ω => ((gram_row i ω, cross_row i ω), gap_row i ω)) μ
  joint_ident : ∀ i,
    IdentDistrib
      (fun ω => ((gram_row i ω, cross_row i ω), gap_row i ω))
      (fun ω => ((gram_row 0 ω, cross_row 0 ω), gap_row 0 ω)) μ μ
  gram_mean_zero : μ[gram_row 0] = 0
  cross_mean_zero : μ[cross_row 0] = 0
  gap_mean_zero : μ[gap_row 0] = 0

namespace ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions

omit [DecidableEq k] in
/-- Compatibility constructor from an explicitly supplied iid additive row.

Its premises are not consequences of Hansen's raw conditional model. In
particular, this declaration must not be used to label an arbitrary row object
as the projected-form or eigenvalue remainder. -/
theorem of_raw_joint_row
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {row : ℕ → Ω → (Matrix k k ℝ × (k → ℝ)) × ℝ}
    (hrayleigh : ∀ m ω,
      LIMLRayleighMinimizer
        (manyInstrumentsLIMLSampleRayleighNumerator (Z m ω) (X m ω) (Y m ω))
        (manyInstrumentsLIMLSampleRayleighDenominator (Z m ω) (X m ω) (Y m ω))
        (limlMuHat m ω))
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.1)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.2)
    (hadjustment_gap_eq_avg : ∀ (m : ℕ) (ω : Ω),
      limlMuHat m ω -
          manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).2)
    (hrow_integrable : Integrable (row 0) μ)
    (hrow_indep : iIndepFun row μ)
    (hrow_ident : ∀ i, IdentDistrib (row i) (row 0) μ μ)
    (hrow_mean_zero : μ[row 0] = 0) :
    ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions
      (ι := ι) μ Z X Y e u2 limlMuHat
      (fun i ω => (row i ω).1.1)
      (fun i ω => (row i ω).1.2)
      (fun i ω => (row i ω).2) where
  finite_sample_rayleigh_minimizer := hrayleigh
  gram_remainder_eq_avg := hgram_remainder_eq_avg
  cross_remainder_eq_avg := hcross_remainder_eq_avg
  adjustment_gap_eq_avg := hadjustment_gap_eq_avg
  gram_integrable := by
    let L : ((Matrix k k ℝ × (k → ℝ)) × ℝ) →L[ℝ] Matrix k k ℝ :=
      (ContinuousLinearMap.fst ℝ (Matrix k k ℝ) (k → ℝ)).comp
        (ContinuousLinearMap.fst ℝ (Matrix k k ℝ × (k → ℝ)) ℝ)
    simpa [L] using L.integrable_comp hrow_integrable
  cross_integrable := by
    let L : ((Matrix k k ℝ × (k → ℝ)) × ℝ) →L[ℝ] (k → ℝ) :=
      (ContinuousLinearMap.snd ℝ (Matrix k k ℝ) (k → ℝ)).comp
        (ContinuousLinearMap.fst ℝ (Matrix k k ℝ × (k → ℝ)) ℝ)
    simpa [L] using L.integrable_comp hrow_integrable
  gap_integrable := by
    let L : ((Matrix k k ℝ × (k → ℝ)) × ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.snd ℝ (Matrix k k ℝ × (k → ℝ)) ℝ
    simpa [L] using L.integrable_comp hrow_integrable
  joint_indep := by
    simpa using hrow_indep
  joint_ident := by
    intro i
    simpa using hrow_ident i
  gram_mean_zero := by
    let L : ((Matrix k k ℝ × (k → ℝ)) × ℝ) →L[ℝ] Matrix k k ℝ :=
      (ContinuousLinearMap.fst ℝ (Matrix k k ℝ) (k → ℝ)).comp
        (ContinuousLinearMap.fst ℝ (Matrix k k ℝ × (k → ℝ)) ℝ)
    have hcoord := congrArg L hrow_mean_zero
    have hL := L.integral_comp_comm hrow_integrable
    rw [← hL] at hcoord
    simpa [L] using hcoord
  cross_mean_zero := by
    let L : ((Matrix k k ℝ × (k → ℝ)) × ℝ) →L[ℝ] (k → ℝ) :=
      (ContinuousLinearMap.snd ℝ (Matrix k k ℝ) (k → ℝ)).comp
        (ContinuousLinearMap.fst ℝ (Matrix k k ℝ × (k → ℝ)) ℝ)
    have hcoord := congrArg L hrow_mean_zero
    have hL := L.integral_comp_comm hrow_integrable
    rw [← hL] at hcoord
    simpa [L] using hcoord
  gap_mean_zero := by
    let L : ((Matrix k k ℝ × (k → ℝ)) × ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.snd ℝ (Matrix k k ℝ × (k → ℝ)) ℝ
    have hcoord := congrArg L hrow_mean_zero
    have hL := L.integral_comp_comm hrow_integrable
    rw [← hL] at hcoord
    simpa [L] using hcoord

omit [DecidableEq k] in
/-- A joint projected-error/Rayleigh row package supplies the projected-error
matrix/vector row-WLLN package. -/
theorem toProjectedErrorRowWLLNConditions
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    (h : ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions
      (ι := ι) μ Z X Y e u2 limlMuHat gram_row cross_row gap_row) :
    ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
      μ Z e u2 gram_row cross_row :=
  ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions.of_joint_wlln
    (μ := μ) (Z := Z) (e := e) (u2 := u2)
    (gram_row := gram_row) (cross_row := cross_row)
    h.gram_remainder_eq_avg h.cross_remainder_eq_avg
    h.gram_integrable h.cross_integrable
    (by
      simpa [Function.comp] using
        h.joint_indep.comp
          (fun (_ : ℕ) (z : (Matrix k k ℝ × (k → ℝ)) × ℝ) => z.1)
          (fun (_ : ℕ) => measurable_fst))
    (by
      intro i
      simpa [Function.comp] using (h.joint_ident i).comp measurable_fst)
    h.gram_mean_zero h.cross_mean_zero

omit [DecidableEq k] in
/-- A joint projected-error/Rayleigh row package supplies the finite-sample
Rayleigh adjustment-gap WLLN package. -/
theorem toRayleighAdjustmentGapWLLNConditions
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    (h : ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions
      (ι := ι) μ Z X Y e u2 limlMuHat gram_row cross_row gap_row) :
    ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions
      (ι := ι) μ Z X Y limlMuHat gap_row where
  finite_sample_rayleigh_minimizer := h.finite_sample_rayleigh_minimizer
  adjustment_gap_eq_avg := h.adjustment_gap_eq_avg
  integrable := h.gap_integrable
  indep := by
    have hindep : iIndepFun gap_row μ := by
      simpa [Function.comp] using
        h.joint_indep.comp
          (fun (_ : ℕ) (z : (Matrix k k ℝ × (k → ℝ)) × ℝ) => z.2)
          (fun (_ : ℕ) => measurable_snd)
    intro i j hij
    exact hindep.indepFun hij
  ident := by
    intro i
    simpa [Function.comp] using (h.joint_ident i).comp measurable_snd
  mean_zero := h.gap_mean_zero

omit [DecidableEq k] in
/-- A joint projected-error/Rayleigh row package supplies the direct
sample-eigenvalue problem package after forgetting the Rayleigh audit field. -/
theorem toSampleEigenvalueProblemConditions
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    (h : ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions
      (ι := ι) μ Z X Y e u2 limlMuHat gram_row cross_row gap_row) :
    ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat :=
  h.toRayleighAdjustmentGapWLLNConditions.toSampleEigenvalueProblemConditions

end ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions

omit [DecidableEq k] in
/-- Build the homoskedastic projection-remainder package when the trace ratio
is identified a.e. by nonsingular instruments.

The two projected-error measurability fields and the two trace-remainder WLLNs
are still the substantive homoskedastic/fourth-moment work.  The trace-ratio
measurability field is derived from `n^{-1}tr(P_Z*) = ℓ_n/n` on the a.e.
nonsingular branch. -/
theorem ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_ae_nonsingular_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hprojected_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω)) μ)
    (hprojected_error_cross_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω)) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) • sampleGram (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (u2 m ω) (e m ω))
      atTop (fun _ => (0 : k → ℝ))) :
    ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2 where
  trace_ratio_meas := fun m =>
    manyInstrumentProjectionTraceRatio_aestronglyMeasurable_of_ae_nonsingular
      (μ := μ) (Z := fun ω => Z m ω) (hnonsing m)
  projected_error_gram_meas := hprojected_error_gram_meas
  projected_error_cross_meas := hprojected_error_cross_meas
  projected_error_gram_trace_remainder_tendsto_zero :=
    hprojected_error_gram_trace_remainder_tendsto_zero
  projected_error_cross_trace_remainder_tendsto_zero :=
    hprojected_error_cross_trace_remainder_tendsto_zero

set_option linter.unusedDecidableInType false in
/-- Build the homoskedastic projection-remainder package from finite-sample
measurability of `Z`, `u₂`, and `e`.

This removes the non-substantive projected-error measurability fields from the
caller-facing assumptions.  The two trace-remainder WLLNs remain exactly the
homoskedastic/fourth-moment work required by Hansen's proof. -/
theorem
ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_measurable_ae_nonsingular_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) • sampleGram (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (u2 m ω) (e m ω))
      atTop (fun _ => (0 : k → ℝ))) :
    ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2 :=
  ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_ae_nonsingular_remainders
    (μ := μ) (Z := Z) (e := e) (u2 := u2)
    hnonsing
    (fun m => manyInstrumentProjectedErrorGram_aestronglyMeasurable
      (μ := μ) (Zmat := Z m) (Umat := u2 m) (hZ_meas m) (hu2_meas m))
    (fun m => manyInstrumentProjectedErrorCross_aestronglyMeasurable
      (μ := μ) (Zmat := Z m) (Umat := u2 m) (evec := e m)
      (hZ_meas m) (hu2_meas m) (he_meas m))
    hprojected_error_gram_trace_remainder_tendsto_zero
    hprojected_error_cross_trace_remainder_tendsto_zero

set_option linter.unusedDecidableInType false in
set_option linter.style.longLine false in
/-- Build the homoskedastic projection-remainder package from finite-sample
measurability and entrywise scalar trace-remainder WLLNs.

This is the preferred local target for the remaining Hansen 12.19
homoskedastic projection step: prove one scalar WLLN for each `u₂'P_Zu₂`
entry and each `u₂'P_Ze` coordinate, then use this constructor to recover the
matrix/vector remainder package consumed by the estimator theorem. -/
theorem
ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_entrywise_measurable_ae_nonsingular_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hentry : ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
      μ Z e u2) :
    ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2 :=
  ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_measurable_ae_nonsingular_remainders
    (μ := μ) (Z := Z) (e := e) (u2 := u2)
    hnonsing hZ_meas hu2_meas he_meas
    hentry.gram_tendsto_zero hentry.cross_tendsto_zero

set_option linter.unusedDecidableInType false in
set_option linter.style.longLine false in
/-- Build the homoskedastic projection-remainder package from finite-sample
measurability and canonical row-average convergence for the two projected-error
trace remainders.

This is the Hansen-facing bridge for the homoskedastic projection step in
Theorem 12.19: the row summands are the exact finite-sample summands defined
from `P_Z*`, `u₂`, and `e`, and the finite-dimensional entrywise package is
assembled internally. -/
theorem
ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_canonical_row_average_measurable_ae_nonsingular_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hcanonical :
      ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions
        μ Z e u2) :
    ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2 :=
  ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_entrywise_measurable_ae_nonsingular_remainders
    (μ := μ) (Z := Z) (e := e) (u2 := u2)
    hnonsing hZ_meas hu2_meas he_meas hcanonical.toEntryWLLNConditions

set_option linter.unusedDecidableInType false in
set_option linter.style.longLine false in
/-- Build the homoskedastic projection-remainder package from finite-sample
measurability and matrix/vector row WLLNs for the two projected-error
remainders.

This is the row-process counterpart of
`of_entrywise_measurable_ae_nonsingular_remainders`: the scalar entrywise
certificates are derived from a finite-dimensional matrix row process and a
finite-dimensional vector row process. -/
theorem
ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_row_wlln_measurable_ae_nonsingular_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hrow : ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
      μ Z e u2 gram_row cross_row) :
    ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2 :=
  ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_entrywise_measurable_ae_nonsingular_remainders
    (μ := μ) (Z := Z) (e := e) (u2 := u2)
    hnonsing hZ_meas hu2_meas he_meas hrow.toEntryWLLNConditions

set_option linter.unusedDecidableInType false in
set_option linter.style.longLine false in
/-- Build the homoskedastic projection-remainder package from one joint iid row
process for the projected-error trace remainders.

This is the row-process bridge that removes the need to state separate
independence and identical-law inputs for the Gram and score remainders.  The
substantive work remains the exact average representation of Hansen's two
projection-trace remainders and zero means for the two row components. -/
theorem
ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_joint_row_wlln_measurable_ae_nonsingular_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gram_row i ω)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, cross_row i ω)
    (hgram_integrable : Integrable (gram_row 0) μ)
    (hcross_integrable : Integrable (cross_row 0) μ)
    (hjoint_indep : iIndepFun (fun i ω => (gram_row i ω, cross_row i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => (gram_row i ω, cross_row i ω))
        (fun ω => (gram_row 0 ω, cross_row 0 ω)) μ μ)
    (hgram_mean_zero : μ[gram_row 0] = 0)
    (hcross_mean_zero : μ[cross_row 0] = 0) :
    ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2 :=
  ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_row_wlln_measurable_ae_nonsingular_remainders
    (μ := μ) (Z := Z) (e := e) (u2 := u2)
    hnonsing hZ_meas hu2_meas he_meas
    (ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions.of_joint_wlln
      (μ := μ) (Z := Z) (e := e) (u2 := u2)
      (gram_row := gram_row) (cross_row := cross_row)
      hgram_remainder_eq_avg hcross_remainder_eq_avg hgram_integrable
      hcross_integrable hjoint_indep hjoint_ident hgram_mean_zero
      hcross_mean_zero)

set_option linter.unusedDecidableInType false in
set_option linter.style.longLine false in
/-- Build the homoskedastic projection-remainder package from pointwise
canonical-row identifications and one joint iid row process.

This is the closest theorem-facing boundary to Hansen's projected-error
calculation currently available in this file: callers identify the abstract
row process with the exact canonical finite-sample summands, while this bridge
derives the aggregate trace-remainder identities and then reuses the ordinary
row-WLLN constructor. -/
theorem
ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_canonical_rows_joint_wlln_measurable_ae_nonsingular_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hgram_canonical_eq_row : ∀ (m : ℕ) (ω : Ω) (i : Fin m),
      manyInstrumentProjectedErrorGramTraceRemainderCanonicalRow
        (Z m ω) (u2 m ω) i = gram_row i.val ω)
    (hcross_canonical_eq_row : ∀ (m : ℕ) (ω : Ω) (i : Fin m),
      manyInstrumentProjectedErrorCrossTraceRemainderCanonicalRow
        (Z m ω) (u2 m ω) (e m ω) i = cross_row i.val ω)
    (hgram_integrable : Integrable (gram_row 0) μ)
    (hcross_integrable : Integrable (cross_row 0) μ)
    (hjoint_indep : iIndepFun (fun i ω => (gram_row i ω, cross_row i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => (gram_row i ω, cross_row i ω))
        (fun ω => (gram_row 0 ω, cross_row 0 ω)) μ μ)
    (hgram_mean_zero : μ[gram_row 0] = 0)
    (hcross_mean_zero : μ[cross_row 0] = 0) :
    ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2 :=
  ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_row_wlln_measurable_ae_nonsingular_remainders
    (μ := μ) (Z := Z) (e := e) (u2 := u2)
    hnonsing hZ_meas hu2_meas he_meas
    (ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions.of_canonical_rows_joint_wlln
      (μ := μ) (Z := Z) (e := e) (u2 := u2)
      (gram_row := gram_row) (cross_row := cross_row)
      hgram_canonical_eq_row hcross_canonical_eq_row hgram_integrable
      hcross_integrable hjoint_indep hjoint_ident hgram_mean_zero
      hcross_mean_zero)

set_option linter.unusedDecidableInType false in
set_option linter.style.longLine false in
/-- Stacked-row version of
`ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_measurable_ae_nonsingular_remainders`.

The matrix `Z m` is still allowed to have a varying instrument codomain; the
reduced-form error rows and scalar structural errors are ordinary fixed-row
processes, so their stacked finite-sample measurability is derived locally. -/
theorem
ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_stacked_measurable_ae_nonsingular_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ i, AEStronglyMeasurable (u2 i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (stackRegressors u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleGram (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross
            (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (stackRegressors u2 m ω) (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ))) :
    ManyInstrumentsHomoskedasticProjectionRemainderConditions
      μ Z (fun m ω => stackErrors e m ω) (fun m ω => stackRegressors u2 m ω) := by
  have hu2_stack_meas : ∀ m,
      AEStronglyMeasurable (fun ω => stackRegressors u2 m ω) μ := by
    intro m
    simpa [stackRegressors] using
      (stackMatrix_aestronglyMeasurable
        (μ := μ) (n := m) (X := u2) hu2_meas)
  have he_stack_meas : ∀ m,
      AEStronglyMeasurable (fun ω => stackErrors e m ω) μ := by
    intro m
    exact
      manyInstrumentVector_aestronglyMeasurable_of_entries (μ := μ)
        (v := fun ω => stackErrors e m ω)
        (fun i => by simpa [stackErrors] using he_meas i.val)
  exact
    ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_measurable_ae_nonsingular_remainders
      (μ := μ) (Z := Z)
      (e := fun m ω => stackErrors e m ω)
      (u2 := fun m ω => stackRegressors u2 m ω)
      hnonsing hZ_meas hu2_stack_meas he_stack_meas
      hprojected_error_gram_trace_remainder_tendsto_zero
      hprojected_error_cross_trace_remainder_tendsto_zero

set_option linter.unusedDecidableInType false in
set_option linter.style.longLine false in
/-- Stacked-row homoskedastic projection-remainder package from entrywise
scalar trace-remainder WLLNs.

This is the fixed-row analogue of
`of_entrywise_measurable_ae_nonsingular_remainders`.  It derives all
finite-sample projected-error measurability locally and leaves only scalar
entrywise `o_p(1)` WLLNs as the stochastic projected-error input. -/
theorem
ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_stacked_entrywise_measurable_ae_nonsingular_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ i, AEStronglyMeasurable (u2 i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hentry :
      ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
        μ Z (fun m ω => stackErrors e m ω)
          (fun m ω => stackRegressors u2 m ω)) :
    ManyInstrumentsHomoskedasticProjectionRemainderConditions
      μ Z (fun m ω => stackErrors e m ω) (fun m ω => stackRegressors u2 m ω) := by
  have hu2_stack_meas : ∀ m,
      AEStronglyMeasurable (fun ω => stackRegressors u2 m ω) μ := by
    intro m
    simpa [stackRegressors] using
      (stackMatrix_aestronglyMeasurable
        (μ := μ) (n := m) (X := u2) hu2_meas)
  have he_stack_meas : ∀ m,
      AEStronglyMeasurable (fun ω => stackErrors e m ω) μ := by
    intro m
    exact
      manyInstrumentVector_aestronglyMeasurable_of_entries (μ := μ)
        (v := fun ω => stackErrors e m ω)
        (fun i => by simpa [stackErrors] using he_meas i.val)
  exact
    ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_entrywise_measurable_ae_nonsingular_remainders
      (μ := μ) (Z := Z)
      (e := fun m ω => stackErrors e m ω)
      (u2 := fun m ω => stackRegressors u2 m ω)
      hnonsing hZ_meas hu2_stack_meas he_stack_meas hentry

omit [DecidableEq k] in
/-- Build the projection-trace moment package from Hansen's instrument-count
ratio and eventual-a.e. nonsingularity of the sample instrument Gram.

The remaining fields are the substantive homoskedastic projection-remainder
and reduced-form moment assumptions; the deterministic trace-ratio convergence
is derived instead of assumed. -/
theorem ManyInstrumentsProjectedTraceMomentConditions.of_eventually_ae_card_ratio_nonsingular
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ} {alpha : ℝ}
    (hcard : Tendsto
      (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ)) atTop (𝓝 alpha))
    (hnonsing : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (htrace_ratio_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectionTraceRatio (Z m ω)) μ)
    (hreduced_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleGram (u2 m ω)) μ)
    (hreduced_error_cross_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (u2 m ω) (e m ω)) μ)
    (hprojected_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω)) μ)
    (hprojected_error_cross_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω)) μ)
    (hreduced_error_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => sampleGram (u2 m ω))
      atTop (fun _ => Sigma22))
    (hreduced_error_cross_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => sampleCrossMoment (u2 m ω) (e m ω))
      atTop (fun _ => Sigma2e))
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) • sampleGram (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (u2 m ω) (e m ω))
      atTop (fun _ => (0 : k → ℝ))) :
    ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha where
  trace_ratio_meas := htrace_ratio_meas
  reduced_error_gram_meas := hreduced_error_gram_meas
  reduced_error_cross_meas := hreduced_error_cross_meas
  projected_error_gram_meas := hprojected_error_gram_meas
  projected_error_cross_meas := hprojected_error_cross_meas
  trace_ratio_tendsto :=
    manyInstrumentProjectionTraceRatio_tendstoInMeasure_of_eventually_ae_card_ratio_nonsingular
      (μ := μ) (Z := Z) hcard hnonsing
  reduced_error_gram_tendsto := hreduced_error_gram_tendsto
  reduced_error_cross_tendsto := hreduced_error_cross_tendsto
  projected_error_gram_trace_remainder_tendsto_zero :=
    hprojected_error_gram_trace_remainder_tendsto_zero
  projected_error_cross_trace_remainder_tendsto_zero :=
    hprojected_error_cross_trace_remainder_tendsto_zero

omit [DecidableEq k] in
/-- Build the full projection-trace moment package from the named reduced-form
WLLN package plus the two homoskedastic projection remainder WLLNs.

This removes duplicate reduced-form error WLLN assumptions from the projection
layer: `sampleGram u₂` and `sampleCrossMoment u₂ e` are inherited from
`ManyInstrumentsReducedFormWLLNConditions`, while the deterministic trace ratio
limit is still derived from the instrument count and eventual-a.e.
nonsingularity. -/
theorem ManyInstrumentsProjectedTraceMomentConditions.of_reduced_form_wlln_projection_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ} {alpha : ℝ}
    (hcard : Tendsto
      (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ)) atTop (𝓝 alpha))
    (hnonsing : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hproj : ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2) :
    ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha :=
  ManyInstrumentsProjectedTraceMomentConditions.of_eventually_ae_card_ratio_nonsingular
    (μ := μ) (Z := Z) (e := e) (u2 := u2)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    hcard hnonsing hproj.trace_ratio_meas hRF.reduced_error_gram_meas
    hRF.reduced_error_score_meas hproj.projected_error_gram_meas
    hproj.projected_error_cross_meas hRF.reduced_error_gram_tendsto
    hRF.reduced_error_score_tendsto
    hproj.projected_error_gram_trace_remainder_tendsto_zero
    hproj.projected_error_cross_trace_remainder_tendsto_zero

omit [DecidableEq k] in
/-- Projection-trace moment package from reduced-form WLLNs and raw
homoskedastic projection-remainder fields, deriving trace-ratio measurability
from a.e. nonsingular instruments.

Compared with
`ManyInstrumentsProjectedTraceMomentConditions.of_reduced_form_wlln_projection_remainders`,
this constructor does not require a prebuilt
`ManyInstrumentsHomoskedasticProjectionRemainderConditions` value and does not
ask for `trace_ratio_meas` separately. -/
theorem
ManyInstrumentsProjectedTraceMomentConditions.of_reduced_form_wlln_ae_nonsingular_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ} {alpha : ℝ}
    (hcard : Tendsto
      (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ)) atTop (𝓝 alpha))
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hprojected_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω)) μ)
    (hprojected_error_cross_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω)) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) • sampleGram (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (u2 m ω) (e m ω))
      atTop (fun _ => (0 : k → ℝ))) :
    ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha := by
  let hproj : ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2 :=
    ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_ae_nonsingular_remainders
      (μ := μ) (Z := Z) (e := e) (u2 := u2)
      hnonsing hprojected_error_gram_meas hprojected_error_cross_meas
      hprojected_error_gram_trace_remainder_tendsto_zero
      hprojected_error_cross_trace_remainder_tendsto_zero
  have hnonsing_eventually : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)) :=
    Filter.Eventually.of_forall hnonsing
  exact
    ManyInstrumentsProjectedTraceMomentConditions.of_reduced_form_wlln_projection_remainders
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      hcard hnonsing_eventually hRF hproj

omit [DecidableEq k] in
/-- Projection-trace consequences imply the projected-error Gram limit
`n^{-1}u₂'P_Zu₂ ->p αΣ₂₂`. -/
theorem manyInstrumentProjectedErrorGram_tendsto_of_trace_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ} {alpha : ℝ}
    (h : ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω))
      atTop (fun _ => alpha • Sigma22) := by
  let r : ℕ → Ω → ℝ := fun m ω => manyInstrumentProjectionTraceRatio (Z m ω)
  let G : ℕ → Ω → Matrix k k ℝ := fun m ω => sampleGram (u2 m ω)
  have hscaled : TendstoInMeasure μ
      (fun m ω => r m ω • G m ω) atTop (fun _ => alpha • Sigma22) :=
    tendstoInMeasure_smul_matrix
      (μ := μ) (r := r) (A := G)
      (c := alpha) (M := Sigma22)
      (by intro m; simpa [r] using h.trace_ratio_meas m)
      (by intro m; simpa [G] using h.reduced_error_gram_meas m)
      (by simpa [r] using h.trace_ratio_tendsto)
      (by simpa [G] using h.reduced_error_gram_tendsto)
  exact TendstoInMeasure.of_sub_tendsto_zero_matrix
    (μ := μ)
    (X := fun m ω => manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω))
    (Y := fun m ω => r m ω • G m ω)
    (C := alpha • Sigma22)
    (by simpa [r, G] using h.projected_error_gram_trace_remainder_tendsto_zero)
    hscaled

omit [DecidableEq k] in
/-- Projection-trace consequences imply the projected-error score limit
`n^{-1}u₂'P_Ze ->p αΣ₂e`. -/
theorem manyInstrumentProjectedErrorCross_tendsto_of_trace_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ} {alpha : ℝ}
    (h : ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω))
      atTop (fun _ => alpha • Sigma2e) := by
  let r : ℕ → Ω → ℝ := fun m ω => manyInstrumentProjectionTraceRatio (Z m ω)
  let s : ℕ → Ω → k → ℝ := fun m ω => sampleCrossMoment (u2 m ω) (e m ω)
  have hscaled : TendstoInMeasure μ
      (fun m ω => r m ω • s m ω) atTop (fun _ => alpha • Sigma2e) :=
    tendstoInMeasure_smul_vector
      (μ := μ) (r := r) (v := s)
      (c := alpha) (g := Sigma2e)
      (by intro m; simpa [r] using h.trace_ratio_meas m)
      (by intro m; simpa [s] using h.reduced_error_cross_meas m)
      (by simpa [r] using h.trace_ratio_tendsto)
      (by simpa [s] using h.reduced_error_cross_tendsto)
  exact TendstoInMeasure.of_sub_tendsto_zero_vector
    (μ := μ)
    (X := fun m ω => manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω))
    (Y := fun m ω => r m ω • s m ω)
    (c := alpha • Sigma2e)
    (by simpa [r, s] using h.projected_error_cross_trace_remainder_tendsto_zero)
    hscaled

/-- Assemble the 2SLS projected reduced-form moment package from signal/cross
component limits plus the lower-level projection-trace error consequences. -/
theorem ManyInstrumentsTwoSLSMomentAssemblyConditions.of_projection_trace_components
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ} {alpha : ℝ}
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) + u2 m ω)
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ)
    (hprojected_signal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hprojected_cross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_signal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (htrace : ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha)
    (hnonsing : IsUnit (H + alpha • Sigma22).det) :
    ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha where
  reduced_form := hreduced
  moment_meas := by
    intro m
    have hsum : AEStronglyMeasurable
        (fun ω =>
          manyInstrumentProjectedSignalGram (Z m ω) (Gamma m) +
              manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω) +
            manyInstrumentProjectedReducedFormCrossGram
              (Z m ω) (Gamma m) (u2 m ω)) μ :=
      ((hprojected_signal_gram_meas m).add
        (htrace.projected_error_gram_meas m)).add
          (hprojected_cross_gram_meas m)
    refine hsum.congr (ae_of_all μ fun ω => ?_)
    change
      manyInstrumentProjectedSignalGram (Z m ω) (Gamma m) +
            manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω) +
          manyInstrumentProjectedReducedFormCrossGram
            (Z m ω) (Gamma m) (u2 m ω) =
        limlNormalizedMomentMatrixStar (Z m ω) (X m ω) 0
    rw [hreduced m ω, manyInstrumentProjectedReducedForm_normalizedMomentMatrix_zero]
  score_meas := by
    intro m
    have hsum : AEStronglyMeasurable
        (fun ω =>
          manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω) +
            manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω)) μ :=
      (hprojected_signal_score_meas m).add (htrace.projected_error_cross_meas m)
    refine hsum.congr (ae_of_all μ fun ω => ?_)
    change
      manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω) +
          manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω) =
        limlNormalizedMomentVectorStar (Z m ω) (X m ω) (e m ω) 0
    rw [hreduced m ω, manyInstrumentProjectedReducedForm_normalizedMomentVector_zero]
  projected_signal_gram_meas := hprojected_signal_gram_meas
  projected_error_gram_meas := htrace.projected_error_gram_meas
  projected_cross_gram_meas := hprojected_cross_gram_meas
  projected_signal_score_meas := hprojected_signal_score_meas
  projected_error_score_meas := htrace.projected_error_cross_meas
  projected_signal_gram_tendsto := hprojected_signal_gram_tendsto
  projected_error_gram_tendsto :=
    manyInstrumentProjectedErrorGram_tendsto_of_trace_remainders htrace
  projected_cross_gram_tendsto_zero := hprojected_cross_gram_tendsto_zero
  projected_signal_score_tendsto_zero := hprojected_signal_score_tendsto_zero
  projected_error_score_tendsto :=
    manyInstrumentProjectedErrorCross_tendsto_of_trace_remainders htrace
  limit_nonsing := hnonsing

/-- Projection-trace assembly with the 2SLS limit nonsingularity discharged from
Hansen's positive-definite signal limit, positive-semidefinite reduced-form
error covariance, and nonnegative instrument-ratio limit. -/
theorem ManyInstrumentsTwoSLSMomentAssemblyConditions.of_projection_trace_components_posSemidef
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ} {alpha : ℝ}
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) + u2 m ω)
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ)
    (hprojected_signal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hprojected_cross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_signal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (htrace : ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha)
    (hH : H.PosDef) (hSigma22 : Sigma22.PosSemidef) (halpha : 0 ≤ alpha) :
    ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTwoSLSMomentAssemblyConditions.of_projection_trace_components
    (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    hreduced hprojected_signal_gram_meas hprojected_cross_gram_meas
    hprojected_signal_score_meas
    hprojected_signal_gram_tendsto hprojected_cross_gram_tendsto_zero
    hprojected_signal_score_tendsto_zero htrace
    (manyInstruments_twoSLS_limit_matrix_nonsingular_of_posSemidef
      hH hSigma22 halpha)

/-- Assemble the 2SLS projected reduced-form package from the OLS reduced-form
assembly and projection-trace error package.

On the eventual-a.e. nonsingular instrument branch, the deterministic identity
`P_Z ZΓ = ZΓ` turns the OLS signal Gram, cross-Gram, and signal-score limits
into their projected counterparts.  Thus this constructor avoids asking for
separate projected-signal WLLNs. -/
theorem ManyInstrumentsTwoSLSMomentAssemblyConditions.of_ols_projection_trace_components_posSemidef
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ} {alpha : ℝ}
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ)
    (htrace : ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha)
    (hnonsing : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hH : H.PosDef) (hSigma22 : Sigma22.PosSemidef) (halpha : 0 ≤ alpha) :
    ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha := by
  have hprojected_signal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H) := by
    refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hOLS.signal_gram_tendsto
    filter_upwards [hnonsing] with m hm
    filter_upwards [hm] with ω hω
    rcases hω with ⟨inst⟩
    letI : Invertible ((Z m ω)ᵀ * Z m ω) := inst
    exact
      (manyInstrumentProjectedSignalGram_eq_signalGram_of_nonsingular
        (Z m ω) (Gamma m)).symm
  have hprojected_cross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)) := by
    refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hOLS.cross_gram_tendsto_zero
    filter_upwards [hnonsing] with m hm
    filter_upwards [hm] with ω hω
    rcases hω with ⟨inst⟩
    letI : Invertible ((Z m ω)ᵀ * Z m ω) := inst
    exact
      (manyInstrumentProjectedReducedFormCrossGram_eq_crossGram_of_nonsingular
        (Z m ω) (Gamma m) (u2 m ω)).symm
  have hprojected_signal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω))
      atTop (fun _ => (0 : k → ℝ)) := by
    refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hOLS.signal_score_tendsto_zero
    filter_upwards [hnonsing] with m hm
    filter_upwards [hm] with ω hω
    rcases hω with ⟨inst⟩
    letI : Invertible ((Z m ω)ᵀ * Z m ω) := inst
    exact
      (manyInstrumentProjectedSignalScore_eq_signalScore_of_nonsingular
        (Z m ω) (Gamma m) (e m ω)).symm
  exact
    ManyInstrumentsTwoSLSMomentAssemblyConditions.of_projection_trace_components_posSemidef
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      hOLS.reduced_form hprojected_signal_gram_meas hprojected_cross_gram_meas
      hprojected_signal_score_meas
      hprojected_signal_gram_tendsto hprojected_cross_gram_tendsto_zero
      hprojected_signal_score_tendsto_zero htrace hH hSigma22 halpha

/-- Assemble the 2SLS projected reduced-form package from the OLS reduced-form
assembly and projection-trace package, deriving projected signal measurability
and limits from `P_Z ZΓ = ZΓ` on the a.e. nonsingular instrument branch.

This is the theorem-facing projected-signal bridge for Hansen Theorem 12.19:
callers only supply the primitive unprojected signal/cross/score WLLNs already
contained in `hOLS`, not separate projected-signal component assumptions. -/
theorem
ManyInstrumentsTwoSLSMomentAssemblyConditions.of_ols_projection_trace_ae_nonsingular
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ} {alpha : ℝ}
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (htrace : ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hH : H.PosDef) (hSigma22 : Sigma22.PosSemidef) (halpha : 0 ≤ alpha) :
    ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha := by
  have hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ := by
    intro m
    exact
      manyInstrumentProjectedSignalGram_aestronglyMeasurable_of_ae_nonsingular
        (μ := μ) (Z := fun ω => Z m ω) (Gamma := Gamma m)
        (hnonsing m) (hOLS.signal_gram_meas m)
  have hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ := by
    intro m
    exact
      manyInstrumentProjectedReducedFormCrossGram_aestronglyMeasurable_of_ae_nonsingular
        (μ := μ) (Z := fun ω => Z m ω) (Gamma := Gamma m)
        (u2 := fun ω => u2 m ω) (hnonsing m) (hOLS.cross_gram_meas m)
  have hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ := by
    intro m
    exact
      manyInstrumentProjectedSignalScore_aestronglyMeasurable_of_ae_nonsingular
        (μ := μ) (Z := fun ω => Z m ω) (Gamma := Gamma m)
        (e := fun ω => e m ω) (hnonsing m) (hOLS.signal_score_meas m)
  have hnonsing_eventually : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)) :=
    Filter.Eventually.of_forall hnonsing
  exact
    ManyInstrumentsTwoSLSMomentAssemblyConditions.of_ols_projection_trace_components_posSemidef
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      hOLS hprojected_signal_gram_meas hprojected_cross_gram_meas
      hprojected_signal_score_meas htrace hnonsing_eventually hH hSigma22 halpha

/-- Assemble the 2SLS `μ = 0` normalized moment-limit package from Hansen's
projected reduced-form moment components. -/
theorem ManyInstrumentsLIMLMomentLimitConditions.of_projected_reduced_form_components
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ} {alpha : ℝ}
    (h : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha) :
    ManyInstrumentsLIMLMomentLimitConditions
      μ Z X e (fun _ _ => 0) (H + alpha • Sigma22) (alpha • Sigma2e) := by
  refine
    { moment_meas := h.moment_meas
      score_meas := h.score_meas
      moment_tendsto := ?_
      score_tendsto := ?_
      limit_nonsing := h.limit_nonsing }
  · have hsignal_plus_error : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          manyInstrumentProjectedSignalGram (Z m ω) (Gamma m) +
            manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω))
        atTop (fun _ => H + alpha • Sigma22) :=
      tendstoInMeasure_add h.projected_signal_gram_meas h.projected_error_gram_meas
        h.projected_signal_gram_tendsto h.projected_error_gram_tendsto
    have htotal : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          manyInstrumentProjectedSignalGram (Z m ω) (Gamma m) +
              manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω) +
            manyInstrumentProjectedReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
        atTop (fun _ => H + alpha • Sigma22 + (0 : Matrix k k ℝ)) :=
      tendstoInMeasure_add
        (fun m => (h.projected_signal_gram_meas m).add
          (h.projected_error_gram_meas m))
        h.projected_cross_gram_meas hsignal_plus_error h.projected_cross_gram_tendsto_zero
    refine TendstoInMeasure.congr' ?_ ?_ htotal
    · filter_upwards [eventually_gt_atTop 0] with m hm
      exact ae_of_all μ (fun ω => by
        haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
        change
          manyInstrumentProjectedSignalGram (Z m ω) (Gamma m) +
                manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω) +
              manyInstrumentProjectedReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω) =
            limlNormalizedMomentMatrixStar (Z m ω) (X m ω) 0
        rw [h.reduced_form m ω,
          manyInstrumentProjectedReducedForm_normalizedMomentMatrix_zero])
    · exact ae_of_all μ (fun _ => by simp)
  · have hscore_sum : TendstoInMeasure μ
        (fun (m : ℕ) ω =>
          manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω) +
            manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω))
        atTop (fun _ => (0 : k → ℝ) + alpha • Sigma2e) :=
      tendstoInMeasure_add h.projected_signal_score_meas h.projected_error_score_meas
        h.projected_signal_score_tendsto_zero h.projected_error_score_tendsto
    refine TendstoInMeasure.congr' ?_ ?_ hscore_sum
    · filter_upwards [eventually_gt_atTop 0] with m hm
      exact ae_of_all μ (fun ω => by
        haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
        change
          manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω) +
              manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω) =
            limlNormalizedMomentVectorStar (Z m ω) (X m ω) (e m ω) 0
        rw [h.reduced_form m ω,
          manyInstrumentProjectedReducedForm_normalizedMomentVector_zero])
    · exact ae_of_all μ (fun _ => by simp)

set_option maxHeartbeats 900000 in
-- Product-space synthesis for the inverse/product/mulVec CMT chain is expensive.
/-- OLS convergence from normalized Gram and score limits. -/
theorem olsBetaStar_tendstoInMeasure_of_moment_limits
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {β g : k → ℝ} {Q : Matrix k k ℝ}
    (h : ManyInstrumentsOLSMomentLimitConditions μ X e Q g)
    (hmodel : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + Q⁻¹ *ᵥ g) := by
  let A : ℕ → Ω → Matrix k k ℝ := fun m ω => sampleGram (X m ω)
  let s : ℕ → Ω → k → ℝ := fun m ω => sampleCrossMoment (X m ω) (e m ω)
  have hA_meas : ∀ m, AEStronglyMeasurable (A m) μ := by
    intro m
    simpa [A] using h.gram_meas m
  have hs_meas : ∀ m, AEStronglyMeasurable (s m) μ := by
    intro m
    simpa [s] using h.score_meas m
  have hA : TendstoInMeasure μ A atTop (fun _ => Q) := by
    simpa [A] using h.gram_tendsto
  have hs : TendstoInMeasure μ s atTop (fun _ => g) := by
    simpa [s] using h.score_tendsto
  have hAinv_meas : ∀ m, AEStronglyMeasurable (fun ω => (A m ω)⁻¹) μ :=
    fun m => aestronglyMeasurable_matrix_inv (hA_meas m)
  have hAinv : TendstoInMeasure μ
      (fun m ω => (A m ω)⁻¹) atTop (fun _ => Q⁻¹) :=
    tendstoInMeasure_matrix_inv (μ := μ) hA_meas hA (fun _ => h.limit_nonsing)
  have hAinvA_meas : ∀ m, AEStronglyMeasurable
      (fun ω => (A m ω)⁻¹ * A m ω) μ := by
    intro m
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hAinv_meas m).prodMk (hA_meas m))
  have hAinvA : TendstoInMeasure μ
      (fun m ω => (A m ω)⁻¹ * A m ω) atTop (fun _ => Q⁻¹ * Q) :=
    tendstoInMeasure_matrix_mul hAinv_meas hA_meas hAinv hA
  have hAinvAβ_meas : ∀ m, AEStronglyMeasurable
      (fun ω => ((A m ω)⁻¹ * A m ω) *ᵥ β) μ := by
    intro m
    exact (Continuous.matrix_mulVec continuous_id continuous_const).comp_aestronglyMeasurable
      (hAinvA_meas m)
  have hAinvAβ : TendstoInMeasure μ
      (fun m ω => ((A m ω)⁻¹ * A m ω) *ᵥ β) atTop (fun _ => β) := by
    have hcont : Continuous (fun M : Matrix k k ℝ => M *ᵥ β) :=
      Continuous.matrix_mulVec continuous_id continuous_const
    have hraw := tendstoInMeasure_continuous_comp hAinvA_meas hAinvA hcont
    refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hraw
    exact ae_of_all μ (fun _ => by
      rw [Matrix.nonsing_inv_mul Q h.limit_nonsing]
      simp)
  have hAinvs_meas : ∀ m, AEStronglyMeasurable
      (fun ω => (A m ω)⁻¹ *ᵥ s m ω) μ := by
    intro m
    exact (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((hAinv_meas m).prodMk (hs_meas m))
  have hAinvs : TendstoInMeasure μ
      (fun m ω => (A m ω)⁻¹ *ᵥ s m ω) atTop (fun _ => Q⁻¹ *ᵥ g) :=
    tendstoInMeasure_mulVec hAinv_meas hs_meas hAinv hs
  have hsum := tendstoInMeasure_add hAinvAβ_meas hAinvs_meas hAinvAβ hAinvs
  refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hsum
  filter_upwards [eventually_gt_atTop 0] with m hm
  exact ae_of_all μ (fun ω => by
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hY : Y m ω = X m ω *ᵥ β + e m ω := hmodel m ω
    change ((A m ω)⁻¹ * A m ω) *ᵥ β + (A m ω)⁻¹ *ᵥ s m ω =
      olsBetaStar (X m ω) (Y m ω)
    rw [hY, olsBetaStar_eq_sampleGramInv_sampleCrossMoment,
      sampleCrossMoment_linear_model]
    simp [A, s, Matrix.mulVec_add, Matrix.mulVec_mulVec])

/-- 2SLS convergence as the `μ = 0` k-class/LIML moment-limit case. -/
theorem twoSLSBetaStar_tendstoInMeasure_of_normalized_moment_limits
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {β g : k → ℝ} {Q : Matrix k k ℝ}
    (h : ManyInstrumentsLIMLMomentLimitConditions μ Z X e (fun _ _ => 0) Q g)
    (hmodel : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + Q⁻¹ *ᵥ g) := by
  have hliml :=
    limlBetaStar_tendstoInMeasure_of_normalized_moment_limits
      (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e)
      (limlMuHat := fun _ _ => 0) (β := β) (g := g) (Q := Q) h hmodel
  simpa using hliml

/-- Proof-facing condition package for Hansen Theorem 12.19.

The structural fields record the model (12.73), signal condition (12.77), and
many-instrument ratio (12.76).  The moment fields are the intermediate
homoskedastic/fourth-moment consequences Hansen uses in (12.78)--(12.81);
the estimator faces are proved from normalized moment convergence by
`olsBetaStar_tendstoInMeasure_of_moment_limits`,
`twoSLSBetaStar_tendstoInMeasure_of_normalized_moment_limits`, and
`limlBetaStar_tendstoInMeasure_beta_of_normalized_moments`. -/
structure ManyInstrumentsTheorem1219Conditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Y : (m : ℕ) → Ω → Fin m → ℝ)
    (Gamma : (m : ℕ) → Matrix (ι m) k ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (H Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ)
    (alpha : ℝ) : Prop where
  alpha_nonneg : 0 ≤ alpha
  alpha_lt_one : alpha < 1
  instrument_ratio_tendsto :
    Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ)) atTop (𝓝 alpha)
  structural_model : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω
  reduced_form : ∀ (m : ℕ) (ω : Ω),
    X m ω = manyInstrumentSignal (Z m ω) (Gamma m) + u2 m ω
  H_posDef : H.PosDef
  ols_limit_matrix_nonsingular : IsUnit (H + Sigma22).det
  twoSLS_limit_matrix_nonsingular : IsUnit (H + alpha • Sigma22).det
  signal_limit : TendstoInMeasure μ
    (fun (m : ℕ) ω => manyInstrumentSignalGram (Z m ω) (Gamma m))
    atTop (fun _ => H)
  reduced_error_gram_limit : TendstoInMeasure μ
    (fun (m : ℕ) ω => sampleGram (u2 m ω))
    atTop (fun _ => Sigma22)
  reduced_error_cross_limit : TendstoInMeasure μ
    (fun (m : ℕ) ω => sampleCrossMoment (u2 m ω) (e m ω))
    atTop (fun _ => Sigma2e)
  projected_error_gram_limit : TendstoInMeasure μ
    (fun (m : ℕ) ω => manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω))
    atTop (fun _ => alpha • Sigma22)
  projected_error_cross_limit : TendstoInMeasure μ
    (fun (m : ℕ) ω => manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω))
    atTop (fun _ => alpha • Sigma2e)
  ols_moments : ManyInstrumentsOLSMomentLimitConditions
    μ X e (H + Sigma22) Sigma2e
  twoSLS_moments : ManyInstrumentsLIMLMomentLimitConditions
    μ Z X e (fun _ _ => 0) (H + alpha • Sigma22) (alpha • Sigma2e)
  liml_moments : ManyInstrumentsLIMLMomentConsistencyConditions μ Z X e limlMuHat H

/-- Build the Hansen-facing Theorem 12.19 condition package from the
reduced-form OLS and projected-2SLS assembly packages.

This keeps the final theorem surface from assuming the OLS and 2SLS
moment-limit packages directly: they are derived from the signal/error/cross
component limits that mirror Hansen's many-instrument decomposition. -/
theorem ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hpos : H.PosDef)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (h2SLS : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha)
    (hLIML : ManyInstrumentsLIMLMomentConsistencyConditions μ Z X e limlMuHat H) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha where
  alpha_nonneg := halpha_nonneg
  alpha_lt_one := halpha_lt_one
  instrument_ratio_tendsto := hratio
  structural_model := hstruct
  reduced_form := hOLS.reduced_form
  H_posDef := hpos
  ols_limit_matrix_nonsingular := hOLS.limit_nonsing
  twoSLS_limit_matrix_nonsingular := h2SLS.limit_nonsing
  signal_limit := hOLS.signal_gram_tendsto
  reduced_error_gram_limit := hOLS.reduced_error_gram_tendsto
  reduced_error_cross_limit := hOLS.reduced_error_score_tendsto
  projected_error_gram_limit := h2SLS.projected_error_gram_tendsto
  projected_error_cross_limit := h2SLS.projected_error_score_tendsto
  ols_moments :=
    ManyInstrumentsOLSMomentLimitConditions.of_reduced_form_components hOLS
  twoSLS_moments :=
    ManyInstrumentsLIMLMomentLimitConditions.of_projected_reduced_form_components h2SLS
  liml_moments := hLIML

/-- Build the Hansen-facing Theorem 12.19 condition package from reduced-form
OLS and projected-2SLS assemblies plus Hansen's LIML eigenvalue-adjustment
limit `μ̂ -> α/(1-α)`.

This wrapper removes the need to assume the LIML zero-score moment package
separately once the OLS and 2SLS moment limits have been proved. -/
theorem ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_mu_tendsto
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hpos : H.PosDef)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (h2SLS : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha)
    (hmu_meas : ∀ m, AEStronglyMeasurable (limlMuHat m) μ)
    (hmu_tendsto : TendstoInMeasure μ limlMuHat atTop
      (fun _ => alpha / (1 - alpha))) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hpos hOLS h2SLS
    (ManyInstrumentsLIMLMomentConsistencyConditions.of_ols_twoSLS_moments_mu_tendsto_posDef
      (μ := μ) (Z := Z) (X := X) (e := e) (limlMuHat := limlMuHat)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      (ManyInstrumentsOLSMomentLimitConditions.of_reduced_form_components hOLS)
      (ManyInstrumentsLIMLMomentLimitConditions.of_projected_reduced_form_components h2SLS)
      hmu_meas hmu_tendsto halpha_lt_one hpos)

/-- Build the Hansen-facing Theorem 12.19 condition package from reduced-form
OLS and projected-2SLS assemblies plus the named LIML eigenvalue limit package.

This is the certificate-shaped variant of
`ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_mu_tendsto`. -/
theorem ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_mu_limit_conditions
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hpos : H.PosDef)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (h2SLS : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha)
    (hmu : ManyInstrumentsLIMLEigenvalueLimitConditions μ limlMuHat alpha) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hpos hOLS h2SLS
    (ManyInstrumentsLIMLEigenvalueLimitConditions.toLIMLMomentConsistencyConditions_posDef
      (μ := μ) (Z := Z) (X := X) (e := e) (limlMuHat := limlMuHat)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      hmu
      (ManyInstrumentsOLSMomentLimitConditions.of_reduced_form_components hOLS)
      (ManyInstrumentsLIMLMomentLimitConditions.of_projected_reduced_form_components h2SLS)
      halpha_lt_one hpos)

/-- Build the Hansen-facing Theorem 12.19 condition package from reduced-form
OLS/projected-2SLS assemblies plus the sample LIML eigenvalue problem.

This is the theorem-facing bridge from the sample eigenvalue adjustment
`μ̂_n - (ℓ_n/n)/(1-ℓ_n/n) = o_p(1)` and Hansen's `ℓ_n/n -> α` to the LIML
cancellation package used for consistency. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_sample_eigenvalue_problem
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hpos : H.PosDef)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (h2SLS : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha)
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_mu_limit_conditions
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hpos hOLS h2SLS
    (hmu.toLIMLEigenvalueLimitConditions
      (ι := ι) (μ := μ) hratio halpha_lt_one)

/-- Ratio-facing variant of
`ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies`.

The side condition `0 ≤ α` is derived from Hansen's primitive instrument-ratio
assumption `ℓ_n/n -> α`. -/
theorem ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hpos : H.PosDef)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (h2SLS : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha)
    (hLIML : ManyInstrumentsLIMLMomentConsistencyConditions μ Z X e limlMuHat H) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hpos hOLS h2SLS hLIML

/-- Ratio-facing variant of
`ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_mu_tendsto`.

The side condition `0 ≤ α` is derived from Hansen's primitive instrument-ratio
assumption `ℓ_n/n -> α`. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_mu_tendsto_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hpos : H.PosDef)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (h2SLS : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha)
    (hmu_meas : ∀ m, AEStronglyMeasurable (limlMuHat m) μ)
    (hmu_tendsto : TendstoInMeasure μ limlMuHat atTop
      (fun _ => alpha / (1 - alpha))) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_mu_tendsto
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hpos hOLS h2SLS hmu_meas hmu_tendsto

/-- Ratio-facing variant of
`ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_mu_limit_conditions`.

The side condition `0 ≤ α` is derived from Hansen's primitive instrument-ratio
assumption `ℓ_n/n -> α`. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_mu_limit_conditions_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hpos : H.PosDef)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (h2SLS : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha)
    (hmu : ManyInstrumentsLIMLEigenvalueLimitConditions μ limlMuHat alpha) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_mu_limit_conditions
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hpos hOLS h2SLS hmu

set_option linter.style.longLine false in
/-- Ratio-facing variant of
`ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_sample_eigenvalue_problem`.

The side condition `0 ≤ α` is derived from Hansen's primitive instrument-ratio
assumption `ℓ_n/n -> α`. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_sample_eigenvalue_problem_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hpos : H.PosDef)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (h2SLS : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha)
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_sample_eigenvalue_problem
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hpos hOLS h2SLS hmu

/-- Build the Hansen-facing Theorem 12.19 condition package from reduced-form
OLS components and the lower-level projection-trace consequences for the 2SLS
projected-error moments.

This composes `ManyInstrumentsTwoSLSMomentAssemblyConditions.of_projection_trace_components`
with `ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies`, so
callers can stay at Hansen's signal/error/projection-trace layer. -/
theorem ManyInstrumentsTheorem1219Conditions.of_projection_trace_assemblies
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hpos : H.PosDef)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ)
    (hprojected_signal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hprojected_cross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_signal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (htrace : ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha)
    (h2SLS_nonsing : IsUnit (H + alpha • Sigma22).det)
    (hLIML : ManyInstrumentsLIMLMomentConsistencyConditions μ Z X e limlMuHat H) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha := by
  let h2SLS : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha :=
    ManyInstrumentsTwoSLSMomentAssemblyConditions.of_projection_trace_components
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      hOLS.reduced_form hprojected_signal_gram_meas hprojected_cross_gram_meas
      hprojected_signal_score_meas
      hprojected_signal_gram_tendsto hprojected_cross_gram_tendsto_zero
      hprojected_signal_score_tendsto_zero htrace h2SLS_nonsing
  exact
    ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hpos hOLS h2SLS hLIML

/-- Projection-trace theorem-facing constructor with the 2SLS limit
nonsingularity discharged from positive semidefiniteness of `Σ₂₂`.

This is the Hansen-facing route when the remaining projection-trace fields have
already been derived from homoskedasticity/fourth-moment assumptions: the caller
does not also need to prove `det (H + αΣ₂₂)` is a unit by hand. -/
theorem ManyInstrumentsTheorem1219Conditions.of_projection_trace_assemblies_posSemidef
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hpos : H.PosDef)
    (hSigma22 : Sigma22.PosSemidef)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ)
    (hprojected_signal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hprojected_cross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_signal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (htrace : ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha)
    (hLIML : ManyInstrumentsLIMLMomentConsistencyConditions μ Z X e limlMuHat H) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219Conditions.of_projection_trace_assemblies
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hpos hOLS
    hprojected_signal_gram_meas hprojected_cross_gram_meas
    hprojected_signal_score_meas hprojected_signal_gram_tendsto
    hprojected_cross_gram_tendsto_zero hprojected_signal_score_tendsto_zero
    htrace
    (manyInstruments_twoSLS_limit_matrix_nonsingular_of_posSemidef
      hpos hSigma22 halpha_nonneg)
    hLIML

/-- Projection-trace theorem-facing constructor with Hansen's LIML eigenvalue
adjustment limit `μ̂ -> α/(1-α)`.

This is the assembly-level route to Theorem 12.19 once the OLS reduced-form
package and the projected-error trace package are available.  It derives both
the projected 2SLS moment package and the LIML zero-score package, so callers
do not need to assume either one directly. -/
theorem ManyInstrumentsTheorem1219Conditions.of_projection_trace_assemblies_posSemidef_mu_tendsto
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hpos : H.PosDef)
    (hSigma22 : Sigma22.PosSemidef)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ)
    (hprojected_signal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hprojected_cross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_signal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (htrace : ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha)
    (hmu_meas : ∀ m, AEStronglyMeasurable (limlMuHat m) μ)
    (hmu_tendsto : TendstoInMeasure μ limlMuHat atTop
      (fun _ => alpha / (1 - alpha))) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha := by
  let h2SLS : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha :=
    ManyInstrumentsTwoSLSMomentAssemblyConditions.of_projection_trace_components_posSemidef
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      hOLS.reduced_form hprojected_signal_gram_meas hprojected_cross_gram_meas
      hprojected_signal_score_meas
      hprojected_signal_gram_tendsto hprojected_cross_gram_tendsto_zero
      hprojected_signal_score_tendsto_zero htrace hpos hSigma22 halpha_nonneg
  exact
    ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_mu_tendsto
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hpos hOLS h2SLS
      hmu_meas hmu_tendsto

/-- Theorem-facing constructor from OLS reduced-form assembly plus the
projection-trace projected-error package.

Compared with `of_projection_trace_assemblies_posSemidef_mu_tendsto`, this
wrapper also derives the projected signal Gram, signal/error cross-Gram, and
signal-score limits from the OLS reduced-form limits using `P_Z ZΓ = ZΓ` on the
eventual-a.e. nonsingular instrument branch.  The remaining projected 2SLS
substance is therefore concentrated in the trace-remainder package. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_ols_projection_trace_components_posSemidef_mu_tendsto
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hH : H.PosDef)
    (hSigma22 : Sigma22.PosSemidef)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ)
    (htrace : ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha)
    (hnonsing : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hmu_meas : ∀ m, AEStronglyMeasurable (limlMuHat m) μ)
    (hmu_tendsto : TendstoInMeasure μ limlMuHat atTop
      (fun _ => alpha / (1 - alpha))) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha := by
  let h2SLS : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha :=
    ManyInstrumentsTwoSLSMomentAssemblyConditions.of_ols_projection_trace_components_posSemidef
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      hOLS hprojected_signal_gram_meas hprojected_cross_gram_meas
      hprojected_signal_score_meas htrace
      hnonsing hH hSigma22 halpha_nonneg
  exact
    ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_mu_tendsto
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hH hOLS h2SLS
      hmu_meas hmu_tendsto

/-- Theorem-facing constructor from the named reduced-form WLLN package, the
two homoskedastic projection remainders, and the current LIML eigenvalue-limit
package.

This is the tightest current 12.19 condition constructor: OLS moments are
derived from `ManyInstrumentsReducedFormWLLNConditions`; projected-error moments
are derived from the trace ratio plus the two projection remainders; projected
signal moments are derived from `P_Z ZΓ = ZΓ` on the eventual-a.e. nonsingular
instrument branch. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_projection_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ)
    (hproj : ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2)
    (hnonsing : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hmu : ManyInstrumentsLIMLEigenvalueAlphaOverOneMinusAlphaCertificate
      μ limlMuHat alpha) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha := by
  let hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e :=
    ManyInstrumentsReducedFormWLLNConditions.toOLSMomentAssemblyConditions hRF
  let htrace : ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha :=
    ManyInstrumentsProjectedTraceMomentConditions.of_reduced_form_wlln_projection_remainders
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      hratio hnonsing hRF hproj
  exact
    ManyInstrumentsTheorem1219Conditions.of_ols_projection_trace_components_posSemidef_mu_tendsto
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF.signal_limit_posDef
      hRF.reduced_error_limit_posSemidef hOLS hprojected_signal_gram_meas
      hprojected_cross_gram_meas hprojected_signal_score_meas htrace hnonsing
      hmu.meas hmu.tendsto

/-- The reduced-form WLLN/projection-remainder constructor with the sample
LIML eigenvalue problem as input.

This wrapper derives `μ̂_n ->p α/(1-α)` from
`ManyInstrumentsLIMLSampleEigenvalueProblemConditions` before applying the
existing many-instrument LIML cancellation route. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_sample_eigenvalue_problem
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ)
    (hproj : ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2)
    (hnonsing : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_projection_remainders
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF
    hprojected_signal_gram_meas hprojected_cross_gram_meas
    hprojected_signal_score_meas hproj hnonsing
    (hmu.toLIMLEigenvalueLimitConditions
      (ι := ι) (μ := μ) hratio halpha_lt_one)

/-- Theorem-facing reduced-form WLLN constructor from raw homoskedastic
projection-remainder fields and the named LIML eigenvalue limit package.

This variant derives the `trace_ratio_meas` field of
`ManyInstrumentsHomoskedasticProjectionRemainderConditions` from a.e.
nonsingular instruments and accepts `ManyInstrumentsLIMLEigenvalueLimitConditions`
directly.  The three displayed Theorem 12.19 probability limits are still the
same limits proved by `manyInstruments_estimators_minus_beta_theorem12_19`. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_ae_nonsingular_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hprojected_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω)) μ)
    (hprojected_error_cross_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω)) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) • sampleGram (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (u2 m ω) (e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hmu : ManyInstrumentsLIMLEigenvalueLimitConditions μ limlMuHat alpha) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha := by
  let hproj : ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2 :=
    ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_ae_nonsingular_remainders
      (μ := μ) (Z := Z) (e := e) (u2 := u2)
      hnonsing hprojected_error_gram_meas hprojected_error_cross_meas
      hprojected_error_gram_trace_remainder_tendsto_zero
      hprojected_error_cross_trace_remainder_tendsto_zero
  have hnonsing_eventually : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)) :=
    Filter.Eventually.of_forall hnonsing
  exact
    ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_projection_remainders
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF
      hprojected_signal_gram_meas hprojected_cross_gram_meas
      hprojected_signal_score_meas hproj hnonsing_eventually
      (show ManyInstrumentsLIMLEigenvalueAlphaOverOneMinusAlphaCertificate
          μ limlMuHat alpha from hmu)

/-- Theorem-facing constructor from the named reduced-form WLLN package and the
two homoskedastic projection remainders, deriving all projected signal
component measurability and limits from the primitive reduced-form package on
an a.e. nonsingular instrument branch.

Compared with `of_reduced_form_wlln_projection_remainders`, this version no
longer asks for projected signal Gram, cross-Gram, or score measurability: they
are inherited from the corresponding unprojected fields in `hRF`. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_projection_remainders_ae_nonsingular
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hproj : ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hmu : ManyInstrumentsLIMLEigenvalueAlphaOverOneMinusAlphaCertificate
      μ limlMuHat alpha) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha := by
  let hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e :=
    ManyInstrumentsReducedFormWLLNConditions.toOLSMomentAssemblyConditions hRF
  have hnonsing_eventually : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)) :=
    Filter.Eventually.of_forall hnonsing
  let htrace : ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha :=
    ManyInstrumentsProjectedTraceMomentConditions.of_reduced_form_wlln_projection_remainders
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      hratio hnonsing_eventually hRF hproj
  let h2SLS : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha :=
    ManyInstrumentsTwoSLSMomentAssemblyConditions.of_ols_projection_trace_ae_nonsingular
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      hOLS htrace hnonsing hRF.signal_limit_posDef
      hRF.reduced_error_limit_posSemidef halpha_nonneg
  exact
    ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_mu_limit_conditions
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF.signal_limit_posDef
      hOLS h2SLS hmu

/-- Theorem-facing reduced-form WLLN constructor from raw homoskedastic
projection-remainder fields and a.e. nonsingular instruments.

This is the strongest currently formalized primitive route to the Theorem
12.19 condition package: unprojected reduced-form WLLNs come from `hRF`,
projected signal components are derived from `P_Z ZΓ = ZΓ`, trace-ratio
measurability/convergence is derived from nonsingularity and the instrument
ratio, and the only remaining projected-error inputs are the two homoskedastic
trace-remainder WLLNs plus projected-error measurability. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_ae_nonsingular_projection_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hprojected_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω)) μ)
    (hprojected_error_cross_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω)) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) • sampleGram (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (u2 m ω) (e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hmu : ManyInstrumentsLIMLEigenvalueLimitConditions μ limlMuHat alpha) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha := by
  let hproj : ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2 :=
    ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_ae_nonsingular_remainders
      (μ := μ) (Z := Z) (e := e) (u2 := u2)
      hnonsing hprojected_error_gram_meas hprojected_error_cross_meas
      hprojected_error_gram_trace_remainder_tendsto_zero
      hprojected_error_cross_trace_remainder_tendsto_zero
  exact
    ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_projection_remainders_ae_nonsingular
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hproj hnonsing
      (show ManyInstrumentsLIMLEigenvalueAlphaOverOneMinusAlphaCertificate
          μ limlMuHat alpha from hmu)

namespace ManyInstrumentsTheorem1219Conditions

open ManyInstrumentsHomoskedasticProjectionRemainderConditions

/-- Theorem-facing reduced-form WLLN constructor with sample LIML eigenvalue
input and entrywise projected-error trace remainders.

This is the non-stacked analogue of
`of_stacked_primitive_wlln_ae_nonsingular_sample_eigenvalue_entrywise_remainders`:
the reduced-form WLLN package is already available, projected-error
measurability is derived from finite-sample measurability of `Z`, `u₂`, and
`e`, scalar entrywise trace-remainder WLLNs assemble the full homoskedastic
projection package, and the LIML adjustment-gap WLLN supplies
`μ̂_n ->p α / (1 - α)`. -/
theorem of_reduced_form_wlln_ae_nonsingular_sample_eigenvalue_entrywise_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hentry : ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
      μ Z e u2)
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha := by
  let hproj : ManyInstrumentsHomoskedasticProjectionRemainderConditions
      μ Z e u2 :=
    of_entrywise_measurable_ae_nonsingular_remainders
      (μ := μ) (Z := Z) (e := e) (u2 := u2)
      hnonsing hZ_meas hu2_meas he_meas hentry
  exact
    ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_projection_remainders_ae_nonsingular
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hproj hnonsing
      (hmu.toLIMLEigenvalueLimitConditions
        (ι := ι) (μ := μ) hratio halpha_lt_one)

/-- Theorem-facing reduced-form WLLN constructor with the remaining projected
error and LIML eigenvalue gaps reduced to scalar Chapter 7 WLLNs.

Compared with
`of_reduced_form_wlln_ae_nonsingular_sample_eigenvalue_entrywise_remainders`,
this version does not take the entrywise projected-error package or the sample
eigenvalue problem package as primitives.  The projected-error package is
assembled from scalar row WLLNs, and the LIML sample-eigenvalue package is
assembled from the scalar adjustment-gap WLLN. -/
theorem of_reduced_form_wlln_ae_nonsingular_scalar_wlln_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : k → k → ℕ → Ω → ℝ}
    {cross_row : k → ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  of_reduced_form_wlln_ae_nonsingular_sample_eigenvalue_entrywise_remainders
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
    hZ_meas hu2_meas he_meas hremainder.toEntryWLLNConditions
    hmu.toSampleEigenvalueProblemConditions

set_option linter.style.longLine false in
/-- Theorem-facing reduced-form WLLN constructor with the projected-error
remainders supplied by their exact canonical row averages.

This is the narrow Hansen-facing boundary for the homoskedastic projection
step: the caller proves convergence of the finite-sample canonical row
averages defined from `P_Z*`, `u₂`, and `e`; the entrywise projected-error
package and the sample LIML eigenvalue package are assembled internally. -/
theorem of_reduced_form_wlln_ae_nonsingular_canonical_row_average_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hcanonical :
      ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions
        μ Z e u2)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  of_reduced_form_wlln_ae_nonsingular_sample_eigenvalue_entrywise_remainders
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
    hZ_meas hu2_meas he_meas hcanonical.toEntryWLLNConditions
    hmu.toSampleEigenvalueProblemConditions

set_option linter.style.longLine false in
/-- Theorem-facing reduced-form WLLN constructor with canonical projected-error
row averages and a finite-sample Rayleigh/eigenvalue adjustment-gap WLLN.

This keeps the remaining LIML primitive at Hansen's generalized Rayleigh
eigenvalue problem for `[Y X]`, then forgets only that audit field to reuse the
existing sample-eigenvalue constructor. -/
theorem of_reduced_form_wlln_ae_nonsingular_canonical_row_average_rayleigh_adjustment_gap
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hcanonical :
      ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions
        μ Z e u2)
    (hrayleigh :
      ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions
        (ι := ι) μ Z X Y limlMuHat gap_row) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  of_reduced_form_wlln_ae_nonsingular_canonical_row_average_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
    hZ_meas hu2_meas he_meas hcanonical
    hrayleigh.toAdjustmentGapWLLNConditions

set_option linter.style.longLine false in
/-- Theorem-facing reduced-form WLLN constructor with the projected-error
remainders supplied by finite-dimensional row WLLNs.

Compared with
`of_reduced_form_wlln_ae_nonsingular_scalar_wlln_sample_eigenvalue`, this
keeps the projected-error input at the matrix/vector row-process level and
only decomposes to coordinates internally. -/
theorem of_reduced_form_wlln_ae_nonsingular_row_wlln_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  of_reduced_form_wlln_ae_nonsingular_sample_eigenvalue_entrywise_remainders
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
    hZ_meas hu2_meas he_meas hremainder.toEntryWLLNConditions
    hmu.toSampleEigenvalueProblemConditions

set_option linter.style.longLine false in
/-- Theorem-facing reduced-form WLLN constructor with row-WLLN projected-error
remainders and Hansen's finite-sample Rayleigh adjustment-gap input.

This removes the direct canonical-row-average and scalar sample-eigenvalue
primitives from the caller boundary: the canonical averages are derived from
the row-WLLN package, and the sample-eigenvalue adjustment package is derived
from the finite-sample Rayleigh certificate. -/
theorem of_reduced_form_wlln_ae_nonsingular_row_wlln_rayleigh_adjustment_gap
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hrayleigh :
      ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions
        (ι := ι) μ Z X Y limlMuHat gap_row) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  of_reduced_form_wlln_ae_nonsingular_canonical_row_average_rayleigh_adjustment_gap
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
    hZ_meas hu2_meas he_meas hremainder.toCanonicalRowAverageConditions
    hrayleigh

set_option linter.style.longLine false in
/-- Theorem-facing reduced-form WLLN constructor from one joint row process for
the projected-error trace remainders and Hansen's finite-sample Rayleigh
adjustment gap.

This is the condition-package analogue of the direct joint-row endpoints.  It
keeps the remaining stochastic input as a single row process and derives both
the projected-error row-WLLN package and the LIML Rayleigh adjustment-gap
package internally. -/
theorem of_reduced_form_wlln_ae_nonsingular_projected_error_rayleigh_joint_row_wlln
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hjoint :
      ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions
        (ι := ι) μ Z X Y e u2 limlMuHat gram_row cross_row gap_row) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  of_reduced_form_wlln_ae_nonsingular_row_wlln_rayleigh_adjustment_gap
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
    (cross_row := cross_row) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
    hZ_meas hu2_meas he_meas hjoint.toProjectedErrorRowWLLNConditions
    hjoint.toRayleighAdjustmentGapWLLNConditions

set_option linter.style.longLine false in
/-- Theorem-facing reduced-form WLLN constructor from one raw joint row
process for the projected-error trace remainders and LIML Rayleigh
adjustment gap.

This wrapper moves the public boundary one step closer to Hansen's
homoskedastic row calculation: the component row-WLLN packages are derived
from a single integrable iid row object by continuous projection. -/
theorem of_reduced_form_wlln_ae_nonsingular_raw_projected_error_rayleigh_joint_row_wlln
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {row : ℕ → Ω → (Matrix k k ℝ × (k → ℝ)) × ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hrayleigh : ∀ m ω,
      LIMLRayleighMinimizer
        (manyInstrumentsLIMLSampleRayleighNumerator (Z m ω) (X m ω) (Y m ω))
        (manyInstrumentsLIMLSampleRayleighDenominator (Z m ω) (X m ω) (Y m ω))
        (limlMuHat m ω))
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.1)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.2)
    (hadjustment_gap_eq_avg : ∀ (m : ℕ) (ω : Ω),
      limlMuHat m ω -
          manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).2)
    (hrow_integrable : Integrable (row 0) μ)
    (hrow_indep : iIndepFun row μ)
    (hrow_ident : ∀ i, IdentDistrib (row i) (row 0) μ μ)
    (hrow_mean_zero : μ[row 0] = 0) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  of_reduced_form_wlln_ae_nonsingular_projected_error_rayleigh_joint_row_wlln
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat)
    (gram_row := fun i ω => (row i ω).1.1)
    (cross_row := fun i ω => (row i ω).1.2)
    (gap_row := fun i ω => (row i ω).2) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
    hZ_meas hu2_meas he_meas
    (ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions.of_raw_joint_row
      (μ := μ) (ι := ι) (Z := Z) (X := X) (Y := Y) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (row := row)
      hrayleigh hgram_remainder_eq_avg hcross_remainder_eq_avg
      hadjustment_gap_eq_avg hrow_integrable hrow_indep hrow_ident
      hrow_mean_zero)

set_option linter.style.longLine false in
/-- Ratio-facing package constructor for Theorem 12.19 from one raw iid joint
row process for the projected-error trace remainders and LIML Rayleigh
adjustment gap.

This removes the redundant `0 ≤ α` caller premise from the raw-row constructor:
nonnegativity follows from Hansen's instrument-count ratio limit. -/
theorem of_reduced_form_wlln_ae_nonsingular_raw_projected_error_rayleigh_joint_row_wlln_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {row : ℕ → Ω → (Matrix k k ℝ × (k → ℝ)) × ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hrayleigh : ∀ m ω,
      LIMLRayleighMinimizer
        (manyInstrumentsLIMLSampleRayleighNumerator (Z m ω) (X m ω) (Y m ω))
        (manyInstrumentsLIMLSampleRayleighDenominator (Z m ω) (X m ω) (Y m ω))
        (limlMuHat m ω))
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.1)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.2)
    (hadjustment_gap_eq_avg : ∀ (m : ℕ) (ω : Ω),
      limlMuHat m ω -
          manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).2)
    (hrow_integrable : Integrable (row 0) μ)
    (hrow_indep : iIndepFun row μ)
    (hrow_ident : ∀ i, IdentDistrib (row i) (row 0) μ μ)
    (hrow_mean_zero : μ[row 0] = 0) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha :=
  of_reduced_form_wlln_ae_nonsingular_raw_projected_error_rayleigh_joint_row_wlln
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (row := row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hrayleigh hgram_remainder_eq_avg hcross_remainder_eq_avg
    hadjustment_gap_eq_avg hrow_integrable hrow_indep hrow_ident hrow_mean_zero

end ManyInstrumentsTheorem1219Conditions

/-- Theorem-facing constructor from stacked row WLLNs, the two homoskedastic
projection remainders, and Hansen's LIML eigenvalue adjustment limit.

This composes `ManyInstrumentsReducedFormWLLNConditions.of_stacked_error_wlln`
with `ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_projection_remainders`.
Thus the unprojected reduced-form error Gram and error-score WLLNs are derived
from ordinary Chapter 7 iid-row WLLNs, rather than being supplied as fields of
the 12.19 condition package. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_stacked_error_wlln_projection_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hsignal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentSignalGram (Z m ω) (Gamma m)) μ)
    (hcross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentReducedFormCrossGram
        (Z m ω) (Gamma m) (stackRegressors u2 m ω)) μ)
    (hsignal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m))
          (stackErrors e m ω)) μ)
    (hsignal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hcross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentReducedFormCrossGram
          (Z m ω) (Gamma m) (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hsignal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m))
          (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hint_outer : Integrable (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hindep_outer :
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))))
    (hident_outer : ∀ i,
      IdentDistrib
        (fun ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))
        (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hint_cross : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hindep_cross :
      Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • u2 i ω)))
    (hident_cross : ∀ i,
      IdentDistrib
        (fun ω => e i ω • u2 i ω)
        (fun ω => e 0 ω • u2 0 ω) μ μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (stackRegressors u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (stackErrors e m ω)) μ)
    (hproj : ManyInstrumentsHomoskedasticProjectionRemainderConditions
      μ Z (fun m ω => stackErrors e m ω) (fun m ω => stackRegressors u2 m ω))
    (hnonsing : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hmu : ManyInstrumentsLIMLEigenvalueAlphaOverOneMinusAlphaCertificate
      μ limlMuHat alpha) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) limlMuHat β H Sigma22 Sigma2e alpha := by
  let hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H Sigma22 Sigma2e :=
    ManyInstrumentsReducedFormWLLNConditions.of_stacked_error_wlln
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      hreduced hgram_meas hscore_meas hsignal_gram_meas hcross_gram_meas
      hsignal_score_meas hsignal_gram_tendsto hcross_gram_tendsto_zero
      hsignal_score_tendsto_zero hint_outer hindep_outer hident_outer hSigma22
      hint_cross hindep_cross hident_cross hSigma2e hH hSigma22_psd
  exact
    ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_projection_remainders
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
      (e := fun m ω => stackErrors e m ω)
      (u2 := fun m ω => stackRegressors u2 m ω)
      (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF
      hprojected_signal_gram_meas hprojected_cross_gram_meas
      hprojected_signal_score_meas hproj hnonsing hmu

/-- Theorem-facing constructor from stacked row WLLNs, a.e. nonsingular
instrument Grams, raw projected-error trace remainders, and Hansen's LIML
eigenvalue adjustment limit.

Compared with `of_stacked_error_wlln_projection_remainders`, this route derives
the projected signal Gram/cross/score measurability and limits from the
unprojected reduced-form WLLN package on the a.e. nonsingular instrument branch.
The only projected-error inputs that remain are the two substantive
homoskedastic trace-remainder WLLNs and their measurability fields. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_stacked_error_wlln_ae_nonsingular_projection_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hsignal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentSignalGram (Z m ω) (Gamma m)) μ)
    (hcross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentReducedFormCrossGram
        (Z m ω) (Gamma m) (stackRegressors u2 m ω)) μ)
    (hsignal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m))
          (stackErrors e m ω)) μ)
    (hsignal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hcross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentReducedFormCrossGram
          (Z m ω) (Gamma m) (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hsignal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m))
          (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hint_outer : Integrable (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hindep_outer :
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))))
    (hident_outer : ∀ i,
      IdentDistrib
        (fun ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))
        (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hint_cross : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hindep_cross :
      Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • u2 i ω)))
    (hident_cross : ∀ i,
      IdentDistrib
        (fun ω => e i ω • u2 i ω)
        (fun ω => e 0 ω • u2 0 ω) μ μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hprojected_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedErrorGram
          (Z m ω) (stackRegressors u2 m ω)) μ)
    (hprojected_error_cross_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedErrorCross
          (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω)) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (stackRegressors u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleGram (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross
            (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (stackRegressors u2 m ω) (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hmu : ManyInstrumentsLIMLEigenvalueLimitConditions μ limlMuHat alpha) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) limlMuHat β H Sigma22 Sigma2e alpha := by
  let hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H Sigma22 Sigma2e :=
    ManyInstrumentsReducedFormWLLNConditions.of_stacked_error_wlln
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      hreduced hgram_meas hscore_meas hsignal_gram_meas hcross_gram_meas
      hsignal_score_meas hsignal_gram_tendsto hcross_gram_tendsto_zero
      hsignal_score_tendsto_zero hint_outer hindep_outer hident_outer hSigma22
      hint_cross hindep_cross hident_cross hSigma2e hH hSigma22_psd
  exact
    ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_ae_nonsingular_projection_remainders
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
      (e := fun m ω => stackErrors e m ω)
      (u2 := fun m ω => stackRegressors u2 m ω)
      (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
      hprojected_error_gram_meas hprojected_error_cross_meas
      hprojected_error_gram_trace_remainder_tendsto_zero
      hprojected_error_cross_trace_remainder_tendsto_zero hmu

/-- Theorem-facing constructor from primitive transformed instrument WLLNs,
Chapter 7 stacked-row WLLNs for reduced-form errors, a.e. nonsingular
instrument Grams, raw projected-error trace remainders, and Hansen's LIML
eigenvalue adjustment limit.

This is the tightest current route for the many-instrument theorem.  It keeps
the primitive `Q̂_ZZ`, `Q̂_Zu₂`, and `n⁻¹Z'e` inputs in the named
`ManyInstrumentsPrimitiveInstrumentMomentWLLNConditions` package, derives the
ordinary reduced-form WLLNs from Chapter 7, derives projected signal components
from `P_Z ZΓ = ZΓ`, and leaves only the two homoskedastic projection-remainder
WLLNs plus the sample LIML eigenvalue limit as substantive 12.19 inputs. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_stacked_primitive_wlln_ae_nonsingular_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hinst : ManyInstrumentsPrimitiveInstrumentMomentWLLNConditions
      μ Z Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H)
    (hint_outer : Integrable (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hindep_outer :
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))))
    (hident_outer : ∀ i,
      IdentDistrib
        (fun ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))
        (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hint_cross : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hindep_cross :
      Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • u2 i ω)))
    (hident_cross : ∀ i,
      IdentDistrib
        (fun ω => e i ω • u2 i ω)
        (fun ω => e 0 ω • u2 0 ω) μ μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hprojected_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedErrorGram
          (Z m ω) (stackRegressors u2 m ω)) μ)
    (hprojected_error_cross_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedErrorCross
          (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω)) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (stackRegressors u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleGram (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross
            (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (stackRegressors u2 m ω) (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hmu : ManyInstrumentsLIMLEigenvalueLimitConditions μ limlMuHat alpha) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) limlMuHat β H Sigma22 Sigma2e alpha := by
  let hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H Sigma22 Sigma2e :=
    ManyInstrumentsReducedFormWLLNConditions.of_stacked_error_primitive_instrument_moment_wlln
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      hreduced hgram_meas hscore_meas hinst hint_outer hindep_outer
      hident_outer hSigma22 hint_cross hindep_cross hident_cross hSigma2e
      hH hSigma22_psd
  exact
    ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_ae_nonsingular_projection_remainders
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
      (e := fun m ω => stackErrors e m ω)
      (u2 := fun m ω => stackRegressors u2 m ω)
      (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
      hprojected_error_gram_meas hprojected_error_cross_meas
      hprojected_error_gram_trace_remainder_tendsto_zero
      hprojected_error_cross_trace_remainder_tendsto_zero hmu

/-- The tightest current theorem-facing constructor with the sample LIML
eigenvalue problem instead of a direct `μ̂ -> α/(1-α)` limit certificate.

This composes the primitive transformed-instrument WLLN route with
`ManyInstrumentsLIMLSampleEigenvalueProblemConditions.toLIMLEigenvalueLimitConditions`.
It does not prove the remaining raw many-instrument eigenvalue/Rayleigh
argument; the substantive LIML input is still the adjustment-gap WLLN. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_stacked_primitive_wlln_ae_nonsingular_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hinst : ManyInstrumentsPrimitiveInstrumentMomentWLLNConditions
      μ Z Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H)
    (hint_outer : Integrable (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hindep_outer :
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))))
    (hident_outer : ∀ i,
      IdentDistrib
        (fun ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))
        (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hint_cross : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hindep_cross :
      Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • u2 i ω)))
    (hident_cross : ∀ i,
      IdentDistrib
        (fun ω => e i ω • u2 i ω)
        (fun ω => e 0 ω • u2 0 ω) μ μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hprojected_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedErrorGram
          (Z m ω) (stackRegressors u2 m ω)) μ)
    (hprojected_error_cross_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedErrorCross
          (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω)) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (stackRegressors u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleGram (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross
            (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (stackRegressors u2 m ω) (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219Conditions.of_stacked_primitive_wlln_ae_nonsingular_remainders
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
    (e := e) (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hreduced hstruct hgram_meas
    hscore_meas hinst hint_outer hindep_outer hident_outer hSigma22
    hint_cross hindep_cross hident_cross hSigma2e hH hSigma22_psd
    hnonsing hprojected_error_gram_meas hprojected_error_cross_meas
    hprojected_error_gram_trace_remainder_tendsto_zero
    hprojected_error_cross_trace_remainder_tendsto_zero
    (hmu.toLIMLEigenvalueLimitConditions
      (ι := ι) (μ := μ) hratio halpha_lt_one)

set_option linter.style.longLine false in
/-- The tight primitive/sample-eigenvalue Theorem 12.19 route with
projected-error measurability derived from finite-sample measurability.

Compared with
`ManyInstrumentsTheorem1219Conditions.of_stacked_primitive_wlln_ae_nonsingular_sample_eigenvalue`,
this wrapper no longer asks for measurability of
`u₂'P_Z*u₂/n` or `u₂'P_Z*e/n` directly.  It derives those fields from
measurability of `Z m`, row measurability of the stacked reduced-form error
process `u₂`, and row measurability of `e`; the two homoskedastic
trace-remainder WLLNs and the sample LIML eigenvalue adjustment gap remain as
the substantive stochastic inputs. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_stacked_primitive_wlln_ae_nonsingular_sample_eigenvalue_measurable_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hinst : ManyInstrumentsPrimitiveInstrumentMomentWLLNConditions
      μ Z Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H)
    (hint_outer : Integrable (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hindep_outer :
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))))
    (hident_outer : ∀ i,
      IdentDistrib
        (fun ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))
        (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hint_cross : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hindep_cross :
      Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • u2 i ω)))
    (hident_cross : ∀ i,
      IdentDistrib
        (fun ω => e i ω • u2 i ω)
        (fun ω => e 0 ω • u2 0 ω) μ μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ i, AEStronglyMeasurable (u2 i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (stackRegressors u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleGram (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross
            (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (stackRegressors u2 m ω) (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) limlMuHat β H Sigma22 Sigma2e alpha := by
  let hproj : ManyInstrumentsHomoskedasticProjectionRemainderConditions
      μ Z (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) :=
    ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_stacked_measurable_ae_nonsingular_remainders
      (μ := μ) (Z := Z) (e := e) (u2 := u2)
      hnonsing hZ_meas hu2_meas he_meas
      hprojected_error_gram_trace_remainder_tendsto_zero
      hprojected_error_cross_trace_remainder_tendsto_zero
  exact
    ManyInstrumentsTheorem1219Conditions.of_stacked_primitive_wlln_ae_nonsingular_sample_eigenvalue
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
      (e := e) (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hreduced hstruct hgram_meas
      hscore_meas hinst hint_outer hindep_outer hident_outer hSigma22
      hint_cross hindep_cross hident_cross hSigma2e hH hSigma22_psd
      hnonsing hproj.projected_error_gram_meas
      hproj.projected_error_cross_meas
      hproj.projected_error_gram_trace_remainder_tendsto_zero
      hproj.projected_error_cross_trace_remainder_tendsto_zero hmu

set_option linter.style.longLine false in
/-- The tight primitive/sample-eigenvalue Theorem 12.19 route with
projected-error trace remainders supplied entrywise.

Compared with
`ManyInstrumentsTheorem1219Conditions.of_stacked_primitive_wlln_ae_nonsingular_sample_eigenvalue_measurable_remainders`,
this wrapper reduces the remaining homoskedastic projection input to scalar
WLLNs for each Gram entry and score coordinate.  Finite-sample projected-error
measurability and the full matrix/vector remainder package are then derived by
`ManyInstrumentsHomoskedasticProjectionRemainderConditions.of_stacked_entrywise_measurable_ae_nonsingular_remainders`. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_stacked_primitive_wlln_ae_nonsingular_sample_eigenvalue_entrywise_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hinst : ManyInstrumentsPrimitiveInstrumentMomentWLLNConditions
      μ Z Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H)
    (hint_outer : Integrable (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hindep_outer :
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))))
    (hident_outer : ∀ i,
      IdentDistrib
        (fun ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))
        (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hint_cross : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hindep_cross :
      Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • u2 i ω)))
    (hident_cross : ∀ i,
      IdentDistrib
        (fun ω => e i ω • u2 i ω)
        (fun ω => e 0 ω • u2 0 ω) μ μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ i, AEStronglyMeasurable (u2 i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hentry :
      ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
        μ Z (fun m ω => stackErrors e m ω)
          (fun m ω => stackRegressors u2 m ω))
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219Conditions.of_stacked_primitive_wlln_ae_nonsingular_sample_eigenvalue_measurable_remainders
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
    (e := e) (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hreduced hstruct hgram_meas
    hscore_meas hinst hint_outer hindep_outer hident_outer hSigma22
    hint_cross hindep_cross hident_cross hSigma2e hH hSigma22_psd
    hnonsing hZ_meas hu2_meas he_meas
    hentry.gram_tendsto_zero hentry.cross_tendsto_zero hmu

/-- Theorem-facing constructor replacing the primitive transformed-instrument
WLLN package by fixed-codomain compressed-signal WLLNs.

This is the current tightest route when `ZΓ` has been identified with a fixed
`k`-dimensional row process.  The raw varying-dimension `Q̂_ZZ`, `Q̂_Zu₂`, and
`n⁻¹Z'e` WLLNs are then derived by
`ManyInstrumentsCompressedSignalWLLNConditions.toPrimitiveInstrumentMomentWLLNConditions`;
the projected-error trace remainders and sample LIML eigenvalue adjustment gap
remain explicit inputs. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_compressed_signal_wlln_ae_nonsingular_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {signal : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hcomp : ManyInstrumentsCompressedSignalWLLNConditions
      μ Z Gamma signal e u2 H)
    (hint_outer : Integrable (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hindep_outer :
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))))
    (hident_outer : ∀ i,
      IdentDistrib
        (fun ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))
        (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hint_cross : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hindep_cross :
      Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • u2 i ω)))
    (hident_cross : ∀ i,
      IdentDistrib
        (fun ω => e i ω • u2 i ω)
        (fun ω => e 0 ω • u2 0 ω) μ μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hprojected_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedErrorGram
          (Z m ω) (stackRegressors u2 m ω)) μ)
    (hprojected_error_cross_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedErrorCross
          (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω)) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (stackRegressors u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleGram (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross
            (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (stackRegressors u2 m ω) (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219Conditions.of_stacked_primitive_wlln_ae_nonsingular_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
    (e := e) (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hreduced hstruct hgram_meas
    hscore_meas hcomp.toPrimitiveInstrumentMomentWLLNConditions
    hint_outer hindep_outer hident_outer hSigma22 hint_cross hindep_cross
    hident_cross hSigma2e hH hSigma22_psd hnonsing
    hprojected_error_gram_meas hprojected_error_cross_meas
    hprojected_error_gram_trace_remainder_tendsto_zero
    hprojected_error_cross_trace_remainder_tendsto_zero hmu

set_option linter.style.longLine false in
/-- Theorem-facing constructor from one iid compressed row process.

This wrapper combines the compressed-signal WLLN route with the measurable
projection-remainder route.  From joint iid rows `((ZΓ)_i, u₂ᵢ, eᵢ)` it derives
the primitive transformed-instrument WLLNs and the independence/identical-law
fields for the ordinary reduced-form error WLLNs.  It still leaves the
integrability and mean identities, the two homoskedastic trace-remainder WLLNs,
and the sample LIML eigenvalue adjustment gap as explicit stochastic inputs. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_iid_compressed_signal_ae_nonsingular_sample_eigenvalue_measurable_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {signal : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hcompressed : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentSignal (Z m ω) (Gamma m) = stackRegressors signal m ω)
    (hsignal_meas : ∀ i, AEStronglyMeasurable (signal i) μ)
    (hjoint_indep : iIndepFun
      (fun i ω => ((signal i ω, u2 i ω), e i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => ((signal i ω, u2 i ω), e i ω))
        (fun ω => ((signal 0 ω, u2 0 ω), e 0 ω)) μ μ)
    (hsignal_norm_sq : Integrable (fun ω => ‖signal 0 ω‖ ^ 2) μ)
    (hsignal_gram_limit : H = popGram μ signal)
    (hsym_cross_integrable : Integrable
      (fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)) μ)
    (hsym_cross_mean_zero :
      μ[fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)] = 0)
    (hsignal_score_integrable : Integrable (fun ω => e 0 ω • signal 0 ω) μ)
    (hsignal_score_mean_zero : μ[fun ω => e 0 ω • signal 0 ω] = 0)
    (hu2_outer_integrable : Integrable
      (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hu2_score_integrable : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ i, AEStronglyMeasurable (u2 i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (stackRegressors u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleGram (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross
            (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (stackRegressors u2 m ω) (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) limlMuHat β H Sigma22 Sigma2e alpha := by
  let hinst : ManyInstrumentsPrimitiveInstrumentMomentWLLNConditions
      μ Z Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H :=
    ManyInstrumentsPrimitiveInstrumentMomentWLLNConditions.of_iid_compressed_signal
      (μ := μ) (Z := Z) (Gamma := Gamma) (signal := signal) (e := e)
      (u2 := u2) (H := H)
      hcompressed hsignal_meas hjoint_indep hjoint_ident hsignal_norm_sq
      hsignal_gram_limit hsym_cross_integrable hsym_cross_mean_zero
      hsignal_score_integrable hsignal_score_mean_zero
  have hindep_outer :
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))) := by
    have hindep : iIndepFun
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω)) μ := by
      simpa [Function.comp] using
        hjoint_indep.comp
          (fun (_ : ℕ) (z : ((k → ℝ) × (k → ℝ)) × ℝ) =>
            Matrix.vecMulVec z.1.2 z.1.2)
          (fun (_ : ℕ) => measurable_manyInstrumentReducedErrorOuter_joint)
    intro i j hij
    exact hindep.indepFun hij
  have hident_outer : ∀ i,
      IdentDistrib
        (fun ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))
        (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ μ := by
    intro i
    simpa [Function.comp] using
      (hjoint_ident i).comp measurable_manyInstrumentReducedErrorOuter_joint
  have hindep_cross :
      Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • u2 i ω)) := by
    have hindep : iIndepFun (fun i ω => e i ω • u2 i ω) μ := by
      simpa [Function.comp] using
        hjoint_indep.comp
          (fun (_ : ℕ) (z : ((k → ℝ) × (k → ℝ)) × ℝ) => z.2 • z.1.2)
          (fun (_ : ℕ) => measurable_manyInstrumentReducedErrorScore_joint)
    intro i j hij
    exact hindep.indepFun hij
  have hident_cross : ∀ i,
      IdentDistrib
        (fun ω => e i ω • u2 i ω)
        (fun ω => e 0 ω • u2 0 ω) μ μ := by
    intro i
    simpa [Function.comp] using
      (hjoint_ident i).comp measurable_manyInstrumentReducedErrorScore_joint
  exact
    ManyInstrumentsTheorem1219Conditions.of_stacked_primitive_wlln_ae_nonsingular_sample_eigenvalue_measurable_remainders
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
      (e := e) (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hreduced hstruct hgram_meas
      hscore_meas hinst hu2_outer_integrable hindep_outer hident_outer
      hSigma22 hu2_score_integrable hindep_cross hident_cross hSigma2e
      hH hSigma22_psd hnonsing hZ_meas hu2_meas he_meas
      hprojected_error_gram_trace_remainder_tendsto_zero
      hprojected_error_cross_trace_remainder_tendsto_zero hmu

set_option linter.style.longLine false in
/-- The iid compressed-signal Theorem 12.19 route with projected-error
trace remainders supplied entrywise.

This is the most concrete current primitive-facing wrapper in this file.  The
ordinary reduced-form WLLNs and transformed-instrument WLLNs are derived from
one iid row process `((ZΓ)_i,u₂_i,e_i)`, while the remaining homoskedastic
projection step is reduced to scalar entrywise WLLN certificates. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_iid_compressed_signal_ae_nonsingular_sample_eigenvalue_entrywise_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {signal : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hcompressed : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentSignal (Z m ω) (Gamma m) = stackRegressors signal m ω)
    (hsignal_meas : ∀ i, AEStronglyMeasurable (signal i) μ)
    (hjoint_indep : iIndepFun
      (fun i ω => ((signal i ω, u2 i ω), e i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => ((signal i ω, u2 i ω), e i ω))
        (fun ω => ((signal 0 ω, u2 0 ω), e 0 ω)) μ μ)
    (hsignal_norm_sq : Integrable (fun ω => ‖signal 0 ω‖ ^ 2) μ)
    (hsignal_gram_limit : H = popGram μ signal)
    (hsym_cross_integrable : Integrable
      (fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)) μ)
    (hsym_cross_mean_zero :
      μ[fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)] = 0)
    (hsignal_score_integrable : Integrable (fun ω => e 0 ω • signal 0 ω) μ)
    (hsignal_score_mean_zero : μ[fun ω => e 0 ω • signal 0 ω] = 0)
    (hu2_outer_integrable : Integrable
      (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hu2_score_integrable : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ i, AEStronglyMeasurable (u2 i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hentry :
      ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
        μ Z (fun m ω => stackErrors e m ω)
          (fun m ω => stackRegressors u2 m ω))
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219Conditions.of_iid_compressed_signal_ae_nonsingular_sample_eigenvalue_measurable_remainders
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
    (signal := signal) (e := e) (u2 := u2) (limlMuHat := limlMuHat)
    (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hreduced hstruct hgram_meas
    hscore_meas hcompressed hsignal_meas hjoint_indep hjoint_ident
    hsignal_norm_sq hsignal_gram_limit hsym_cross_integrable
    hsym_cross_mean_zero hsignal_score_integrable hsignal_score_mean_zero
    hu2_outer_integrable hSigma22 hu2_score_integrable hSigma2e hH
    hSigma22_psd hnonsing hZ_meas hu2_meas he_meas
    hentry.gram_tendsto_zero hentry.cross_tendsto_zero hmu

/-- Projection-trace theorem-facing constructor from raw reduced-form OLS
components, with both OLS and 2SLS limit nonsingularity discharged from
`H.PosDef`, `Σ₂₂.PosSemidef`, and `0 ≤ α`.

This is the most direct Hansen-facing assembly currently available for
Theorem 12.19: after the substantive OLS WLLNs, projection-trace remainders,
and LIML zero-score package are supplied, no separate determinant assumptions
for `(H + Σ₂₂)` or `(H + αΣ₂₂)` remain. -/
theorem ManyInstrumentsTheorem1219Conditions.of_projection_trace_components_posSemidef
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hH : H.PosDef)
    (hSigma22 : Sigma22.PosSemidef)
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) + u2 m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (e m ω)) μ)
    (hsignal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentSignalGram (Z m ω) (Gamma m)) μ)
    (hreduced_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleGram (u2 m ω)) μ)
    (hcross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hsignal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m)) (e m ω)) μ)
    (hreduced_error_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (u2 m ω) (e m ω)) μ)
    (hsignal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hreduced_error_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => sampleGram (u2 m ω))
      atTop (fun _ => Sigma22))
    (hcross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hsignal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m)) (e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hreduced_error_score_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => sampleCrossMoment (u2 m ω) (e m ω))
      atTop (fun _ => Sigma2e))
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ)
    (hprojected_signal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hprojected_cross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_signal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (htrace : ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha)
    (hLIML : ManyInstrumentsLIMLMomentConsistencyConditions μ Z X e limlMuHat H) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha := by
  let hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e :=
    ManyInstrumentsOLSMomentAssemblyConditions.of_components_posSemidef
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      hreduced hgram_meas hscore_meas hsignal_gram_meas
      hreduced_error_gram_meas hcross_gram_meas hsignal_score_meas
      hreduced_error_score_meas hsignal_gram_tendsto
      hreduced_error_gram_tendsto hcross_gram_tendsto_zero
      hsignal_score_tendsto_zero hreduced_error_score_tendsto hH hSigma22
  exact
    ManyInstrumentsTheorem1219Conditions.of_projection_trace_assemblies_posSemidef
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hH hSigma22 hOLS
      hprojected_signal_gram_meas hprojected_cross_gram_meas
      hprojected_signal_score_meas
      hprojected_signal_gram_tendsto hprojected_cross_gram_tendsto_zero
      hprojected_signal_score_tendsto_zero htrace hLIML

/-- Direct projection-trace constructor with Hansen's LIML eigenvalue adjustment
limit `μ̂ -> α/(1-α)`.

This is the most direct currently formalized route to the full Theorem 12.19
condition package: it composes the reduced-form OLS component limits, the
projection-trace 2SLS component limits, positivity-derived nonsingularity, and
the existing LIML cancellation theorem. -/
theorem ManyInstrumentsTheorem1219Conditions.of_projection_trace_components_posSemidef_mu_tendsto
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hH : H.PosDef)
    (hSigma22 : Sigma22.PosSemidef)
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) + u2 m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (e m ω)) μ)
    (hsignal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentSignalGram (Z m ω) (Gamma m)) μ)
    (hreduced_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleGram (u2 m ω)) μ)
    (hcross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hsignal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m)) (e m ω)) μ)
    (hreduced_error_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (u2 m ω) (e m ω)) μ)
    (hsignal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hreduced_error_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => sampleGram (u2 m ω))
      atTop (fun _ => Sigma22))
    (hcross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hsignal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m)) (e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hreduced_error_score_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => sampleCrossMoment (u2 m ω) (e m ω))
      atTop (fun _ => Sigma2e))
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ)
    (hprojected_signal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hprojected_cross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_signal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (htrace : ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha)
    (hmu_meas : ∀ m, AEStronglyMeasurable (limlMuHat m) μ)
    (hmu_tendsto : TendstoInMeasure μ limlMuHat atTop
      (fun _ => alpha / (1 - alpha))) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha := by
  let hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e :=
    ManyInstrumentsOLSMomentAssemblyConditions.of_components_posSemidef
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      hreduced hgram_meas hscore_meas hsignal_gram_meas
      hreduced_error_gram_meas hcross_gram_meas hsignal_score_meas
      hreduced_error_score_meas hsignal_gram_tendsto
      hreduced_error_gram_tendsto hcross_gram_tendsto_zero
      hsignal_score_tendsto_zero hreduced_error_score_tendsto hH hSigma22
  let h2SLS : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e alpha :=
    ManyInstrumentsTwoSLSMomentAssemblyConditions.of_projection_trace_components_posSemidef
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      hreduced hprojected_signal_gram_meas hprojected_cross_gram_meas
      hprojected_signal_score_meas
      hprojected_signal_gram_tendsto hprojected_cross_gram_tendsto_zero
      hprojected_signal_score_tendsto_zero htrace hH hSigma22 halpha_nonneg
  exact
    ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_mu_tendsto
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hH hOLS h2SLS
      hmu_meas hmu_tendsto

/-- Centered proof-facing condition package for Hansen Theorem 12.19.

Bekker-style many-instrument arguments naturally prove the centered displayed
limits.  This package avoids requiring separate uncentered estimator-limit
fields when the centered faces are already available. -/
structure ManyInstrumentsTheorem1219CenteredConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Y : (m : ℕ) → Ω → Fin m → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (H Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ)
    (alpha : ℝ) : Prop where
  ols_centered : TendstoInMeasure μ
    (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
    atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e)
  twoSLS_centered : TendstoInMeasure μ
    (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
    atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha)
  liml_centered : TendstoInMeasure μ
    (fun (m : ℕ) ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
    atTop (fun _ => (0 : k → ℝ))

/-- Hansen Theorem 12.19: with `ℓ_n/n -> α`, OLS and 2SLS have the displayed
inconsistent probability limits, while LIML is consistent. -/
theorem manyInstruments_estimators_theorem12_19
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (h : ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  ⟨by
      simpa [manyInstrumentsOLSBias] using
        olsBetaStar_tendstoInMeasure_of_moment_limits
          (μ := μ) (X := X) (Y := Y) (e := e)
          (β := β) (g := Sigma2e) (Q := H + Sigma22)
          h.ols_moments h.structural_model,
    by
      simpa [manyInstrumentsTwoSLSBias] using
        twoSLSBetaStar_tendstoInMeasure_of_normalized_moment_limits
          (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e)
          (β := β) (g := alpha • Sigma2e) (Q := H + alpha • Sigma22)
          h.twoSLS_moments h.structural_model,
    limlBetaStar_tendstoInMeasure_beta_of_normalized_moments
      h.liml_moments h.structural_model⟩

section ManyInstrumentsTheorem1219EntrywiseSampleEigenvalueEndpoint

open ManyInstrumentsTheorem1219Conditions

/-- Hansen Theorem 12.19 directly from reduced-form WLLNs, a.e. nonsingular
instruments, entrywise projected-error trace remainders, and the sample LIML
eigenvalue adjustment-gap WLLN. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hentry : ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
      μ Z e u2)
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
    (e := e) (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (of_reduced_form_wlln_ae_nonsingular_sample_eigenvalue_entrywise_remainders
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
      hZ_meas hu2_meas he_meas hentry hmu)

/-- Ratio-facing reduced-form endpoint for Hansen Theorem 12.19.

This removes the explicit `0 ≤ α` caller obligation from
`manyInstruments_estimators_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue`;
it follows from Hansen's instrument-ratio convergence assumption. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hentry : ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
      μ Z e u2)
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hentry hmu

set_option linter.style.longLine false in
/-- Hansen Theorem 12.19 directly from reduced-form WLLNs, canonical
projected-error row-average convergence, and a scalar LIML adjustment-gap WLLN.

This endpoint exposes the exact finite-sample canonical projected-error
averages as the projection primitive, rather than requiring callers to first
package their consequences entrywise. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_canonical_row_average_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hcanonical :
      ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions
        μ Z e u2)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
    hu2_meas he_meas hcanonical.toEntryWLLNConditions
    hmu.toSampleEigenvalueProblemConditions

set_option linter.style.longLine false in
/-- Ratio-facing reduced-form canonical-row endpoint for Hansen Theorem 12.19. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_canonical_row_average_sample_eigenvalue_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hcanonical :
      ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions
        μ Z e u2)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19_of_reduced_form_canonical_row_average_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gap_row := gap_row)
    (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hcanonical hmu

set_option linter.style.longLine false in
/-- Ratio-facing Hansen Theorem 12.19 endpoint from reduced-form WLLNs,
canonical projected-error row averages, and the finite-sample Rayleigh
adjustment-gap WLLN.

This is the uncentered companion to
`manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_canonical_row_average_rayleigh_adjustment_gap_of_card_ratio_autoMeas`.
It keeps the LIML primitive at Hansen's finite-sample generalized Rayleigh
problem while exposing the projected-error input in exact canonical-row
notation. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_canonical_row_average_rayleigh_adjustment_gap_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hcanonical :
      ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions
        μ Z e u2)
    (hrayleigh :
      ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions
        (ι := ι) μ Z X Y limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_ae_nonsingular_canonical_row_average_rayleigh_adjustment_gap
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
      halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
      hcanonical hrayleigh)

set_option linter.style.longLine false in
/-- Canonical-row Rayleigh Hansen Theorem 12.19 in textbook k-class notation.

This is the strongest canonical-row/Rayleigh theorem-facing facade with LIML
written directly as `limlKClassBetaStar ... κ̂`, where `κ̂ = μ̂ + 1`. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_canonical_row_average_rayleigh_adjustment_gap_kappa_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hcanonical :
      ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions
        μ Z e u2)
    (hrayleigh :
      ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions
        (ι := ι) μ Z X Y limlMuHat gap_row)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω))
      atTop (fun _ => β) := by
  have hbase :=
    manyInstruments_estimators_theorem12_19_of_reduced_form_canonical_row_average_rayleigh_adjustment_gap_of_card_ratio
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
      hcanonical hrayleigh
  have hliml : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω))
      atTop (fun _ => β) := by
    refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hbase.2.2
    intro m
    exact ae_of_all μ (fun ω => by
      simp [limlBetaStar_eq_kClass_add_one, hkappa m ω])
  exact ⟨hbase.1, hbase.2.1, hliml⟩

/-- Hansen Theorem 12.19 directly from one iid compressed-signal row process,
a.e. nonsingular instruments, entrywise projected-error trace remainders, and
the sample LIML eigenvalue adjustment-gap WLLN. -/
theorem
manyInstruments_estimators_theorem12_19_of_iid_compressed_signal_entrywise_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {signal : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hcompressed : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentSignal (Z m ω) (Gamma m) = stackRegressors signal m ω)
    (hsignal_meas : ∀ i, AEStronglyMeasurable (signal i) μ)
    (hjoint_indep : iIndepFun
      (fun i ω => ((signal i ω, u2 i ω), e i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => ((signal i ω, u2 i ω), e i ω))
        (fun ω => ((signal 0 ω, u2 0 ω), e 0 ω)) μ μ)
    (hsignal_norm_sq : Integrable (fun ω => ‖signal 0 ω‖ ^ 2) μ)
    (hsignal_gram_limit : H = popGram μ signal)
    (hsym_cross_integrable : Integrable
      (fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)) μ)
    (hsym_cross_mean_zero :
      μ[fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)] = 0)
    (hsignal_score_integrable : Integrable (fun ω => e 0 ω • signal 0 ω) μ)
    (hsignal_score_mean_zero : μ[fun ω => e 0 ω • signal 0 ω] = 0)
    (hu2_outer_integrable : Integrable
      (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hu2_score_integrable : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ i, AEStronglyMeasurable (u2 i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hentry :
      ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
        μ Z (fun m ω => stackErrors e m ω)
          (fun m ω => stackRegressors u2 m ω))
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
    (e := fun m ω => stackErrors e m ω)
    (u2 := fun m ω => stackRegressors u2 m ω)
    (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (of_iid_compressed_signal_ae_nonsingular_sample_eigenvalue_entrywise_remainders
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
      (signal := signal) (e := e) (u2 := u2) (limlMuHat := limlMuHat)
      (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hreduced hstruct hgram_meas
        hscore_meas hcompressed hsignal_meas hjoint_indep hjoint_ident
        hsignal_norm_sq hsignal_gram_limit hsym_cross_integrable
        hsym_cross_mean_zero hsignal_score_integrable hsignal_score_mean_zero
        hu2_outer_integrable hSigma22 hu2_score_integrable hSigma2e hH
        hSigma22_psd hnonsing hZ_meas hu2_meas he_meas hentry hmu)

set_option linter.style.longLine false in
/-- Hansen Theorem 12.19 from reduced-form WLLNs and scalar sample-average WLLNs
for the projected-error trace remainders and LIML eigenvalue adjustment gap.

This is the theorem-facing endpoint when the remaining many-instrument
projection/eigenvalue work has been reduced to ordinary scalar row WLLNs. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_scalar_wlln_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : k → k → ℕ → Ω → ℝ}
    {cross_row : k → ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
    hu2_meas he_meas hremainder.toEntryWLLNConditions
    hmu.toSampleEigenvalueProblemConditions

set_option linter.style.longLine false in
/-- Ratio-facing reduced-form scalar-WLLN endpoint for Hansen Theorem 12.19.

This removes the explicit `0 ≤ α` caller obligation from
`manyInstruments_estimators_theorem12_19_of_reduced_form_scalar_wlln_sample_eigenvalue`;
it follows from Hansen's instrument-ratio convergence assumption. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_scalar_wlln_sample_eigenvalue_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : k → k → ℕ → Ω → ℝ}
    {cross_row : k → ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19_of_reduced_form_scalar_wlln_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
    (cross_row := cross_row) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hremainder hmu

set_option linter.style.longLine false in
/-- Hansen Theorem 12.19 from reduced-form WLLNs, matrix/vector row WLLNs for
the projected-error trace remainders, and a scalar LIML adjustment-gap WLLN. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
    hu2_meas he_meas hremainder.toEntryWLLNConditions
    hmu.toSampleEigenvalueProblemConditions

set_option linter.style.longLine false in
/-- Ratio-facing reduced-form row-WLLN endpoint for Hansen Theorem 12.19. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
    (cross_row := cross_row) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hremainder hmu

set_option linter.style.longLine false in
/-- Ratio-facing Hansen Theorem 12.19 endpoint from reduced-form WLLNs,
projected-error row WLLNs, and the finite-sample Rayleigh adjustment-gap WLLN.

Compared with
`manyInstruments_estimators_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue_of_card_ratio`,
this replaces the scalar sample-eigenvalue adjustment package by Hansen's
finite-sample generalized Rayleigh certificate for `[Y X]`. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_row_wlln_rayleigh_adjustment_gap_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hrayleigh :
      ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions
        (ι := ι) μ Z X Y limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_ae_nonsingular_row_wlln_rayleigh_adjustment_gap
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
      halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
      hremainder hrayleigh)

set_option linter.style.longLine false in
/-- Row-WLLN Rayleigh Hansen Theorem 12.19 in textbook k-class notation.

This is the row-WLLN companion of
`manyInstruments_estimators_theorem12_19_of_reduced_form_canonical_row_average_rayleigh_adjustment_gap_kappa_of_card_ratio`:
it consumes the matrix/vector projected-error row-WLLN package directly and
writes LIML as `limlKClassBetaStar ... κ̂`, where `κ̂ = μ̂ + 1`. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_row_wlln_rayleigh_adjustment_gap_kappa_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hrayleigh :
      ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions
        (ι := ι) μ Z X Y limlMuHat gap_row)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω))
      atTop (fun _ => β) := by
  have hbase :=
    manyInstruments_estimators_theorem12_19_of_reduced_form_row_wlln_rayleigh_adjustment_gap_of_card_ratio
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
      hremainder hrayleigh
  have hliml : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω))
      atTop (fun _ => β) := by
    refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hbase.2.2
    intro m
    exact ae_of_all μ (fun ω => by
      simp [limlBetaStar_eq_kClass_add_one, hkappa m ω])
  exact ⟨hbase.1, hbase.2.1, hliml⟩

set_option linter.style.longLine false in
/-- Hansen Theorem 12.19 from a single joint row process for the
projected-error trace remainders.

This is the uncentered counterpart to
`manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_joint_row_wlln_sample_eigenvalue_autoMeas`:
the separate matrix and vector row-WLLN independence/identical-law fields are
derived by measurable projection from one joint row process. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_joint_row_wlln_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gram_row i ω)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, cross_row i ω)
    (hgram_integrable : Integrable (gram_row 0) μ)
    (hcross_integrable : Integrable (cross_row 0) μ)
    (hjoint_indep : iIndepFun (fun i ω => (gram_row i ω, cross_row i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => (gram_row i ω, cross_row i ω))
        (fun ω => (gram_row 0 ω, cross_row 0 ω)) μ μ)
    (hgram_mean_zero : μ[gram_row 0] = 0)
    (hcross_mean_zero : μ[cross_row 0] = 0)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
    (cross_row := cross_row) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
    hu2_meas he_meas
    (ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions.of_joint_wlln
      (μ := μ) (Z := Z) (e := e) (u2 := u2)
      (gram_row := gram_row) (cross_row := cross_row)
      hgram_remainder_eq_avg hcross_remainder_eq_avg hgram_integrable
      hcross_integrable hjoint_indep hjoint_ident hgram_mean_zero
      hcross_mean_zero)
    hmu

set_option linter.style.longLine false in
/-- Ratio-facing version of the uncentered joint-row Theorem 12.19 endpoint. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_joint_row_wlln_sample_eigenvalue_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gram_row i ω)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, cross_row i ω)
    (hgram_integrable : Integrable (gram_row 0) μ)
    (hcross_integrable : Integrable (cross_row 0) μ)
    (hjoint_indep : iIndepFun (fun i ω => (gram_row i ω, cross_row i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => (gram_row i ω, cross_row i ω))
        (fun ω => (gram_row 0 ω, cross_row 0 ω)) μ μ)
    (hgram_mean_zero : μ[gram_row 0] = 0)
    (hcross_mean_zero : μ[cross_row 0] = 0)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19_of_reduced_form_joint_row_wlln_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
    (cross_row := cross_row) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hgram_remainder_eq_avg hcross_remainder_eq_avg hgram_integrable
    hcross_integrable hjoint_indep hjoint_ident hgram_mean_zero
    hcross_mean_zero hmu

set_option linter.style.longLine false in
/-- Ratio-facing Hansen Theorem 12.19 endpoint from one joint row process for
the projected-error trace remainders and Hansen's finite-sample Rayleigh
adjustment gap.

This mirrors the centered joint-row Rayleigh endpoint and removes the separate
row-WLLN/sample-eigenvalue packages from the uncentered caller boundary. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_projected_error_rayleigh_joint_row_wlln_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hjoint :
      ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions
        (ι := ι) μ Z X Y e u2 limlMuHat gram_row cross_row gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19_of_reduced_form_row_wlln_rayleigh_adjustment_gap_of_card_ratio
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
    (cross_row := cross_row) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hjoint.toProjectedErrorRowWLLNConditions
    hjoint.toRayleighAdjustmentGapWLLNConditions

set_option linter.style.longLine false in
/-- Ratio-facing Hansen Theorem 12.19 endpoint from one raw iid joint row
process for the projected-error trace remainders and LIML Rayleigh adjustment
gap.

This is the theorem-facing facade over
`ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions.of_raw_joint_row`. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {row : ℕ → Ω → (Matrix k k ℝ × (k → ℝ)) × ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hrayleigh : ∀ m ω,
      LIMLRayleighMinimizer
        (manyInstrumentsLIMLSampleRayleighNumerator (Z m ω) (X m ω) (Y m ω))
        (manyInstrumentsLIMLSampleRayleighDenominator (Z m ω) (X m ω) (Y m ω))
        (limlMuHat m ω))
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.1)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.2)
    (hadjustment_gap_eq_avg : ∀ (m : ℕ) (ω : Ω),
      limlMuHat m ω -
          manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).2)
    (hrow_integrable : Integrable (row 0) μ)
    (hrow_indep : iIndepFun row μ)
    (hrow_ident : ∀ i, IdentDistrib (row i) (row 0) μ μ)
    (hrow_mean_zero : μ[row 0] = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19_of_reduced_form_projected_error_rayleigh_joint_row_wlln_of_card_ratio
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat)
    (gram_row := fun i ω => (row i ω).1.1)
    (cross_row := fun i ω => (row i ω).1.2)
    (gap_row := fun i ω => (row i ω).2) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    (ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions.of_raw_joint_row
      (μ := μ) (ι := ι) (Z := Z) (X := X) (Y := Y) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (row := row)
      hrayleigh hgram_remainder_eq_avg hcross_remainder_eq_avg
      hadjustment_gap_eq_avg hrow_integrable hrow_indep hrow_ident
      hrow_mean_zero)

set_option linter.style.longLine false in
/-- Hansen Theorem 12.19 from one iid compressed-signal row process and scalar
row-WLLN certificates for the projected-error and LIML eigenvalue remainders. -/
theorem
manyInstruments_estimators_theorem12_19_of_iid_compressed_signal_scalar_wlln_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {signal : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : k → k → ℕ → Ω → ℝ}
    {cross_row : k → ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hcompressed : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentSignal (Z m ω) (Gamma m) = stackRegressors signal m ω)
    (hsignal_meas : ∀ i, AEStronglyMeasurable (signal i) μ)
    (hjoint_indep : iIndepFun
      (fun i ω => ((signal i ω, u2 i ω), e i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => ((signal i ω, u2 i ω), e i ω))
        (fun ω => ((signal 0 ω, u2 0 ω), e 0 ω)) μ μ)
    (hsignal_norm_sq : Integrable (fun ω => ‖signal 0 ω‖ ^ 2) μ)
    (hsignal_gram_limit : H = popGram μ signal)
    (hsym_cross_integrable : Integrable
      (fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)) μ)
    (hsym_cross_mean_zero :
      μ[fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)] = 0)
    (hsignal_score_integrable : Integrable (fun ω => e 0 ω • signal 0 ω) μ)
    (hsignal_score_mean_zero : μ[fun ω => e 0 ω • signal 0 ω] = 0)
    (hu2_outer_integrable : Integrable
      (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hu2_score_integrable : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ i, AEStronglyMeasurable (u2 i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions
        μ Z (fun m ω => stackErrors e m ω)
          (fun m ω => stackRegressors u2 m ω) gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19_of_iid_compressed_signal_entrywise_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
    (signal := signal) (e := e) (u2 := u2) (limlMuHat := limlMuHat)
    (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hreduced hstruct hgram_meas
    hscore_meas hcompressed hsignal_meas hjoint_indep hjoint_ident
    hsignal_norm_sq hsignal_gram_limit hsym_cross_integrable
    hsym_cross_mean_zero hsignal_score_integrable hsignal_score_mean_zero
    hu2_outer_integrable hSigma22 hu2_score_integrable hSigma2e hH
    hSigma22_psd hnonsing hZ_meas hu2_meas he_meas
    hremainder.toEntryWLLNConditions hmu.toSampleEigenvalueProblemConditions

end ManyInstrumentsTheorem1219EntrywiseSampleEigenvalueEndpoint

/-- Hansen Theorem 12.19 from centered estimator limits, returning the exact
centered displayed claims. -/
theorem manyInstruments_estimators_minus_beta_theorem12_19_of_centered
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (h : ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  ⟨h.ols_centered, h.twoSLS_centered, h.liml_centered⟩

/-- Uncentered compatibility wrapper from the centered many-instrument package. -/
theorem manyInstruments_estimators_theorem12_19_of_centered
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (h : ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω) - β) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) := by
  have hOLS := tendstoInMeasure_continuous_comp hOLS_meas h.ols_centered
    (by fun_prop : Continuous fun x : k → ℝ => β + x)
  have hOLS' : TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) := by
    refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hOLS
    intro m
    exact ae_of_all μ (fun ω => by
      ext i
      simp [Pi.add_apply, Pi.sub_apply])
  have h2 := tendstoInMeasure_continuous_comp h2SLS_meas h.twoSLS_centered
    (by fun_prop : Continuous fun x : k → ℝ => β + x)
  have h2' : TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) := by
    refine TendstoInMeasure.congr ?_ EventuallyEq.rfl h2
    intro m
    exact ae_of_all μ (fun ω => by
      ext i
      simp [Pi.add_apply, Pi.sub_apply])
  have hL := tendstoInMeasure_continuous_comp hLIML_meas h.liml_centered
    (by fun_prop : Continuous fun x : k → ℝ => β + x)
  have hL' : TendstoInMeasure μ
      (fun (m : ℕ) ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) := by
    refine TendstoInMeasure.congr ?_ ?_ hL
    · intro m
      exact ae_of_all μ (fun ω => by
        ext i
        simp [Pi.add_apply, Pi.sub_apply])
    · exact ae_of_all μ (fun _ => by
        ext i
        simp [Pi.add_apply])
  exact ⟨hOLS', h2', hL'⟩

/-- Hansen Theorem 12.19 OLS face in centered form:
`β̂_OLS - β ->p (H + Σ₂₂)^{-1} Σ₂e`. -/
theorem manyInstruments_olsBetaStar_minus_beta_tendstoInMeasure
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (h : ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha)
    (hmeas : ∀ m, AEStronglyMeasurable (fun ω => olsBetaStar (X m ω) (Y m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) := by
  have hlevel : TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) := by
    simpa [manyInstrumentsOLSBias] using
      olsBetaStar_tendstoInMeasure_of_moment_limits
        (μ := μ) (X := X) (Y := Y) (e := e)
        (β := β) (g := Sigma2e) (Q := H + Sigma22)
        h.ols_moments h.structural_model
  have hdiff := tendstoInMeasure_continuous_comp hmeas hlevel
    (by fun_prop : Continuous fun x : k → ℝ => x - β)
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hdiff
  exact ae_of_all μ (fun _ => by
    ext i
    simp [Pi.sub_apply, Pi.add_apply])

/-- Hansen Theorem 12.19 2SLS face in centered form:
`β̂_2SLS - β ->p (H + αΣ₂₂)^{-1} αΣ₂e`. -/
theorem manyInstruments_twoSLSBetaStar_minus_beta_tendstoInMeasure
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (h : ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha)
    (hmeas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) := by
  have hlevel : TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) := by
    simpa [manyInstrumentsTwoSLSBias] using
      twoSLSBetaStar_tendstoInMeasure_of_normalized_moment_limits
        (μ := μ) (Z := Z) (X := X) (Y := Y) (e := e)
        (β := β) (g := alpha • Sigma2e) (Q := H + alpha • Sigma22)
        h.twoSLS_moments h.structural_model
  have hdiff := tendstoInMeasure_continuous_comp hmeas hlevel
    (by fun_prop : Continuous fun x : k → ℝ => x - β)
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hdiff
  exact ae_of_all μ (fun _ => by
    ext i
    simp [Pi.sub_apply, Pi.add_apply])

/-- Hansen Theorem 12.19 LIML face in centered form:
`β̂_LIML - β ->p 0`. -/
theorem manyInstruments_limlBetaStar_minus_beta_tendstoInMeasure
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (h : ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha)
    (hmeas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hliml : TendstoInMeasure μ
      (fun (m : ℕ) ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
    limlBetaStar_tendstoInMeasure_beta_of_normalized_moments
      h.liml_moments h.structural_model
  have hdiff := tendstoInMeasure_continuous_comp hmeas hliml
    (by fun_prop : Continuous fun x : k → ℝ => x - β)
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hdiff
  exact ae_of_all μ (fun _ => by
    ext i
    simp [Pi.sub_apply])

/-- Build the centered Hansen Theorem 12.19 package from the stronger
many-instrument condition package.  The centered faces are derived from
moment convergence rather than assumed as primitive estimator limits. -/
theorem ManyInstrumentsTheorem1219CenteredConditions.of_theorem_conditions
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (h : ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha where
  ols_centered := manyInstruments_olsBetaStar_minus_beta_tendstoInMeasure h hOLS_meas
  twoSLS_centered :=
    manyInstruments_twoSLSBetaStar_minus_beta_tendstoInMeasure h h2SLS_meas
  liml_centered := manyInstruments_limlBetaStar_minus_beta_tendstoInMeasure h hLIML_meas

/-- Centered Theorem 12.19 package from reduced-form OLS assembly,
projection-trace 2SLS components, and Hansen's LIML eigenvalue adjustment
limit `μ̂ -> α/(1-α)`.

This bridge derives the centered OLS, 2SLS, and LIML displayed limits from
moment/projection components.  It asks only for estimator measurability, not
for any centered estimator limit as an input. -/
theorem
ManyInstrumentsTheorem1219CenteredConditions.of_projection_trace_assemblies_posSemidef_mu_tendsto
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hpos : H.PosDef)
    (hSigma22 : Sigma22.PosSemidef)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ)
    (hprojected_signal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hprojected_cross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedReducedFormCrossGram (Z m ω) (Gamma m) (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_signal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (htrace : ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha)
    (hmu_meas : ∀ m, AEStronglyMeasurable (limlMuHat m) μ)
    (hmu_tendsto : TendstoInMeasure μ limlMuHat atTop
      (fun _ => alpha / (1 - alpha)))
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219CenteredConditions.of_theorem_conditions
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (ManyInstrumentsTheorem1219Conditions.of_projection_trace_assemblies_posSemidef_mu_tendsto
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hpos hSigma22 hOLS
      hprojected_signal_gram_meas hprojected_cross_gram_meas
      hprojected_signal_score_meas
      hprojected_signal_gram_tendsto hprojected_cross_gram_tendsto_zero
      hprojected_signal_score_tendsto_zero htrace hmu_meas hmu_tendsto)
    hOLS_meas h2SLS_meas hLIML_meas

/-- Centered Theorem 12.19 package from OLS reduced-form assembly plus the
projection-trace projected-error package.

This is the centered analogue of
`ManyInstrumentsTheorem1219Conditions.of_ols_projection_trace_components_posSemidef_mu_tendsto`:
projected signal limits are derived from the OLS reduced-form limits on the
eventual-a.e. nonsingular instrument branch, and no centered estimator limit is
assumed. -/
theorem
ManyInstrumentsTheorem1219CenteredConditions.of_ols_projection_trace_components_mu_tendsto
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hH : H.PosDef)
    (hSigma22 : Sigma22.PosSemidef)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ)
    (htrace : ManyInstrumentsProjectedTraceMomentConditions
      μ Z e u2 Sigma22 Sigma2e alpha)
    (hnonsing : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hmu_meas : ∀ m, AEStronglyMeasurable (limlMuHat m) μ)
    (hmu_tendsto : TendstoInMeasure μ limlMuHat atTop
      (fun _ => alpha / (1 - alpha)))
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219CenteredConditions.of_theorem_conditions
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (ManyInstrumentsTheorem1219Conditions.of_ols_projection_trace_components_posSemidef_mu_tendsto
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hH hSigma22 hOLS
      hprojected_signal_gram_meas hprojected_cross_gram_meas
      hprojected_signal_score_meas htrace hnonsing hmu_meas hmu_tendsto)
    hOLS_meas h2SLS_meas hLIML_meas

/-- Centered Theorem 12.19 package from the named reduced-form WLLN package,
the two homoskedastic projection remainders, and the current LIML
eigenvalue-limit package. -/
theorem
ManyInstrumentsTheorem1219CenteredConditions.of_reduced_form_wlln_projection_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ)
    (hproj : ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2)
    (hnonsing : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hmu : ManyInstrumentsLIMLEigenvalueAlphaOverOneMinusAlphaCertificate
      μ limlMuHat alpha)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219CenteredConditions.of_theorem_conditions
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_projection_remainders
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF
      hprojected_signal_gram_meas hprojected_cross_gram_meas
      hprojected_signal_score_meas hproj hnonsing hmu)
    hOLS_meas h2SLS_meas hLIML_meas

/-- Centered Theorem 12.19 package from the named reduced-form WLLN package,
the two homoskedastic projection remainders, and the sample LIML eigenvalue
problem.

This is the centered analogue of
`ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_sample_eigenvalue_problem`:
it first derives `μ̂_n ->p α/(1-α)` from the adjustment-gap WLLN and Hansen's
instrument-count ratio, then reuses the existing centered theorem route. -/
theorem
ManyInstrumentsTheorem1219CenteredConditions.of_reduced_form_wlln_sample_eigenvalue_problem
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω)) μ)
    (hproj : ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2)
    (hnonsing : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219CenteredConditions.of_reduced_form_wlln_projection_remainders
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF
    hprojected_signal_gram_meas hprojected_cross_gram_meas
    hprojected_signal_score_meas hproj hnonsing
    (hmu.toLIMLEigenvalueLimitConditions
      (ι := ι) (μ := μ) hratio halpha_lt_one)
    hOLS_meas h2SLS_meas hLIML_meas

/-- Centered Theorem 12.19 package from the named reduced-form WLLN package and
homoskedastic projection remainders, deriving projected signal components from
the primitive reduced-form package on an a.e. nonsingular instrument branch. -/
theorem
ManyInstrumentsTheorem1219CenteredConditions.of_wlln_projection_remainders_ae_nonsingular
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hproj : ManyInstrumentsHomoskedasticProjectionRemainderConditions μ Z e u2)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hmu : ManyInstrumentsLIMLEigenvalueAlphaOverOneMinusAlphaCertificate
      μ limlMuHat alpha)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219CenteredConditions.of_theorem_conditions
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_projection_remainders_ae_nonsingular
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hproj hnonsing hmu)
    hOLS_meas h2SLS_meas hLIML_meas

/-- Centered Theorem 12.19 package from named reduced-form WLLNs, raw
homoskedastic projection-remainder fields, and the LIML eigenvalue certificate.
Projected signal components and trace-ratio measurability are both derived from
the a.e. nonsingular instrument branch. -/
theorem
ManyInstrumentsTheorem1219CenteredConditions.of_wlln_ae_nonsingular_projection_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hprojected_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω)) μ)
    (hprojected_error_cross_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω)) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) • sampleGram (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (u2 m ω) (e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hmu : ManyInstrumentsLIMLEigenvalueLimitConditions μ limlMuHat alpha)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219CenteredConditions.of_theorem_conditions
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (ManyInstrumentsTheorem1219Conditions.of_reduced_form_wlln_ae_nonsingular_projection_remainders
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
      hprojected_error_gram_meas hprojected_error_cross_meas
      hprojected_error_gram_trace_remainder_tendsto_zero
      hprojected_error_cross_trace_remainder_tendsto_zero hmu)
    hOLS_meas h2SLS_meas hLIML_meas

/-- Centered Theorem 12.19 package from named reduced-form WLLNs, raw
homoskedastic projection-remainder fields, and the sample LIML eigenvalue
problem.

The eigenvalue input is the centered adjustment-gap WLLN for
`μ̂_n - (ℓ_n/n)/(1-ℓ_n/n)`.  The conversion to `μ̂_n ->p α/(1-α)` is handled
inside this wrapper. -/
theorem
ManyInstrumentsTheorem1219CenteredConditions.of_wlln_ae_nonsingular_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hprojected_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω)) μ)
    (hprojected_error_cross_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω)) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) • sampleGram (u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (u2 m ω) (e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219CenteredConditions.of_wlln_ae_nonsingular_projection_remainders
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
    hprojected_error_gram_meas hprojected_error_cross_meas
    hprojected_error_gram_trace_remainder_tendsto_zero
    hprojected_error_cross_trace_remainder_tendsto_zero
    (hmu.toLIMLEigenvalueLimitConditions
      (ι := ι) (μ := μ) hratio halpha_lt_one)
    hOLS_meas h2SLS_meas hLIML_meas

/-- Centered Theorem 12.19 package from stacked row WLLNs, projection
remainders, and Hansen's LIML eigenvalue adjustment limit. -/
theorem
ManyInstrumentsTheorem1219CenteredConditions.of_stacked_error_wlln_projection_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hsignal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentSignalGram (Z m ω) (Gamma m)) μ)
    (hcross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentReducedFormCrossGram
        (Z m ω) (Gamma m) (stackRegressors u2 m ω)) μ)
    (hsignal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m))
          (stackErrors e m ω)) μ)
    (hsignal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hcross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentReducedFormCrossGram
          (Z m ω) (Gamma m) (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hsignal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m))
          (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hint_outer : Integrable (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hindep_outer :
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))))
    (hident_outer : ∀ i,
      IdentDistrib
        (fun ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))
        (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hint_cross : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hindep_cross :
      Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • u2 i ω)))
    (hident_cross : ∀ i,
      IdentDistrib
        (fun ω => e i ω • u2 i ω)
        (fun ω => e 0 ω • u2 0 ω) μ μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hprojected_signal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ)
    (hprojected_cross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (stackRegressors u2 m ω)) μ)
    (hprojected_signal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (stackErrors e m ω)) μ)
    (hproj : ManyInstrumentsHomoskedasticProjectionRemainderConditions
      μ Z (fun m ω => stackErrors e m ω) (fun m ω => stackRegressors u2 m ω))
    (hnonsing : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hmu : ManyInstrumentsLIMLEigenvalueAlphaOverOneMinusAlphaCertificate
      μ limlMuHat alpha)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219CenteredConditions.of_theorem_conditions
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
    (e := fun m ω => stackErrors e m ω)
    (u2 := fun m ω => stackRegressors u2 m ω)
    (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (ManyInstrumentsTheorem1219Conditions.of_stacked_error_wlln_projection_remainders
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
      (e := e) (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hreduced hstruct hgram_meas
      hscore_meas hsignal_gram_meas hcross_gram_meas hsignal_score_meas
      hsignal_gram_tendsto hcross_gram_tendsto_zero hsignal_score_tendsto_zero
      hint_outer hindep_outer hident_outer hSigma22 hint_cross hindep_cross
      hident_cross hSigma2e hH hSigma22_psd hprojected_signal_gram_meas
      hprojected_cross_gram_meas
      hprojected_signal_score_meas hproj hnonsing hmu)
    hOLS_meas h2SLS_meas hLIML_meas

/-- Centered Theorem 12.19 package from stacked row WLLNs, a.e. nonsingular
instrument Grams, raw projected-error trace remainders, and Hansen's LIML
eigenvalue adjustment limit.

This is the centered-statistic counterpart of
`ManyInstrumentsTheorem1219Conditions.of_stacked_error_wlln_ae_nonsingular_projection_remainders`;
it derives the reduced-form WLLN package from Chapter 7 iid-row WLLNs and then
uses the a.e. nonsingular projected-signal bridge. -/
theorem
ManyInstrumentsTheorem1219CenteredConditions.of_stacked_wlln_ae_nonsingular_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hsignal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentSignalGram (Z m ω) (Gamma m)) μ)
    (hcross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentReducedFormCrossGram
        (Z m ω) (Gamma m) (stackRegressors u2 m ω)) μ)
    (hsignal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m))
          (stackErrors e m ω)) μ)
    (hsignal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hcross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentReducedFormCrossGram
          (Z m ω) (Gamma m) (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hsignal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m))
          (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hint_outer : Integrable (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hindep_outer :
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))))
    (hident_outer : ∀ i,
      IdentDistrib
        (fun ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))
        (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hint_cross : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hindep_cross :
      Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • u2 i ω)))
    (hident_cross : ∀ i,
      IdentDistrib
        (fun ω => e i ω • u2 i ω)
        (fun ω => e 0 ω • u2 0 ω) μ μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hprojected_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedErrorGram
          (Z m ω) (stackRegressors u2 m ω)) μ)
    (hprojected_error_cross_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedErrorCross
          (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω)) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (stackRegressors u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleGram (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross
            (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (stackRegressors u2 m ω) (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hmu : ManyInstrumentsLIMLEigenvalueLimitConditions μ limlMuHat alpha)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha := by
  let hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H Sigma22 Sigma2e :=
    ManyInstrumentsReducedFormWLLNConditions.of_stacked_error_wlln
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      hreduced hgram_meas hscore_meas hsignal_gram_meas hcross_gram_meas
      hsignal_score_meas hsignal_gram_tendsto hcross_gram_tendsto_zero
      hsignal_score_tendsto_zero hint_outer hindep_outer hident_outer hSigma22
      hint_cross hindep_cross hident_cross hSigma2e hH hSigma22_psd
  exact
    ManyInstrumentsTheorem1219CenteredConditions.of_wlln_ae_nonsingular_projection_remainders
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
      (e := fun m ω => stackErrors e m ω)
      (u2 := fun m ω => stackRegressors u2 m ω)
      (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
      hprojected_error_gram_meas hprojected_error_cross_meas
      hprojected_error_gram_trace_remainder_tendsto_zero
      hprojected_error_cross_trace_remainder_tendsto_zero hmu
      hOLS_meas h2SLS_meas hLIML_meas

/-- Centered Theorem 12.19 package from stacked row WLLNs, a.e. nonsingular
instrument Grams, raw projected-error trace remainders, and the sample LIML
eigenvalue problem. -/
theorem
ManyInstrumentsTheorem1219CenteredConditions.of_stacked_wlln_ae_nonsingular_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hsignal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentSignalGram (Z m ω) (Gamma m)) μ)
    (hcross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentReducedFormCrossGram
        (Z m ω) (Gamma m) (stackRegressors u2 m ω)) μ)
    (hsignal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m))
          (stackErrors e m ω)) μ)
    (hsignal_gram_tendsto : TendstoInMeasure μ
      (fun (m : ℕ) ω => manyInstrumentSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H))
    (hcross_gram_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentReducedFormCrossGram
          (Z m ω) (Gamma m) (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hsignal_score_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        sampleCrossMoment (manyInstrumentSignal (Z m ω) (Gamma m))
          (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hint_outer : Integrable (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hindep_outer :
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))))
    (hident_outer : ∀ i,
      IdentDistrib
        (fun ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))
        (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hint_cross : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hindep_cross :
      Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • u2 i ω)))
    (hident_cross : ∀ i,
      IdentDistrib
        (fun ω => e i ω • u2 i ω)
        (fun ω => e 0 ω • u2 0 ω) μ μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hprojected_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedErrorGram
          (Z m ω) (stackRegressors u2 m ω)) μ)
    (hprojected_error_cross_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedErrorCross
          (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω)) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (stackRegressors u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleGram (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross
            (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (stackRegressors u2 m ω) (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha := by
  let hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H Sigma22 Sigma2e :=
    ManyInstrumentsReducedFormWLLNConditions.of_stacked_error_wlln
      (μ := μ) (Z := Z) (X := X) (Gamma := Gamma) (e := e) (u2 := u2)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      hreduced hgram_meas hscore_meas hsignal_gram_meas hcross_gram_meas
      hsignal_score_meas hsignal_gram_tendsto hcross_gram_tendsto_zero
      hsignal_score_tendsto_zero hint_outer hindep_outer hident_outer hSigma22
      hint_cross hindep_cross hident_cross hSigma2e hH hSigma22_psd
  exact
    ManyInstrumentsTheorem1219CenteredConditions.of_wlln_ae_nonsingular_sample_eigenvalue
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
      (e := fun m ω => stackErrors e m ω)
      (u2 := fun m ω => stackRegressors u2 m ω)
      (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
      hprojected_error_gram_meas hprojected_error_cross_meas
      hprojected_error_gram_trace_remainder_tendsto_zero
      hprojected_error_cross_trace_remainder_tendsto_zero hmu
      hOLS_meas h2SLS_meas hLIML_meas

namespace ManyInstrumentsTheorem1219CenteredConditions

/-- Centered Theorem 12.19 package from primitive transformed-instrument WLLNs,
stacked row WLLNs for reduced-form errors, a.e. nonsingular instruments,
homoskedastic projection-remainder fields, and the sample LIML eigenvalue
adjustment-gap package.

This is the estimator-limit counterpart of
`ManyInstrumentsTheorem1219Conditions.of_stacked_primitive_wlln_ae_nonsingular_sample_eigenvalue`.
It still leaves the primitive instrument WLLNs, projection remainders, and raw
sample-eigenvalue adjustment gap as the substantive stochastic inputs. -/
theorem
of_stacked_primitive_wlln_ae_nonsingular_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hinst : ManyInstrumentsPrimitiveInstrumentMomentWLLNConditions
      μ Z Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H)
    (hint_outer : Integrable (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hindep_outer :
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))))
    (hident_outer : ∀ i,
      IdentDistrib
        (fun ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))
        (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hint_cross : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hindep_cross :
      Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • u2 i ω)))
    (hident_cross : ∀ i,
      IdentDistrib
        (fun ω => e i ω • u2 i ω)
        (fun ω => e 0 ω • u2 0 ω) μ μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hprojected_error_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedErrorGram
          (Z m ω) (stackRegressors u2 m ω)) μ)
    (hprojected_error_cross_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        manyInstrumentProjectedErrorCross
          (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω)) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (stackRegressors u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleGram (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross
            (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (stackRegressors u2 m ω) (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219CenteredConditions.of_theorem_conditions
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
    (e := fun m ω => stackErrors e m ω)
    (u2 := fun m ω => stackRegressors u2 m ω)
    (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (ManyInstrumentsTheorem1219Conditions.of_stacked_primitive_wlln_ae_nonsingular_sample_eigenvalue
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
      (e := e) (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hreduced hstruct hgram_meas
      hscore_meas hinst hint_outer hindep_outer hident_outer hSigma22
      hint_cross hindep_cross hident_cross hSigma2e hH hSigma22_psd
      hnonsing hprojected_error_gram_meas hprojected_error_cross_meas
      hprojected_error_gram_trace_remainder_tendsto_zero
      hprojected_error_cross_trace_remainder_tendsto_zero hmu)
    hOLS_meas h2SLS_meas hLIML_meas

set_option linter.style.longLine false in
/-- Centered Theorem 12.19 package from primitive transformed-instrument WLLNs
with projected-error measurability derived from finite-sample measurability.

This is the centered-statistic counterpart of
`ManyInstrumentsTheorem1219Conditions.of_stacked_primitive_wlln_ae_nonsingular_sample_eigenvalue_measurable_remainders`.
It leaves the same substantive inputs: primitive transformed-instrument WLLNs,
ordinary reduced-form error WLLNs, the two homoskedastic trace-remainder WLLNs,
and the sample LIML eigenvalue adjustment-gap package. -/
theorem
of_stacked_primitive_wlln_ae_nonsingular_sample_eigenvalue_measurable_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hinst : ManyInstrumentsPrimitiveInstrumentMomentWLLNConditions
      μ Z Gamma (fun m ω => stackErrors e m ω)
        (fun m ω => stackRegressors u2 m ω) H)
    (hint_outer : Integrable (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hindep_outer :
      Pairwise ((· ⟂ᵢ[μ] ·) on
        (fun i ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))))
    (hident_outer : ∀ i,
      IdentDistrib
        (fun ω => Matrix.vecMulVec (u2 i ω) (u2 i ω))
        (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hint_cross : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hindep_cross :
      Pairwise ((· ⟂ᵢ[μ] ·) on (fun i ω => e i ω • u2 i ω)))
    (hident_cross : ∀ i,
      IdentDistrib
        (fun ω => e i ω • u2 i ω)
        (fun ω => e 0 ω • u2 0 ω) μ μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ i, AEStronglyMeasurable (u2 i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hprojected_error_gram_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorGram (Z m ω) (stackRegressors u2 m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleGram (stackRegressors u2 m ω))
      atTop (fun _ => (0 : Matrix k k ℝ)))
    (hprojected_error_cross_trace_remainder_tendsto_zero : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        manyInstrumentProjectedErrorCross
            (Z m ω) (stackRegressors u2 m ω) (stackErrors e m ω) -
          manyInstrumentProjectionTraceRatio (Z m ω) •
            sampleCrossMoment (stackRegressors u2 m ω) (stackErrors e m ω))
      atTop (fun _ => (0 : k → ℝ)))
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha :=
  ManyInstrumentsTheorem1219CenteredConditions.of_theorem_conditions
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
    (e := fun m ω => stackErrors e m ω)
    (u2 := fun m ω => stackRegressors u2 m ω)
    (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (ManyInstrumentsTheorem1219Conditions.of_stacked_primitive_wlln_ae_nonsingular_sample_eigenvalue_measurable_remainders
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
      (e := e) (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hreduced hstruct hgram_meas
      hscore_meas hinst hint_outer hindep_outer hident_outer hSigma22
      hint_cross hindep_cross hident_cross hSigma2e hH hSigma22_psd
      hnonsing hZ_meas hu2_meas he_meas
      hprojected_error_gram_trace_remainder_tendsto_zero
      hprojected_error_cross_trace_remainder_tendsto_zero hmu)
    hOLS_meas h2SLS_meas hLIML_meas

end ManyInstrumentsTheorem1219CenteredConditions

section ManyInstrumentsTheorem1219CenteredEntrywiseSampleEigenvalueEndpoint

open ManyInstrumentsHomoskedasticProjectionRemainderConditions
open ManyInstrumentsTheorem1219CenteredConditions

namespace ManyInstrumentsTheorem1219CenteredConditions

/-- Centered Theorem 12.19 package from reduced-form WLLNs, a.e. nonsingular
instruments, entrywise projected-error trace remainders, and the sample LIML
eigenvalue adjustment-gap WLLN.

This is the centered counterpart of the uncentered entrywise/sample-eigenvalue
constructor.
It exposes the same primitive boundary while returning the centered estimator
condition package used by Hansen's displayed bias statements. -/
theorem
of_reduced_form_wlln_ae_nonsingular_sample_eigenvalue_entrywise_remainders
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hentry : ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
      μ Z e u2)
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha := by
  let hproj : ManyInstrumentsHomoskedasticProjectionRemainderConditions
      μ Z e u2 :=
    of_entrywise_measurable_ae_nonsingular_remainders
      (μ := μ) (Z := Z) (e := e) (u2 := u2)
      hnonsing hZ_meas hu2_meas he_meas hentry
  exact
    ManyInstrumentsTheorem1219CenteredConditions.of_wlln_ae_nonsingular_sample_eigenvalue
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
      (e := e) (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
      hproj.projected_error_gram_meas
      hproj.projected_error_cross_meas
      hproj.projected_error_gram_trace_remainder_tendsto_zero
      hproj.projected_error_cross_trace_remainder_tendsto_zero
      hmu hOLS_meas h2SLS_meas hLIML_meas

set_option linter.style.longLine false in
/-- Centered Theorem 12.19 package from reduced-form WLLNs with scalar
projected-error row WLLNs and a scalar LIML adjustment-gap WLLN.

This mirrors the uncentered scalar-WLLN constructor, but returns the centered
estimator-limit package directly. -/
theorem
of_reduced_form_wlln_ae_nonsingular_scalar_wlln_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : k → k → ℕ → Ω → ℝ}
    {cross_row : k → ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha :=
  of_reduced_form_wlln_ae_nonsingular_sample_eigenvalue_entrywise_remainders
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
    hZ_meas hu2_meas he_meas hremainder.toEntryWLLNConditions
    hmu.toSampleEigenvalueProblemConditions hOLS_meas h2SLS_meas hLIML_meas

set_option linter.style.longLine false in
/-- Centered Theorem 12.19 package from reduced-form WLLNs, canonical
projected-error row-average convergence, and a scalar LIML adjustment-gap WLLN.

This centered constructor keeps the projected-error primitive at the exact
canonical finite-sample row-average layer and converts it through the existing
entrywise bridge internally. -/
theorem
of_reduced_form_wlln_ae_nonsingular_canonical_row_average_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hcanonical :
      ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions
        μ Z e u2)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha :=
  of_reduced_form_wlln_ae_nonsingular_sample_eigenvalue_entrywise_remainders
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
    hZ_meas hu2_meas he_meas hcanonical.toEntryWLLNConditions
    hmu.toSampleEigenvalueProblemConditions hOLS_meas h2SLS_meas hLIML_meas

set_option linter.style.longLine false in
/-- Centered Theorem 12.19 package from reduced-form WLLNs with matrix/vector
projected-error row WLLNs and a scalar LIML adjustment-gap WLLN.

This is the centered condition-package analogue of the row-WLLN estimator
endpoint. -/
theorem
of_reduced_form_wlln_ae_nonsingular_row_wlln_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    ManyInstrumentsTheorem1219CenteredConditions
      μ Z X Y limlMuHat β H Sigma22 Sigma2e alpha :=
  of_reduced_form_wlln_ae_nonsingular_sample_eigenvalue_entrywise_remainders
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
    hZ_meas hu2_meas he_meas hremainder.toEntryWLLNConditions
    hmu.toSampleEigenvalueProblemConditions hOLS_meas h2SLS_meas hLIML_meas

end ManyInstrumentsTheorem1219CenteredConditions

/-- Hansen Theorem 12.19 in centered form directly from reduced-form WLLNs,
a.e. nonsingular instruments, entrywise projected-error trace remainders, and
the sample LIML eigenvalue adjustment-gap WLLN. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hentry : ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
      μ Z e u2)
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_centered
    (μ := μ) (Z := Z) (X := X) (Y := Y) (limlMuHat := limlMuHat)
    (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (alpha := alpha)
      (of_reduced_form_wlln_ae_nonsingular_sample_eigenvalue_entrywise_remainders
        (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
        (u2 := u2) (limlMuHat := limlMuHat) (β := β)
        (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
        halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing
        hZ_meas hu2_meas he_meas hentry hmu hOLS_meas h2SLS_meas hLIML_meas)

set_option linter.style.longLine false in
/-- Ratio-facing centered reduced-form endpoint for Hansen Theorem 12.19.

This removes the explicit `0 ≤ α` caller obligation from the centered
entrywise/sample-eigenvalue endpoint; it follows from Hansen's instrument-ratio
convergence assumption. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hentry : ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
      μ Z e u2)
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hentry hmu hOLS_meas h2SLS_meas hLIML_meas

set_option linter.style.longLine false in
/-- Auto-measurable centered entrywise/sample-eigenvalue endpoint for Hansen
Theorem 12.19.

This is the same theorem as
`manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue`,
but estimator measurability is derived from the reduced-form equation,
structural equation, row measurability, and the LIML eigenvalue measurability
stored in the sample-eigenvalue package. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hentry : ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
      μ Z e u2)
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hmeas :=
    manyInstruments_estimator_measurability_of_reduced_form
      (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      hRF.reduced_form hstruct hZ_meas hu2_meas he_meas hmu.meas
  exact
    manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
      hu2_meas he_meas hentry hmu hmeas.1 hmeas.2.1 hmeas.2.2

set_option linter.style.longLine false in
/-- Ratio-facing auto-measurable centered entrywise/sample-eigenvalue endpoint
for Hansen Theorem 12.19. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hentry : ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
      μ Z e u2)
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue_autoMeas
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hentry hmu

set_option linter.style.longLine false in
/-- Centered Hansen Theorem 12.19 directly from one iid compressed-signal row
process, a.e. nonsingular instruments, entrywise projected-error trace
remainders, and the sample LIML eigenvalue adjustment-gap WLLN. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_iid_compressed_signal_entrywise_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {signal : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hcompressed : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentSignal (Z m ω) (Gamma m) = stackRegressors signal m ω)
    (hsignal_meas : ∀ i, AEStronglyMeasurable (signal i) μ)
    (hjoint_indep : iIndepFun
      (fun i ω => ((signal i ω, u2 i ω), e i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => ((signal i ω, u2 i ω), e i ω))
        (fun ω => ((signal 0 ω, u2 0 ω), e 0 ω)) μ μ)
    (hsignal_norm_sq : Integrable (fun ω => ‖signal 0 ω‖ ^ 2) μ)
    (hsignal_gram_limit : H = popGram μ signal)
    (hsym_cross_integrable : Integrable
      (fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)) μ)
    (hsym_cross_mean_zero :
      μ[fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)] = 0)
    (hsignal_score_integrable : Integrable (fun ω => e 0 ω • signal 0 ω) μ)
    (hsignal_score_mean_zero : μ[fun ω => e 0 ω • signal 0 ω] = 0)
    (hu2_outer_integrable : Integrable
      (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hu2_score_integrable : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ i, AEStronglyMeasurable (u2 i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hentry :
      ManyInstrumentsProjectedErrorTraceRemainderEntryWLLNConditions
        μ Z (fun m ω => stackErrors e m ω)
          (fun m ω => stackRegressors u2 m ω))
    (hmu : ManyInstrumentsLIMLSampleEigenvalueProblemConditions
      (ι := ι) μ limlMuHat)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_centered
    (μ := μ) (Z := Z) (X := X) (Y := Y) (limlMuHat := limlMuHat)
    (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (alpha := alpha)
    (ManyInstrumentsTheorem1219CenteredConditions.of_theorem_conditions
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
      (e := fun m ω => stackErrors e m ω)
      (u2 := fun m ω => stackRegressors u2 m ω)
      (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      (ManyInstrumentsTheorem1219Conditions.of_iid_compressed_signal_ae_nonsingular_sample_eigenvalue_entrywise_remainders
        (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
        (signal := signal) (e := e) (u2 := u2) (limlMuHat := limlMuHat)
        (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
        (alpha := alpha)
        halpha_nonneg halpha_lt_one hratio hreduced hstruct hgram_meas
        hscore_meas hcompressed hsignal_meas hjoint_indep hjoint_ident
        hsignal_norm_sq hsignal_gram_limit hsym_cross_integrable
        hsym_cross_mean_zero hsignal_score_integrable hsignal_score_mean_zero
        hu2_outer_integrable hSigma22 hu2_score_integrable hSigma2e hH
        hSigma22_psd hnonsing hZ_meas hu2_meas he_meas hentry hmu)
      hOLS_meas h2SLS_meas hLIML_meas)

set_option linter.style.longLine false in
/-- Centered Hansen Theorem 12.19 from reduced-form WLLNs and scalar
sample-average WLLNs for the projected-error trace remainders and LIML
eigenvalue adjustment gap. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_scalar_wlln_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : k → k → ℕ → Ω → ℝ}
    {cross_row : k → ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
    hu2_meas he_meas hremainder.toEntryWLLNConditions
    hmu.toSampleEigenvalueProblemConditions hOLS_meas h2SLS_meas hLIML_meas

set_option linter.style.longLine false in
/-- Ratio-facing centered reduced-form scalar-WLLN endpoint for Hansen
Theorem 12.19.

This removes the explicit `0 ≤ α` caller obligation from the centered scalar
WLLN endpoint; it follows from Hansen's instrument-ratio convergence
assumption. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_scalar_wlln_sample_eigenvalue_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : k → k → ℕ → Ω → ℝ}
    {cross_row : k → ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_scalar_wlln_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
    (cross_row := cross_row) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hremainder hmu hOLS_meas h2SLS_meas hLIML_meas

set_option linter.style.longLine false in
/-- Auto-measurable centered reduced-form scalar-WLLN endpoint for Hansen
Theorem 12.19.

This removes the three finite-sample estimator measurability premises from
`manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_scalar_wlln_sample_eigenvalue`.
They follow from the reduced-form equation, structural equation, row
measurability of `Z`, `u₂`, `e`, and the sample LIML adjustment measurability
already recorded in the eigenvalue-gap package. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_scalar_wlln_sample_eigenvalue_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : k → k → ℕ → Ω → ℝ}
    {cross_row : k → ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hmeas :=
    manyInstruments_estimator_measurability_of_reduced_form
      (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      hRF.reduced_form hstruct hZ_meas hu2_meas he_meas hmu.meas
  exact
    manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_scalar_wlln_sample_eigenvalue
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
      hu2_meas he_meas hremainder hmu hmeas.1 hmeas.2.1 hmeas.2.2

set_option linter.style.longLine false in
/-- Ratio-facing auto-measurable centered scalar-WLLN endpoint for Hansen
Theorem 12.19. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_scalar_wlln_sample_eigenvalue_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : k → k → ℕ → Ω → ℝ}
    {cross_row : k → ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_scalar_wlln_sample_eigenvalue_autoMeas
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
    (cross_row := cross_row) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hremainder hmu

set_option linter.style.longLine false in
/-- Auto-measurable centered reduced-form canonical-row endpoint for Hansen
Theorem 12.19.

This is the theorem-facing canonical projected-error route: estimator
measurability is derived from the reduced-form and structural equations, while
the projection input is exactly
`ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions`. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_canonical_row_average_sample_eigenvalue_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hcanonical :
      ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions
        μ Z e u2)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hmeas :=
    manyInstruments_estimator_measurability_of_reduced_form
      (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      hRF.reduced_form hstruct hZ_meas hu2_meas he_meas hmu.meas
  exact
    manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
      hu2_meas he_meas hcanonical.toEntryWLLNConditions
      hmu.toSampleEigenvalueProblemConditions hmeas.1 hmeas.2.1 hmeas.2.2

set_option linter.style.longLine false in
/-- Ratio-facing auto-measurable centered canonical-row endpoint for Hansen
Theorem 12.19. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_canonical_row_average_sample_eigenvalue_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hcanonical :
      ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions
        μ Z e u2)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_canonical_row_average_sample_eigenvalue_autoMeas
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gap_row := gap_row)
    (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hcanonical hmu

set_option linter.style.longLine false in
/-- Ratio-facing auto-measurable centered canonical-row endpoint for Hansen
Theorem 12.19 with the LIML eigenvalue input stated as the finite-sample
Rayleigh adjustment-gap WLLN. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_canonical_row_average_rayleigh_adjustment_gap_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hcanonical :
      ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions
        μ Z e u2)
    (hrayleigh :
      ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions
        (ι := ι) μ Z X Y limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_canonical_row_average_sample_eigenvalue_of_card_ratio_autoMeas
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gap_row := gap_row)
    (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (alpha := alpha)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hcanonical hrayleigh.toAdjustmentGapWLLNConditions

set_option linter.style.longLine false in
/-- Centered canonical-row Rayleigh Hansen Theorem 12.19 in textbook k-class
notation.

This is the centered auto-measurable companion of
`manyInstruments_estimators_theorem12_19_of_reduced_form_canonical_row_average_rayleigh_adjustment_gap_kappa_of_card_ratio`. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_canonical_row_average_rayleigh_adjustment_gap_kappa_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hcanonical :
      ManyInstrumentsProjectedErrorTraceRemainderCanonicalRowAverageConditions
        μ Z e u2)
    (hrayleigh :
      ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions
        (ι := ι) μ Z X Y limlMuHat gap_row)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hbase :=
    manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_canonical_row_average_rayleigh_adjustment_gap_of_card_ratio_autoMeas
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
      hcanonical hrayleigh
  have hliml : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
    refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hbase.2.2
    intro m
    exact ae_of_all μ (fun ω => by
      simp [limlBetaStar_eq_kClass_add_one, hkappa m ω])
  exact ⟨hbase.1, hbase.2.1, hliml⟩

set_option linter.style.longLine false in
/-- Ratio-facing auto-measurable centered row-WLLN endpoint for Hansen
Theorem 12.19 with the LIML eigenvalue input stated as the finite-sample
Rayleigh adjustment-gap WLLN. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_rayleigh_adjustment_gap_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hrayleigh :
      ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions
        (ι := ι) μ Z X Y limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_canonical_row_average_rayleigh_adjustment_gap_of_card_ratio_autoMeas
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hremainder.toCanonicalRowAverageConditions hrayleigh

set_option linter.style.longLine false in
/-- Centered row-WLLN Rayleigh Hansen Theorem 12.19 in textbook k-class
notation.

This is the centered auto-measurable companion of
`manyInstruments_estimators_theorem12_19_of_reduced_form_row_wlln_rayleigh_adjustment_gap_kappa_of_card_ratio`. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_rayleigh_adjustment_gap_kappa_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hrayleigh :
      ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions
        (ι := ι) μ Z X Y limlMuHat gap_row)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hbase :=
    manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_rayleigh_adjustment_gap_of_card_ratio_autoMeas
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
      hremainder hrayleigh
  have hliml : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
    refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hbase.2.2
    intro m
    exact ae_of_all μ (fun ω => by
      simp [limlBetaStar_eq_kClass_add_one, hkappa m ω])
  exact ⟨hbase.1, hbase.2.1, hliml⟩

set_option linter.style.longLine false in
/-- Centered Hansen Theorem 12.19 from reduced-form WLLNs, matrix/vector row
WLLNs for the projected-error trace remainders, and a scalar LIML
adjustment-gap WLLN. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_entrywise_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
    hu2_meas he_meas hremainder.toEntryWLLNConditions
    hmu.toSampleEigenvalueProblemConditions hOLS_meas h2SLS_meas hLIML_meas

set_option linter.style.longLine false in
/-- Ratio-facing centered reduced-form row-WLLN endpoint for Hansen
Theorem 12.19. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
    (cross_row := cross_row) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hremainder hmu hOLS_meas h2SLS_meas hLIML_meas

set_option linter.style.longLine false in
/-- Auto-measurable centered reduced-form row-WLLN endpoint for Hansen
Theorem 12.19.

This removes the three finite-sample estimator measurability premises from
`manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue`.
They follow from the reduced-form equation, structural equation, row
measurability of `Z`, `u₂`, `e`, and the sample LIML adjustment measurability
already recorded in the eigenvalue-gap package. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hmeas :=
    manyInstruments_estimator_measurability_of_reduced_form
      (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (β := β)
      hRF.reduced_form hstruct hZ_meas hu2_meas he_meas hmu.meas
  exact
    manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
      hu2_meas he_meas hremainder hmu hmeas.1 hmeas.2.1 hmeas.2.2

set_option linter.style.longLine false in
/-- Ratio-facing auto-measurable centered row-WLLN endpoint for Hansen
Theorem 12.19. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue_autoMeas
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
    (cross_row := cross_row) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hremainder hmu

set_option linter.style.longLine false in
/-- Auto-measurable centered Theorem 12.19 endpoint from a single joint row
process for the projected-error trace remainders.

Compared with
`manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue_autoMeas`,
this wrapper derives the separate Gram and score row-WLLN independence and
identical-law fields from one joint row process. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_joint_row_wlln_sample_eigenvalue_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gram_row i ω)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, cross_row i ω)
    (hgram_integrable : Integrable (gram_row 0) μ)
    (hcross_integrable : Integrable (cross_row 0) μ)
    (hjoint_indep : iIndepFun (fun i ω => (gram_row i ω, cross_row i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => (gram_row i ω, cross_row i ω))
        (fun ω => (gram_row 0 ω, cross_row 0 ω)) μ μ)
    (hgram_mean_zero : μ[gram_row 0] = 0)
    (hcross_mean_zero : μ[cross_row 0] = 0)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue_autoMeas
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
    (cross_row := cross_row) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
    hu2_meas he_meas
    (ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions.of_joint_wlln
      (μ := μ) (Z := Z) (e := e) (u2 := u2)
      (gram_row := gram_row) (cross_row := cross_row)
      hgram_remainder_eq_avg hcross_remainder_eq_avg hgram_integrable
      hcross_integrable hjoint_indep hjoint_ident hgram_mean_zero
      hcross_mean_zero)
    hmu

set_option linter.style.longLine false in
/-- Ratio-facing version of the joint-row projected-error remainder endpoint
for Hansen Theorem 12.19. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_joint_row_wlln_sample_eigenvalue_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, gram_row i ω)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, cross_row i ω)
    (hgram_integrable : Integrable (gram_row 0) μ)
    (hcross_integrable : Integrable (cross_row 0) μ)
    (hjoint_indep : iIndepFun (fun i ω => (gram_row i ω, cross_row i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => (gram_row i ω, cross_row i ω))
        (fun ω => (gram_row 0 ω, cross_row 0 ω)) μ μ)
    (hgram_mean_zero : μ[gram_row 0] = 0)
    (hcross_mean_zero : μ[cross_row 0] = 0)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_joint_row_wlln_sample_eigenvalue_autoMeas
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
    (cross_row := cross_row) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hgram_remainder_eq_avg hcross_remainder_eq_avg hgram_integrable
    hcross_integrable hjoint_indep hjoint_ident hgram_mean_zero
    hcross_mean_zero hmu

set_option linter.style.longLine false in
/-- Ratio-facing centered Theorem 12.19 endpoint from one joint row process for
the projected-error trace remainders and Hansen's finite-sample Rayleigh
adjustment gap.

This is the strongest centered row-process facade in this file: the separate
projected-error row-WLLN and LIML adjustment-gap packages are both derived from
`ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions`. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_projected_error_rayleigh_joint_row_wlln_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hjoint :
      ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions
        (ι := ι) μ Z X Y e u2 limlMuHat gram_row cross_row gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_rayleigh_adjustment_gap_of_card_ratio_autoMeas
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
    (cross_row := cross_row) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hjoint.toProjectedErrorRowWLLNConditions
    hjoint.toRayleighAdjustmentGapWLLNConditions

set_option linter.style.longLine false in
/-- Ratio-facing centered Hansen Theorem 12.19 endpoint from one raw iid joint
row process for the projected-error trace remainders and LIML Rayleigh
adjustment gap. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {row : ℕ → Ω → (Matrix k k ℝ × (k → ℝ)) × ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hrayleigh : ∀ m ω,
      LIMLRayleighMinimizer
        (manyInstrumentsLIMLSampleRayleighNumerator (Z m ω) (X m ω) (Y m ω))
        (manyInstrumentsLIMLSampleRayleighDenominator (Z m ω) (X m ω) (Y m ω))
        (limlMuHat m ω))
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.1)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.2)
    (hadjustment_gap_eq_avg : ∀ (m : ℕ) (ω : Ω),
      limlMuHat m ω -
          manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).2)
    (hrow_integrable : Integrable (row 0) μ)
    (hrow_indep : iIndepFun row μ)
    (hrow_ident : ∀ i, IdentDistrib (row i) (row 0) μ μ)
    (hrow_mean_zero : μ[row 0] = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_projected_error_rayleigh_joint_row_wlln_of_card_ratio_autoMeas
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat)
    (gram_row := fun i ω => (row i ω).1.1)
    (cross_row := fun i ω => (row i ω).1.2)
    (gap_row := fun i ω => (row i ω).2) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    (ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions.of_raw_joint_row
      (μ := μ) (ι := ι) (Z := Z) (X := X) (Y := Y) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (row := row)
      hrayleigh hgram_remainder_eq_avg hcross_remainder_eq_avg
      hadjustment_gap_eq_avg hrow_integrable hrow_indep hrow_ident
      hrow_mean_zero)

set_option linter.style.longLine false in
/-- Centered Hansen Theorem 12.19 from one iid compressed-signal row process and
scalar row-WLLN certificates for the projected-error and LIML eigenvalue
remainders. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_iid_compressed_signal_scalar_wlln_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {signal : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : k → k → ℕ → Ω → ℝ}
    {cross_row : k → ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hcompressed : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentSignal (Z m ω) (Gamma m) = stackRegressors signal m ω)
    (hsignal_meas : ∀ i, AEStronglyMeasurable (signal i) μ)
    (hjoint_indep : iIndepFun
      (fun i ω => ((signal i ω, u2 i ω), e i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => ((signal i ω, u2 i ω), e i ω))
        (fun ω => ((signal 0 ω, u2 0 ω), e 0 ω)) μ μ)
    (hsignal_norm_sq : Integrable (fun ω => ‖signal 0 ω‖ ^ 2) μ)
    (hsignal_gram_limit : H = popGram μ signal)
    (hsym_cross_integrable : Integrable
      (fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)) μ)
    (hsym_cross_mean_zero :
      μ[fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)] = 0)
    (hsignal_score_integrable : Integrable (fun ω => e 0 ω • signal 0 ω) μ)
    (hsignal_score_mean_zero : μ[fun ω => e 0 ω • signal 0 ω] = 0)
    (hu2_outer_integrable : Integrable
      (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hu2_score_integrable : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ i, AEStronglyMeasurable (u2 i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions
        μ Z (fun m ω => stackErrors e m ω)
          (fun m ω => stackRegressors u2 m ω) gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_centered
    (μ := μ) (Z := Z) (X := X) (Y := Y) (limlMuHat := limlMuHat)
    (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (alpha := alpha)
    (ManyInstrumentsTheorem1219CenteredConditions.of_theorem_conditions
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
      (e := fun m ω => stackErrors e m ω)
      (u2 := fun m ω => stackRegressors u2 m ω)
      (limlMuHat := limlMuHat) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      (ManyInstrumentsTheorem1219Conditions.of_iid_compressed_signal_ae_nonsingular_sample_eigenvalue_entrywise_remainders
        (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
        (signal := signal) (e := e) (u2 := u2) (limlMuHat := limlMuHat)
        (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
        (alpha := alpha)
        halpha_nonneg halpha_lt_one hratio hreduced hstruct hgram_meas
        hscore_meas hcompressed hsignal_meas hjoint_indep hjoint_ident
        hsignal_norm_sq hsignal_gram_limit hsym_cross_integrable
        hsym_cross_mean_zero hsignal_score_integrable hsignal_score_mean_zero
        hu2_outer_integrable hSigma22 hu2_score_integrable hSigma2e hH
        hSigma22_psd hnonsing hZ_meas hu2_meas he_meas
        hremainder.toEntryWLLNConditions hmu.toSampleEigenvalueProblemConditions)
      hOLS_meas h2SLS_meas hLIML_meas)

set_option linter.style.longLine false in
/-- Auto-measurable centered iid compressed-signal endpoint for Hansen Theorem
12.19.

This wrapper removes the three estimator-measurability premises from
`manyInstruments_estimators_minus_beta_theorem12_19_of_iid_compressed_signal_scalar_wlln_sample_eigenvalue`.
They are derived from the reduced-form equation, the structural equation,
row measurability of `Z`, `u₂`, and `e`, and the LIML adjustment measurability
carried by the sample-eigenvalue WLLN package. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_iid_compressed_signal_scalar_wlln_sample_eigenvalue_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {signal : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : k → k → ℕ → Ω → ℝ}
    {cross_row : k → ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hcompressed : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentSignal (Z m ω) (Gamma m) = stackRegressors signal m ω)
    (hsignal_meas : ∀ i, AEStronglyMeasurable (signal i) μ)
    (hjoint_indep : iIndepFun
      (fun i ω => ((signal i ω, u2 i ω), e i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => ((signal i ω, u2 i ω), e i ω))
        (fun ω => ((signal 0 ω, u2 0 ω), e 0 ω)) μ μ)
    (hsignal_norm_sq : Integrable (fun ω => ‖signal 0 ω‖ ^ 2) μ)
    (hsignal_gram_limit : H = popGram μ signal)
    (hsym_cross_integrable : Integrable
      (fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)) μ)
    (hsym_cross_mean_zero :
      μ[fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)] = 0)
    (hsignal_score_integrable : Integrable (fun ω => e 0 ω • signal 0 ω) μ)
    (hsignal_score_mean_zero : μ[fun ω => e 0 ω • signal 0 ω] = 0)
    (hu2_outer_integrable : Integrable
      (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hu2_score_integrable : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ i, AEStronglyMeasurable (u2 i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions
        μ Z (fun m ω => stackErrors e m ω)
          (fun m ω => stackRegressors u2 m ω) gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hu2_stack_meas : ∀ m,
      AEStronglyMeasurable (fun ω => stackRegressors u2 m ω) μ := by
    intro m
    simpa [stackRegressors] using
      (stackMatrix_aestronglyMeasurable
        (μ := μ) (n := m) (X := u2) hu2_meas)
  have he_stack_meas : ∀ m,
      AEStronglyMeasurable (fun ω => stackErrors e m ω) μ := by
    intro m
    exact
      manyInstrumentVector_aestronglyMeasurable_of_entries (μ := μ)
        (v := fun ω => stackErrors e m ω)
        (fun i => by simpa [stackErrors] using he_meas i.val)
  have hmeas :=
    manyInstruments_estimator_measurability_of_reduced_form
      (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
      (e := fun m ω => stackErrors e m ω)
      (u2 := fun m ω => stackRegressors u2 m ω)
      (limlMuHat := limlMuHat) (β := β)
      hreduced hstruct hZ_meas hu2_stack_meas he_stack_meas hmu.meas
  exact
    manyInstruments_estimators_minus_beta_theorem12_19_of_iid_compressed_signal_scalar_wlln_sample_eigenvalue
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
      (signal := signal) (e := e) (u2 := u2) (limlMuHat := limlMuHat)
      (gram_row := gram_row) (cross_row := cross_row) (gap_row := gap_row)
      (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hreduced hstruct hgram_meas
      hscore_meas hcompressed hsignal_meas hjoint_indep hjoint_ident
      hsignal_norm_sq hsignal_gram_limit hsym_cross_integrable
      hsym_cross_mean_zero hsignal_score_integrable hsignal_score_mean_zero
      hu2_outer_integrable hSigma22 hu2_score_integrable hSigma2e hH
      hSigma22_psd hnonsing hZ_meas hu2_meas he_meas hremainder hmu
      hmeas.1 hmeas.2.1 hmeas.2.2

set_option linter.style.longLine false in
/-- Ratio-facing auto-measurable iid compressed-signal endpoint for Hansen
Theorem 12.19.

This is the iid compressed-row analogue of the reduced-form ratio-facing
wrappers: the nonnegativity of Hansen's instrument ratio limit `α` is derived
from `ℓ_n / n -> α`, so callers do not provide it separately. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_iid_compressed_signal_scalar_wlln_sample_eigenvalue_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {signal : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    {u2 : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : k → k → ℕ → Ω → ℝ}
    {cross_row : k → ℕ → Ω → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hreduced : ∀ (m : ℕ) (ω : Ω),
      X m ω = manyInstrumentSignal (Z m ω) (Gamma m) +
        stackRegressors u2 m ω)
    (hstruct : ∀ (m : ℕ) (ω : Ω),
      Y m ω = X m ω *ᵥ β + stackErrors e m ω)
    (hgram_meas : ∀ m, AEStronglyMeasurable (fun ω => sampleGram (X m ω)) μ)
    (hscore_meas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleCrossMoment (X m ω) (stackErrors e m ω)) μ)
    (hcompressed : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentSignal (Z m ω) (Gamma m) = stackRegressors signal m ω)
    (hsignal_meas : ∀ i, AEStronglyMeasurable (signal i) μ)
    (hjoint_indep : iIndepFun
      (fun i ω => ((signal i ω, u2 i ω), e i ω)) μ)
    (hjoint_ident : ∀ i,
      IdentDistrib
        (fun ω => ((signal i ω, u2 i ω), e i ω))
        (fun ω => ((signal 0 ω, u2 0 ω), e 0 ω)) μ μ)
    (hsignal_norm_sq : Integrable (fun ω => ‖signal 0 ω‖ ^ 2) μ)
    (hsignal_gram_limit : H = popGram μ signal)
    (hsym_cross_integrable : Integrable
      (fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)) μ)
    (hsym_cross_mean_zero :
      μ[fun ω => manyInstrumentSymCrossRow (signal 0 ω) (u2 0 ω)] = 0)
    (hsignal_score_integrable : Integrable (fun ω => e 0 ω • signal 0 ω) μ)
    (hsignal_score_mean_zero : μ[fun ω => e 0 ω • signal 0 ω] = 0)
    (hu2_outer_integrable : Integrable
      (fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)) μ)
    (hSigma22 : Sigma22 = μ[fun ω => Matrix.vecMulVec (u2 0 ω) (u2 0 ω)])
    (hu2_score_integrable : Integrable (fun ω => e 0 ω • u2 0 ω) μ)
    (hSigma2e : Sigma2e = μ[fun ω => e 0 ω • u2 0 ω])
    (hH : H.PosDef) (hSigma22_psd : Sigma22.PosSemidef)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ i, AEStronglyMeasurable (u2 i) μ)
    (he_meas : ∀ i, AEStronglyMeasurable (e i) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions
        μ Z (fun m ω => stackErrors e m ω)
          (fun m ω => stackRegressors u2 m ω) gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_estimators_minus_beta_theorem12_19_of_iid_compressed_signal_scalar_wlln_sample_eigenvalue_autoMeas
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma)
    (signal := signal) (e := e) (u2 := u2) (limlMuHat := limlMuHat)
    (gram_row := gram_row) (cross_row := cross_row) (gap_row := gap_row)
    (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hreduced hstruct hgram_meas hscore_meas
    hcompressed hsignal_meas hjoint_indep hjoint_ident hsignal_norm_sq
    hsignal_gram_limit hsym_cross_integrable hsym_cross_mean_zero
    hsignal_score_integrable hsignal_score_mean_zero hu2_outer_integrable
    hSigma22 hu2_score_integrable hSigma2e hH hSigma22_psd hnonsing
    hZ_meas hu2_meas he_meas hremainder hmu

end ManyInstrumentsTheorem1219CenteredEntrywiseSampleEigenvalueEndpoint

/-- Hansen Theorem 12.19 LIML consistency in k-class notation, using
`κ̂ = μ̂ + 1`. -/
theorem manyInstruments_limlKClassBetaStar_add_one_minus_beta_tendstoInMeasure
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (h : ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha)
    (hmeas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω + 1) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hliml := manyInstruments_limlBetaStar_minus_beta_tendstoInMeasure h hmeas
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hliml
  intro m
  exact ae_of_all μ (fun ω => by
    simp [limlBetaStar_eq_kClass_add_one])

/-- K-class version of Hansen Theorem 12.19 for any estimator sequence `κ̂`
known pointwise to satisfy `κ̂ = μ̂ + 1`. -/
theorem manyInstruments_limlKClassBetaStar_kappa_minus_beta_tendstoInMeasure
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (h : ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha)
    (hmeas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hκ := manyInstruments_limlKClassBetaStar_add_one_minus_beta_tendstoInMeasure h hmeas
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hκ
  intro m
  exact ae_of_all μ (fun ω => by
    simp [hkappa m ω])

/-- Hansen Theorem 12.19 LIML consistency in k-class notation,
`κ̂ = μ̂ + 1`, stated in the uncentered textbook form. -/
theorem manyInstruments_limlKClassBetaStar_add_one_tendstoInMeasure
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (h : ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω + 1))
      atTop (fun _ => β) := by
  have hliml := (manyInstruments_estimators_theorem12_19 h).2.2
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hliml
  intro m
  exact ae_of_all μ (fun ω => by
    simp [limlBetaStar_eq_kClass_add_one])

/-- K-class version of Hansen Theorem 12.19 for any estimator sequence `κ̂`
known pointwise to satisfy `κ̂ = μ̂ + 1`, stated in the uncentered textbook
form `β̂_LIML ->p β`. -/
theorem manyInstruments_limlKClassBetaStar_kappa_tendstoInMeasure
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (h : ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω))
      atTop (fun _ => β) := by
  have hκ := manyInstruments_limlKClassBetaStar_add_one_tendstoInMeasure h
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hκ
  intro m
  exact ae_of_all μ (fun ω => by
    simp [hkappa m ω])

set_option linter.style.longLine false in
/-- Package-level Rayleigh endpoint for Hansen Theorem 12.19 LIML consistency
in k-class notation `κ̂ = μ̂ + 1`.

This is the bundled-condition analogue of the raw joint-row wrapper below:
callers who already have
`ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions` need not unpack it
just to rewrite LIML into Hansen's displayed k-class form. -/
theorem
manyInstruments_limlKClassBetaStar_add_one_tendstoInMeasure_of_reduced_form_projected_error_rayleigh_joint_row_wlln_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hjoint :
      ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions
        (ι := ι) μ Z X Y e u2 limlMuHat gram_row cross_row gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω + 1))
      atTop (fun _ => β) := by
  have hliml :=
    (manyInstruments_estimators_theorem12_19_of_reduced_form_projected_error_rayleigh_joint_row_wlln_of_card_ratio
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha) halpha_lt_one hratio hstruct hRF hnonsing
      hZ_meas hu2_meas he_meas hjoint).2.2
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hliml
  intro m
  exact ae_of_all μ (fun ω => by
    simp [limlBetaStar_eq_kClass_add_one])

set_option linter.style.longLine false in
/-- Package-level k-class version of Hansen Theorem 12.19 for any pointwise
`κ̂ = μ̂ + 1` sequence. -/
theorem
manyInstruments_limlKClassBetaStar_kappa_tendstoInMeasure_of_reduced_form_projected_error_rayleigh_joint_row_wlln_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hjoint :
      ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions
        (ι := ι) μ Z X Y e u2 limlMuHat gram_row cross_row gap_row)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω))
      atTop (fun _ => β) := by
  have hκ :=
    manyInstruments_limlKClassBetaStar_add_one_tendstoInMeasure_of_reduced_form_projected_error_rayleigh_joint_row_wlln_of_card_ratio
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha) halpha_lt_one hratio hstruct hRF hnonsing
      hZ_meas hu2_meas he_meas hjoint
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hκ
  intro m
  exact ae_of_all μ (fun ω => by
    simp [hkappa m ω])

set_option linter.style.longLine false in
/-- Hansen Theorem 12.19 in textbook k-class notation over the bundled
projected-error/Rayleigh row-WLLN condition package. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_projected_error_rayleigh_joint_row_wlln_kappa_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hjoint :
      ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions
        (ι := ι) μ Z X Y e u2 limlMuHat gram_row cross_row gap_row)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω))
      atTop (fun _ => β) := by
  have hbase :=
    manyInstruments_estimators_theorem12_19_of_reduced_form_projected_error_rayleigh_joint_row_wlln_of_card_ratio
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha) halpha_lt_one hratio hstruct hRF hnonsing
      hZ_meas hu2_meas he_meas hjoint
  have hliml :=
    manyInstruments_limlKClassBetaStar_kappa_tendstoInMeasure_of_reduced_form_projected_error_rayleigh_joint_row_wlln_of_card_ratio
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (kappaHat := kappaHat)
      (gram_row := gram_row) (cross_row := cross_row) (gap_row := gap_row)
      (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha) halpha_lt_one hratio hstruct hRF hnonsing
      hZ_meas hu2_meas he_meas hjoint hkappa
  exact ⟨hbase.1, hbase.2.1, hliml⟩

set_option linter.style.longLine false in
/-- Centered package-level Rayleigh endpoint for Hansen Theorem 12.19 LIML
consistency in k-class notation `κ̂ = μ̂ + 1`. -/
theorem
manyInstruments_limlKClassBetaStar_add_one_minus_beta_tendstoInMeasure_of_reduced_form_projected_error_rayleigh_joint_row_wlln_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hjoint :
      ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions
        (ι := ι) μ Z X Y e u2 limlMuHat gram_row cross_row gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω + 1) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hliml :=
    (manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_projected_error_rayleigh_joint_row_wlln_of_card_ratio_autoMeas
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha) halpha_lt_one hratio hstruct hRF hnonsing
      hZ_meas hu2_meas he_meas hjoint).2.2
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hliml
  intro m
  exact ae_of_all μ (fun ω => by
    simp [limlBetaStar_eq_kClass_add_one])

set_option linter.style.longLine false in
/-- Centered package-level k-class version of Hansen Theorem 12.19 for any
pointwise `κ̂ = μ̂ + 1` sequence. -/
theorem
manyInstruments_limlKClassBetaStar_kappa_minus_beta_tendstoInMeasure_of_reduced_form_projected_error_rayleigh_joint_row_wlln_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hjoint :
      ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions
        (ι := ι) μ Z X Y e u2 limlMuHat gram_row cross_row gap_row)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hκ :=
    manyInstruments_limlKClassBetaStar_add_one_minus_beta_tendstoInMeasure_of_reduced_form_projected_error_rayleigh_joint_row_wlln_of_card_ratio_autoMeas
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha) halpha_lt_one hratio hstruct hRF hnonsing
      hZ_meas hu2_meas he_meas hjoint
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hκ
  intro m
  exact ae_of_all μ (fun ω => by
    simp [hkappa m ω])

set_option linter.style.longLine false in
/-- Centered Hansen Theorem 12.19 in textbook k-class notation over the
bundled projected-error/Rayleigh row-WLLN condition package. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_projected_error_rayleigh_joint_row_wlln_kappa_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hjoint :
      ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions
        (ι := ι) μ Z X Y e u2 limlMuHat gram_row cross_row gap_row)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hbase :=
    manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_projected_error_rayleigh_joint_row_wlln_of_card_ratio_autoMeas
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha) halpha_lt_one hratio hstruct hRF hnonsing
      hZ_meas hu2_meas he_meas hjoint
  have hliml :=
    manyInstruments_limlKClassBetaStar_kappa_minus_beta_tendstoInMeasure_of_reduced_form_projected_error_rayleigh_joint_row_wlln_of_card_ratio_autoMeas
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (kappaHat := kappaHat)
      (gram_row := gram_row) (cross_row := cross_row) (gap_row := gap_row)
      (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha) halpha_lt_one hratio hstruct hRF hnonsing
      hZ_meas hu2_meas he_meas hjoint hkappa
  exact ⟨hbase.1, hbase.2.1, hliml⟩

set_option linter.style.longLine false in
/-- Raw joint-row Rayleigh endpoint for Hansen Theorem 12.19 LIML
consistency in k-class notation `κ̂ = μ̂ + 1`.

This is a thin notation bridge over
`manyInstruments_estimators_theorem12_19_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_of_card_ratio`. -/
theorem
manyInstruments_limlKClassBetaStar_add_one_tendstoInMeasure_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {row : ℕ → Ω → (Matrix k k ℝ × (k → ℝ)) × ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hrayleigh : ∀ m ω,
      LIMLRayleighMinimizer
        (manyInstrumentsLIMLSampleRayleighNumerator (Z m ω) (X m ω) (Y m ω))
        (manyInstrumentsLIMLSampleRayleighDenominator (Z m ω) (X m ω) (Y m ω))
        (limlMuHat m ω))
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.1)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.2)
    (hadjustment_gap_eq_avg : ∀ (m : ℕ) (ω : Ω),
      limlMuHat m ω -
          manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).2)
    (hrow_integrable : Integrable (row 0) μ)
    (hrow_indep : iIndepFun row μ)
    (hrow_ident : ∀ i, IdentDistrib (row i) (row 0) μ μ)
    (hrow_mean_zero : μ[row 0] = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω + 1))
      atTop (fun _ => β) := by
  have hliml :=
    (manyInstruments_estimators_theorem12_19_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_of_card_ratio
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (row := row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha) halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
      hu2_meas he_meas hrayleigh hgram_remainder_eq_avg
      hcross_remainder_eq_avg hadjustment_gap_eq_avg hrow_integrable
      hrow_indep hrow_ident hrow_mean_zero).2.2
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hliml
  intro m
  exact ae_of_all μ (fun ω => by
    simp [limlBetaStar_eq_kClass_add_one])

set_option linter.style.longLine false in
/-- Centered raw joint-row Rayleigh endpoint for Hansen Theorem 12.19 LIML
consistency in k-class notation `κ̂ = μ̂ + 1`. -/
theorem
manyInstruments_limlKClassBetaStar_add_one_minus_beta_tendstoInMeasure_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {row : ℕ → Ω → (Matrix k k ℝ × (k → ℝ)) × ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hrayleigh : ∀ m ω,
      LIMLRayleighMinimizer
        (manyInstrumentsLIMLSampleRayleighNumerator (Z m ω) (X m ω) (Y m ω))
        (manyInstrumentsLIMLSampleRayleighDenominator (Z m ω) (X m ω) (Y m ω))
        (limlMuHat m ω))
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.1)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.2)
    (hadjustment_gap_eq_avg : ∀ (m : ℕ) (ω : Ω),
      limlMuHat m ω -
          manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).2)
    (hrow_integrable : Integrable (row 0) μ)
    (hrow_indep : iIndepFun row μ)
    (hrow_ident : ∀ i, IdentDistrib (row i) (row 0) μ μ)
    (hrow_mean_zero : μ[row 0] = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω + 1) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hliml :=
    (manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_of_card_ratio_autoMeas
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (row := row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha) halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
      hu2_meas he_meas hrayleigh hgram_remainder_eq_avg
      hcross_remainder_eq_avg hadjustment_gap_eq_avg hrow_integrable
      hrow_indep hrow_ident hrow_mean_zero).2.2
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hliml
  intro m
  exact ae_of_all μ (fun ω => by
    simp [limlBetaStar_eq_kClass_add_one])

set_option linter.style.longLine false in
/-- Raw joint-row Rayleigh endpoint for any pointwise
`κ̂ = μ̂ + 1` sequence, stated in the uncentered Hansen Theorem 12.19 k-class
form. -/
theorem
manyInstruments_limlKClassBetaStar_kappa_tendstoInMeasure_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {row : ℕ → Ω → (Matrix k k ℝ × (k → ℝ)) × ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hrayleigh : ∀ m ω,
      LIMLRayleighMinimizer
        (manyInstrumentsLIMLSampleRayleighNumerator (Z m ω) (X m ω) (Y m ω))
        (manyInstrumentsLIMLSampleRayleighDenominator (Z m ω) (X m ω) (Y m ω))
        (limlMuHat m ω))
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.1)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.2)
    (hadjustment_gap_eq_avg : ∀ (m : ℕ) (ω : Ω),
      limlMuHat m ω -
          manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).2)
    (hrow_integrable : Integrable (row 0) μ)
    (hrow_indep : iIndepFun row μ)
    (hrow_ident : ∀ i, IdentDistrib (row i) (row 0) μ μ)
    (hrow_mean_zero : μ[row 0] = 0)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω))
      atTop (fun _ => β) := by
  have hκ :=
    manyInstruments_limlKClassBetaStar_add_one_tendstoInMeasure_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_of_card_ratio
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (row := row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha) halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
      hu2_meas he_meas hrayleigh hgram_remainder_eq_avg
      hcross_remainder_eq_avg hadjustment_gap_eq_avg hrow_integrable
      hrow_indep hrow_ident hrow_mean_zero
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hκ
  intro m
  exact ae_of_all μ (fun ω => by
    simp [hkappa m ω])

set_option linter.style.longLine false in
/-- Hansen Theorem 12.19 in the textbook k-class notation.

This bundles the OLS and 2SLS probability limits with LIML written as
`limlKClassBetaStar ... κ̂`, where `κ̂ = μ̂ + 1`, over the strongest raw
joint-row Rayleigh facade. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_kappa_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {row : ℕ → Ω → (Matrix k k ℝ × (k → ℝ)) × ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hrayleigh : ∀ m ω,
      LIMLRayleighMinimizer
        (manyInstrumentsLIMLSampleRayleighNumerator (Z m ω) (X m ω) (Y m ω))
        (manyInstrumentsLIMLSampleRayleighDenominator (Z m ω) (X m ω) (Y m ω))
        (limlMuHat m ω))
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.1)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.2)
    (hadjustment_gap_eq_avg : ∀ (m : ℕ) (ω : Ω),
      limlMuHat m ω -
          manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).2)
    (hrow_integrable : Integrable (row 0) μ)
    (hrow_indep : iIndepFun row μ)
    (hrow_ident : ∀ i, IdentDistrib (row i) (row 0) μ μ)
    (hrow_mean_zero : μ[row 0] = 0)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω))
      atTop (fun _ => β) := by
  have hbase :=
    manyInstruments_estimators_theorem12_19_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_of_card_ratio
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (row := row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha) halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
      hu2_meas he_meas hrayleigh hgram_remainder_eq_avg
      hcross_remainder_eq_avg hadjustment_gap_eq_avg hrow_integrable
      hrow_indep hrow_ident hrow_mean_zero
  have hliml :=
    manyInstruments_limlKClassBetaStar_kappa_tendstoInMeasure_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_of_card_ratio
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (kappaHat := kappaHat)
      (row := row) (β := β) (H := H) (Sigma22 := Sigma22)
      (Sigma2e := Sigma2e) (alpha := alpha) halpha_lt_one hratio
      hstruct hRF hnonsing hZ_meas hu2_meas he_meas hrayleigh
      hgram_remainder_eq_avg hcross_remainder_eq_avg
      hadjustment_gap_eq_avg hrow_integrable hrow_indep hrow_ident
      hrow_mean_zero hkappa
  exact ⟨hbase.1, hbase.2.1, hliml⟩

set_option linter.style.longLine false in
/-- Centered raw joint-row Rayleigh endpoint for any pointwise
`κ̂ = μ̂ + 1` sequence. -/
theorem
manyInstruments_limlKClassBetaStar_kappa_minus_beta_tendstoInMeasure_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {row : ℕ → Ω → (Matrix k k ℝ × (k → ℝ)) × ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hrayleigh : ∀ m ω,
      LIMLRayleighMinimizer
        (manyInstrumentsLIMLSampleRayleighNumerator (Z m ω) (X m ω) (Y m ω))
        (manyInstrumentsLIMLSampleRayleighDenominator (Z m ω) (X m ω) (Y m ω))
        (limlMuHat m ω))
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.1)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.2)
    (hadjustment_gap_eq_avg : ∀ (m : ℕ) (ω : Ω),
      limlMuHat m ω -
          manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).2)
    (hrow_integrable : Integrable (row 0) μ)
    (hrow_indep : iIndepFun row μ)
    (hrow_ident : ∀ i, IdentDistrib (row i) (row 0) μ μ)
    (hrow_mean_zero : μ[row 0] = 0)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hκ :=
    manyInstruments_limlKClassBetaStar_add_one_minus_beta_tendstoInMeasure_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_of_card_ratio_autoMeas
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (row := row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha) halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
      hu2_meas he_meas hrayleigh hgram_remainder_eq_avg
      hcross_remainder_eq_avg hadjustment_gap_eq_avg hrow_integrable
      hrow_indep hrow_ident hrow_mean_zero
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hκ
  intro m
  exact ae_of_all μ (fun ω => by
    simp [hkappa m ω])

set_option linter.style.longLine false in
/-- Centered Hansen Theorem 12.19 in textbook k-class notation.

This bundles the centered OLS and 2SLS probability limits with LIML written as
`limlKClassBetaStar ... κ̂`, where `κ̂ = μ̂ + 1`, over the strongest raw
joint-row Rayleigh facade. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_kappa_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {row : ℕ → Ω → (Matrix k k ℝ × (k → ℝ)) × ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hrayleigh : ∀ m ω,
      LIMLRayleighMinimizer
        (manyInstrumentsLIMLSampleRayleighNumerator (Z m ω) (X m ω) (Y m ω))
        (manyInstrumentsLIMLSampleRayleighDenominator (Z m ω) (X m ω) (Y m ω))
        (limlMuHat m ω))
    (hgram_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorGramTraceRemainder (Z m ω) (u2 m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.1)
    (hcross_remainder_eq_avg : ∀ (m : ℕ) (ω : Ω),
      manyInstrumentProjectedErrorCrossTraceRemainder (Z m ω) (u2 m ω) (e m ω) =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).1.2)
    (hadjustment_gap_eq_avg : ∀ (m : ℕ) (ω : Ω),
      limlMuHat m ω -
          manyInstrumentsLIMLEigenvalueCardRatioAdjustment (ι := ι) m =
        (m : ℝ)⁻¹ • ∑ i ∈ Finset.range m, (row i ω).2)
    (hrow_integrable : Integrable (row 0) μ)
    (hrow_indep : iIndepFun row μ)
    (hrow_ident : ∀ i, IdentDistrib (row i) (row 0) μ μ)
    (hrow_mean_zero : μ[row 0] = 0)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hbase :=
    manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_of_card_ratio_autoMeas
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (row := row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha) halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
      hu2_meas he_meas hrayleigh hgram_remainder_eq_avg
      hcross_remainder_eq_avg hadjustment_gap_eq_avg hrow_integrable
      hrow_indep hrow_ident hrow_mean_zero
  have hliml :=
    manyInstruments_limlKClassBetaStar_kappa_minus_beta_tendstoInMeasure_of_reduced_form_raw_projected_error_rayleigh_joint_row_wlln_of_card_ratio_autoMeas
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (kappaHat := kappaHat)
      (row := row) (β := β) (H := H) (Sigma22 := Sigma22)
      (Sigma2e := Sigma2e) (alpha := alpha) halpha_lt_one hratio
      hstruct hRF hnonsing hZ_meas hu2_meas he_meas hrayleigh
      hgram_remainder_eq_avg hcross_remainder_eq_avg
      hadjustment_gap_eq_avg hrow_integrable hrow_indep hrow_ident
      hrow_mean_zero hkappa
  exact ⟨hbase.1, hbase.2.1, hliml⟩

set_option linter.style.longLine false in
/-- Row-WLLN Hansen Theorem 12.19 LIML consistency in k-class notation
`κ̂ = μ̂ + 1`.

This theorem-facing wrapper avoids asking callers to first cite the
`limlBetaStar` endpoint and then rewrite to Hansen's displayed k-class form. -/
theorem
manyInstruments_limlKClassBetaStar_add_one_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω + 1))
      atTop (fun _ => β) := by
  have hliml :=
    (manyInstruments_estimators_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
      hu2_meas he_meas hremainder hmu).2.2
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hliml
  intro m
  exact ae_of_all μ (fun ω => by
    simp [limlBetaStar_eq_kClass_add_one])

set_option linter.style.longLine false in
/-- Ratio-facing row-WLLN k-class endpoint for Hansen Theorem 12.19. -/
theorem
manyInstruments_limlKClassBetaStar_add_one_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω + 1))
      atTop (fun _ => β) :=
  manyInstruments_limlKClassBetaStar_add_one_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
    (cross_row := cross_row) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hremainder hmu

set_option linter.style.longLine false in
/-- Row-WLLN Hansen Theorem 12.19 LIML consistency for any k-class sequence
`κ̂` known pointwise to satisfy `κ̂ = μ̂ + 1`. -/
theorem
manyInstruments_limlKClassBetaStar_kappa_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω))
      atTop (fun _ => β) := by
  have hκ :=
    manyInstruments_limlKClassBetaStar_add_one_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
      hu2_meas he_meas hremainder hmu
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hκ
  intro m
  exact ae_of_all μ (fun ω => by
    simp [hkappa m ω])

set_option linter.style.longLine false in
/-- Ratio-facing row-WLLN k-class endpoint for any pointwise
`κ̂ = μ̂ + 1` sequence. -/
theorem
manyInstruments_limlKClassBetaStar_kappa_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_limlKClassBetaStar_kappa_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (kappaHat := kappaHat)
    (gram_row := gram_row) (cross_row := cross_row) (gap_row := gap_row)
    (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hremainder hmu hkappa

set_option linter.style.longLine false in
/-- Centered row-WLLN Hansen Theorem 12.19 LIML consistency in k-class notation
`κ̂ = μ̂ + 1`.

This is the centered version of
`manyInstruments_limlKClassBetaStar_add_one_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue`;
it reuses the auto-measurable centered estimator endpoint and only rewrites
`limlBetaStar` into Hansen's k-class notation. -/
theorem
manyInstruments_limlKClassBetaStar_add_one_minus_beta_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω + 1) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hliml :=
    (manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue_autoMeas
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
      hu2_meas he_meas hremainder hmu).2.2
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hliml
  intro m
  exact ae_of_all μ (fun ω => by
    simp [limlBetaStar_eq_kClass_add_one])

set_option linter.style.longLine false in
/-- Ratio-facing centered row-WLLN k-class endpoint for Hansen Theorem 12.19. -/
theorem
manyInstruments_limlKClassBetaStar_add_one_minus_beta_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω + 1) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_limlKClassBetaStar_add_one_minus_beta_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
    (cross_row := cross_row) (gap_row := gap_row) (β := β)
    (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hremainder hmu

set_option linter.style.longLine false in
/-- Centered row-WLLN k-class endpoint for any pointwise
`κ̂ = μ̂ + 1` sequence. -/
theorem
manyInstruments_limlKClassBetaStar_kappa_minus_beta_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hκ :=
    manyInstruments_limlKClassBetaStar_add_one_minus_beta_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_nonneg halpha_lt_one hratio hstruct hRF hnonsing hZ_meas
      hu2_meas he_meas hremainder hmu
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hκ
  intro m
  exact ae_of_all μ (fun ω => by
    simp [hkappa m ω])

set_option linter.style.longLine false in
/-- Ratio-facing centered row-WLLN k-class endpoint for any pointwise
`κ̂ = μ̂ + 1` sequence. -/
theorem
manyInstruments_limlKClassBetaStar_kappa_minus_beta_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  manyInstruments_limlKClassBetaStar_kappa_minus_beta_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue
    (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
    (u2 := u2) (limlMuHat := limlMuHat) (kappaHat := kappaHat)
    (gram_row := gram_row) (cross_row := cross_row) (gap_row := gap_row)
    (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (alpha := alpha)
    (manyInstruments_alpha_nonneg_of_card_ratio_tendsto (ι := ι) hratio)
    halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
    hremainder hmu hkappa

set_option linter.style.longLine false in
/-- Row-WLLN Hansen Theorem 12.19 in textbook k-class notation.

This bundles the OLS and 2SLS probability limits with LIML written directly as
`limlKClassBetaStar ... κ̂`, where `κ̂ = μ̂ + 1`, at the row-WLLN
sample-eigenvalue boundary. -/
theorem
manyInstruments_estimators_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue_kappa_of_card_ratio
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω))
      atTop (fun _ => β) := by
  have hbase :=
    manyInstruments_estimators_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue_of_card_ratio
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
      hremainder hmu
  have hliml :=
    manyInstruments_limlKClassBetaStar_kappa_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue_of_card_ratio
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (kappaHat := kappaHat)
      (gram_row := gram_row) (cross_row := cross_row) (gap_row := gap_row)
      (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha) halpha_lt_one hratio hstruct hRF hnonsing
      hZ_meas hu2_meas he_meas hremainder hmu hkappa
  exact ⟨hbase.1, hbase.2.1, hliml⟩

set_option linter.style.longLine false in
/-- Centered row-WLLN Hansen Theorem 12.19 in textbook k-class notation.

This bundles the centered OLS and 2SLS probability limits with LIML written
directly as `limlKClassBetaStar ... κ̂ - β`, where `κ̂ = μ̂ + 1`, and derives
estimator measurability from the reduced-form data. -/
theorem
manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue_kappa_of_card_ratio_autoMeas
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {gram_row : ℕ → Ω → Matrix k k ℝ}
    {cross_row : ℕ → Ω → k → ℝ}
    {gap_row : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio :
      Tendsto (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
        atTop (𝓝 alpha))
    (hstruct : ∀ (m : ℕ) (ω : Ω), Y m ω = X m ω *ᵥ β + e m ω)
    (hRF : ManyInstrumentsReducedFormWLLNConditions
      μ Z X Gamma e u2 H Sigma22 Sigma2e)
    (hnonsing : ∀ m, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)))
    (hZ_meas : ∀ m, AEStronglyMeasurable (Z m) μ)
    (hu2_meas : ∀ m, AEStronglyMeasurable (u2 m) μ)
    (he_meas : ∀ m, AEStronglyMeasurable (e m) μ)
    (hremainder :
      ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
        μ Z e u2 gram_row cross_row)
    (hmu :
      ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
        (ι := ι) μ limlMuHat gap_row)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hbase :=
    manyInstruments_estimators_minus_beta_theorem12_19_of_reduced_form_row_wlln_sample_eigenvalue_of_card_ratio_autoMeas
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (gram_row := gram_row)
      (cross_row := cross_row) (gap_row := gap_row) (β := β)
      (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e) (alpha := alpha)
      halpha_lt_one hratio hstruct hRF hnonsing hZ_meas hu2_meas he_meas
      hremainder hmu
  have hliml :=
    manyInstruments_limlKClassBetaStar_kappa_minus_beta_tendstoInMeasure_of_reduced_form_row_wlln_sample_eigenvalue_of_card_ratio
      (μ := μ) (Z := Z) (X := X) (Y := Y) (Gamma := Gamma) (e := e)
      (u2 := u2) (limlMuHat := limlMuHat) (kappaHat := kappaHat)
      (gram_row := gram_row) (cross_row := cross_row) (gap_row := gap_row)
      (β := β) (H := H) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (alpha := alpha) halpha_lt_one hratio hstruct hRF hnonsing
      hZ_meas hu2_meas he_meas hremainder hmu hkappa
  exact ⟨hbase.1, hbase.2.1, hliml⟩

/-- Hansen Theorem 12.19 assembled in the centered form: OLS and 2SLS have
the displayed many-instrument asymptotic biases, while LIML is centered
`o_p(1)`. -/
theorem manyInstruments_estimators_minus_beta_theorem12_19
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (h : ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) := by
  exact
    ⟨manyInstruments_olsBetaStar_minus_beta_tendstoInMeasure h hOLS_meas,
      manyInstruments_twoSLSBetaStar_minus_beta_tendstoInMeasure h h2SLS_meas,
      manyInstruments_limlBetaStar_minus_beta_tendstoInMeasure h hLIML_meas⟩

/-- Hansen Theorem 12.19 in textbook k-class notation over the canonical
many-instrument condition package. -/
theorem manyInstruments_estimators_theorem12_19_kappa
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (h : ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω))
      atTop (fun _ => β + manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω))
      atTop (fun _ => β) :=
  ⟨(manyInstruments_estimators_theorem12_19 h).1,
    (manyInstruments_estimators_theorem12_19 h).2.1,
    manyInstruments_limlKClassBetaStar_kappa_tendstoInMeasure h hkappa⟩

/-- Hansen Theorem 12.19 in the centered textbook form, with LIML written
directly in k-class notation over the canonical many-instrument condition
package. -/
theorem manyInstruments_estimators_minus_beta_theorem12_19_kappa
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {alpha : ℝ}
    (h : ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H Sigma22 Sigma2e alpha)
    (hkappa : ∀ m ω, kappaHat m ω = limlMuHat m ω + 1)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (X m ω) (Y m ω)) μ)
    (h2SLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) μ)
    (hLIML_meas : ∀ m, AEStronglyMeasurable
      (fun ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω => olsBetaStar (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsOLSBias H Sigma22 Sigma2e) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω) - β)
      atTop (fun _ => manyInstrumentsTwoSLSBias H Sigma22 Sigma2e alpha) ∧
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        limlKClassBetaStar (Z m ω) (X m ω) (Y m ω) (kappaHat m ω) - β)
      atTop (fun _ => (0 : k → ℝ)) :=
  ⟨manyInstruments_olsBetaStar_minus_beta_tendstoInMeasure h hOLS_meas,
    manyInstruments_twoSLSBetaStar_minus_beta_tendstoInMeasure h h2SLS_meas,
    manyInstruments_limlKClassBetaStar_kappa_minus_beta_tendstoInMeasure
      h hLIML_meas hkappa⟩

/-! ## Raw conditional model and generalized-pencil route

The compatibility interfaces above include sample-average decompositions of
projected quadratic forms and of the LIML eigenvalue gap.  Those are not raw
many-instrument assumptions: projection couples all observations, and a
generalized eigenvalue is not an additive row statistic.  The declarations
below provide the canonical replacement boundary.  Projected quadratic forms
are controlled by conditional mean-square bounds, while the LIML adjustment
is obtained by continuous mapping from the normalized sample pencil.
-/

/-- Loading from the reduced-form signal `s = ZΓ` into the joint data row
`[Y X]`: its first column is `s'β` and its remaining columns are `s`. -/
noncomputable def manyInstrumentsStructuralLoading
    (β : k → ℝ) : Matrix k (Sum Unit k) ℝ :=
  fun i j => match j with
    | Sum.inl _ => β i
    | Sum.inr h => if i = h then 1 else 0

/-- Structural-residual direction `[1; -β]`.  It annihilates the signal
loading and therefore attains the smallest limiting LIML root. -/
def manyInstrumentsStructuralResidualDirection
    (β : k → ℝ) : Sum Unit k → ℝ
  | Sum.inl _ => 1
  | Sum.inr j => -β j

/-- Full reduced-form error row `[e,u₂]`. -/
noncomputable def manyInstrumentsReducedFormErrorData
    {n : Type*} [Fintype n]
    (e : n → ℝ) (u2 : Matrix n k ℝ) : Matrix n (Sum Unit k) ℝ :=
  Matrix.fromCols (fun i (_ : Unit) => e i) u2

/-- Hansen's primitive reduced-form error row `[u₁,u₂]` in (12.74).

The separate name prevents the first coordinate from being confused with the
structural error `e = u₁ - β'u₂` used by the internal proof engine. -/
noncomputable def manyInstrumentsHansenReducedFormErrorData
    {n : Type*} [Fintype n]
    (u1 : n → ℝ) (u2 : Matrix n k ℝ) : Matrix n (Sum Unit k) ℝ :=
  Matrix.fromCols (fun i (_ : Unit) => u1 i) u2

/-- Hansen's structural error `e = u₁ - β'u₂` from the reduced form (12.73). -/
noncomputable def manyInstrumentsStructuralError
    {n : Type*} [Fintype n]
    (u1 : n → ℝ) (u2 : Matrix n k ℝ) (β : k → ℝ) : n → ℝ :=
  fun i => u1 i - dotProduct (u2 i) β

/-- Loading that maps Hansen's primitive row `[u₁,u₂]` to the internal
structural-error row `[u₁ - β'u₂,u₂]`. -/
noncomputable def manyInstrumentsStructuralErrorLoading
    (β : k → ℝ) : Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  fun i j => match i, j with
    | Sum.inl _, Sum.inl _ => 1
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr a, Sum.inl _ => -β a
    | Sum.inr a, Sum.inr b => if a = b then 1 else 0

/-- The internal covariance of `[e,u₂]`, derived by congruence from Hansen's
primitive covariance `Σ = Var([u₁,u₂] | Z)` in (12.74). -/
noncomputable def manyInstrumentsStructuralErrorCovariance
    (β : k → ℝ) (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) :
    Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  (manyInstrumentsStructuralErrorLoading β)ᵀ * Sigma *
    manyInstrumentsStructuralErrorLoading β

@[simp]
theorem manyInstrumentsHansenReducedFormErrorData_mul_structuralErrorLoading
    {n : Type*} [Fintype n]
    (u1 : n → ℝ) (u2 : Matrix n k ℝ) (β : k → ℝ) :
    manyInstrumentsHansenReducedFormErrorData u1 u2 *
        manyInstrumentsStructuralErrorLoading β =
      manyInstrumentsReducedFormErrorData
        (manyInstrumentsStructuralError u1 u2 β) u2 := by
  classical
  ext i j
  cases j with
  | inl u =>
      simp [manyInstrumentsHansenReducedFormErrorData,
        manyInstrumentsReducedFormErrorData, manyInstrumentsStructuralError,
        manyInstrumentsStructuralErrorLoading, Matrix.mul_apply, dotProduct]
      ring
  | inr a =>
      simp [manyInstrumentsHansenReducedFormErrorData,
        manyInstrumentsReducedFormErrorData,
        manyInstrumentsStructuralErrorLoading, Matrix.mul_apply]

private theorem manyInstrumentsStructuralErrorLoading_mulVec_injective
    (β : k → ℝ) :
    Function.Injective (manyInstrumentsStructuralErrorLoading β).mulVec := by
  intro x y hxy
  funext j
  cases j with
  | inl u =>
      simpa [manyInstrumentsStructuralErrorLoading, Matrix.mulVec, dotProduct]
        using congrFun hxy (Sum.inl u)
  | inr a =>
      have h0 := congrFun hxy (Sum.inl ())
      have ha := congrFun hxy (Sum.inr a)
      simp [manyInstrumentsStructuralErrorLoading, Matrix.mulVec, dotProduct] at h0 ha
      linear_combination ha + β a * h0

/-- Positive definiteness of Hansen's primitive covariance is preserved by
the invertible loading into the internal `[e,u₂]` coordinates. -/
theorem manyInstrumentsStructuralErrorCovariance_posDef
    (β : k → ℝ) {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hSigma : Sigma.PosDef) :
    (manyInstrumentsStructuralErrorCovariance β Sigma).PosDef := by
  simpa [manyInstrumentsStructuralErrorCovariance, Matrix.conjTranspose]
    using hSigma.conjTranspose_mul_mul_same
      (manyInstrumentsStructuralErrorLoading_mulVec_injective β)

/-- Loading from the structural-error row `[e,u₂]` to the reduced-form error
row `[e + u₂'β,u₂]` of the joint data `[Y,X]`.

This distinction matters for the LIML pencil: the covariance in the raw model
is indexed by `[e,u₂]`, whereas the finite-sample pencil is formed from
`[Y,X]`. -/
noncomputable def manyInstrumentsReducedFormErrorLoading
    (β : k → ℝ) : Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  fun i j => match i, j with
    | Sum.inl _, Sum.inl _ => 1
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr a, Sum.inl _ => β a
    | Sum.inr a, Sum.inr b => if a = b then 1 else 0

/-- Covariance of the reduced-form error row `[e + u₂'β,u₂]`, obtained from
the raw structural-error covariance `Cov[e,u₂]` by congruence. -/
noncomputable def manyInstrumentsJointReducedFormCovariance
    (β : k → ℝ) (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) :
    Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  (manyInstrumentsReducedFormErrorLoading β)ᵀ * Sigma *
    manyInstrumentsReducedFormErrorLoading β

private theorem manyInstrumentsReducedFormErrorLoading_mulVec_injective
    (β : k → ℝ) :
    Function.Injective (manyInstrumentsReducedFormErrorLoading β).mulVec := by
  intro x y hxy
  funext j
  cases j with
  | inl u =>
      simpa [manyInstrumentsReducedFormErrorLoading, Matrix.mulVec, dotProduct]
        using congrFun hxy (Sum.inl u)
  | inr a =>
      have h0 := congrFun hxy (Sum.inl ())
      have ha := congrFun hxy (Sum.inr a)
      simp [manyInstrumentsReducedFormErrorLoading, Matrix.mulVec, dotProduct] at h0 ha
      calc
        x (Sum.inr a) =
            (β a * x (Sum.inl ()) + x (Sum.inr a)) - β a * x (Sum.inl ()) := by
          ring
        _ = (β a * y (Sum.inl ()) + y (Sum.inr a)) - β a * y (Sum.inl ()) := by
          rw [ha, h0]
        _ = y (Sum.inr a) := by ring

/-- Positive definiteness of the raw structural-error covariance is preserved
by the invertible loading into the joint `[Y,X]` reduced form. -/
theorem manyInstrumentsJointReducedFormCovariance_posDef
    (β : k → ℝ) {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hSigma : Sigma.PosDef) :
    (manyInstrumentsJointReducedFormCovariance β Sigma).PosDef := by
  simpa [manyInstrumentsJointReducedFormCovariance, Matrix.conjTranspose]
    using hSigma.conjTranspose_mul_mul_same
      (manyInstrumentsReducedFormErrorLoading_mulVec_injective β)

@[simp]
theorem manyInstrumentsStructuralErrorLoading_mul_reducedFormErrorLoading
    (β : k → ℝ) :
    manyInstrumentsStructuralErrorLoading β *
        manyInstrumentsReducedFormErrorLoading β = 1 := by
  classical
  ext i j
  cases i <;> cases j <;>
    simp [manyInstrumentsStructuralErrorLoading,
      manyInstrumentsReducedFormErrorLoading, Matrix.mul_apply,
      Matrix.one_apply, eq_comm]

/-- Transforming Hansen's covariance from `[u₁,u₂]` to `[e,u₂]` and then
back to the joint reduced-form coordinates recovers exactly the covariance
`Σ` printed in (12.74). -/
@[simp]
theorem manyInstrumentsJointReducedFormCovariance_structuralErrorCovariance
    (β : k → ℝ) (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) :
    manyInstrumentsJointReducedFormCovariance β
        (manyInstrumentsStructuralErrorCovariance β Sigma) = Sigma := by
  rw [manyInstrumentsJointReducedFormCovariance,
    manyInstrumentsStructuralErrorCovariance]
  calc
    (manyInstrumentsReducedFormErrorLoading β)ᵀ *
          ((manyInstrumentsStructuralErrorLoading β)ᵀ * Sigma *
            manyInstrumentsStructuralErrorLoading β) *
          manyInstrumentsReducedFormErrorLoading β =
        (manyInstrumentsStructuralErrorLoading β *
          manyInstrumentsReducedFormErrorLoading β)ᵀ * Sigma *
          (manyInstrumentsStructuralErrorLoading β *
            manyInstrumentsReducedFormErrorLoading β) := by
      rw [Matrix.transpose_mul]
      noncomm_ring
    _ = Sigma := by simp

/-- The `u₂u₂'` block of Hansen's full reduced-form error covariance. -/
def manyInstrumentsSigma22
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) : Matrix k k ℝ :=
  fun a b => Sigma (Sum.inr a) (Sum.inr b)

/-- The `u₂e` block of Hansen's full reduced-form error covariance. -/
def manyInstrumentsSigma2e
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) : k → ℝ :=
  fun a => Sigma (Sum.inr a) (Sum.inl ())

/-- Hansen's covariance `Σ₂e = Σ₂₁ - Σ₂₂β`, where `Σ` is the primitive
covariance of `[u₁,u₂]` in (12.74) and `e = u₁ - β'u₂`. -/
noncomputable def manyInstrumentsHansenSigma2e
    (β : k → ℝ) (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) : k → ℝ :=
  manyInstrumentsSigma2e Sigma - manyInstrumentsSigma22 Sigma *ᵥ β

@[simp]
theorem manyInstrumentsSigma22_structuralErrorCovariance
    (β : k → ℝ) (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) :
    manyInstrumentsSigma22
        (manyInstrumentsStructuralErrorCovariance β Sigma) =
      manyInstrumentsSigma22 Sigma := by
  classical
  ext a b
  simp [manyInstrumentsSigma22, manyInstrumentsStructuralErrorCovariance,
    manyInstrumentsStructuralErrorLoading, Matrix.mul_apply]

@[simp]
theorem manyInstrumentsSigma2e_structuralErrorCovariance
    (β : k → ℝ) (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) :
    manyInstrumentsSigma2e
        (manyInstrumentsStructuralErrorCovariance β Sigma) =
      manyInstrumentsHansenSigma2e β Sigma := by
  classical
  ext a
  simp [manyInstrumentsSigma2e, manyInstrumentsHansenSigma2e,
    manyInstrumentsSigma22, manyInstrumentsStructuralErrorCovariance,
    manyInstrumentsStructuralErrorLoading, Matrix.mul_apply, Matrix.mulVec,
    dotProduct]
  ring

/-- Normalized full reduced-error projected moment `n⁻¹u'P_Zu`.

Unlike `sampleGram (P_Z u)`, this is Hansen's quadratic form directly and
does not hide symmetry/idempotence behind a transformed-row representation. -/
noncomputable def manyInstrumentsProjectedFullErrorMoment
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (e : n → ℝ) (u2 : Matrix n k ℝ) :
    Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  let U := manyInstrumentsReducedFormErrorData e u2
  (Fintype.card n : ℝ)⁻¹ • (Uᵀ * instrumentProjectionStar Z * U)

/-- Centered projected reduced-error moment from Hansen's conditional
homoskedastic calculation. -/
noncomputable def manyInstrumentsProjectedFullErrorCentered
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (e : n → ℝ) (u2 : Matrix n k ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) :
    Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  manyInstrumentsProjectedFullErrorMoment Z e u2 -
    manyInstrumentProjectionTraceRatio Z • Sigma

/-- Hansen's normalized finite-sample LIML pencil
`(n⁻¹[Y X]'P_Z[Y X], n⁻¹[Y X]'M_Z[Y X])`. -/
noncomputable def manyInstrumentsLIMLNormalizedSamplePencil
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Y : (m : ℕ) → Ω → Fin m → ℝ)
    (m : ℕ) (ω : Ω) :
    Matrix (Sum Unit k) (Sum Unit k) ℝ ×
      Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  ((m : ℝ)⁻¹ • manyInstrumentsLIMLSampleRayleighNumerator
      (Z m ω) (X m ω) (Y m ω),
    (m : ℝ)⁻¹ • manyInstrumentsLIMLSampleRayleighDenominator
      (Z m ω) (X m ω) (Y m ω))

/-- Limiting numerator of the many-instrument LIML pencil:
`B'HB + αΣ`. -/
noncomputable def manyInstrumentsLIMLLimitNumerator
    (β : k → ℝ) (H : Matrix k k ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) (alpha : ℝ) :
    Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  (manyInstrumentsStructuralLoading β)ᵀ * H *
      manyInstrumentsStructuralLoading β +
        alpha • manyInstrumentsJointReducedFormCovariance β Sigma

/-- Limiting denominator of the many-instrument LIML pencil: `(1-α)Σ`. -/
noncomputable def manyInstrumentsLIMLLimitDenominator
    (β : k → ℝ) (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) (alpha : ℝ) :
    Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  (1 - alpha) • manyInstrumentsJointReducedFormCovariance β Sigma

omit [Fintype k] [DecidableEq k] in
@[simp]
theorem manyInstrumentsStructuralResidualDirection_inl
    (β : k → ℝ) (u : Unit) :
    manyInstrumentsStructuralResidualDirection β (Sum.inl u) = 1 := rfl

omit [Fintype k] [DecidableEq k] in
@[simp]
theorem manyInstrumentsStructuralResidualDirection_inr
    (β : k → ℝ) (j : k) :
    manyInstrumentsStructuralResidualDirection β (Sum.inr j) = -β j := rfl

/-- The structural-residual direction annihilates the signal loading. -/
theorem manyInstrumentsStructuralLoading_mulVec_residualDirection
    (β : k → ℝ) :
    manyInstrumentsStructuralLoading β *ᵥ
        manyInstrumentsStructuralResidualDirection β = 0 := by
  ext i
  simp [manyInstrumentsStructuralLoading,
    manyInstrumentsStructuralResidualDirection, Matrix.mulVec, dotProduct]

omit [Fintype k] [DecidableEq k] in
/-- The structural-residual direction is nonzero. -/
theorem manyInstrumentsStructuralResidualDirection_ne_zero
    (β : k → ℝ) : manyInstrumentsStructuralResidualDirection β ≠ 0 := by
  intro h
  have hh := congrFun h (Sum.inl ())
  simp at hh

private theorem manyInstruments_signal_quadratic_eq
    (H : Matrix k k ℝ) (β : k → ℝ) (g : Sum Unit k → ℝ) :
    g ⬝ᵥ (((manyInstrumentsStructuralLoading β)ᵀ * H *
          manyInstrumentsStructuralLoading β) *ᵥ g) =
      (manyInstrumentsStructuralLoading β *ᵥ g) ⬝ᵥ
        (H *ᵥ (manyInstrumentsStructuralLoading β *ᵥ g)) := by
  calc
    g ⬝ᵥ (((manyInstrumentsStructuralLoading β)ᵀ * H *
          manyInstrumentsStructuralLoading β) *ᵥ g) =
        g ⬝ᵥ (((manyInstrumentsStructuralLoading β)ᵀ *
          (H * manyInstrumentsStructuralLoading β)) *ᵥ g) := by
      rw [Matrix.mul_assoc]
    _ = g ⬝ᵥ ((manyInstrumentsStructuralLoading β)ᵀ *ᵥ
          (H *ᵥ (manyInstrumentsStructuralLoading β *ᵥ g))) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = (manyInstrumentsStructuralLoading β *ᵥ g) ⬝ᵥ
        (H *ᵥ (manyInstrumentsStructuralLoading β *ᵥ g)) := by
      conv_lhs =>
        rw [Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose]
        simp
      rw [Matrix.mulVec_mulVec]

private theorem manyInstruments_limit_numerator_quadratic
    (β : k → ℝ) (H : Matrix k k ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) (alpha : ℝ)
    (g : Sum Unit k → ℝ) :
    g ⬝ᵥ (manyInstrumentsLIMLLimitNumerator β H Sigma alpha *ᵥ g) =
      g ⬝ᵥ (((manyInstrumentsStructuralLoading β)ᵀ * H *
        manyInstrumentsStructuralLoading β) *ᵥ g) +
        alpha * (g ⬝ᵥ
          (manyInstrumentsJointReducedFormCovariance β Sigma *ᵥ g)) := by
  rw [manyInstrumentsLIMLLimitNumerator, Matrix.add_mulVec, dotProduct_add,
    Matrix.smul_mulVec, dotProduct_smul]
  rfl

private theorem manyInstruments_limit_denominator_quadratic
    (β : k → ℝ) (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) (alpha : ℝ)
    (g : Sum Unit k → ℝ) :
    g ⬝ᵥ (manyInstrumentsLIMLLimitDenominator β Sigma alpha *ᵥ g) =
      (1 - alpha) * (g ⬝ᵥ
        (manyInstrumentsJointReducedFormCovariance β Sigma *ᵥ g)) := by
  rw [manyInstrumentsLIMLLimitDenominator, Matrix.smul_mulVec,
    dotProduct_smul]
  rfl

/-- The positive-denominator Rayleigh minimum of the limiting
many-instrument pencil is `α/(1-α)`.

The witness is `[1;-β]`; positive definiteness of `Σ` makes it admissible.
The lower bound is the nonnegative signal quadratic form. -/
theorem manyInstrumentsLIMLLimit_rayleighMinimizer
    (β : k → ℝ) (H : Matrix k k ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) (alpha : ℝ)
    (hH : H.PosSemidef) (hSigma : Sigma.PosDef) (halpha : alpha < 1) :
    LIMLRayleighMinimizer
      (manyInstrumentsLIMLLimitNumerator β H Sigma alpha)
      (manyInstrumentsLIMLLimitDenominator β Sigma alpha)
      (alpha / (1 - alpha)) := by
  have hc : 0 < 1 - alpha := by linarith
  have hc0 : 1 - alpha ≠ 0 := hc.ne'
  have hg0 : manyInstrumentsStructuralResidualDirection β ≠ 0 :=
    manyInstrumentsStructuralResidualDirection_ne_zero β
  have hJoint : (manyInstrumentsJointReducedFormCovariance β Sigma).PosDef :=
    manyInstrumentsJointReducedFormCovariance_posDef β hSigma
  have hq0 : 0 < manyInstrumentsStructuralResidualDirection β ⬝ᵥ
      (manyInstrumentsJointReducedFormCovariance β Sigma *ᵥ
        manyInstrumentsStructuralResidualDirection β) :=
    hJoint.dotProduct_mulVec_pos hg0
  constructor
  · refine ⟨manyInstrumentsStructuralResidualDirection β, ?_, ?_⟩
    · rw [limlRayleighAdmissible,
        manyInstruments_limit_denominator_quadratic]
      positivity
    · rw [limlRayleighQuotient,
        manyInstruments_limit_numerator_quadratic,
        manyInstruments_limit_denominator_quadratic,
        manyInstruments_signal_quadratic_eq,
        manyInstrumentsStructuralLoading_mulVec_residualDirection]
      simp
      field_simp [hc0, hq0.ne']
  · intro g hg
    have hden : 0 < (1 - alpha) * (g ⬝ᵥ
        (manyInstrumentsJointReducedFormCovariance β Sigma *ᵥ g)) := by
      rw [limlRayleighAdmissible,
        manyInstruments_limit_denominator_quadratic] at hg
      exact hg
    have hsignal : 0 ≤ g ⬝ᵥ
        (((manyInstrumentsStructuralLoading β)ᵀ * H *
          manyInstrumentsStructuralLoading β) *ᵥ g) := by
      rw [manyInstruments_signal_quadratic_eq]
      exact hH.dotProduct_mulVec_nonneg _
    rw [limlRayleighQuotient,
      manyInstruments_limit_numerator_quadratic,
      manyInstruments_limit_denominator_quadratic]
    apply (le_div_iff₀ hden).2
    field_simp [hc0]
    nlinarith

/-- Chapter 11 rank-one generalized-pencil lower-bound certificate for the
same limiting root. -/
theorem manyInstrumentsLIMLLimit_generalizedEigenProductLowerBound
    (β : k → ℝ) (H : Matrix k k ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) (alpha : ℝ)
    (hH : H.PosSemidef) (halpha : alpha < 1) :
    generalizedEigenDetProductLowerBound
      (manyInstrumentsLIMLLimitNumerator β H Sigma alpha)
      (manyInstrumentsLIMLLimitDenominator β Sigma alpha)
      (fun _ : Unit => alpha / (1 - alpha)) := by
  apply generalizedEigenDetProductLowerBound_rankOne_of_rayleigh_bound
  intro g hnorm
  have hc : 0 < 1 - alpha := by linarith
  have hc0 : 1 - alpha ≠ 0 := hc.ne'
  have hsignal : 0 ≤ g ⬝ᵥ
      (((manyInstrumentsStructuralLoading β)ᵀ * H *
        manyInstrumentsStructuralLoading β) *ᵥ g) := by
    rw [manyInstruments_signal_quadratic_eq]
    exact hH.dotProduct_mulVec_nonneg _
  rw [manyInstruments_limit_numerator_quadratic]
  rw [manyInstruments_limit_denominator_quadratic] at hnorm
  have hq : g ⬝ᵥ
      (manyInstrumentsJointReducedFormCovariance β Sigma *ᵥ g) =
        (1 - alpha)⁻¹ := by
    field_simp [hc0]
    nlinarith
  rw [hq]
  field_simp [hc0]
  nlinarith

namespace LIMLRayleighMinimizer

omit [Fintype k] [DecidableEq k] in
/-- Two minimum-value certificates for the same positive-denominator
Rayleigh problem have the same scalar value. -/
theorem value_unique
    {d : Type*} [Fintype d]
    {A B : Matrix d d ℝ} {x y : ℝ}
    (hx : LIMLRayleighMinimizer A B x)
    (hy : LIMLRayleighMinimizer A B y) : x = y := by
  rcases hx.value with ⟨gx, hgx, hvx⟩
  rcases hy.value with ⟨gy, hgy, hvy⟩
  apply le_antisymm
  · simpa [hvy] using hx.lower_bound gy hgy
  · simpa [hvx] using hy.lower_bound gx hgx

end LIMLRayleighMinimizer

omit [Fintype k] [DecidableEq k] in
noncomputable local instance manyInstrumentsAnyMatrixMeasurableSpace
    {r c : Type*} [Fintype r] [Fintype c] :
    MeasurableSpace (Matrix r c ℝ) :=
  matrixBorelMeasurableSpace r c

omit [Fintype k] [DecidableEq k] in
local instance manyInstrumentsAnyMatrixBorelSpace
    {r c : Type*} [Fintype r] [Fintype c] :
    BorelSpace (Matrix r c ℝ) :=
  matrixBorelSpace r c

private noncomputable def manyInstrumentsStructuralErrorMap
    (β : k → ℝ) :
    (Sum Unit k → ℝ) →L[ℝ] (Sum Unit k → ℝ) :=
  (Matrix.toLin' (manyInstrumentsStructuralErrorLoading β)ᵀ).toContinuousLinearMap

@[simp] private theorem manyInstrumentsStructuralErrorMap_apply
    {n : Type*} [Fintype n] (u1 : n → ℝ) (u2 : Matrix n k ℝ)
    (β : k → ℝ) (i : n) :
    manyInstrumentsStructuralErrorMap β
        (manyInstrumentsHansenReducedFormErrorData u1 u2 i) =
      manyInstrumentsReducedFormErrorData
        (manyInstrumentsStructuralError u1 u2 β) u2 i := by
  classical
  ext j
  cases j with
  | inl u =>
      simp [manyInstrumentsStructuralErrorMap, Matrix.toLin'_apply,
        manyInstrumentsHansenReducedFormErrorData,
        manyInstrumentsReducedFormErrorData, manyInstrumentsStructuralError,
        manyInstrumentsStructuralErrorLoading, Matrix.mulVec, dotProduct,
        mul_comm]
      ring
  | inr a =>
      simp [manyInstrumentsStructuralErrorMap, Matrix.toLin'_apply,
        manyInstrumentsHansenReducedFormErrorData,
        manyInstrumentsReducedFormErrorData,
        manyInstrumentsStructuralErrorLoading, Matrix.mulVec, dotProduct]

private noncomputable def manyInstrumentsMatrixLeftRightMap
    {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a b ℝ) (B : Matrix c d ℝ) :
    Matrix b c ℝ →L[ℝ] Matrix a d ℝ :=
  ({ toFun := fun M => A * M * B
     map_add' := by
       intro M N
       ext i j
       simp [Matrix.mul_apply, Finset.sum_add_distrib, add_mul, mul_add]
     map_smul' := by
       intro r M
       ext i j
       simp [Matrix.mul_apply, Finset.mul_sum, mul_comm, mul_left_comm] } :
      Matrix b c ℝ →ₗ[ℝ] Matrix a d ℝ).toContinuousLinearMap

@[simp] private theorem manyInstrumentsMatrixLeftRightMap_apply
    {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    (A : Matrix a b ℝ) (B : Matrix c d ℝ) (M : Matrix b c ℝ) :
    manyInstrumentsMatrixLeftRightMap A B M = A * M * B :=
  rfl

private theorem condExpOn_manyInstruments_matrix_mul_left_right
    {ζ a b c d : Type*} [MeasurableSpace ζ]
    [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    {μ : Measure Ω} {Z : Ω → ζ} (A : Matrix a b ℝ) (B : Matrix c d ℝ)
    {F : Ω → Matrix b c ℝ} {M : Matrix b c ℝ}
    (hF : Integrable F μ)
    (hcond : condExpOn μ F Z =ᵐ[μ] fun _ => M) :
    condExpOn μ (fun ω => A * F ω * B) Z =ᵐ[μ] fun _ => A * M * B := by
  let T : Matrix b c ℝ →L[ℝ] Matrix a d ℝ :=
    manyInstrumentsMatrixLeftRightMap A B
  have hcomm :
      T ∘ condExpOn μ F Z =ᵐ[μ] condExpOn μ (T ∘ F) Z := by
    simpa [condExpOn] using
      (T.comp_condExp_comm (μ := μ) (m := conditioningSpace Z) hF)
  have hconst :
      T ∘ condExpOn μ F Z =ᵐ[μ] fun _ => A * M * B := by
    filter_upwards [hcond] with ω hω
    change A * condExpOn μ F Z ω * B = A * M * B
    exact congrArg (fun N => A * N * B) hω
  have htarget : condExpOn μ (T ∘ F) Z =ᵐ[μ] fun _ => A * M * B :=
    hcomm.symm.trans hconst
  simpa [T, Function.comp_def] using htarget

private theorem manyInstruments_vecMulVec_structuralErrorMap
    (β : k → ℝ) (x : Sum Unit k → ℝ) :
    Matrix.vecMulVec (manyInstrumentsStructuralErrorMap β x)
        (manyInstrumentsStructuralErrorMap β x) =
      (manyInstrumentsStructuralErrorLoading β)ᵀ *
        Matrix.vecMulVec x x * manyInstrumentsStructuralErrorLoading β := by
  change Matrix.vecMulVec
      ((manyInstrumentsStructuralErrorLoading β)ᵀ *ᵥ x)
      ((manyInstrumentsStructuralErrorLoading β)ᵀ *ᵥ x) = _
  calc
    Matrix.vecMulVec
        ((manyInstrumentsStructuralErrorLoading β)ᵀ *ᵥ x)
        ((manyInstrumentsStructuralErrorLoading β)ᵀ *ᵥ x) =
      (manyInstrumentsStructuralErrorLoading β)ᵀ *
        Matrix.vecMulVec x
          ((manyInstrumentsStructuralErrorLoading β)ᵀ *ᵥ x) := by
            rw [Matrix.mul_vecMulVec]
    _ = (manyInstrumentsStructuralErrorLoading β)ᵀ *
        (Matrix.vecMulVec x x *
          ((manyInstrumentsStructuralErrorLoading β)ᵀ)ᵀ) := by
            rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
    _ = (manyInstrumentsStructuralErrorLoading β)ᵀ *
        Matrix.vecMulVec x x * manyInstrumentsStructuralErrorLoading β := by
            simp [Matrix.mul_assoc]

/-- Hansen-facing conditional error model for (12.74)--(12.75).

Its primitive row is exactly `[u₁,u₂]`, its conditional covariance is exactly
Hansen's `Σ`, and the structural error is derived later as `e = u₁ - β'u₂`.
No transformed conditional moment is included as an assumption. -/
structure ManyInstrumentsHansenConditionalHomoskedasticFourthMomentModel
    [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (u1 : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) (B : ℝ) : Prop where
  instrument_measurable : ∀ m, Measurable (Z m)
  error_row_memLp_four : ∀ m (i : Fin m), MemLp
    (fun ω => manyInstrumentsHansenReducedFormErrorData (u1 m ω) (u2 m ω) i) 4 μ
  rows_conditionally_independent : ∀ m,
    iCondIndepFun (conditioningSpace (Z m))
      (conditioningSpace_le (instrument_measurable m))
      (fun i ω => manyInstrumentsHansenReducedFormErrorData (u1 m ω) (u2 m ω) i) μ
  conditional_mean_zero : ∀ m (i : Fin m),
    condExpOn μ
      (fun ω => manyInstrumentsHansenReducedFormErrorData (u1 m ω) (u2 m ω) i)
      (Z m) =ᵐ[μ] 0
  conditional_second_moment : ∀ m (i : Fin m),
    condExpOn μ
      (fun ω => Matrix.vecMulVec
        (manyInstrumentsHansenReducedFormErrorData (u1 m ω) (u2 m ω) i)
        (manyInstrumentsHansenReducedFormErrorData (u1 m ω) (u2 m ω) i))
      (Z m) =ᵐ[μ] fun _ => Sigma
  fourth_bound_nonneg : 0 ≤ B
  conditional_fourth_bound : ∀ m (i : Fin m),
    ∀ᵐ ω ∂μ, condExpOn μ
      (fun ω' => ‖manyInstrumentsHansenReducedFormErrorData
        (u1 m ω') (u2 m ω') i‖ ^ 4) (Z m) ω ≤ B

/-- Fourth-moment bound after the fixed loading from Hansen's `[u₁,u₂]` row
to the internal `[e,u₂]` row. -/
noncomputable def manyInstrumentsStructuralFourthMomentBound
    (β : k → ℝ) (B : ℝ) : ℝ :=
  ‖manyInstrumentsStructuralErrorMap β‖ ^ 4 * B

/-- Internal conditional-homoskedastic, conditionally independent,
bounded-fourth-moment model for the transformed row `[e,u₂]`.

No projected quadratic-form convergence and no LIML eigenvalue convergence is
a field.  The Hansen-facing package above uses the primitive row `[u₁,u₂]` and
derives this proof-engine model through the structural-error loading. -/
structure ManyInstrumentsConditionalHomoskedasticFourthMomentModel
    [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) (B : ℝ) : Prop where
  instrument_measurable : ∀ m, Measurable (Z m)
  error_row_memLp_four : ∀ m (i : Fin m), MemLp
    (fun ω => manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω) i) 4 μ
  rows_conditionally_independent : ∀ m,
    iCondIndepFun (conditioningSpace (Z m))
      (conditioningSpace_le (instrument_measurable m))
      (fun i ω => manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω) i) μ
  conditional_mean_zero : ∀ m (i : Fin m),
    condExpOn μ
      (fun ω => manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω) i)
      (Z m) =ᵐ[μ] 0
  conditional_second_moment : ∀ m (i : Fin m),
    condExpOn μ
      (fun ω => Matrix.vecMulVec
        (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω) i)
        (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω) i))
      (Z m) =ᵐ[μ] fun _ => Sigma
  fourth_bound_nonneg : 0 ≤ B
  conditional_fourth_bound : ∀ m (i : Fin m),
    ∀ᵐ ω ∂μ, condExpOn μ
      (fun ω' => ‖manyInstrumentsReducedFormErrorData
        (e m ω') (u2 m ω') i‖ ^ 4) (Z m) ω ≤ B

omit [∀ m, DecidableEq (ι m)] in
/-- Hansen's primitive conditional model implies the internal `[e,u₂]` model
by the fixed loading `e = u₁ - β'u₂`.  The covariance and fourth-moment bound
are conclusions of the transformation, not additional assumptions. -/
theorem ManyInstrumentsHansenConditionalHomoskedasticFourthMomentModel.toStructuralErrorModel
    [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {u1 : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ} {B : ℝ}
    (h : ManyInstrumentsHansenConditionalHomoskedasticFourthMomentModel
      (ι := ι) μ Z u1 u2 Sigma B)
    (β : k → ℝ) :
    ManyInstrumentsConditionalHomoskedasticFourthMomentModel
      (ι := ι) μ Z
        (fun m ω => manyInstrumentsStructuralError (u1 m ω) (u2 m ω) β)
        u2 (manyInstrumentsStructuralErrorCovariance β Sigma)
        (manyInstrumentsStructuralFourthMomentBound β B) where
  instrument_measurable := h.instrument_measurable
  error_row_memLp_four := by
    intro m i
    let T := manyInstrumentsStructuralErrorMap β
    have hmap := (h.error_row_memLp_four m i).continuousLinearMap_comp T
    simpa [T, Function.comp_def] using hmap
  rows_conditionally_independent := by
    intro m
    let T := manyInstrumentsStructuralErrorMap β
    have hcomp := (h.rows_conditionally_independent m).comp
      (fun _ => T) (fun _ => T.continuous.measurable)
    simpa [T, Function.comp_def] using hcomp
  conditional_mean_zero := by
    intro m i
    let U : Ω → Sum Unit k → ℝ := fun ω =>
      manyInstrumentsHansenReducedFormErrorData (u1 m ω) (u2 m ω) i
    let T := manyInstrumentsStructuralErrorMap β
    have hUint : Integrable U μ :=
      (h.error_row_memLp_four m i).integrable (by norm_num)
    have hcomm :
        T ∘ condExpOn μ U (Z m) =ᵐ[μ] condExpOn μ (T ∘ U) (Z m) := by
      simpa [condExpOn] using
        (T.comp_condExp_comm (μ := μ) (m := conditioningSpace (Z m)) hUint)
    have hzero : T ∘ condExpOn μ U (Z m) =ᵐ[μ] 0 := by
      filter_upwards [h.conditional_mean_zero m i] with ω hω
      change T (condExpOn μ U (Z m) ω) = 0
      rw [show condExpOn μ U (Z m) ω = 0 by simpa [U] using hω]
      exact map_zero T
    have htarget := hcomm.symm.trans hzero
    simpa [T, U, Function.comp_def] using htarget
  conditional_second_moment := by
    intro m i
    let U : Ω → Sum Unit k → ℝ := fun ω =>
      manyInstrumentsHansenReducedFormErrorData (u1 m ω) (u2 m ω) i
    have hU4 (c : Sum Unit k) : MemLp (fun ω => U ω c) 4 μ := by
      simpa [U] using (h.error_row_memLp_four m i).eval c
    have hOuter : Integrable (fun ω => Matrix.vecMulVec (U ω) (U ω)) μ :=
      vecMulVec_integrable_of_coordinate_memLp_four hU4
    have htransform := condExpOn_manyInstruments_matrix_mul_left_right
      (μ := μ) (Z := Z m)
      (manyInstrumentsStructuralErrorLoading β)ᵀ
      (manyInstrumentsStructuralErrorLoading β) hOuter
      (h.conditional_second_moment m i)
    have hpoint :
        (fun ω => Matrix.vecMulVec
          (manyInstrumentsStructuralErrorMap β (U ω))
          (manyInstrumentsStructuralErrorMap β (U ω))) =
        fun ω => (manyInstrumentsStructuralErrorLoading β)ᵀ *
          Matrix.vecMulVec (U ω) (U ω) *
            manyInstrumentsStructuralErrorLoading β := by
      funext ω
      exact manyInstruments_vecMulVec_structuralErrorMap β (U ω)
    rw [← hpoint] at htransform
    simpa [U, manyInstrumentsStructuralErrorCovariance] using htransform
  fourth_bound_nonneg := by
    exact mul_nonneg (pow_nonneg (norm_nonneg _) _) h.fourth_bound_nonneg
  conditional_fourth_bound := by
    intro m i
    let U : Ω → Sum Unit k → ℝ := fun ω =>
      manyInstrumentsHansenReducedFormErrorData (u1 m ω) (u2 m ω) i
    let T := manyInstrumentsStructuralErrorMap β
    let c : ℝ := ‖T‖ ^ 4
    have hU4 : MemLp U 4 μ := by
      simpa [U] using h.error_row_memLp_four m i
    have hTU4 : MemLp (T ∘ U) 4 μ := hU4.continuousLinearMap_comp T
    have hUInt : Integrable (fun ω => ‖U ω‖ ^ 4) μ :=
      hU4.integrable_norm_pow'
    have hTUInt : Integrable (fun ω => ‖T (U ω)‖ ^ 4) μ := by
      simpa [Function.comp_def] using hTU4.integrable_norm_pow'
    have hscaledInt : Integrable (fun ω => c * ‖U ω‖ ^ 4) μ :=
      hUInt.const_mul c
    have hpoint : ∀ ω, ‖T (U ω)‖ ^ 4 ≤ c * ‖U ω‖ ^ 4 := by
      intro ω
      calc
        ‖T (U ω)‖ ^ 4 ≤ (‖T‖ * ‖U ω‖) ^ 4 := by
          gcongr
          exact T.le_opNorm (U ω)
        _ = c * ‖U ω‖ ^ 4 := by simp [c, mul_pow]
    have hmono :
        condExpOn μ (fun ω => ‖T (U ω)‖ ^ 4) (Z m) ≤ᵐ[μ]
          condExpOn μ (fun ω => c * ‖U ω‖ ^ 4) (Z m) := by
      simpa [condExpOn] using condExp_mono hTUInt hscaledInt
        (ae_of_all μ hpoint)
    have hscale :
        condExpOn μ (fun ω => c * ‖U ω‖ ^ 4) (Z m) =ᵐ[μ]
          fun ω => c * condExpOn μ (fun ω => ‖U ω‖ ^ 4) (Z m) ω := by
      simpa [condExpOn, Pi.smul_apply, smul_eq_mul] using
        (condExp_smul (μ := μ) (m := conditioningSpace (Z m))
          c (fun ω => ‖U ω‖ ^ 4))
    filter_upwards [hmono, hscale, h.conditional_fourth_bound m i] with ω hle hscaleω hbound
    calc
      condExpOn μ
          (fun ω' => ‖manyInstrumentsReducedFormErrorData
            (manyInstrumentsStructuralError (u1 m ω') (u2 m ω') β)
            (u2 m ω') i‖ ^ 4) (Z m) ω =
          condExpOn μ (fun ω' => ‖T (U ω')‖ ^ 4) (Z m) ω := by
            congr 2
            funext ω'
            rw [show T (U ω') = manyInstrumentsReducedFormErrorData
              (manyInstrumentsStructuralError (u1 m ω') (u2 m ω') β)
              (u2 m ω') i by simp [T, U]]
      _ ≤ condExpOn μ (fun ω' => c * ‖U ω'‖ ^ 4) (Z m) ω := hle
      _ = c * condExpOn μ (fun ω' => ‖U ω'‖ ^ 4) (Z m) ω := hscaleω
      _ ≤ c * B := mul_le_mul_of_nonneg_left hbound (pow_nonneg (norm_nonneg _) _)
      _ = manyInstrumentsStructuralFourthMomentBound β B := by
        rfl

/-- Internal non-circular raw model package for Hansen Theorem 12.19.

Its error coordinates are the transformed proof coordinates `[e,u₂]`.  The
Hansen-facing package below instead takes primitive errors `[u₁,u₂]`, with `Σ`
exactly as in (12.74), and derives this package through a fixed loading.

In particular it contains neither estimator limits, projected-form WLLNs, nor
an assumed LIML adjustment/eigenvalue gap. -/
structure ManyInstrumentsTheorem1219RawModelConditions
    [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Y : (m : ℕ) → Ω → Fin m → ℝ)
    (Gamma : (m : ℕ) → Matrix (ι m) k ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (β : k → ℝ) (H : Matrix k k ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ)
    (alpha B : ℝ) : Prop where
  reduced_form : ∀ m ω,
    X m ω = manyInstrumentSignal (Z m ω) (Gamma m) + u2 m ω
  structural : ∀ m ω, Y m ω = X m ω *ᵥ β + e m ω
  instrument_ratio : Tendsto
    (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
    atTop (𝓝 alpha)
  alpha_lt_one : alpha < 1
  signal_gram_measurable : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentSignalGram (Z m ω) (Gamma m)) μ
  signal_gram_tendsto : TendstoInMeasure μ
    (fun m ω => manyInstrumentSignalGram (Z m ω) (Gamma m))
    atTop (fun _ => H)
  signal_posDef : H.PosDef
  /-- Corrected LIML nondegeneracy assumption.  Hansen (12.74) identifies the
  covariance but does not explicitly state positive definiteness. -/
  error_covariance_posDef : Sigma.PosDef
  instrument_gram_nonsingular : ∀ m, ∀ᵐ ω ∂μ,
    Nonempty (Invertible ((Z m ω)ᵀ * Z m ω))
  errors : ManyInstrumentsConditionalHomoskedasticFourthMomentModel
    (ι := ι) μ Z e u2 Sigma B

/-- Hansen-facing raw condition package for Theorem 12.19.

The primitive errors are exactly `[u₁,u₂]`; `Σ` is exactly their conditional
covariance in Hansen (12.74); and `e = u₁ - β'u₂` is derived rather than
silently substituted into the covariance assumption.  The package also makes
explicit (12.77), conditional row independence used in Hansen's calculation,
and the instrument-rank condition used to identify `P_Z` with the Star
projection.  It contains no estimator limit, projected-form WLLN, or assumed
LIML eigenvalue limit. -/
structure ManyInstrumentsTheorem1219HansenRawModelConditions
    [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Y : (m : ℕ) → Ω → Fin m → ℝ)
    (Gamma : (m : ℕ) → Matrix (ι m) k ℝ)
    (u1 : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (β : k → ℝ) (H : Matrix k k ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ)
    (alpha B : ℝ) : Prop where
  reduced_form : ∀ m ω,
    X m ω = manyInstrumentSignal (Z m ω) (Gamma m) + u2 m ω
  structural : ∀ m ω, Y m ω = X m ω *ᵥ β +
    manyInstrumentsStructuralError (u1 m ω) (u2 m ω) β
  instrument_ratio : Tendsto
    (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
    atTop (𝓝 alpha)
  alpha_lt_one : alpha < 1
  signal_gram_measurable : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentSignalGram (Z m ω) (Gamma m)) μ
  signal_gram_tendsto : TendstoInMeasure μ
    (fun m ω => manyInstrumentSignalGram (Z m ω) (Gamma m))
    atTop (fun _ => H)
  signal_posDef : H.PosDef
  /-- Corrected LIML nondegeneracy assumption.  Hansen's (12.74) specifies
  `Σ = Var([u₁,u₂] | Z)` but does not explicitly require `Σ.PosDef`. -/
  error_covariance_posDef : Sigma.PosDef
  instrument_gram_nonsingular : ∀ m, ∀ᵐ ω ∂μ,
    Nonempty (Invertible ((Z m ω)ᵀ * Z m ω))
  errors : ManyInstrumentsHansenConditionalHomoskedasticFourthMomentModel
    (ι := ι) μ Z u1 u2 Sigma B

/-- Thin bridge from the literal Hansen `[u₁,u₂]` package to the existing
internal `[e,u₂]` raw endpoint. -/
theorem ManyInstrumentsTheorem1219HansenRawModelConditions.toRawModelConditions
    [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {u1 : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {alpha B : ℝ}
    (h : ManyInstrumentsTheorem1219HansenRawModelConditions
      μ Z X Y Gamma u1 u2 β H Sigma alpha B) :
    ManyInstrumentsTheorem1219RawModelConditions
      μ Z X Y Gamma
        (fun m ω => manyInstrumentsStructuralError (u1 m ω) (u2 m ω) β)
        u2 β H (manyInstrumentsStructuralErrorCovariance β Sigma) alpha
        (manyInstrumentsStructuralFourthMomentBound β B) where
  reduced_form := h.reduced_form
  structural := h.structural
  instrument_ratio := h.instrument_ratio
  alpha_lt_one := h.alpha_lt_one
  signal_gram_measurable := h.signal_gram_measurable
  signal_gram_tendsto := h.signal_gram_tendsto
  signal_posDef := h.signal_posDef
  error_covariance_posDef :=
    manyInstrumentsStructuralErrorCovariance_posDef β h.error_covariance_posDef
  instrument_gram_nonsingular := h.instrument_gram_nonsingular
  errors := h.errors.toStructuralErrorModel β

/-- Honest concentration input for Hansen's projected quadratic form.

The `O(1/n)` entrywise mean-square bounds are the direct consequences of
conditional homoskedasticity, bounded conditional fourth moments, projection
symmetry/idempotence, `tr(P_Z)=ℓ`, and `Σ_j P_ij²=P_ii`.  Unlike the legacy row
packages, this does not assert that a projected quadratic form is an iid row
average. -/
structure ManyInstrumentsProjectionQuadraticMeanSquareConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) (C : ℝ) : Prop where
  bound_nonneg : 0 ≤ C
  centered_meas : ∀ m, AEStronglyMeasurable
    (fun ω => manyInstrumentsProjectedFullErrorCentered
      (Z m ω) (e m ω) (u2 m ω) Sigma) μ
  entry_sq_integrable : ∀ m (a b : Sum Unit k), Integrable
    (fun ω => ‖manyInstrumentsProjectedFullErrorCentered
      (Z m ω) (e m ω) (u2 m ω) Sigma a b‖ ^ (2 : ℝ)) μ
  entry_mean_square_bound : ∀ a b : Sum Unit k, ∀ᶠ m in atTop,
    (∫ ω, ‖manyInstrumentsProjectedFullErrorCentered
      (Z m ω) (e m ω) (u2 m ω) Sigma a b‖ ^ (2 : ℝ) ∂μ) ≤ C / (m : ℝ)

private theorem manyInstruments_tendstoInMeasure_zero_of_integral_sq_le_inv
    {E : ℕ → Ω → ℝ} {C : ℝ}
    (hInt : ∀ m, Integrable (fun ω => ‖E m ω‖ ^ (2 : ℝ)) μ)
    (hbound : ∀ᶠ m in atTop,
      (∫ ω, ‖E m ω‖ ^ (2 : ℝ) ∂μ) ≤ C / (m : ℝ)) :
    TendstoInMeasure μ E atTop (fun _ => 0) := by
  have hupper : Tendsto (fun m : ℕ => C / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop C
  have hnonneg : ∀ᶠ m in atTop,
      (0 : ℝ) ≤ ∫ ω, ‖E m ω‖ ^ (2 : ℝ) ∂μ :=
    Eventually.of_forall fun m => integral_nonneg fun ω =>
      Real.rpow_nonneg (norm_nonneg (E m ω)) _
  have hmoment : Tendsto
      (fun m => ∫ ω, ‖E m ω‖ ^ (2 : ℝ) ∂μ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hupper hnonneg hbound
  have hscaled : Tendsto
      (fun m => (∫ ω, ‖E m ω‖ ^ (2 : ℝ) ∂μ) /
        (fun _ : ℕ => (1 : ℝ)) m ^ (2 : ℝ)) atTop (𝓝 0) := by
    simpa using hmoment
  have hraw := TendstoInMeasure.of_integral_norm_rpow_scaled_tendsto_zero
    (μ := μ) (X := E) (a := fun _ : ℕ => (1 : ℝ)) (p := (2 : ℝ))
    (by norm_num) (Eventually.of_forall fun _ => by norm_num) hInt hscaled
  simpa using hraw

omit [DecidableEq k] in
/-- Conditional-projection `O(1/n)` mean-square bounds imply the centered
matrix WLLN, entrywise and hence jointly in the fixed `(1+k)` dimension. -/
theorem ManyInstrumentsProjectionQuadraticMeanSquareConditions.centered_tendsto_zero
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ} {C : ℝ}
    (h : ManyInstrumentsProjectionQuadraticMeanSquareConditions
      μ Z e u2 Sigma C) :
    TendstoInMeasure μ
      (fun m ω => manyInstrumentsProjectedFullErrorCentered
        (Z m ω) (e m ω) (u2 m ω) Sigma)
      atTop (fun _ => (0 : Matrix (Sum Unit k) (Sum Unit k) ℝ)) := by
  refine tendstoInMeasure_pi (fun a => ?_)
  refine tendstoInMeasure_pi (fun b => ?_)
  exact manyInstruments_tendstoInMeasure_zero_of_integral_sq_le_inv
    (μ := μ) (E := fun m ω => manyInstrumentsProjectedFullErrorCentered
      (Z m ω) (e m ω) (u2 m ω) Sigma a b)
    (h.entry_sq_integrable · a b) (h.entry_mean_square_bound a b)

omit [Fintype k] [DecidableEq k] in
private theorem manyInstrumentsProjectedFullErrorMoment_inr_inr
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (e : n → ℝ) (u2 : Matrix n k ℝ) :
    (manyInstrumentsProjectedFullErrorMoment Z e u2).submatrix Sum.inr Sum.inr =
      manyInstrumentProjectedErrorGram Z u2 := by
  have hdirect : manyInstrumentProjectedErrorGram Z u2 =
      (Fintype.card n : ℝ)⁻¹ •
        (u2ᵀ * instrumentProjectionStar Z * u2) := by
    rw [manyInstrumentProjectedErrorGram, sampleGram, Matrix.transpose_mul,
      instrumentProjectionStar_transpose]
    congr 1
    rw [Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (instrumentProjectionStar Z),
      instrumentProjectionStar_idempotent]
  rw [hdirect]
  ext a b
  simp [manyInstrumentsProjectedFullErrorMoment,
    manyInstrumentsReducedFormErrorData, Matrix.mul_apply]

omit [Fintype k] [DecidableEq k] in
private theorem manyInstrumentsProjectedFullErrorMoment_inr_inl
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (e : n → ℝ) (u2 : Matrix n k ℝ) :
    (fun a => manyInstrumentsProjectedFullErrorMoment Z e u2
      (Sum.inr a) (Sum.inl ())) =
        manyInstrumentProjectedErrorCross Z u2 e := by
  rw [manyInstrumentProjectedErrorCross, sampleCrossMoment,
    Matrix.transpose_mul, instrumentProjectionStar_transpose]
  ext a
  simp [manyInstrumentsProjectedFullErrorMoment,
    manyInstrumentsReducedFormErrorData, Matrix.mul_apply, Matrix.mulVec,
    dotProduct]

omit [Fintype k] [DecidableEq k] in
private theorem ManyInstrumentsProjectionQuadraticMeanSquareConditions.projected_meas
    [Finite k]
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ} {C : ℝ}
    (h : ManyInstrumentsProjectionQuadraticMeanSquareConditions
      μ Z e u2 Sigma C)
    (htrace_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectionTraceRatio (Z m ω)) μ) :
    ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentsProjectedFullErrorMoment
        (Z m ω) (e m ω) (u2 m ω)) μ := by
  classical
  letI := Fintype.ofFinite k
  intro m
  have hideal : AEStronglyMeasurable
      (fun ω => manyInstrumentProjectionTraceRatio (Z m ω) • Sigma) μ := by
    change AEStronglyMeasurable
      (fun ω a b => manyInstrumentProjectionTraceRatio (Z m ω) * Sigma a b) μ
    rw [aestronglyMeasurable_iff_aemeasurable, aemeasurable_pi_iff]
    intro a
    rw [aemeasurable_pi_iff]
    intro b
    exact ((htrace_meas m).mul_const (Sigma a b)).aemeasurable
  refine ((h.centered_meas m).add hideal).congr (ae_of_all μ fun ω => ?_)
  simp [manyInstrumentsProjectedFullErrorCentered]

omit [DecidableEq k] in
/-- Combining the honest projected-form concentration bound with projection
trace convergence gives `n⁻¹u'P_Zu ->p αΣ`. -/
theorem ManyInstrumentsProjectionQuadraticMeanSquareConditions.projected_tendsto
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ} {C alpha : ℝ}
    (h : ManyInstrumentsProjectionQuadraticMeanSquareConditions
      μ Z e u2 Sigma C)
    (htrace_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectionTraceRatio (Z m ω)) μ)
    (htrace : TendstoInMeasure μ
      (fun m ω => manyInstrumentProjectionTraceRatio (Z m ω))
      atTop (fun _ => alpha)) :
    TendstoInMeasure μ
      (fun m ω => manyInstrumentsProjectedFullErrorMoment
        (Z m ω) (e m ω) (u2 m ω))
      atTop (fun _ => alpha • Sigma) := by
  have hideal : TendstoInMeasure μ
      (fun m ω => manyInstrumentProjectionTraceRatio (Z m ω) • Sigma)
      atTop (fun _ => alpha • Sigma) := by
    have hSigma : TendstoInMeasure μ
        (fun _ : ℕ => fun _ : Ω => Sigma) atTop (fun _ => Sigma) := by
      exact tendstoInMeasure_of_tendsto_ae
        (fun _ => aestronglyMeasurable_const)
        (ae_of_all μ fun _ => tendsto_const_nhds)
    exact tendstoInMeasure_smul_matrix htrace_meas
      (fun _ => aestronglyMeasurable_const) htrace hSigma
  exact TendstoInMeasure.of_sub_tendsto_zero_matrix
    (by simpa [manyInstrumentsProjectedFullErrorCentered] using
      h.centered_tendsto_zero) hideal

omit [DecidableEq k] in
/-- The raw model supplies projection-trace convergence and measurability;
therefore the only additional input needed for the full projected-error WLLN
is the honest conditional mean-square concentration bound. -/
theorem ManyInstrumentsTheorem1219RawModelConditions.projected_full_error_tendsto
    [StandardBorelSpace Ω]
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {alpha B C : ℝ}
    (hraw : ManyInstrumentsTheorem1219RawModelConditions
      μ Z X Y Gamma e u2 β H Sigma alpha B)
    (hquad : ManyInstrumentsProjectionQuadraticMeanSquareConditions
      μ Z e u2 Sigma C) :
    TendstoInMeasure μ
      (fun m ω => manyInstrumentsProjectedFullErrorMoment
        (Z m ω) (e m ω) (u2 m ω))
      atTop (fun _ => alpha • Sigma) := by
  apply hquad.projected_tendsto
  · intro m
    exact manyInstrumentProjectionTraceRatio_aestronglyMeasurable_of_ae_nonsingular
      (hraw.instrument_gram_nonsingular m)
  · exact
      manyInstrumentProjectionTraceRatio_tendstoInMeasure_of_eventually_ae_card_ratio_nonsingular
        hraw.instrument_ratio
        (Eventually.of_forall hraw.instrument_gram_nonsingular)

omit [DecidableEq k] in
/-- The `u₂u₂'` principal block of the full projected-error concentration is
the projected-error Gram used in the 2SLS bread. -/
theorem ManyInstrumentsTheorem1219RawModelConditions.projected_error_gram_tendsto
    [StandardBorelSpace Ω]
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {alpha B C : ℝ}
    (hraw : ManyInstrumentsTheorem1219RawModelConditions
      μ Z X Y Gamma e u2 β H Sigma alpha B)
    (hquad : ManyInstrumentsProjectionQuadraticMeanSquareConditions
      μ Z e u2 Sigma C) :
    TendstoInMeasure μ
      (fun m ω => manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω))
      atTop (fun _ => alpha • manyInstrumentsSigma22 Sigma) := by
  have hfull := hraw.projected_full_error_tendsto hquad
  have htrace_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectionTraceRatio (Z m ω)) μ := fun m =>
    manyInstrumentProjectionTraceRatio_aestronglyMeasurable_of_ae_nonsingular
      (hraw.instrument_gram_nonsingular m)
  have hblock := tendstoInMeasure_continuous_comp
    (hquad.projected_meas htrace_meas) hfull
      (continuous_id.matrix_submatrix Sum.inr Sum.inr)
  refine TendstoInMeasure.congr (fun m => ae_of_all μ fun ω => ?_)
    (ae_of_all μ fun _ => ?_) hblock
  · exact manyInstrumentsProjectedFullErrorMoment_inr_inr
      (Z m ω) (e m ω) (u2 m ω)
  · ext a b
    simp [manyInstrumentsSigma22]

omit [DecidableEq k] in
/-- The `u₂e` block of the full projected-error concentration is the projected
error score used in the 2SLS numerator. -/
theorem ManyInstrumentsTheorem1219RawModelConditions.projected_error_cross_tendsto
    [StandardBorelSpace Ω]
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {alpha B C : ℝ}
    (hraw : ManyInstrumentsTheorem1219RawModelConditions
      μ Z X Y Gamma e u2 β H Sigma alpha B)
    (hquad : ManyInstrumentsProjectionQuadraticMeanSquareConditions
      μ Z e u2 Sigma C) :
    TendstoInMeasure μ
      (fun m ω => manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω))
      atTop (fun _ => alpha • manyInstrumentsSigma2e Sigma) := by
  have hfull := hraw.projected_full_error_tendsto hquad
  have htrace_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectionTraceRatio (Z m ω)) μ := fun m =>
    manyInstrumentProjectionTraceRatio_aestronglyMeasurable_of_ae_nonsingular
      (hraw.instrument_gram_nonsingular m)
  have hentry_cont : Continuous
      (fun M : Matrix (Sum Unit k) (Sum Unit k) ℝ =>
        fun a => M (Sum.inr a) (Sum.inl ())) := by
    fun_prop
  have hblock := tendstoInMeasure_continuous_comp
    (hquad.projected_meas htrace_meas) hfull hentry_cont
  refine TendstoInMeasure.congr (fun m => ae_of_all μ fun ω => ?_)
    (ae_of_all μ fun _ => ?_) hblock
  · exact manyInstrumentsProjectedFullErrorMoment_inr_inl
      (Z m ω) (e m ω) (u2 m ω)
  · ext a
    simp [manyInstrumentsSigma2e]

/-- The honest full projected-error concentration bound supplies the two
projected reduced-form error limits needed by the 2SLS assembly.  All signal
terms are transported from the unprojected OLS assembly using `P_Z ZΓ = ZΓ` on
the raw model's a.e. nonsingular branch. -/
theorem ManyInstrumentsTheorem1219RawModelConditions.toTwoSLSMomentAssemblyConditions
    [StandardBorelSpace Ω]
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {alpha B C : ℝ}
    (hraw : ManyInstrumentsTheorem1219RawModelConditions
      μ Z X Y Gamma e u2 β H Sigma alpha B)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H (manyInstrumentsSigma22 Sigma)
        (manyInstrumentsSigma2e Sigma))
    (hquad : ManyInstrumentsProjectionQuadraticMeanSquareConditions
      μ Z e u2 Sigma C) :
    ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H (manyInstrumentsSigma22 Sigma)
        (manyInstrumentsSigma2e Sigma) alpha := by
  let hnonsing : ∀ᶠ m in atTop, ∀ᵐ ω ∂μ,
      Nonempty (Invertible ((Z m ω)ᵀ * Z m ω)) :=
    Eventually.of_forall hraw.instrument_gram_nonsingular
  have htrace_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectionTraceRatio (Z m ω)) μ := fun m =>
    manyInstrumentProjectionTraceRatio_aestronglyMeasurable_of_ae_nonsingular
      (hraw.instrument_gram_nonsingular m)
  have hfull_meas := hquad.projected_meas htrace_meas
  have hsignal_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m)) μ := by
    intro m
    refine (hOLS.signal_gram_meas m).congr ?_
    filter_upwards [hraw.instrument_gram_nonsingular m] with ω hω
    rcases hω with ⟨inst⟩
    letI : Invertible ((Z m ω)ᵀ * Z m ω) := inst
    exact (manyInstrumentProjectedSignalGram_eq_signalGram_of_nonsingular
      (Z m ω) (Gamma m)).symm
  have hcross_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) μ := by
    intro m
    refine (hOLS.cross_gram_meas m).congr ?_
    filter_upwards [hraw.instrument_gram_nonsingular m] with ω hω
    rcases hω with ⟨inst⟩
    letI : Invertible ((Z m ω)ᵀ * Z m ω) := inst
    exact (manyInstrumentProjectedReducedFormCrossGram_eq_crossGram_of_nonsingular
      (Z m ω) (Gamma m) (u2 m ω)).symm
  have hsignal_score_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedSignalScore
        (Z m ω) (Gamma m) (e m ω)) μ := by
    intro m
    refine (hOLS.signal_score_meas m).congr ?_
    filter_upwards [hraw.instrument_gram_nonsingular m] with ω hω
    rcases hω with ⟨inst⟩
    letI : Invertible ((Z m ω)ᵀ * Z m ω) := inst
    exact (manyInstrumentProjectedSignalScore_eq_signalScore_of_nonsingular
      (Z m ω) (Gamma m) (e m ω)).symm
  have herror_gram_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω)) μ := by
    intro m
    have hblock := (continuous_id.matrix_submatrix Sum.inr Sum.inr)
      |>.comp_aestronglyMeasurable (hfull_meas m)
    refine hblock.congr (ae_of_all μ fun ω => ?_)
    exact manyInstrumentsProjectedFullErrorMoment_inr_inr
      (Z m ω) (e m ω) (u2 m ω)
  have herror_cross_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectedErrorCross
        (Z m ω) (u2 m ω) (e m ω)) μ := by
    intro m
    have hentry_cont : Continuous
        (fun M : Matrix (Sum Unit k) (Sum Unit k) ℝ =>
          fun a => M (Sum.inr a) (Sum.inl ())) := by
      fun_prop
    have hblock := hentry_cont.comp_aestronglyMeasurable (hfull_meas m)
    refine hblock.congr (ae_of_all μ fun ω => ?_)
    exact manyInstrumentsProjectedFullErrorMoment_inr_inl
      (Z m ω) (e m ω) (u2 m ω)
  have hsignal_gram_tendsto : TendstoInMeasure μ
      (fun m ω => manyInstrumentProjectedSignalGram (Z m ω) (Gamma m))
      atTop (fun _ => H) := by
    refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hOLS.signal_gram_tendsto
    filter_upwards [hnonsing] with m hm
    filter_upwards [hm] with ω hω
    rcases hω with ⟨inst⟩
    letI : Invertible ((Z m ω)ᵀ * Z m ω) := inst
    exact (manyInstrumentProjectedSignalGram_eq_signalGram_of_nonsingular
      (Z m ω) (Gamma m)).symm
  have hcross_gram_tendsto : TendstoInMeasure μ
      (fun m ω => manyInstrumentProjectedReducedFormCrossGram
        (Z m ω) (Gamma m) (u2 m ω)) atTop (fun _ => 0) := by
    refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hOLS.cross_gram_tendsto_zero
    filter_upwards [hnonsing] with m hm
    filter_upwards [hm] with ω hω
    rcases hω with ⟨inst⟩
    letI : Invertible ((Z m ω)ᵀ * Z m ω) := inst
    exact (manyInstrumentProjectedReducedFormCrossGram_eq_crossGram_of_nonsingular
      (Z m ω) (Gamma m) (u2 m ω)).symm
  have hsignal_score_tendsto : TendstoInMeasure μ
      (fun m ω => manyInstrumentProjectedSignalScore
        (Z m ω) (Gamma m) (e m ω)) atTop (fun _ => 0) := by
    refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl hOLS.signal_score_tendsto_zero
    filter_upwards [hnonsing] with m hm
    filter_upwards [hm] with ω hω
    rcases hω with ⟨inst⟩
    letI : Invertible ((Z m ω)ᵀ * Z m ω) := inst
    exact (manyInstrumentProjectedSignalScore_eq_signalScore_of_nonsingular
      (Z m ω) (Gamma m) (e m ω)).symm
  refine
    { reduced_form := hraw.reduced_form
      moment_meas := ?_
      score_meas := ?_
      projected_signal_gram_meas := hsignal_gram_meas
      projected_error_gram_meas := herror_gram_meas
      projected_cross_gram_meas := hcross_gram_meas
      projected_signal_score_meas := hsignal_score_meas
      projected_error_score_meas := herror_cross_meas
      projected_signal_gram_tendsto := hsignal_gram_tendsto
      projected_error_gram_tendsto := hraw.projected_error_gram_tendsto hquad
      projected_cross_gram_tendsto_zero := hcross_gram_tendsto
      projected_signal_score_tendsto_zero := hsignal_score_tendsto
      projected_error_score_tendsto := hraw.projected_error_cross_tendsto hquad
      limit_nonsing := ?_ }
  · intro m
    have hsum := ((hsignal_gram_meas m).add (herror_gram_meas m)).add
      (hcross_gram_meas m)
    refine hsum.congr (ae_of_all μ fun ω => ?_)
    change
      manyInstrumentProjectedSignalGram (Z m ω) (Gamma m) +
          manyInstrumentProjectedErrorGram (Z m ω) (u2 m ω) +
        manyInstrumentProjectedReducedFormCrossGram
          (Z m ω) (Gamma m) (u2 m ω) =
      limlNormalizedMomentMatrixStar (Z m ω) (X m ω) 0
    rw [hraw.reduced_form m ω,
      manyInstrumentProjectedReducedForm_normalizedMomentMatrix_zero]
  · intro m
    have hsum := (hsignal_score_meas m).add (herror_cross_meas m)
    refine hsum.congr (ae_of_all μ fun ω => ?_)
    change
      manyInstrumentProjectedSignalScore (Z m ω) (Gamma m) (e m ω) +
        manyInstrumentProjectedErrorCross (Z m ω) (u2 m ω) (e m ω) =
      limlNormalizedMomentVectorStar (Z m ω) (X m ω) (e m ω) 0
    rw [hraw.reduced_form m ω,
      manyInstrumentProjectedReducedForm_normalizedMomentVector_zero]
  · apply manyInstruments_twoSLS_limit_matrix_nonsingular_of_posSemidef
      hraw.signal_posDef
    · simpa [manyInstrumentsSigma22] using
        hraw.error_covariance_posDef.posSemidef.submatrix Sum.inr
    · exact manyInstruments_alpha_nonneg_of_card_ratio_tendsto
        hraw.instrument_ratio

/-- Reconstruct the normalized joint `[Y,X]` moment from the regressor Gram,
regressor/error score, and structural-error second moment under `Y = Xβ + e`.

Writing `B = [β,I]` and `c = [1,0]`, this is
`B'AB + B'sc' + cs'B + qcc'`.  The map is useful for both the ordinary and
projected moments and keeps the normalized-pencil proof at the same moment
layer already used by the OLS and 2SLS faces of Theorem 12.19. -/
noncomputable def manyInstrumentsStructuralJointMoment
    (β : k → ℝ) (A : Matrix k k ℝ) (s : k → ℝ) (q : ℝ) :
    Matrix (Sum Unit k) (Sum Unit k) ℝ
  | Sum.inl _, Sum.inl _ =>
      β ⬝ᵥ (A *ᵥ β) + β ⬝ᵥ s + β ⬝ᵥ s + q
  | Sum.inl _, Sum.inr b => β ⬝ᵥ (fun a => A a b) + s b
  | Sum.inr a, Sum.inl _ => (A *ᵥ β) a + s a
  | Sum.inr a, Sum.inr b => A a b

private theorem manyInstruments_sumSwap2
    {a b : Type*} [Fintype a] [Fintype b] (f : a → b → ℝ) :
    (∑ i, ∑ j, f i j) = ∑ j, ∑ i, f i j := Finset.sum_comm

private theorem manyInstruments_sumSwap3
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (f : a → b → c → ℝ) :
    (∑ i, ∑ j, ∑ h, f i j h) = ∑ j, ∑ h, ∑ i, f i j h := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

private theorem manyInstruments_sumRotate3
    {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (f : a → b → c → ℝ) :
    (∑ i, ∑ j, ∑ h, f i j h) = ∑ h, ∑ i, ∑ j, f i j h := by
  calc
    (∑ i, ∑ j, ∑ h, f i j h) = ∑ i, ∑ h, ∑ j, f i j h := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ h, ∑ i, ∑ j, f i j h := Finset.sum_comm

private theorem manyInstruments_sumPerm4
    {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    (f : a → b → c → d → ℝ) :
    (∑ i, ∑ j, ∑ h, ∑ l, f i j h l) =
      ∑ l, ∑ j, ∑ i, ∑ h, f i j h l := by
  calc
    (∑ i, ∑ j, ∑ h, ∑ l, f i j h l) =
        ∑ i, ∑ j, ∑ l, ∑ h, f i j h l := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ l, ∑ j, ∑ h, f i j h l := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ l, ∑ i, ∑ j, ∑ h, f i j h l := Finset.sum_comm
    _ = ∑ l, ∑ j, ∑ i, ∑ h, f i j h l := by
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_comm]

omit [DecidableEq k] [∀ m, DecidableEq (ι m)] in
private theorem manyInstruments_normalizedRayleighNumerator_eq_structuralJointMoment
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y e : n → ℝ)
    (u2 : Matrix n k ℝ) (β : k → ℝ)
    (hY : Y = X *ᵥ β + e) :
    (Fintype.card n : ℝ)⁻¹ •
        manyInstrumentsLIMLSampleRayleighNumerator Z X Y =
      manyInstrumentsStructuralJointMoment β
        (limlNormalizedMomentMatrixStar Z X 0)
        (limlNormalizedMomentVectorStar Z X e 0)
        (manyInstrumentsProjectedFullErrorMoment Z e u2
          (Sum.inl ()) (Sum.inl ())) := by
  subst Y
  have hP : ∀ i j, instrumentProjectionStar Z i j =
      instrumentProjectionStar Z j i := by
    intro i j
    have hij := congrFun (congrFun (instrumentProjectionStar_transpose Z) j) i
    simpa using hij
  ext a b
  cases a with
  | inl ua =>
      cases b with
      | inl ub =>
          simp [manyInstrumentsLIMLSampleRayleighNumerator,
            manyInstrumentsStructuralJointMoment,
            manyInstrumentsProjectedFullErrorMoment,
            manyInstrumentsReducedFormErrorData,
            limlNormalizedMomentMatrixStar, limlMomentMatrixStar,
            limlNormalizedMomentVectorStar, limlMomentVectorStar,
            limlWeightMatrixStar, Matrix.mul_apply, Matrix.mulVec, dotProduct,
            Matrix.smul_apply, hP, mul_add, add_mul,
            Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
          rw [manyInstruments_sumPerm4
            (fun (i : n) (a : k) (j : n) (b : k) =>
              (Fintype.card n : ℝ)⁻¹ *
                (X j b * β b * instrumentProjectionStar Z i j *
                  (X i a * β a)))]
          rw [manyInstruments_sumSwap3
            (fun (i : n) (a : k) (j : n) =>
              (Fintype.card n : ℝ)⁻¹ *
                (e j * instrumentProjectionStar Z i j * (X i a * β a)))]
          rw [manyInstruments_sumRotate3
            (fun (i j : n) (a : k) =>
              (Fintype.card n : ℝ)⁻¹ *
                (X j a * β a * instrumentProjectionStar Z i j * e i))]
          have hquad (a b : k) (i j : n) :
              (Fintype.card n : ℝ)⁻¹ *
                  (X j a * β a * instrumentProjectionStar Z i j *
                    (X i b * β b)) =
                β a * ((Fintype.card n : ℝ)⁻¹ *
                  (X j a * instrumentProjectionStar Z i j * X i b) * β b) := by
            ring
          have hcrossSymm (a : k) (i j : n) :
              (Fintype.card n : ℝ)⁻¹ *
                  (e j * instrumentProjectionStar Z i j * (X i a * β a)) =
                β a * ((Fintype.card n : ℝ)⁻¹ *
                  (X i a * instrumentProjectionStar Z j i * e j)) := by
            rw [hP]
            ring
          have hcross (a : k) (i j : n) :
              (Fintype.card n : ℝ)⁻¹ *
                  (X j a * β a * instrumentProjectionStar Z i j * e i) =
                β a * ((Fintype.card n : ℝ)⁻¹ *
                  (X j a * instrumentProjectionStar Z i j * e i)) := by
            ring
          simp_rw [hquad, hcrossSymm, hcross]
          ring
      | inr b =>
          simp [manyInstrumentsLIMLSampleRayleighNumerator,
            manyInstrumentsStructuralJointMoment,
            limlNormalizedMomentMatrixStar, limlMomentMatrixStar,
            limlNormalizedMomentVectorStar, limlMomentVectorStar,
            limlWeightMatrixStar, Matrix.mul_apply, Matrix.mulVec, dotProduct,
            Matrix.smul_apply, hP, mul_add, add_mul,
            Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
          rw [manyInstruments_sumRotate3
            (fun (i j : n) (a : k) =>
              (Fintype.card n : ℝ)⁻¹ *
                (X j a * β a * instrumentProjectionStar Z i j * X i b))]
          rw [manyInstruments_sumSwap2
            (fun (i j : n) => (Fintype.card n : ℝ)⁻¹ *
              (e j * instrumentProjectionStar Z i j * X i b))]
          have hcross (i j : n) :
              (Fintype.card n : ℝ)⁻¹ *
                  (e j * instrumentProjectionStar Z i j * X i b) =
                (Fintype.card n : ℝ)⁻¹ *
                  (X i b * instrumentProjectionStar Z j i * e j) := by
            rw [hP]
            ring
          simp_rw [hcross]
          simp only [mul_comm, mul_left_comm, mul_assoc]
  | inr a =>
      cases b with
      | inl ub =>
          simp [manyInstrumentsLIMLSampleRayleighNumerator,
            manyInstrumentsStructuralJointMoment,
            limlNormalizedMomentMatrixStar, limlMomentMatrixStar,
            limlNormalizedMomentVectorStar, limlMomentVectorStar,
            limlWeightMatrixStar, Matrix.mul_apply, Matrix.mulVec, dotProduct,
            Matrix.smul_apply, hP, mul_add,
            Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
          rw [manyInstruments_sumSwap2
            (fun (i : n) (b : k) =>
              ∑ j : n, (Fintype.card n : ℝ)⁻¹ *
                (X j a * instrumentProjectionStar Z i j * (X i b * β b)))]
          simp only [mul_comm, mul_left_comm, mul_assoc]
      | inr b =>
          simp [manyInstrumentsLIMLSampleRayleighNumerator,
            manyInstrumentsStructuralJointMoment,
            limlNormalizedMomentMatrixStar, limlMomentMatrixStar,
            limlWeightMatrixStar, Matrix.mul_apply, Matrix.smul_apply]

omit [DecidableEq k] [∀ m, DecidableEq (ι m)] in
private theorem manyInstruments_sampleGram_rayleighData_eq_structuralJointMoment
    {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n k ℝ) (Y e : n → ℝ) (u2 : Matrix n k ℝ)
    (β : k → ℝ) (hY : Y = X *ᵥ β + e) :
    sampleGram (manyInstrumentsLIMLSampleRayleighData X Y) =
      manyInstrumentsStructuralJointMoment β (sampleGram X)
        (sampleCrossMoment X e)
        (sampleGram (manyInstrumentsReducedFormErrorData e u2)
          (Sum.inl ()) (Sum.inl ())) := by
  subst Y
  ext a b
  cases a with
  | inl ua =>
      cases b with
      | inl ub =>
          simp [manyInstrumentsLIMLSampleRayleighData,
            manyInstrumentsStructuralJointMoment,
            manyInstrumentsReducedFormErrorData, sampleGram, sampleCrossMoment,
            Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.smul_apply,
            mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
            Finset.sum_mul]
          rw [manyInstruments_sumSwap3
            (fun i a b => (Fintype.card n : ℝ)⁻¹ *
              (X i b * β b * (X i a * β a)))]
          rw [manyInstruments_sumSwap2
            (fun i a => (Fintype.card n : ℝ)⁻¹ *
              (e i * (X i a * β a)))]
          rw [manyInstruments_sumSwap2
            (fun i a => (Fintype.card n : ℝ)⁻¹ *
              (X i a * β a * e i))]
          simp only [mul_comm, mul_left_comm, mul_assoc]
          ring
      | inr b =>
          simp [manyInstrumentsLIMLSampleRayleighData,
            manyInstrumentsStructuralJointMoment,
            sampleGram, sampleCrossMoment,
            Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.smul_apply,
            mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
            Finset.sum_mul]
          rw [Finset.sum_comm]
          simp only [mul_comm, mul_left_comm, mul_assoc]
  | inr a =>
      cases b with
      | inl ub =>
          simp [manyInstrumentsLIMLSampleRayleighData,
            manyInstrumentsStructuralJointMoment,
            sampleGram, sampleCrossMoment,
            Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.smul_apply,
            mul_add, Finset.sum_add_distrib, Finset.mul_sum,
            Finset.sum_mul]
          rw [Finset.sum_comm]
          simp only [mul_comm, mul_left_comm, mul_assoc]
      | inr b =>
          simp [manyInstrumentsLIMLSampleRayleighData,
            manyInstrumentsStructuralJointMoment, sampleGram,
            Matrix.mul_apply, Matrix.smul_apply]

omit [Fintype k] [DecidableEq k] [∀ m, DecidableEq (ι m)] in
private theorem manyInstruments_normalizedRayleighDenominator_eq_total_sub_numerator
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (Y : n → ℝ) :
    (Fintype.card n : ℝ)⁻¹ •
        manyInstrumentsLIMLSampleRayleighDenominator Z X Y =
      sampleGram (manyInstrumentsLIMLSampleRayleighData X Y) -
        (Fintype.card n : ℝ)⁻¹ •
          manyInstrumentsLIMLSampleRayleighNumerator Z X Y := by
  simp [manyInstrumentsLIMLSampleRayleighDenominator,
    manyInstrumentsLIMLSampleRayleighNumerator,
    manyInstrumentsLIMLSampleRayleighData, sampleGram, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_assoc, smul_sub]

omit [∀ m, DecidableEq (ι m)] in
private theorem manyInstruments_structuralJointMoment_limit
    (β : k → ℝ) (H : Matrix k k ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) (r : ℝ)
    (hSigma : Sigma.PosDef) :
    manyInstrumentsStructuralJointMoment β
        (H + r • manyInstrumentsSigma22 Sigma)
        (r • manyInstrumentsSigma2e Sigma)
        (r * Sigma (Sum.inl ()) (Sum.inl ())) =
      (manyInstrumentsStructuralLoading β)ᵀ * H *
          manyInstrumentsStructuralLoading β +
        r • manyInstrumentsJointReducedFormCovariance β Sigma := by
  have hsymm : ∀ a b, Sigma a b = Sigma b a := by
    intro a b
    have hab := congrFun (congrFun hSigma.isHermitian.eq b) a
    simpa [Matrix.conjTranspose_apply] using hab
  ext a b
  cases a with
  | inl ua =>
      cases b with
      | inl ub =>
          simp [manyInstrumentsStructuralJointMoment,
            manyInstrumentsStructuralLoading, manyInstrumentsSigma22,
            manyInstrumentsSigma2e, manyInstrumentsJointReducedFormCovariance,
            manyInstrumentsReducedFormErrorLoading, Matrix.mul_apply,
            Matrix.mulVec, dotProduct, Matrix.smul_apply, hsymm,
            mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
            Finset.sum_mul]
          rw [manyInstruments_sumSwap2
            (fun x i => β x * (H x i * β i))]
          simp only [mul_comm, mul_left_comm]
          ring
      | inr b =>
          simp [manyInstrumentsStructuralJointMoment,
            manyInstrumentsStructuralLoading, manyInstrumentsSigma22,
            manyInstrumentsSigma2e, manyInstrumentsJointReducedFormCovariance,
            manyInstrumentsReducedFormErrorLoading, Matrix.mul_apply,
            dotProduct, Matrix.smul_apply, hsymm,
            mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
            Finset.sum_mul]
          simp only [mul_left_comm]
          ring
  | inr a =>
      cases b with
      | inl ub =>
          simp [manyInstrumentsStructuralJointMoment,
            manyInstrumentsStructuralLoading, manyInstrumentsSigma22,
            manyInstrumentsSigma2e, manyInstrumentsJointReducedFormCovariance,
            manyInstrumentsReducedFormErrorLoading, Matrix.mul_apply,
            Matrix.mulVec, dotProduct, Matrix.smul_apply, hsymm,
            mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
          simp only [mul_comm, mul_left_comm]
          ring
      | inr b =>
          simp [manyInstrumentsStructuralJointMoment,
            manyInstrumentsStructuralLoading, manyInstrumentsSigma22,
            manyInstrumentsJointReducedFormCovariance,
            manyInstrumentsReducedFormErrorLoading, Matrix.mul_apply,
            Matrix.smul_apply, hsymm]

omit [MeasurableSpace Ω] in
private theorem condExp_mul_eq_mul_condExp_of_condIndepFun
    {mc mΩ : MeasurableSpace Ω} [@StandardBorelSpace Ω mΩ]
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hm : mc ≤ mΩ)
    (hfg : CondIndepFun (mΩ := mΩ) mc hm f g μ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    μ[fun ω => f ω * g ω | mc] =ᵐ[μ]
      fun ω => μ[f | mc] ω * μ[g | mc] ω := by
  let f' : Ω → ℝ := hf.1.mk f
  let g' : Ω → ℝ := hg.1.mk g
  have hf'_meas : Measurable f' := hf.1.measurable_mk
  have hg'_meas : Measurable g' := hg.1.measurable_mk
  have hff' : f =ᵐ[μ] f' := hf.1.ae_eq_mk
  have hgg' : g =ᵐ[μ] g' := hg.1.ae_eq_mk
  have hf'_Lp : MemLp f' 2 μ := (memLp_congr_ae hff').mp hf
  have hg'_Lp : MemLp g' 2 μ := (memLp_congr_ae hgg').mp hg
  have hff'_cond :
      ∀ᵐ z ∂μ.trim hm, f =ᵐ[condExpKernel μ mc z] f' := by
    apply @Measure.ae_ae_of_ae_comp Ω Ω mc mΩ
      (μ.trim hm) (condExpKernel μ mc) (fun z => f z = f' z)
    rw [condExpKernel_comp_trim hm]
    exact hff'
  have hgg'_cond :
      ∀ᵐ z ∂μ.trim hm, g =ᵐ[condExpKernel μ mc z] g' := by
    apply @Measure.ae_ae_of_ae_comp Ω Ω mc mΩ
      (μ.trim hm) (condExpKernel μ mc) (fun z => g z = g' z)
    rw [condExpKernel_comp_trim hm]
    exact hgg'
  have hfg' : CondIndepFun (mΩ := mΩ) mc hm f' g' μ :=
    Kernel.IndepFun.congr' hfg hff'_cond hgg'_cond
  have hmap :=
    (condIndepFun_iff_map_prod_eq_prod_map_map hf'_meas hg'_meas).mp hfg'
  have hkernel :
      (fun z => ∫ y, f' y * g' y ∂condExpKernel μ mc z) =ᵐ[μ.trim hm]
        fun z =>
          (∫ y, f' y ∂condExpKernel μ mc z) *
            ∫ y, g' y ∂condExpKernel μ mc z := by
    filter_upwards [hmap] with z hz
    have hpair : Measurable (fun y => (f' y, g' y)) :=
      hf'_meas.prodMk hg'_meas
    calc
      (∫ y, f' y * g' y ∂condExpKernel μ mc z) =
          ∫ x : ℝ × ℝ, x.1 * x.2 ∂((condExpKernel μ mc).map
            (fun y => (f' y, g' y))) z := by
              rw [Kernel.map_apply _ hpair]
              rw [integral_map hpair.aemeasurable]
              fun_prop
      _ = ∫ x : ℝ × ℝ, x.1 * x.2 ∂
          (((condExpKernel μ mc).map f' ×ₖ
            (condExpKernel μ mc).map g') z) := by
              rw [hz]
      _ = ∫ x : ℝ × ℝ, x.1 * x.2 ∂
          (((condExpKernel μ mc).map f') z).prod
            (((condExpKernel μ mc).map g') z) := by
              rw [Kernel.prod_apply]
      _ = (∫ x, x ∂((condExpKernel μ mc).map f') z) *
          ∫ y, y ∂((condExpKernel μ mc).map g') z :=
            integral_prod_mul id id
      _ = (∫ y, f' y ∂condExpKernel μ mc z) *
          ∫ y, g' y ∂condExpKernel μ mc z := by
            rw [Kernel.map_apply _ hf'_meas,
              Kernel.map_apply _ hg'_meas]
            rw [integral_map hf'_meas.aemeasurable (by fun_prop),
              integral_map hg'_meas.aemeasurable (by fun_prop)]
  have hf'_int : Integrable f' μ := hf'_Lp.integrable (by norm_num)
  have hg'_int : Integrable g' μ := hg'_Lp.integrable (by norm_num)
  have hf'g'_Lp : MemLp (fun ω => f' ω * g' ω) 1 μ := by
    simpa only [Pi.mul_apply] using hg'_Lp.mul hf'_Lp
  have hf'g'_int : Integrable (fun ω => f' ω * g' ω) μ :=
    hf'g'_Lp.integrable le_rfl
  have hfactor' :
      μ[fun ω => f' ω * g' ω | mc] =ᵐ[μ]
        fun ω => μ[f' | mc] ω * μ[g' | mc] ω := by
    calc
      μ[fun ω => f' ω * g' ω | mc] =ᵐ[μ]
          (fun z => ∫ y, f' y * g' y ∂condExpKernel μ mc z) :=
            condExp_ae_eq_integral_condExpKernel hm hf'g'_int
      _ =ᵐ[μ] (fun z =>
          (∫ y, f' y ∂condExpKernel μ mc z) *
            ∫ y, g' y ∂condExpKernel μ mc z) :=
              ae_eq_of_ae_eq_trim hkernel
      _ =ᵐ[μ] (fun z => μ[f' | mc] z * μ[g' | mc] z) := by
        filter_upwards [
          (condExp_ae_eq_integral_condExpKernel hm hf'_int).symm,
          (condExp_ae_eq_integral_condExpKernel hm hg'_int).symm
        ] with z hfz hgz
        rw [hfz, hgz]
  have hprod :
      (fun ω => f ω * g ω) =ᵐ[μ] fun ω => f' ω * g' ω := by
    filter_upwards [hff', hgg'] with ω hfω hgω
    rw [hfω, hgω]
  calc
    μ[fun ω => f ω * g ω | mc] =ᵐ[μ]
        μ[fun ω => f' ω * g' ω | mc] := condExp_congr_ae hprod
    _ =ᵐ[μ] (fun ω => μ[f' | mc] ω * μ[g' | mc] ω) := hfactor'
    _ =ᵐ[μ] (fun ω => μ[f | mc] ω * μ[g | mc] ω) := by
      filter_upwards [condExp_congr_ae hff', condExp_congr_ae hgg'] with ω hfω hgω
      rw [hfω, hgω]

private theorem integral_sq_sum_le_card_mul_of_centered_uncorrelated
    {I : Type*} [Fintype I] [DecidableEq I]
    {Q : I → Ω → ℝ} {B : ℝ}
    (hQ : ∀ i, MemLp (Q i) 2 μ)
    (hmean : ∀ i, ∫ ω, Q i ω ∂μ = 0)
    (hcross : ∀ i j, i ≠ j → ∫ ω, Q i ω * Q j ω ∂μ = 0)
    (hvar : ∀ i, Var[Q i; μ] ≤ B) :
    Integrable (fun ω => (∑ i, Q i ω) ^ 2) μ ∧
      (∫ ω, (∑ i, Q i ω) ^ 2 ∂μ) ≤ (Fintype.card I : ℝ) * B := by
  have hsumLp : MemLp (fun ω => ∑ i, Q i ω) 2 μ :=
    memLp_finset_sum Finset.univ (fun i _ => hQ i)
  have hsumMean : ∫ ω, ∑ i, Q i ω ∂μ = 0 := by
    rw [integral_finset_sum Finset.univ]
    · simp [hmean]
    · intro i _
      exact (hQ i).integrable (by norm_num)
  have hsumSqInt : Integrable (fun ω => (∑ i, Q i ω) ^ 2) μ := by
    simpa only [Pi.mul_apply, pow_two] using hsumLp.integrable_mul hsumLp
  refine ⟨hsumSqInt, ?_⟩
  calc
    (∫ ω, (∑ i, Q i ω) ^ 2 ∂μ) = Var[fun ω => ∑ i, Q i ω; μ] :=
      (variance_of_integral_eq_zero hsumLp.aemeasurable hsumMean).symm
    _ = ∑ i, ∑ j, cov[Q i, Q j; μ] := variance_fun_sum hQ
    _ = ∑ i, Var[Q i; μ] := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← covariance_self (hQ i).aemeasurable]
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [covariance_eq_sub (hQ i) (hQ j), hmean i, hmean j]
        simpa only [Pi.mul_apply, mul_zero, sub_zero] using hcross i j hji.symm
      · simp
    _ ≤ ∑ _i : I, B := Finset.sum_le_sum fun i _ => hvar i
    _ = (Fintype.card I : ℝ) * B := by simp

omit [DecidableEq k] [∀ m, DecidableEq (ι m)] in
private theorem manyInstruments_unprojectedFullError_entry_meanSquare
    [StandardBorelSpace Ω]
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ} {B : ℝ}
    (h : ManyInstrumentsConditionalHomoskedasticFourthMomentModel
      μ Z e u2 Sigma B)
    (m : ℕ) (hm : 0 < m) (a b : Sum Unit k) :
    Integrable
        (fun ω => ‖(sampleGram
          (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω)) - Sigma) a b‖ ^
            (2 : ℝ)) μ ∧
      (∫ ω, ‖(sampleGram
          (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω)) - Sigma) a b‖ ^
            (2 : ℝ) ∂μ) ≤ B / (m : ℝ) := by
  let U : Fin m → Ω → Sum Unit k → ℝ := fun i ω =>
    manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω) i
  let V : Fin m → Ω → ℝ := fun i ω => U i ω a * U i ω b
  let Q : Fin m → Ω → ℝ := fun i ω => V i ω - Sigma a b
  have hU4 (i : Fin m) (c : Sum Unit k) :
      MemLp (fun ω => U i ω c) 4 μ := by
    simpa [U] using (h.error_row_memLp_four m i).eval c
  have hV2 (i : Fin m) : MemLp (V i) 2 μ := by
    simpa [V] using mul_memLp_two_of_memLp_four (hU4 i a) (hU4 i b)
  have hVint (i : Fin m) : Integrable (V i) μ :=
    (hV2 i).integrable (by norm_num)
  have hQ2 (i : Fin m) : MemLp (Q i) 2 μ := by
    simpa [Q] using (hV2 i).sub (memLp_const (Sigma a b))
  have hOuterInt (i : Fin m) : Integrable
      (fun ω => Matrix.vecMulVec (U i ω) (U i ω)) μ :=
    vecMulVec_integrable_of_coordinate_memLp_four (fun c => hU4 i c)
  have hVcond (i : Fin m) :
      condExpOn μ (V i) (Z m) =ᵐ[μ] fun _ => Sigma a b := by
    have hcoord :
        (fun ω => condExpOn μ
          (fun ω => Matrix.vecMulVec (U i ω) (U i ω)) (Z m) ω a b) =ᵐ[μ]
          condExpOn μ (V i) (Z m) := by
      simpa [condExpOn, Matrix.vecMulVec_apply, V] using
        condExp_apply_apply
          (m := conditioningSpace (Z m)) (μ := μ)
          (f := fun ω => Matrix.vecMulVec (U i ω) (U i ω))
          (hOuterInt i) a b
    have hmatrix :
        (fun ω => condExpOn μ
          (fun ω => Matrix.vecMulVec (U i ω) (U i ω)) (Z m) ω a b) =ᵐ[μ]
          fun _ => Sigma a b := by
      filter_upwards [h.conditional_second_moment m i] with ω hω
      exact congrFun (congrFun hω a) b
    exact hcoord.symm.trans hmatrix
  have hVmean (i : Fin m) : ∫ ω, V i ω ∂μ = Sigma a b := by
    calc
      (∫ ω, V i ω ∂μ) = ∫ ω, condExpOn μ (V i) (Z m) ω ∂μ := by
        symm
        simpa [condExpOn] using
          (integral_condExp
            (m := conditioningSpace (Z m)) (μ := μ) (f := V i)
            (conditioningSpace_le (h.instrument_measurable m)))
      _ = ∫ _ω, Sigma a b ∂μ := integral_congr_ae (hVcond i)
      _ = Sigma a b := by simp
  have hQmean (i : Fin m) : ∫ ω, Q i ω ∂μ = 0 := by
    rw [show (fun ω => Q i ω) = fun ω => V i ω - Sigma a b by rfl]
    rw [integral_sub (hVint i) (integrable_const (Sigma a b)), hVmean i]
    simp
  have hQcond (i : Fin m) : condExpOn μ (Q i) (Z m) =ᵐ[μ] 0 := by
    calc
      condExpOn μ (Q i) (Z m) =ᵐ[μ]
          condExpOn μ (V i) (Z m) -
            condExpOn μ (fun _ => Sigma a b) (Z m) := by
        simpa [condExpOn, Q] using
          condExp_sub (hVint i) (integrable_const (Sigma a b))
            (conditioningSpace (Z m))
      _ =ᵐ[μ] (fun _ => Sigma a b) - (fun _ => Sigma a b) := by
        have hconst :
            condExpOn μ (fun _ : Ω => Sigma a b) (Z m) = fun _ => Sigma a b := by
          simpa [condExpOn] using
            (condExp_const (μ := μ)
              (conditioningSpace_le (h.instrument_measurable m)) (Sigma a b))
        exact (hVcond i).sub (ae_of_all μ fun ω => congrFun hconst ω)
      _ =ᵐ[μ] 0 := by simp
  have hQcross (i j : Fin m) (hij : i ≠ j) :
      ∫ ω, Q i ω * Q j ω ∂μ = 0 := by
    have hrow := (h.rows_conditionally_independent m).condIndepFun hij
    have hphi : Measurable
        (fun x : Sum Unit k → ℝ => x a * x b - Sigma a b) := by
      fun_prop
    have hQind : CondIndepFun
        (conditioningSpace (Z m))
        (conditioningSpace_le (h.instrument_measurable m))
        (Q i) (Q j) μ := by
      simpa [Q, V, U, Function.comp_def] using hrow.comp hphi hphi
    have hfactor := condExp_mul_eq_mul_condExp_of_condIndepFun
      (conditioningSpace_le (h.instrument_measurable m)) hQind (hQ2 i) (hQ2 j)
    have hcondzero :
        condExpOn μ (fun ω => Q i ω * Q j ω) (Z m) =ᵐ[μ] 0 := by
      calc
        condExpOn μ (fun ω => Q i ω * Q j ω) (Z m) =ᵐ[μ]
            fun ω => condExpOn μ (Q i) (Z m) ω *
              condExpOn μ (Q j) (Z m) ω := by
          simpa [condExpOn] using hfactor
        _ =ᵐ[μ] 0 := by
          filter_upwards [hQcond i, hQcond j] with ω hi hj
          simp [hi, hj]
    calc
      (∫ ω, Q i ω * Q j ω ∂μ) =
          ∫ ω, condExpOn μ (fun ω => Q i ω * Q j ω) (Z m) ω ∂μ := by
        symm
        simpa [condExpOn] using
          (integral_condExp
            (m := conditioningSpace (Z m)) (μ := μ)
            (f := fun ω => Q i ω * Q j ω)
            (conditioningSpace_le (h.instrument_measurable m)))
      _ = 0 := by rw [integral_congr_ae hcondzero]; simp
  have hNorm4Int (i : Fin m) : Integrable (fun ω => ‖U i ω‖ ^ 4) μ := by
    simpa [U] using (h.error_row_memLp_four m i).integrable_norm_pow'
  have hNorm4Bound (i : Fin m) : ∫ ω, ‖U i ω‖ ^ 4 ∂μ ≤ B := by
    calc
      (∫ ω, ‖U i ω‖ ^ 4 ∂μ) =
          ∫ ω, condExpOn μ (fun ω => ‖U i ω‖ ^ 4) (Z m) ω ∂μ := by
        symm
        simpa [condExpOn] using
          (integral_condExp
            (m := conditioningSpace (Z m)) (μ := μ)
            (f := fun ω => ‖U i ω‖ ^ 4)
            (conditioningSpace_le (h.instrument_measurable m)))
      _ ≤ ∫ _ω, B ∂μ := by
        apply integral_mono_ae integrable_condExp (integrable_const B)
        simpa [U] using h.conditional_fourth_bound m i
      _ = B := by simp
  have hVSqBound (i : Fin m) : ∫ ω, (V i ω) ^ 2 ∂μ ≤ B := by
    have hpoint : ∀ ω, (V i ω) ^ 2 ≤ ‖U i ω‖ ^ 4 := by
      intro ω
      have ha : |U i ω a| ≤ ‖U i ω‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (U i ω) a
      have hb : |U i ω b| ≤ ‖U i ω‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (U i ω) b
      calc
        (V i ω) ^ 2 = |U i ω a| ^ 2 * |U i ω b| ^ 2 := by
          change (U i ω a * U i ω b) ^ 2 = _
          rw [mul_pow, sq_abs, sq_abs]
        _ ≤ ‖U i ω‖ ^ 2 * ‖U i ω‖ ^ 2 := by gcongr
        _ = ‖U i ω‖ ^ 4 := by ring
    calc
      (∫ ω, (V i ω) ^ 2 ∂μ) ≤ ∫ ω, ‖U i ω‖ ^ 4 ∂μ :=
        integral_mono_ae (hV2 i).integrable_sq (hNorm4Int i) (ae_of_all μ hpoint)
      _ ≤ B := hNorm4Bound i
  have hQVarBound (i : Fin m) : Var[Q i; μ] ≤ B := by
    calc
      Var[Q i; μ] = Var[V i; μ] := by
        simpa [Q] using variance_sub_const (hV2 i).1 (Sigma a b)
      _ = (∫ ω, (V i ω) ^ 2 ∂μ) - (Sigma a b) ^ 2 := by
        rw [variance_eq_sub (hV2 i), hVmean i]
        simp only [Pi.pow_apply]
      _ ≤ ∫ ω, (V i ω) ^ 2 ∂μ := sub_le_self _ (sq_nonneg _)
      _ ≤ B := hVSqBound i
  have hsum := integral_sq_sum_le_card_mul_of_centered_uncorrelated
    hQ2 hQmean hQcross hQVarBound
  have hsumBound : (∫ ω, (∑ i, Q i ω) ^ 2 ∂μ) ≤ (m : ℝ) * B := by
    simpa using hsum.2
  have hsumLp : MemLp (fun ω => ∑ i, Q i ω) 2 μ :=
    memLp_finset_sum Finset.univ (fun i _ => hQ2 i)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  have hrepr (ω : Ω) :
      (sampleGram
          (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω)) - Sigma) a b =
        (m : ℝ)⁻¹ * ∑ i, Q i ω := by
    rw [sampleGram_eq_average_vecMulVec]
    have houter :
        (∑ i : Fin m, Matrix.vecMulVec
          (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω) i)
          (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω) i)) a b =
          ∑ i : Fin m,
            manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω) i a *
              manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω) i b := by
      simp [Matrix.sum_apply, Matrix.vecMulVec_apply]
    simp only [Matrix.sub_apply, Matrix.smul_apply]
    rw [houter]
    simp [Q, V, U, Finset.sum_sub_distrib]
    field_simp
  have hentryLp : MemLp
      (fun ω => (sampleGram
        (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω)) - Sigma) a b) 2 μ := by
    exact (memLp_congr_ae (ae_of_all μ hrepr)).mpr
      (hsumLp.const_mul (m : ℝ)⁻¹)
  refine ⟨?_, ?_⟩
  · exact hentryLp.integrable_norm_rpow (by norm_num) (by norm_num)
  · calc
      (∫ ω, ‖(sampleGram
          (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω)) - Sigma) a b‖ ^
            (2 : ℝ) ∂μ) =
          ∫ ω, ((m : ℝ)⁻¹ * ∑ i, Q i ω) ^ 2 ∂μ := by
        apply integral_congr_ae
        exact ae_of_all μ fun ω => by
          change ‖(sampleGram
            (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω)) - Sigma) a b‖ ^
              (2 : ℝ) = _
          rw [hrepr]
          simpa [Real.norm_eq_abs] using (sq_abs ((m : ℝ)⁻¹ * ∑ i, Q i ω))
      _ = (m : ℝ)⁻¹ ^ 2 * ∫ ω, (∑ i, Q i ω) ^ 2 ∂μ := by
        simp_rw [mul_pow]
        rw [integral_const_mul]
      _ ≤ (m : ℝ)⁻¹ ^ 2 * ((m : ℝ) * B) :=
        mul_le_mul_of_nonneg_left hsumBound (sq_nonneg _)
      _ = B / (m : ℝ) := by field_simp

/-- Honest unprojected full-error WLLN used in the many-instrument LIML
denominator.  It is the matrix form of the ordinary WLLN for the structural
error row `[e,u₂]`; unlike the projected quadratic-form package, it is an
unweighted sample average. -/
structure ManyInstrumentsUnprojectedFullErrorMomentConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : (m : ℕ) → Ω → Fin m → ℝ)
    (u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) : Prop where
  full_error_meas : ∀ m, AEStronglyMeasurable
    (fun ω => sampleGram
      (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω))) μ
  full_error_tendsto : TendstoInMeasure μ
    (fun m ω => sampleGram
      (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω)))
    atTop (fun _ => Sigma)

omit [DecidableEq k] [∀ m, DecidableEq (ι m)] in
/-- The raw conditional-homoskedastic fourth-moment model implies the ordinary
unprojected WLLN for the full structural-error row.  The proof centers each
row-product entry, uses conditional independence to eliminate cross-row
covariances, and obtains the sharp `B / n` mean-square bound. -/
theorem
ManyInstrumentsConditionalHomoskedasticFourthMomentModel.toUnprojectedFullErrorMomentConditions
    [StandardBorelSpace Ω]
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ} {B : ℝ}
    (h : ManyInstrumentsConditionalHomoskedasticFourthMomentModel
      μ Z e u2 Sigma B) :
    ManyInstrumentsUnprojectedFullErrorMomentConditions μ e u2 Sigma := by
  have hfullMeas : ∀ m, AEStronglyMeasurable
      (fun ω => sampleGram
        (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω))) μ := by
    intro m
    have hrows : MemLp
        (fun ω => manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω)) 4 μ :=
      MemLp.of_eval fun i => h.error_row_memLp_four m i
    have hsampleGramContinuous : Continuous
        (fun X : Matrix (Fin m) (Sum Unit k) ℝ => sampleGram X) := by
      unfold sampleGram
      fun_prop
    exact hsampleGramContinuous.comp_aestronglyMeasurable hrows.1
  refine ⟨hfullMeas, ?_⟩
  apply TendstoInMeasure.of_sub_tendsto_zero_matrix
  · refine tendstoInMeasure_pi (fun a => ?_)
    refine tendstoInMeasure_pi (fun b => ?_)
    apply manyInstruments_tendstoInMeasure_zero_of_integral_sq_le_inv
    · intro m
      by_cases hm : 0 < m
      · exact (manyInstruments_unprojectedFullError_entry_meanSquare
          h m hm a b).1
      · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
        subst m
        simp [sampleGram]
    · filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
      exact (manyInstruments_unprojectedFullError_entry_meanSquare
        h m hm a b).2
  · exact tendstoInMeasure_of_tendsto_ae
      (fun _ => aestronglyMeasurable_const)
      (ae_of_all μ fun _ => tendsto_const_nhds)

/-- Joint convergence of the two normalized sample-pencil matrices.  This is
the honest spectral input to the LIML CMT; it does not assume an eigenvalue
gap or the LIML adjustment limit. -/
structure ManyInstrumentsLIMLNormalizedPencilConvergenceConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Y : (m : ℕ) → Ω → Fin m → ℝ)
    (β : k → ℝ) (H : Matrix k k ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) (alpha : ℝ) : Prop where
  pencil_meas : ∀ m, AEStronglyMeasurable
    (manyInstrumentsLIMLNormalizedSamplePencil Z X Y m) μ
  pencil_tendsto : TendstoInMeasure μ
    (manyInstrumentsLIMLNormalizedSamplePencil Z X Y) atTop
    (fun _ => (manyInstrumentsLIMLLimitNumerator β H Sigma alpha,
      manyInstrumentsLIMLLimitDenominator β Sigma alpha))

section NormalizedPencilAssembly

attribute [-instance] manyInstrumentsMatrixBorelMeasurableSpaceInst
  manyInstrumentsMatrixBorelSpaceInst

private noncomputable def manyInstrumentsOutcomeMomentCoord
    (M : Matrix (Sum Unit k) (Sum Unit k) ℝ) : ℝ :=
  M (Sum.inl ()) (Sum.inl ())

omit [Fintype k] [DecidableEq k] in
private theorem manyInstrumentsOutcomeMomentCoord_continuous : Continuous
    (manyInstrumentsOutcomeMomentCoord (k := k)) := by
  exact (continuous_apply (Sum.inl ())).comp (continuous_apply (Sum.inl ()))

omit [DecidableEq k] in
private theorem manyInstrumentsStructuralJointMoment_continuous (β : k → ℝ) :
    Continuous
      (fun p : Matrix k k ℝ × ((k → ℝ) × ℝ) =>
        manyInstrumentsStructuralJointMoment β p.1 p.2.1 p.2.2) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  cases a <;> cases b <;>
    simp [manyInstrumentsStructuralJointMoment] <;> fun_prop

set_option maxHeartbeats 3000000 in
omit [DecidableEq k] in
private theorem manyInstrumentsStructuralJointMoment_tendsto
    (β : k → ℝ)
    (A : ℕ → Ω → Matrix k k ℝ) (s : ℕ → Ω → (k → ℝ))
    (q : ℕ → Ω → ℝ) (A0 : Matrix k k ℝ) (s0 : k → ℝ) (q0 : ℝ)
    (hA_meas : ∀ m, AEStronglyMeasurable (A m) μ)
    (hs_meas : ∀ m, AEStronglyMeasurable (s m) μ)
    (hq_meas : ∀ m, AEStronglyMeasurable (q m) μ)
    (hA : TendstoInMeasure μ A atTop (fun _ => A0))
    (hs : TendstoInMeasure μ s atTop (fun _ => s0))
    (hq : TendstoInMeasure μ q atTop (fun _ => q0)) :
    TendstoInMeasure μ
      (fun m ω => manyInstrumentsStructuralJointMoment β
        (A m ω) (s m ω) (q m ω)) atTop
      (fun _ => manyInstrumentsStructuralJointMoment β A0 s0 q0) := by
  have hinputs_meas : ∀ m, AEStronglyMeasurable
      (fun ω => (A m ω, (s m ω, q m ω))) μ := fun m =>
    (hA_meas m).prodMk ((hs_meas m).prodMk (hq_meas m))
  have hinputs : TendstoInMeasure μ
      (fun m ω => (A m ω, (s m ω, q m ω))) atTop
      (fun _ => (A0, (s0, q0))) :=
    tendstoInMeasure_prodMk hA (tendstoInMeasure_prodMk hs hq)
  refine tendstoInMeasure_pi (fun a => ?_)
  refine tendstoInMeasure_pi (fun b => ?_)
  have hcoord_cont : Continuous
      (fun p : Matrix k k ℝ × ((k → ℝ) × ℝ) =>
        manyInstrumentsStructuralJointMoment β p.1 p.2.1 p.2.2 a b) := by
    cases a <;> cases b <;>
      simp [manyInstrumentsStructuralJointMoment] <;> fun_prop
  exact tendstoInMeasure_continuous_comp hinputs_meas hinputs hcoord_cont

omit [DecidableEq k] [IsProbabilityMeasure μ] in
private theorem manyInstrumentsStructuralJointMoment_aestronglyMeasurable
    (β : k → ℝ)
    (A : ℕ → Ω → Matrix k k ℝ) (s : ℕ → Ω → (k → ℝ))
    (q : ℕ → Ω → ℝ)
    (hA_meas : ∀ m, AEStronglyMeasurable (A m) μ)
    (hs_meas : ∀ m, AEStronglyMeasurable (s m) μ)
    (hq_meas : ∀ m, AEStronglyMeasurable (q m) μ) :
    ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentsStructuralJointMoment β
        (A m ω) (s m ω) (q m ω)) μ := by
  intro m
  change AEStronglyMeasurable
    (fun ω a b => manyInstrumentsStructuralJointMoment β
      (A m ω) (s m ω) (q m ω) a b) μ
  rw [aestronglyMeasurable_iff_aemeasurable, aemeasurable_pi_iff]
  intro a
  rw [aemeasurable_pi_iff]
  intro b
  have hAcoord (i j : k) : AEStronglyMeasurable
      (fun ω => A m ω i j) μ :=
    (continuous_apply j).comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable (hA_meas m))
  have hscoord (i : k) : AEStronglyMeasurable (fun ω => s m ω i) μ :=
    (continuous_apply i).comp_aestronglyMeasurable (hs_meas m)
  have hAvec (i : k) : AEStronglyMeasurable
      (fun ω => (A m ω *ᵥ β) i) μ := by
    have hsum := Finset.aestronglyMeasurable_sum Finset.univ
        (fun j _ => (hAcoord i j).mul
          (aestronglyMeasurable_const : AEStronglyMeasurable
            (fun _ : Ω => β j) μ))
    change AEStronglyMeasurable (fun ω => ∑ j, A m ω i j * β j) μ
    convert hsum using 1
    ext ω
    simp only [Finset.sum_apply, Pi.mul_apply]
  have hbetaAvec : AEStronglyMeasurable
      (fun ω => β ⬝ᵥ (A m ω *ᵥ β)) μ := by
    have hsum := Finset.aestronglyMeasurable_sum Finset.univ
        (fun i _ => (aestronglyMeasurable_const : AEStronglyMeasurable
          (fun _ : Ω => β i) μ).mul (hAvec i))
    change AEStronglyMeasurable (fun ω => ∑ i, β i * (A m ω *ᵥ β) i) μ
    convert hsum using 1
    ext ω
    simp only [Finset.sum_apply, Pi.mul_apply]
  have hbetas : AEStronglyMeasurable (fun ω => β ⬝ᵥ s m ω) μ := by
    have hsum := Finset.aestronglyMeasurable_sum Finset.univ
        (fun i _ => (aestronglyMeasurable_const : AEStronglyMeasurable
          (fun _ : Ω => β i) μ).mul (hscoord i))
    change AEStronglyMeasurable (fun ω => ∑ i, β i * s m ω i) μ
    convert hsum using 1
    ext ω
    simp only [Finset.sum_apply, Pi.mul_apply]
  cases a with
  | inl _ =>
      cases b with
      | inl _ =>
          exact (hbetaAvec.add hbetas |>.add hbetas |>.add (hq_meas m)).aemeasurable
      | inr j =>
          have hbetaCol : AEStronglyMeasurable
              (fun ω => β ⬝ᵥ (fun i => A m ω i j)) μ := by
            have hsum := Finset.aestronglyMeasurable_sum Finset.univ
                (fun i _ => (aestronglyMeasurable_const : AEStronglyMeasurable
                  (fun _ : Ω => β i) μ).mul (hAcoord i j))
            change AEStronglyMeasurable (fun ω => ∑ i, β i * A m ω i j) μ
            convert hsum using 1
            ext ω
            simp only [Finset.sum_apply, Pi.mul_apply]
          exact (hbetaCol.add (hscoord j)).aemeasurable
  | inr i =>
      cases b with
      | inl _ => exact ((hAvec i).add (hscoord i)).aemeasurable
      | inr j => exact (hAcoord i j).aemeasurable

set_option maxHeartbeats 3000000 in
private theorem manyInstruments_totalStructuralJointMoment_tendsto
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hOLS : ManyInstrumentsOLSMomentLimitConditions μ X e
      (H + manyInstrumentsSigma22 Sigma) (manyInstrumentsSigma2e Sigma))
    (hunprojected : ManyInstrumentsUnprojectedFullErrorMomentConditions
      μ e u2 Sigma) :
    TendstoInMeasure μ
      (fun m ω => manyInstrumentsStructuralJointMoment β
        (sampleGram (X m ω)) (sampleCrossMoment (X m ω) (e m ω))
        (manyInstrumentsOutcomeMomentCoord (sampleGram
          (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω))))) atTop
      (fun _ => manyInstrumentsStructuralJointMoment β
        (H + manyInstrumentsSigma22 Sigma) (manyInstrumentsSigma2e Sigma)
        (Sigma (Sum.inl ()) (Sum.inl ()))) := by
  have hcoord_meas_new : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentsOutcomeMomentCoord (sampleGram
        (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω)))) μ := fun m =>
    manyInstrumentsOutcomeMomentCoord_continuous.comp_aestronglyMeasurable
      (hunprojected.full_error_meas m)
  have hcoord_tendsto_new : TendstoInMeasure μ
      (fun m ω => manyInstrumentsOutcomeMomentCoord (sampleGram
        (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω)))) atTop
      (fun _ => Sigma (Sum.inl ()) (Sum.inl ())) := by
    simpa [manyInstrumentsOutcomeMomentCoord] using
      tendstoInMeasure_continuous_comp hunprojected.full_error_meas
        hunprojected.full_error_tendsto
        manyInstrumentsOutcomeMomentCoord_continuous
  exact manyInstrumentsStructuralJointMoment_tendsto (μ := μ) β
    (fun m ω => sampleGram (X m ω))
    (fun m ω => sampleCrossMoment (X m ω) (e m ω))
    (fun m ω => manyInstrumentsOutcomeMomentCoord (sampleGram
      (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω))))
    (H + manyInstrumentsSigma22 Sigma) (manyInstrumentsSigma2e Sigma)
    (Sigma (Sum.inl ()) (Sum.inl ())) hOLS.gram_meas hOLS.score_meas
    hcoord_meas_new hOLS.gram_tendsto hOLS.score_tendsto hcoord_tendsto_new

set_option maxHeartbeats 3000000 in
private theorem manyInstruments_projectedStructuralJointMoment_tendsto
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ} {alpha : ℝ}
    (hProjected : ManyInstrumentsLIMLMomentLimitConditions μ Z X e
      (fun _ _ => 0) (H + alpha • manyInstrumentsSigma22 Sigma)
        (alpha • manyInstrumentsSigma2e Sigma))
    (hfull_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentsProjectedFullErrorMoment
        (Z m ω) (e m ω) (u2 m ω)) μ)
    (hfull_tendsto : TendstoInMeasure μ
      (fun m ω => manyInstrumentsProjectedFullErrorMoment
        (Z m ω) (e m ω) (u2 m ω)) atTop
      (fun _ => alpha • Sigma)) :
    TendstoInMeasure μ
      (fun m ω => manyInstrumentsStructuralJointMoment β
        (limlNormalizedMomentMatrixStar (Z m ω) (X m ω) 0)
        (limlNormalizedMomentVectorStar (Z m ω) (X m ω) (e m ω) 0)
        (manyInstrumentsOutcomeMomentCoord
          (manyInstrumentsProjectedFullErrorMoment
            (Z m ω) (e m ω) (u2 m ω)))) atTop
      (fun _ => manyInstrumentsStructuralJointMoment β
        (H + alpha • manyInstrumentsSigma22 Sigma)
        (alpha • manyInstrumentsSigma2e Sigma)
        (alpha * Sigma (Sum.inl ()) (Sum.inl ()))) := by
  have hcoord_meas_new : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentsOutcomeMomentCoord
        (manyInstrumentsProjectedFullErrorMoment
          (Z m ω) (e m ω) (u2 m ω))) μ := fun m =>
    manyInstrumentsOutcomeMomentCoord_continuous.comp_aestronglyMeasurable
      (hfull_meas m)
  have hcoord_tendsto_new : TendstoInMeasure μ
      (fun m ω => manyInstrumentsOutcomeMomentCoord
        (manyInstrumentsProjectedFullErrorMoment
          (Z m ω) (e m ω) (u2 m ω))) atTop
      (fun _ => alpha * Sigma (Sum.inl ()) (Sum.inl ())) := by
    have hraw := tendstoInMeasure_continuous_comp hfull_meas hfull_tendsto
      manyInstrumentsOutcomeMomentCoord_continuous
    simpa [manyInstrumentsOutcomeMomentCoord, Matrix.smul_apply] using hraw
  exact manyInstrumentsStructuralJointMoment_tendsto (μ := μ) β
    (fun m ω => limlNormalizedMomentMatrixStar (Z m ω) (X m ω) 0)
    (fun m ω => limlNormalizedMomentVectorStar (Z m ω) (X m ω) (e m ω) 0)
    (fun m ω => manyInstrumentsOutcomeMomentCoord
      (manyInstrumentsProjectedFullErrorMoment (Z m ω) (e m ω) (u2 m ω)))
    (H + alpha • manyInstrumentsSigma22 Sigma)
    (alpha • manyInstrumentsSigma2e Sigma)
    (alpha * Sigma (Sum.inl ()) (Sum.inl ())) hProjected.moment_meas
    hProjected.score_meas hcoord_meas_new hProjected.moment_tendsto
    hProjected.score_tendsto hcoord_tendsto_new

set_option maxHeartbeats 900000 in
omit [IsProbabilityMeasure μ] in
private theorem manyInstruments_totalStructuralJointMoment_identify_limit
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hSigma : Sigma.PosDef)
    (h : TendstoInMeasure μ
      (fun m ω => manyInstrumentsStructuralJointMoment β
        (sampleGram (X m ω)) (sampleCrossMoment (X m ω) (e m ω))
        (manyInstrumentsOutcomeMomentCoord (sampleGram
          (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω))))) atTop
      (fun _ => manyInstrumentsStructuralJointMoment β
        (H + manyInstrumentsSigma22 Sigma) (manyInstrumentsSigma2e Sigma)
        (Sigma (Sum.inl ()) (Sum.inl ())))) :
    TendstoInMeasure μ
      (fun m ω => manyInstrumentsStructuralJointMoment β
        (sampleGram (X m ω)) (sampleCrossMoment (X m ω) (e m ω))
        (manyInstrumentsOutcomeMomentCoord (sampleGram
          (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω))))) atTop
      (fun _ => (manyInstrumentsStructuralLoading β)ᵀ * H *
          manyInstrumentsStructuralLoading β +
        manyInstrumentsJointReducedFormCovariance β Sigma) := by
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl)
    (ae_of_all μ fun _ => ?_) h
  simpa using manyInstruments_structuralJointMoment_limit β H Sigma 1 hSigma

set_option maxHeartbeats 900000 in
omit [IsProbabilityMeasure μ] in
private theorem manyInstruments_projectedStructuralJointMoment_identify_limit
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ} {alpha : ℝ}
    (hSigma : Sigma.PosDef)
    (h : TendstoInMeasure μ
      (fun m ω => manyInstrumentsStructuralJointMoment β
        (limlNormalizedMomentMatrixStar (Z m ω) (X m ω) 0)
        (limlNormalizedMomentVectorStar (Z m ω) (X m ω) (e m ω) 0)
        (manyInstrumentsOutcomeMomentCoord
          (manyInstrumentsProjectedFullErrorMoment
            (Z m ω) (e m ω) (u2 m ω)))) atTop
      (fun _ => manyInstrumentsStructuralJointMoment β
        (H + alpha • manyInstrumentsSigma22 Sigma)
        (alpha • manyInstrumentsSigma2e Sigma)
        (alpha * Sigma (Sum.inl ()) (Sum.inl ())))) :
    TendstoInMeasure μ
      (fun m ω => manyInstrumentsStructuralJointMoment β
        (limlNormalizedMomentMatrixStar (Z m ω) (X m ω) 0)
        (limlNormalizedMomentVectorStar (Z m ω) (X m ω) (e m ω) 0)
        (manyInstrumentsOutcomeMomentCoord
          (manyInstrumentsProjectedFullErrorMoment
            (Z m ω) (e m ω) (u2 m ω)))) atTop
      (fun _ => manyInstrumentsLIMLLimitNumerator β H Sigma alpha) := by
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl)
    (ae_of_all μ fun _ => ?_) h
  exact manyInstruments_structuralJointMoment_limit β H Sigma alpha hSigma

set_option maxHeartbeats 900000 in
private theorem manyInstruments_normalizedPencil_of_joint_limits
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ} {alpha : ℝ}
    (hstruct : ∀ m ω, Y m ω = X m ω *ᵥ β + e m ω)
    (htotal_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentsStructuralJointMoment β
        (sampleGram (X m ω)) (sampleCrossMoment (X m ω) (e m ω))
        (manyInstrumentsOutcomeMomentCoord (sampleGram
          (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω))))) μ)
    (htotal_tendsto : TendstoInMeasure μ
      (fun m ω => manyInstrumentsStructuralJointMoment β
        (sampleGram (X m ω)) (sampleCrossMoment (X m ω) (e m ω))
        (manyInstrumentsOutcomeMomentCoord (sampleGram
          (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω))))) atTop
      (fun _ => (manyInstrumentsStructuralLoading β)ᵀ * H *
          manyInstrumentsStructuralLoading β +
        manyInstrumentsJointReducedFormCovariance β Sigma))
    (hprojected_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentsStructuralJointMoment β
        (limlNormalizedMomentMatrixStar (Z m ω) (X m ω) 0)
        (limlNormalizedMomentVectorStar (Z m ω) (X m ω) (e m ω) 0)
        (manyInstrumentsOutcomeMomentCoord
          (manyInstrumentsProjectedFullErrorMoment
            (Z m ω) (e m ω) (u2 m ω)))) μ)
    (hprojected_tendsto : TendstoInMeasure μ
      (fun m ω => manyInstrumentsStructuralJointMoment β
        (limlNormalizedMomentMatrixStar (Z m ω) (X m ω) 0)
        (limlNormalizedMomentVectorStar (Z m ω) (X m ω) (e m ω) 0)
        (manyInstrumentsOutcomeMomentCoord
          (manyInstrumentsProjectedFullErrorMoment
            (Z m ω) (e m ω) (u2 m ω)))) atTop
      (fun _ => manyInstrumentsLIMLLimitNumerator β H Sigma alpha)) :
    ManyInstrumentsLIMLNormalizedPencilConvergenceConditions
      μ Z X Y β H Sigma alpha := by
  let totalJoint : ℕ → Ω → Matrix (Sum Unit k) (Sum Unit k) ℝ := fun m ω =>
    manyInstrumentsStructuralJointMoment β
    (sampleGram (X m ω)) (sampleCrossMoment (X m ω) (e m ω))
    (manyInstrumentsOutcomeMomentCoord (sampleGram
      (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω))))
  let projectedJoint : ℕ → Ω → Matrix (Sum Unit k) (Sum Unit k) ℝ := fun m ω =>
    manyInstrumentsStructuralJointMoment β
    (limlNormalizedMomentMatrixStar (Z m ω) (X m ω) 0)
    (limlNormalizedMomentVectorStar (Z m ω) (X m ω) (e m ω) 0)
    (manyInstrumentsOutcomeMomentCoord (manyInstrumentsProjectedFullErrorMoment
      (Z m ω) (e m ω) (u2 m ω)))
  have hdenom_meas : ∀ m, AEStronglyMeasurable
      (fun ω => totalJoint m ω - projectedJoint m ω) μ := by
    intro m
    have htotal : AEStronglyMeasurable (totalJoint m) μ := by
      simpa [totalJoint] using htotal_meas m
    have hprojected : AEStronglyMeasurable (projectedJoint m) μ := by
      simpa [projectedJoint] using hprojected_meas m
    exact htotal.sub hprojected
  have hdenom_tendsto : TendstoInMeasure μ
      (fun m ω => totalJoint m ω - projectedJoint m ω) atTop
      (fun _ => manyInstrumentsLIMLLimitDenominator β Sigma alpha) := by
    have hpair_meas : ∀ m, AEStronglyMeasurable
        (fun ω => (totalJoint m ω, projectedJoint m ω)) μ := by
      intro m
      have htotal : AEStronglyMeasurable (totalJoint m) μ := by
        simpa [totalJoint] using htotal_meas m
      have hprojected : AEStronglyMeasurable (projectedJoint m) μ := by
        simpa [projectedJoint] using hprojected_meas m
      exact htotal.prodMk hprojected
    have htotal_tendsto' : TendstoInMeasure μ totalJoint atTop
        (fun _ => (manyInstrumentsStructuralLoading β)ᵀ * H *
          manyInstrumentsStructuralLoading β +
            manyInstrumentsJointReducedFormCovariance β Sigma) := by
      simpa [totalJoint] using htotal_tendsto
    have hprojected_tendsto' : TendstoInMeasure μ projectedJoint atTop
        (fun _ => manyInstrumentsLIMLLimitNumerator β H Sigma alpha) := by
      simpa [projectedJoint] using hprojected_tendsto
    have hpair_tendsto := tendstoInMeasure_prodMk
      htotal_tendsto' hprojected_tendsto'
    have hsub_cont : Continuous
        (fun p : Matrix (Sum Unit k) (Sum Unit k) ℝ ×
          Matrix (Sum Unit k) (Sum Unit k) ℝ => p.1 - p.2) := by fun_prop
    have hsub := tendstoInMeasure_continuous_comp hpair_meas hpair_tendsto hsub_cont
    refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl)
      (ae_of_all μ fun _ => ?_) hsub
    ext a b
    simp [manyInstrumentsLIMLLimitNumerator,
      manyInstrumentsLIMLLimitDenominator, Matrix.smul_apply]
    ring
  refine
    { pencil_meas := ?_
      pencil_tendsto := ?_ }
  · intro m
    have hprojected : AEStronglyMeasurable (projectedJoint m) μ := by
      simpa [projectedJoint] using hprojected_meas m
    have hpair := hprojected.prodMk (hdenom_meas m)
    refine hpair.congr (ae_of_all μ fun ω => ?_)
    simp only [manyInstrumentsLIMLNormalizedSamplePencil]
    rw [hstruct m ω]
    have hnum : (m : ℝ)⁻¹ •
          manyInstrumentsLIMLSampleRayleighNumerator
            (Z m ω) (X m ω) (X m ω *ᵥ β + e m ω) = projectedJoint m ω := by
      simpa [projectedJoint, manyInstrumentsOutcomeMomentCoord] using
        manyInstruments_normalizedRayleighNumerator_eq_structuralJointMoment
          (Z m ω) (X m ω) (X m ω *ᵥ β + e m ω)
            (e m ω) (u2 m ω) β rfl
    have htotal : sampleGram (manyInstrumentsLIMLSampleRayleighData
          (X m ω) (X m ω *ᵥ β + e m ω)) = totalJoint m ω := by
      simpa [totalJoint, manyInstrumentsOutcomeMomentCoord] using
        manyInstruments_sampleGram_rayleighData_eq_structuralJointMoment
          (X m ω) (X m ω *ᵥ β + e m ω) (e m ω) (u2 m ω) β rfl
    have hden : (m : ℝ)⁻¹ •
          manyInstrumentsLIMLSampleRayleighDenominator
            (Z m ω) (X m ω) (X m ω *ᵥ β + e m ω) =
        sampleGram (manyInstrumentsLIMLSampleRayleighData
          (X m ω) (X m ω *ᵥ β + e m ω)) -
          (m : ℝ)⁻¹ • manyInstrumentsLIMLSampleRayleighNumerator
            (Z m ω) (X m ω) (X m ω *ᵥ β + e m ω) := by
      simpa using manyInstruments_normalizedRayleighDenominator_eq_total_sub_numerator
        (Z m ω) (X m ω) (X m ω *ᵥ β + e m ω)
    apply Prod.ext
    · exact hnum.symm
    · rw [← htotal, ← hnum]
      exact hden.symm
  · have hprojected_tendsto' : TendstoInMeasure μ projectedJoint atTop
        (fun _ => manyInstrumentsLIMLLimitNumerator β H Sigma alpha) := by
      simpa [projectedJoint] using hprojected_tendsto
    have hpair_tendsto := tendstoInMeasure_prodMk
      hprojected_tendsto' hdenom_tendsto
    refine TendstoInMeasure.congr (fun m => ?_) EventuallyEq.rfl hpair_tendsto
    exact ae_of_all μ fun ω => by
      simp only [manyInstrumentsLIMLNormalizedSamplePencil]
      rw [hstruct m ω]
      have hnum : (m : ℝ)⁻¹ •
            manyInstrumentsLIMLSampleRayleighNumerator
              (Z m ω) (X m ω) (X m ω *ᵥ β + e m ω) = projectedJoint m ω := by
        simpa [projectedJoint, manyInstrumentsOutcomeMomentCoord] using
          manyInstruments_normalizedRayleighNumerator_eq_structuralJointMoment
            (Z m ω) (X m ω) (X m ω *ᵥ β + e m ω)
              (e m ω) (u2 m ω) β rfl
      have htotal : sampleGram (manyInstrumentsLIMLSampleRayleighData
            (X m ω) (X m ω *ᵥ β + e m ω)) = totalJoint m ω := by
        simpa [totalJoint, manyInstrumentsOutcomeMomentCoord] using
          manyInstruments_sampleGram_rayleighData_eq_structuralJointMoment
            (X m ω) (X m ω *ᵥ β + e m ω) (e m ω) (u2 m ω) β rfl
      have hden : (m : ℝ)⁻¹ •
            manyInstrumentsLIMLSampleRayleighDenominator
              (Z m ω) (X m ω) (X m ω *ᵥ β + e m ω) =
          sampleGram (manyInstrumentsLIMLSampleRayleighData
            (X m ω) (X m ω *ᵥ β + e m ω)) -
            (m : ℝ)⁻¹ • manyInstrumentsLIMLSampleRayleighNumerator
              (Z m ω) (X m ω) (X m ω *ᵥ β + e m ω) := by
        simpa using manyInstruments_normalizedRayleighDenominator_eq_total_sub_numerator
          (Z m ω) (X m ω) (X m ω *ᵥ β + e m ω)
      apply Prod.ext
      · exact hnum.symm
      · rw [← htotal, ← hnum]
        exact hden.symm

set_option maxHeartbeats 900000 in
/-- Derive the normalized many-instrument LIML pencil from the raw model and
the same OLS and projected-error moments used by the OLS and 2SLS faces of
Theorem 12.19.  The ordinary unprojected full-error WLLN is derived internally
from conditional independence and the bounded conditional fourth moment. -/
theorem ManyInstrumentsLIMLNormalizedPencilConvergenceConditions.of_rawModel_moments
    [StandardBorelSpace Ω]
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {alpha B C : ℝ}
    (hraw : ManyInstrumentsTheorem1219RawModelConditions
      μ Z X Y Gamma e u2 β H Sigma alpha B)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H (manyInstrumentsSigma22 Sigma)
        (manyInstrumentsSigma2e Sigma))
    (hquad : ManyInstrumentsProjectionQuadraticMeanSquareConditions
      μ Z e u2 Sigma C) :
    ManyInstrumentsLIMLNormalizedPencilConvergenceConditions
      μ Z X Y β H Sigma alpha := by
  let hunprojected : ManyInstrumentsUnprojectedFullErrorMomentConditions
      μ e u2 Sigma := hraw.errors.toUnprojectedFullErrorMomentConditions
  let h2SLSNew : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H (manyInstrumentsSigma22 Sigma)
        (manyInstrumentsSigma2e Sigma) alpha :=
    hraw.toTwoSLSMomentAssemblyConditions hOLS hquad
  let hOLSNew : ManyInstrumentsOLSMomentLimitConditions μ X e
      (H + manyInstrumentsSigma22 Sigma) (manyInstrumentsSigma2e Sigma) :=
    ManyInstrumentsOLSMomentLimitConditions.of_reduced_form_components hOLS
  let hProjectedNew : ManyInstrumentsLIMLMomentLimitConditions μ Z X e
      (fun _ _ => 0) (H + alpha • manyInstrumentsSigma22 Sigma)
        (alpha • manyInstrumentsSigma2e Sigma) :=
    ManyInstrumentsLIMLMomentLimitConditions.of_projected_reduced_form_components
      h2SLSNew
  have htrace_meas_new : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentProjectionTraceRatio (Z m ω)) μ := fun m =>
    manyInstrumentProjectionTraceRatio_aestronglyMeasurable_of_ae_nonsingular
      (hraw.instrument_gram_nonsingular m)
  have hprojected_meas_new : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentsProjectedFullErrorMoment
        (Z m ω) (e m ω) (u2 m ω)) μ :=
    hquad.projected_meas htrace_meas_new
  have hprojected_tendsto_new : TendstoInMeasure μ
      (fun m ω => manyInstrumentsProjectedFullErrorMoment
        (Z m ω) (e m ω) (u2 m ω)) atTop
      (fun _ => alpha • Sigma) :=
    hraw.projected_full_error_tendsto hquad
  have htotal_coord_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentsOutcomeMomentCoord (sampleGram
        (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω)))) μ := fun m =>
    manyInstrumentsOutcomeMomentCoord_continuous.comp_aestronglyMeasurable
      (hunprojected.full_error_meas m)
  have htotal_meas_new :=
    manyInstrumentsStructuralJointMoment_aestronglyMeasurable (μ := μ) β
      (fun m ω => sampleGram (X m ω))
      (fun m ω => sampleCrossMoment (X m ω) (e m ω))
      (fun m ω => manyInstrumentsOutcomeMomentCoord (sampleGram
        (manyInstrumentsReducedFormErrorData (e m ω) (u2 m ω))))
      hOLSNew.gram_meas hOLSNew.score_meas htotal_coord_meas
  have htotal_tendsto_raw :=
    manyInstruments_totalStructuralJointMoment_tendsto (β := β)
      hOLSNew hunprojected
  have htotal_tendsto_new :=
    manyInstruments_totalStructuralJointMoment_identify_limit
      hraw.error_covariance_posDef htotal_tendsto_raw
  have hprojected_coord_meas : ∀ m, AEStronglyMeasurable
      (fun ω => manyInstrumentsOutcomeMomentCoord
        (manyInstrumentsProjectedFullErrorMoment
          (Z m ω) (e m ω) (u2 m ω))) μ := fun m =>
    manyInstrumentsOutcomeMomentCoord_continuous.comp_aestronglyMeasurable
      (hprojected_meas_new m)
  have hjoint_meas_new :=
    manyInstrumentsStructuralJointMoment_aestronglyMeasurable (μ := μ) β
      (fun m ω => limlNormalizedMomentMatrixStar (Z m ω) (X m ω) 0)
      (fun m ω => limlNormalizedMomentVectorStar
        (Z m ω) (X m ω) (e m ω) 0)
      (fun m ω => manyInstrumentsOutcomeMomentCoord
        (manyInstrumentsProjectedFullErrorMoment
          (Z m ω) (e m ω) (u2 m ω)))
      hProjectedNew.moment_meas hProjectedNew.score_meas hprojected_coord_meas
  have hjoint_tendsto_raw :=
    manyInstruments_projectedStructuralJointMoment_tendsto (β := β) hProjectedNew
      hprojected_meas_new hprojected_tendsto_new
  have hjoint_tendsto_new :=
    manyInstruments_projectedStructuralJointMoment_identify_limit
      hraw.error_covariance_posDef hjoint_tendsto_raw
  exact manyInstruments_normalizedPencil_of_joint_limits hraw.structural
    htotal_meas_new htotal_tendsto_new hjoint_meas_new hjoint_tendsto_new

/-- Locally continuous generalized-eigenvalue selector certificate, matching the
weak-IV selector/CMT architecture but applied to the many-instrument
normalized pencil.

Only continuity at the limiting pencil is required.  The sample minimizer is
retained as an audit field.  The deterministic limit minimizer identifies the
selector's limiting value; no stochastic eigenvalue gap is assumed. -/
structure ManyInstrumentsLIMLGeneralizedEigenvalueSelectorCertificate
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ)
    (X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ)
    (Y : (m : ℕ) → Ω → Fin m → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (H : Matrix k k ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) (alpha : ℝ)
    (muSelector :
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ) → ℝ) : Prop where
  selector_cont : ContinuousAt muSelector
    (manyInstrumentsLIMLLimitNumerator β H Sigma alpha,
      manyInstrumentsLIMLLimitDenominator β Sigma alpha)
  mu_meas : ∀ m, AEStronglyMeasurable (limlMuHat m) μ
  sample_selector_eq : ∀ m, limlMuHat m =ᵐ[μ] fun ω =>
    muSelector (manyInstrumentsLIMLNormalizedSamplePencil Z X Y m ω)
  sample_rayleigh_minimizer : ∀ m, ∀ᵐ ω ∂μ,
    LIMLRayleighMinimizer
      (manyInstrumentsLIMLNormalizedSamplePencil Z X Y m ω).1
      (manyInstrumentsLIMLNormalizedSamplePencil Z X Y m ω).2
      (limlMuHat m ω)
  limit_rayleigh_minimizer : LIMLRayleighMinimizer
    (manyInstrumentsLIMLLimitNumerator β H Sigma alpha)
    (manyInstrumentsLIMLLimitDenominator β Sigma alpha)
    (muSelector (manyInstrumentsLIMLLimitNumerator β H Sigma alpha,
      manyInstrumentsLIMLLimitDenominator β Sigma alpha))

/-- Normalized-pencil convergence plus the continuous generalized-eigenvalue
selector derives `μ̂ ->p α/(1-α)` by CMT. -/
theorem manyInstruments_limlMuHat_tendsto_of_normalizedPencil_selector
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ} {alpha : ℝ}
    {muSelector :
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ) → ℝ}
    (hpencil : ManyInstrumentsLIMLNormalizedPencilConvergenceConditions
      μ Z X Y β H Sigma alpha)
    (hselector : ManyInstrumentsLIMLGeneralizedEigenvalueSelectorCertificate
      μ Z X Y limlMuHat β H Sigma alpha muSelector)
    (hH : H.PosSemidef) (hSigma : Sigma.PosDef) (halpha : alpha < 1) :
    ManyInstrumentsLIMLEigenvalueLimitConditions μ limlMuHat alpha where
  meas := hselector.mu_meas
  tendsto := by
    have hbenchmark := manyInstrumentsLIMLLimit_rayleighMinimizer
      β H Sigma alpha hH hSigma halpha
    have hvalue :
        muSelector (manyInstrumentsLIMLLimitNumerator β H Sigma alpha,
          manyInstrumentsLIMLLimitDenominator β Sigma alpha) =
            alpha / (1 - alpha) :=
      LIMLRayleighMinimizer.value_unique
        hselector.limit_rayleigh_minimizer hbenchmark
    have hselector_meas : ∀ m, AEStronglyMeasurable
        (fun ω => muSelector
          (manyInstrumentsLIMLNormalizedSamplePencil Z X Y m ω)) μ := by
      intro m
      exact (hselector.mu_meas m).congr (hselector.sample_selector_eq m)
    have hraw := tendstoInMeasure_continuousAt_const_comp
      hpencil.pencil_meas hselector_meas hpencil.pencil_tendsto
        hselector.selector_cont
    refine TendstoInMeasure.congr (fun m => (hselector.sample_selector_eq m).symm)
      (ae_of_all μ fun _ => hvalue) hraw

/-- Assemble the canonical Theorem 12.19 condition package through normalized
pencil convergence and generalized-eigenvalue CMT.

This replaces the legacy adjustment-gap WLLN input.  The OLS and projected
2SLS assemblies remain separate because they also supply the two non-LIML
faces of Hansen's theorem. -/
theorem
ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_normalizedPencil_selector
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ} {alpha : ℝ}
    {muSelector :
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ) → ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio : Tendsto
      (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
      atTop (𝓝 alpha))
    (hstruct : ∀ m ω, Y m ω = X m ω *ᵥ β + e m ω)
    (hH : H.PosDef) (hSigma : Sigma.PosDef)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H (manyInstrumentsSigma22 Sigma)
        (manyInstrumentsSigma2e Sigma))
    (h2SLS : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H (manyInstrumentsSigma22 Sigma)
        (manyInstrumentsSigma2e Sigma) alpha)
    (hpencil : ManyInstrumentsLIMLNormalizedPencilConvergenceConditions
      μ Z X Y β H Sigma alpha)
    (hselector : ManyInstrumentsLIMLGeneralizedEigenvalueSelectorCertificate
      μ Z X Y limlMuHat β H Sigma alpha muSelector) :
    ManyInstrumentsTheorem1219Conditions
      μ Z X Y Gamma e u2 limlMuHat β H
        (manyInstrumentsSigma22 Sigma) (manyInstrumentsSigma2e Sigma) alpha := by
  have hmu := manyInstruments_limlMuHat_tendsto_of_normalizedPencil_selector
    hpencil hselector hH.posSemidef hSigma halpha_lt_one
  exact
    ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_mu_limit_conditions
      (manyInstruments_alpha_nonneg_of_card_ratio_tendsto hratio)
      halpha_lt_one hratio hstruct hH hOLS h2SLS hmu

/-- Hansen Theorem 12.19 through the genuine generalized-pencil route.

The LIML conclusion is obtained from normalized pencil convergence and the
continuous selector.  No additive eigenvalue-gap decomposition is exposed. -/
theorem manyInstruments_estimators_theorem12_19_of_normalizedPencil_selector
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ} {alpha : ℝ}
    {muSelector :
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ) → ℝ}
    (halpha_lt_one : alpha < 1)
    (hratio : Tendsto
      (fun m : ℕ => (Fintype.card (ι m) : ℝ) / (m : ℝ))
      atTop (𝓝 alpha))
    (hstruct : ∀ m ω, Y m ω = X m ω *ᵥ β + e m ω)
    (hH : H.PosDef) (hSigma : Sigma.PosDef)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H (manyInstrumentsSigma22 Sigma)
        (manyInstrumentsSigma2e Sigma))
    (h2SLS : ManyInstrumentsTwoSLSMomentAssemblyConditions
      μ Z X Gamma e u2 H (manyInstrumentsSigma22 Sigma)
        (manyInstrumentsSigma2e Sigma) alpha)
    (hpencil : ManyInstrumentsLIMLNormalizedPencilConvergenceConditions
      μ Z X Y β H Sigma alpha)
    (hselector : ManyInstrumentsLIMLGeneralizedEigenvalueSelectorCertificate
      μ Z X Y limlMuHat β H Sigma alpha muSelector) :
    TendstoInMeasure μ
      (fun m ω => olsBetaStar (X m ω) (Y m ω)) atTop
      (fun _ => β + manyInstrumentsOLSBias H
        (manyInstrumentsSigma22 Sigma) (manyInstrumentsSigma2e Sigma)) ∧
    TendstoInMeasure μ
      (fun m ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) atTop
      (fun _ => β + manyInstrumentsTwoSLSBias H
        (manyInstrumentsSigma22 Sigma) (manyInstrumentsSigma2e Sigma) alpha) ∧
    TendstoInMeasure μ
      (fun m ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) :=
  manyInstruments_estimators_theorem12_19
    (ManyInstrumentsTheorem1219Conditions.of_reduced_form_assemblies_normalizedPencil_selector
      halpha_lt_one hratio hstruct hH hSigma hOLS h2SLS hpencil hselector)

/-- Hansen Theorem 12.19 from the raw model, the remaining OLS/projected
concentration certificates, and a locally continuous generalized-root selector.

The raw package contains model (12.73), conditional assumptions (12.74)--(12.75),
the dimension ratio (12.76), and the signal-Gram limit (12.77), together with
the additional nondegeneracy assumption `Sigma.PosDef`.  The OLS
assembly is the fixed-dimensional WLLN output for the unprojected error and
signal-error moments.  The mean-square package is Hansen's conditional
quadratic-form calculation leading to (12.81), and is used here to derive the
projected 2SLS error moments rather than assume their probability limits.  The
normalized pencil is derived from these inputs and the raw model's ordinary
full-error WLLN; the local selector is the remaining spectral CMT boundary. -/
theorem manyInstruments_estimators_theorem12_19_of_rawModel_concentration_selector
    [StandardBorelSpace Ω]
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {e : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {alpha B C : ℝ}
    {muSelector :
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ) → ℝ}
    (hraw : ManyInstrumentsTheorem1219RawModelConditions
      μ Z X Y Gamma e u2 β H Sigma alpha B)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma e u2 H (manyInstrumentsSigma22 Sigma)
        (manyInstrumentsSigma2e Sigma))
    (hquad : ManyInstrumentsProjectionQuadraticMeanSquareConditions
      μ Z e u2 Sigma C)
    (hselector : ManyInstrumentsLIMLGeneralizedEigenvalueSelectorCertificate
      μ Z X Y limlMuHat β H Sigma alpha muSelector) :
    TendstoInMeasure μ
      (fun m ω => olsBetaStar (X m ω) (Y m ω)) atTop
      (fun _ => β + manyInstrumentsOLSBias H
        (manyInstrumentsSigma22 Sigma) (manyInstrumentsSigma2e Sigma)) ∧
    TendstoInMeasure μ
      (fun m ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) atTop
      (fun _ => β + manyInstrumentsTwoSLSBias H
        (manyInstrumentsSigma22 Sigma) (manyInstrumentsSigma2e Sigma) alpha) ∧
    TendstoInMeasure μ
      (fun m ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) := by
  let hpencil : ManyInstrumentsLIMLNormalizedPencilConvergenceConditions
      μ Z X Y β H Sigma alpha :=
    ManyInstrumentsLIMLNormalizedPencilConvergenceConditions.of_rawModel_moments
      hraw hOLS hquad
  apply manyInstruments_estimators_theorem12_19_of_normalizedPencil_selector
    hraw.alpha_lt_one hraw.instrument_ratio hraw.structural hraw.signal_posDef
      hraw.error_covariance_posDef hOLS
      (hraw.toTwoSLSMomentAssemblyConditions hOLS hquad) hpencil hselector

/-- Hansen Theorem 12.19 from the literal reduced-form errors `[u₁,u₂]` and
covariance `Σ` of (12.74).

The structural error is defined as `e = u₁ - β'u₂`.  Consequently the OLS and
2SLS biases use Hansen's exact `Σ₂e = Σ₂₁ - Σ₂₂β`, while the three conclusions
are otherwise identical to the existing raw-model endpoint.  The projected
quadratic and selector certificates are stated in the derived `[e,u₂]`
coordinates used by the internal proof engine. -/
theorem manyInstruments_estimators_theorem12_19_of_hansenRawModel_concentration_selector
    [StandardBorelSpace Ω]
    {Z : (m : ℕ) → Ω → Matrix (Fin m) (ι m) ℝ}
    {X : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {Y : (m : ℕ) → Ω → Fin m → ℝ}
    {Gamma : (m : ℕ) → Matrix (ι m) k ℝ}
    {u1 : (m : ℕ) → Ω → Fin m → ℝ}
    {u2 : (m : ℕ) → Ω → Matrix (Fin m) k ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {H : Matrix k k ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {alpha B C : ℝ}
    {muSelector :
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ) → ℝ}
    (hraw : ManyInstrumentsTheorem1219HansenRawModelConditions
      μ Z X Y Gamma u1 u2 β H Sigma alpha B)
    (hOLS : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma
        (fun m ω => manyInstrumentsStructuralError (u1 m ω) (u2 m ω) β)
        u2 H (manyInstrumentsSigma22 Sigma)
          (manyInstrumentsHansenSigma2e β Sigma))
    (hquad : ManyInstrumentsProjectionQuadraticMeanSquareConditions
      μ Z (fun m ω => manyInstrumentsStructuralError (u1 m ω) (u2 m ω) β)
        u2 (manyInstrumentsStructuralErrorCovariance β Sigma) C)
    (hselector : ManyInstrumentsLIMLGeneralizedEigenvalueSelectorCertificate
      μ Z X Y limlMuHat β H
        (manyInstrumentsStructuralErrorCovariance β Sigma) alpha muSelector) :
    TendstoInMeasure μ
      (fun m ω => olsBetaStar (X m ω) (Y m ω)) atTop
      (fun _ => β + manyInstrumentsOLSBias H
        (manyInstrumentsSigma22 Sigma) (manyInstrumentsHansenSigma2e β Sigma)) ∧
    TendstoInMeasure μ
      (fun m ω => twoSLSBetaStar (Z m ω) (X m ω) (Y m ω)) atTop
      (fun _ => β + manyInstrumentsTwoSLSBias H
        (manyInstrumentsSigma22 Sigma) (manyInstrumentsHansenSigma2e β Sigma) alpha) ∧
    TendstoInMeasure μ
      (fun m ω => limlBetaStar (Z m ω) (X m ω) (Y m ω) (limlMuHat m ω))
      atTop (fun _ => β) := by
  have hOLS' : ManyInstrumentsOLSMomentAssemblyConditions
      μ Z X Gamma
        (fun m ω => manyInstrumentsStructuralError (u1 m ω) (u2 m ω) β)
        u2 H
          (manyInstrumentsSigma22
            (manyInstrumentsStructuralErrorCovariance β Sigma))
          (manyInstrumentsSigma2e
            (manyInstrumentsStructuralErrorCovariance β Sigma)) := by
    rw [manyInstrumentsSigma22_structuralErrorCovariance,
      manyInstrumentsSigma2e_structuralErrorCovariance]
    exact hOLS
  simpa only [manyInstrumentsSigma22_structuralErrorCovariance,
    manyInstrumentsSigma2e_structuralErrorCovariance] using
    (manyInstruments_estimators_theorem12_19_of_rawModel_concentration_selector
      (hraw := hraw.toRawModelConditions) (hOLS := hOLS')
      (hquad := hquad) (hselector := hselector))

end NormalizedPencilAssembly

/- The following compatibility packages encode projected quadratic forms or
an eigenvalue adjustment as iid additive rows.  Projection and generalized
eigenvalue selection do not have that form.  They remain available only so
existing same-file compatibility wrappers elaborate; new theorem-facing work
must use the conditional mean-square and normalized-pencil route above. -/
attribute [deprecated ManyInstrumentsProjectionQuadraticMeanSquareConditions
    (since := "2026-07-11")]
  ManyInstrumentsProjectedErrorTraceRemainderRowWLLNConditions
  ManyInstrumentsProjectedErrorTraceRemainderScalarWLLNConditions

attribute [deprecated ManyInstrumentsLIMLNormalizedPencilConvergenceConditions
    (since := "2026-07-11")]
  ManyInstrumentsLIMLSampleEigenvalueAdjustmentGapWLLNConditions
  ManyInstrumentsLIMLFiniteSampleRayleighAdjustmentGapWLLNConditions
  ManyInstrumentsProjectedErrorRayleighJointRowWLLNConditions

end Asymptotics

end HansenEconometrics
