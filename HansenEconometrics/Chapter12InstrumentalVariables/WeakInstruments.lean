import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.AsymptoticUtils.StochasticOrder
import HansenEconometrics.Chapter12InstrumentalVariables.Asymptotics
import HansenEconometrics.Chapter12InstrumentalVariables.LIML

/-!
# Chapter 12 — weak instruments

This file gives the theorem surface for Hansen Theorem 12.18.  The displayed
weak-instrument limits are named separately from the estimator convergence
package, and the OLS face now has a moment-level constructor from normalized
bread and score convergence.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix Matrix.Norms.Elementwise Function Topology MeasureTheory ProbabilityTheory

namespace HansenEconometrics

open Matrix

variable {k l : Type*}
variable [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]

@[reducible]
private noncomputable def weakIVMatrixBorelMeasurableSpaceInst
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurableSpace (Matrix ι κ ℝ) :=
  matrixBorelMeasurableSpace ι κ

private lemma weakIVMatrixBorelSpaceInst
    {ι κ : Type*} [Fintype ι] [Fintype κ] :
    @BorelSpace (Matrix ι κ ℝ) _
      (weakIVMatrixBorelMeasurableSpaceInst (ι := ι) (κ := κ)) :=
  matrixBorelSpace ι κ

attribute [local instance] weakIVMatrixBorelMeasurableSpaceInst weakIVMatrixBorelSpaceInst

/-- OLS weak-instrument probability limit drift,
`Σ₂₂^{-1} Σ₂e`, from Hansen Theorem 12.18. -/
noncomputable def weakIVOLSBias
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) : k → ℝ :=
  Sigma22⁻¹ *ᵥ Sigma2e

/-- Weak first-stage Gaussian/local-to-zero limit matrix `Q_ZZ C + Ξ₂`. -/
noncomputable def weakIVFirstStageLimit
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ) : Matrix l k ℝ :=
  QZZ * C + Xi2

/-- Hansen's weak-instrument LIML Rayleigh numerator matrix,
`(Q_ZZ C + Ξ₂)' Q_ZZ^{-1} (Q_ZZ C + Ξ₂)`. -/
noncomputable def weakIVLIMLRayleighMatrix
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ) : Matrix k k ℝ :=
  limlRayleighMatrix QZZ (weakIVFirstStageLimit QZZ C Xi2)

/-- Hansen's weak-instrument LIML Rayleigh quotient whose minimum is `µ*`. -/
noncomputable def weakIVLIMLRayleighQuotient
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ)
    (Sigma22 : Matrix k k ℝ) (γ : k → ℝ) : ℝ :=
  limlRayleighQuotient (weakIVLIMLRayleighMatrix QZZ C Xi2) Sigma22 γ

/-- Hansen's weak-IV 2SLS random limit drift,
`(A' Q_ZZ^{-1} A)^{-1} A' Q_ZZ^{-1} ξ_e`, where
`A = Q_ZZ C + Ξ₂`. -/
noncomputable def weakIV2SLSBias
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ) (xie : l → ℝ) : k → ℝ :=
  let A := weakIVFirstStageLimit QZZ C Xi2
  (Aᵀ * QZZ⁻¹ * A)⁻¹ *ᵥ ((Aᵀ * QZZ⁻¹) *ᵥ xie)

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] in
/-- Scalar just-identified specialization of the weak-IV 2SLS limit.

For `QZZ = 1` and one endogenous regressor/instrument, Hansen's generic
Theorem 12.18 2SLS drift collapses to the ratio `ξe / (µ + ξ₂)` used in the
Stock-Yogo discussion following the theorem. -/
theorem weakIV2SLSBias_unit_apply_eq_ratio
    (mu xi2 xie : ℝ) :
    weakIV2SLSBias
        (k := Unit) (l := Unit)
        (1 : Matrix Unit Unit ℝ)
        (fun _ _ => mu) (fun _ _ => xi2) (fun _ => xie) () =
      xie / (mu + xi2) := by
  classical
  by_cases h : mu + xi2 = 0
  · simp [weakIV2SLSBias, weakIVFirstStageLimit, Matrix.mul_apply, h]
  · simp [weakIV2SLSBias, weakIVFirstStageLimit, Matrix.mulVec,
      dotProduct, Matrix.mul_apply, div_eq_mul_inv]
    field_simp [h]

/-- Hansen's weak-IV LIML random limit drift.  The scalar `mustar` is the
limiting LIML eigenvalue adjustment appearing in Theorem 12.18. -/
noncomputable def weakIVLIMLBias
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ) (xie : l → ℝ)
    (mustar : ℝ) (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) : k → ℝ :=
  let A := weakIVFirstStageLimit QZZ C Xi2
  (Aᵀ * QZZ⁻¹ * A - mustar • Sigma22)⁻¹ *ᵥ
    (((Aᵀ * QZZ⁻¹) *ᵥ xie) - mustar • Sigma2e)

/-- Hansen's weak-IV k-class random limit drift.  The k-class parameter `κ`
corresponds to the Section 12.19 LIML adjustment `μ = κ - 1`. -/
noncomputable def weakIVKClassBias
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ) (xie : l → ℝ)
    (kappa : ℝ) (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) : k → ℝ :=
  weakIVLIMLBias QZZ C Xi2 xie (kappa - 1) Sigma22 Sigma2e

/-- The `μ` parametrization of the weak-IV LIML limit is the k-class
parametrization with `κ = μ + 1`. -/
theorem weakIVLIMLBias_eq_kClassBias_add_one
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ) (xie : l → ℝ)
    (mustar : ℝ) (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) :
    weakIVLIMLBias QZZ C Xi2 xie mustar Sigma22 Sigma2e =
      weakIVKClassBias QZZ C Xi2 xie (mustar + 1) Sigma22 Sigma2e := by
  unfold weakIVKClassBias
  ring_nf

section Asymptotics

variable {Ω Ωlim : Type*} [MeasurableSpace Ω] [MeasurableSpace Ωlim]
variable {μ : Measure Ω} {ν : Measure Ωlim}
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Hansen-normalized OLS bread used by the weak-IV OLS face:
`Q̂_XX = n^{-1} X'X`. -/
noncomputable def weakIVOLSNormalizedBread
    (X : ℕ → Ω → k → ℝ) (m : ℕ) (ω : Ω) : Matrix k k ℝ :=
  sampleGram (stackRegressors X m ω)

/-- Hansen-normalized OLS structural-error score used by the weak-IV OLS face:
`n^{-1} X'e`. -/
noncomputable def weakIVOLSNormalizedScore
    (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (m : ℕ) (ω : Ω) : k → ℝ :=
  sampleCrossMoment (stackRegressors X m ω) (stackErrors e m ω)

/-- Hansen-normalized 2SLS weak-instrument bread,
`Q̂_XZ Q̂_ZZ^{-1} Q̂_ZX`. -/
noncomputable def weakIV2SLSNormalizedBread
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (m : ℕ) (ω : Ω) : Matrix k k ℝ :=
  twoSLSBread
    (sampleQXZ (stackRegressors Z m ω) (stackRegressors X m ω))
    (sampleQZZ (stackRegressors Z m ω))
    (sampleQZX (stackRegressors Z m ω) (stackRegressors X m ω))

/-- Hansen-normalized 2SLS structural-error score,
`Q̂_XZ Q̂_ZZ^{-1} n^{-1}Z'e`. -/
noncomputable def weakIV2SLSNormalizedScore
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (m : ℕ) (ω : Ω) : k → ℝ :=
  (sampleQXZ (stackRegressors Z m ω) (stackRegressors X m ω) *
      (sampleQZZ (stackRegressors Z m ω))⁻¹) *ᵥ
    sampleCrossMoment (stackRegressors Z m ω) (stackErrors e m ω)

/-- Root-scaled weak-IV first-stage moment `n^{-1/2} Z'X`.

This is Hansen's local-to-zero first-stage object in Theorem 12.18.  It is
separate from the strong-IV sample moment `n^{-1}Z'X` used in Theorems
12.1--12.3. -/
noncomputable def weakIV2SLSRootScaledFirstStage
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (m : ℕ) (ω : Ω) : Matrix l k ℝ :=
  Real.sqrt (m : ℝ) •
    sampleQZX (stackRegressors Z m ω) (stackRegressors X m ω)

/-- Root-scaled weak-IV instrument-error score `n^{-1/2} Z'e`. -/
noncomputable def weakIV2SLSRootScaledInstrumentScore
    (Z : ℕ → Ω → l → ℝ) (e : ℕ → Ω → ℝ)
    (m : ℕ) (ω : Ω) : l → ℝ :=
  Real.sqrt (m : ℝ) •
    sampleCrossMoment (stackRegressors Z m ω) (stackErrors e m ω)

/-- Hansen-scaled weak-IV 2SLS bread:
`(n^{-1/2}X'Z) Q̂_ZZ^{-1} (n^{-1/2}Z'X)`. -/
noncomputable def weakIV2SLSRootScaledBread
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (m : ℕ) (ω : Ω) : Matrix k k ℝ :=
  let A := weakIV2SLSRootScaledFirstStage Z X m ω
  Aᵀ * (sampleQZZ (stackRegressors Z m ω))⁻¹ * A

/-- Hansen-scaled weak-IV 2SLS structural-error score:
`(n^{-1/2}X'Z) Q̂_ZZ^{-1} (n^{-1/2}Z'e)`. -/
noncomputable def weakIV2SLSRootScaledScore
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (m : ℕ) (ω : Ω) : k → ℝ :=
  let A := weakIV2SLSRootScaledFirstStage Z X m ω
  (Aᵀ * (sampleQZZ (stackRegressors Z m ω))⁻¹) *ᵥ
    weakIV2SLSRootScaledInstrumentScore Z e m ω

/-- Random weak-IV 2SLS bread limit,
`(Q_ZZ C + Ξ₂)' Q_ZZ^{-1} (Q_ZZ C + Ξ₂)`. -/
noncomputable def weakIV2SLSLimitBread
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ) : Matrix k k ℝ :=
  let A := weakIVFirstStageLimit QZZ C Xi2
  Aᵀ * QZZ⁻¹ * A

/-- Random weak-IV 2SLS structural-error score limit,
`(Q_ZZ C + Ξ₂)' Q_ZZ^{-1} ξ_e`. -/
noncomputable def weakIV2SLSLimitScore
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ) (xie : l → ℝ) : k → ℝ :=
  let A := weakIVFirstStageLimit QZZ C Xi2
  (Aᵀ * QZZ⁻¹) *ᵥ xie

/-- Primitive weak-IV 2SLS sample moments: instrument Gram, first-stage
cross moment, and instrument-error score.  This is the lower-level surface
behind Hansen's local-to-zero first-stage CLT in Theorem 12.18. -/
noncomputable def weakIV2SLSPrimitiveMoments
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (m : ℕ) (ω : Ω) :
    Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) :=
  (sampleQZZ (stackRegressors Z m ω),
    sampleQZX (stackRegressors Z m ω) (stackRegressors X m ω),
    sampleCrossMoment (stackRegressors Z m ω) (stackErrors e m ω))

/-- Primitive root-scaled weak-IV 2SLS sample moments:
`(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)`.

This is the literal local-to-zero first-stage CLT surface in Hansen Theorem
12.18. -/
noncomputable def weakIV2SLSRootPrimitiveMoments
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (m : ℕ) (ω : Ω) :
    Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) :=
  (sampleQZZ (stackRegressors Z m ω),
    weakIV2SLSRootScaledFirstStage Z X m ω,
    weakIV2SLSRootScaledInstrumentScore Z e m ω)

/-- Primitive weak-IV 2SLS limit moments:
`(Q_ZZ, Q_ZZ C + Ξ₂, ξ_e)`. -/
noncomputable def weakIV2SLSPrimitiveLimit
    (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (η : Ωlim) :
    Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) :=
  (QZZ, weakIVFirstStageLimit QZZ C (Xi2 η), xie η)

/-- Continuous-map target from primitive weak-IV moments to projected 2SLS
bread and structural-error score. -/
noncomputable def weakIV2SLSProjectedBreadScoreFromPrimitive
    (p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) :
    Matrix k k ℝ × (k → ℝ) :=
  let QZZhat := p.1
  let QZXhat := p.2.1
  let zScore := p.2.2
  (QZXhatᵀ * QZZhat⁻¹ * QZXhat,
    (QZXhatᵀ * QZZhat⁻¹) *ᵥ zScore)

omit [Fintype k] [DecidableEq k] [MeasurableSpace Ω] in
/-- The projected bread/score map applied to the root-scaled primitive moments
is exactly Hansen's root-scaled weak-IV bread/score pair. -/
theorem weakIV2SLSProjectedBreadScoreFromRootPrimitive_eq
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (m : ℕ) (ω : Ω) :
    weakIV2SLSProjectedBreadScoreFromPrimitive
        (weakIV2SLSRootPrimitiveMoments Z X e m ω) =
      (weakIV2SLSRootScaledBread Z X m ω,
        weakIV2SLSRootScaledScore Z X e m ω) := by
  simp [weakIV2SLSProjectedBreadScoreFromPrimitive,
    weakIV2SLSRootPrimitiveMoments, weakIV2SLSRootScaledBread,
    weakIV2SLSRootScaledScore]

/-- Hansen-normalized LIML weak-instrument bread,
`n^{-1}X'(P_Z - μ̂ M_Z)X`. -/
noncomputable def weakIVLIMLNormalizedBread
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (limlMuHat : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : Matrix k k ℝ :=
  limlNormalizedMomentMatrixStar
    (stackRegressors Z m ω) (stackRegressors X m ω) (limlMuHat m ω)

/-- Hansen-normalized LIML structural-error score,
`n^{-1}X'(P_Z - μ̂ M_Z)e`. -/
noncomputable def weakIVLIMLNormalizedScore
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (limlMuHat : ℕ → Ω → ℝ)
    (m : ℕ) (ω : Ω) : k → ℝ :=
  limlNormalizedMomentVectorStar
    (stackRegressors Z m ω) (stackRegressors X m ω) (stackErrors e m ω)
    (limlMuHat m ω)

/-- Finite-sample LIML adjustment used by the weak-IV k-class weight.

Hansen Theorem 12.18 tracks the scaled eigenvalue adjustment `µ̂_n`, whose
limit is `µ*`; the finite-sample estimator itself uses `µ̂_n / n` in
`P_Z - (µ̂_n/n) M_Z`. -/
noncomputable def weakIVLIMLFiniteSampleMu
    (limlMuHat : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  (m : ℝ)⁻¹ * limlMuHat m ω

/-- Weak-IV-scaled LIML bread:
`X'P_ZX - µ̂_n n^{-1}X'M_ZX`.

This is `n` times the Hansen-normalized LIML bread with the finite-sample
adjustment `µ̂_n / n`.  It is the moment surface whose inverse-score term has
the weak-instrument LIML limit in Theorem 12.18. -/
noncomputable def weakIVLIMLWeakScaledBread
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (limlMuHat : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : Matrix k k ℝ :=
  (m : ℝ) •
    weakIVLIMLNormalizedBread Z X (weakIVLIMLFiniteSampleMu limlMuHat) m ω

/-- Weak-IV-scaled LIML structural-error score:
`X'P_Ze - µ̂_n n^{-1}X'M_Ze`.

This is `n` times the Hansen-normalized LIML structural-error score with the
finite-sample adjustment `µ̂_n / n`. -/
noncomputable def weakIVLIMLWeakScaledScore
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (limlMuHat : ℕ → Ω → ℝ)
    (m : ℕ) (ω : Ω) : k → ℝ :=
  (m : ℝ) •
    weakIVLIMLNormalizedScore Z X e (weakIVLIMLFiniteSampleMu limlMuHat) m ω

section FiniteSampleWeakIVMeasurability

omit [IsProbabilityMeasure μ] in
private theorem weakIV_stackScalar_aestronglyMeasurable
    {n : ℕ} {Y : ℕ → Ω → ℝ}
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ) :
    AEStronglyMeasurable (fun ω => (fun i : Fin n => Y i.val ω)) μ := by
  rw [aestronglyMeasurable_iff_aemeasurable]
  rw [aemeasurable_pi_iff]
  intro i
  exact (hY i.val).aemeasurable

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
omit [IsProbabilityMeasure μ] in
/-- Row measurability implies measurability of the weak-IV OLS normalized
bread `n^{-1}X'X`. -/
theorem weakIVOLSNormalizedBread_aestronglyMeasurable_of_rows
    {X : ℕ → Ω → k → ℝ}
    (hX : ∀ i, AEStronglyMeasurable (X i) μ) :
    ∀ m, AEStronglyMeasurable
      (fun ω => weakIVOLSNormalizedBread X m ω) μ := by
  intro m
  have hXmat : AEStronglyMeasurable
      (fun ω => stackRegressors X m ω) μ := by
    simpa [stackRegressors] using
      (stackMatrix_aestronglyMeasurable (μ := μ) (n := m) hX)
  have hXt : AEStronglyMeasurable
      (fun ω => (stackRegressors X m ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hXmat
  have hGram : AEStronglyMeasurable
      (fun ω => (stackRegressors X m ω)ᵀ * stackRegressors X m ω) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXt.prodMk hXmat)
  have hScaled : AEStronglyMeasurable
      (fun ω => (Fintype.card (Fin m) : ℝ)⁻¹ •
        ((stackRegressors X m ω)ᵀ * stackRegressors X m ω)) μ :=
    hGram.const_smul (Fintype.card (Fin m) : ℝ)⁻¹
  simpa [weakIVOLSNormalizedBread, sampleGram] using hScaled

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
omit [IsProbabilityMeasure μ] in
/-- Row measurability implies measurability of the weak-IV OLS normalized
structural-error score `n^{-1}X'e`. -/
theorem weakIVOLSNormalizedScore_aestronglyMeasurable_of_rows
    {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ) :
    ∀ m, AEStronglyMeasurable
      (fun ω => weakIVOLSNormalizedScore X e m ω) μ := by
  intro m
  have hXmat : AEStronglyMeasurable
      (fun ω => stackRegressors X m ω) μ := by
    simpa [stackRegressors] using
      (stackMatrix_aestronglyMeasurable (μ := μ) (n := m) hX)
  have hevec : AEStronglyMeasurable
      (fun ω => stackErrors e m ω) μ := by
    simpa [stackErrors] using
      (weakIV_stackScalar_aestronglyMeasurable (μ := μ) (n := m) he)
  have hXt : AEStronglyMeasurable
      (fun ω => (stackRegressors X m ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hXmat
  have hCross : AEStronglyMeasurable
      (fun ω => (stackRegressors X m ω)ᵀ *ᵥ stackErrors e m ω) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXt.prodMk hevec)
  have hScaled : AEStronglyMeasurable
      (fun ω => (Fintype.card (Fin m) : ℝ)⁻¹ •
        ((stackRegressors X m ω)ᵀ *ᵥ stackErrors e m ω)) μ :=
    hCross.const_smul (Fintype.card (Fin m) : ℝ)⁻¹
  simpa [weakIVOLSNormalizedScore, sampleCrossMoment] using hScaled

omit [IsProbabilityMeasure μ] in
private theorem weakIV_instrumentProjectionStar_aestronglyMeasurable
    {n : ℕ} {Zmat : Ω → Matrix (Fin n) l ℝ}
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
  have hLeft : AEStronglyMeasurable
      (fun ω => Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hZmat.prodMk hZZinv)
  have hProj : AEStronglyMeasurable
      (fun ω => Zmat ω * ((Zmat ω)ᵀ * Zmat ω)⁻¹ * (Zmat ω)ᵀ) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hLeft.prodMk hZt)
  simpa [instrumentProjectionStar, Matrix.mul_assoc] using hProj

omit [IsProbabilityMeasure μ] in
private theorem weakIV_limlWeightMatrixStar_aestronglyMeasurable
    {n : ℕ} {Zmat : Ω → Matrix (Fin n) l ℝ} {muHat : Ω → ℝ}
    (hZmat : AEStronglyMeasurable Zmat μ)
    (hmu : AEStronglyMeasurable muHat μ) :
    AEStronglyMeasurable
      (fun ω => limlWeightMatrixStar (Zmat ω) (muHat ω)) μ := by
  have hP :=
    weakIV_instrumentProjectionStar_aestronglyMeasurable
      (μ := μ) (Zmat := Zmat) hZmat
  have hResid : AEStronglyMeasurable
      (fun ω => (1 : Matrix (Fin n) (Fin n) ℝ) -
        instrumentProjectionStar (Zmat ω)) μ :=
    aestronglyMeasurable_const.sub hP
  exact hP.sub (hmu.smul hResid)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
omit [IsProbabilityMeasure μ] in
private theorem weakIV_limlNormalizedMomentMatrixStar_aestronglyMeasurable
    {n : ℕ} {Zmat : Ω → Matrix (Fin n) l ℝ}
    {Xmat : Ω → Matrix (Fin n) k ℝ} {muHat : Ω → ℝ}
    (hZmat : AEStronglyMeasurable Zmat μ)
    (hXmat : AEStronglyMeasurable Xmat μ)
    (hmu : AEStronglyMeasurable muHat μ) :
    AEStronglyMeasurable
      (fun ω => limlNormalizedMomentMatrixStar (Zmat ω) (Xmat ω) (muHat ω)) μ := by
  have hW :=
    weakIV_limlWeightMatrixStar_aestronglyMeasurable
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
  have hScaled : AEStronglyMeasurable
      (fun ω => (Fintype.card (Fin n) : ℝ)⁻¹ •
        ((Xmat ω)ᵀ * limlWeightMatrixStar (Zmat ω) (muHat ω) * Xmat ω)) μ :=
    hM.const_smul (Fintype.card (Fin n) : ℝ)⁻¹
  simpa [limlNormalizedMomentMatrixStar, limlMomentMatrixStar] using hScaled

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
omit [IsProbabilityMeasure μ] in
private theorem weakIV_limlNormalizedMomentVectorStar_aestronglyMeasurable
    {n : ℕ} {Zmat : Ω → Matrix (Fin n) l ℝ}
    {Xmat : Ω → Matrix (Fin n) k ℝ} {evec : Ω → Fin n → ℝ}
    {muHat : Ω → ℝ}
    (hZmat : AEStronglyMeasurable Zmat μ)
    (hXmat : AEStronglyMeasurable Xmat μ)
    (hevec : AEStronglyMeasurable evec μ)
    (hmu : AEStronglyMeasurable muHat μ) :
    AEStronglyMeasurable
      (fun ω => limlNormalizedMomentVectorStar
        (Zmat ω) (Xmat ω) (evec ω) (muHat ω)) μ := by
  have hW :=
    weakIV_limlWeightMatrixStar_aestronglyMeasurable
      (μ := μ) (Zmat := Zmat) hZmat hmu
  have hXt : AEStronglyMeasurable (fun ω => (Xmat ω)ᵀ) μ :=
    (continuous_id.matrix_transpose).comp_aestronglyMeasurable hXmat
  have hXtW : AEStronglyMeasurable
      (fun ω => (Xmat ω)ᵀ * limlWeightMatrixStar (Zmat ω) (muHat ω)) μ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXt.prodMk hW)
  have hV : AEStronglyMeasurable
      (fun ω => ((Xmat ω)ᵀ * limlWeightMatrixStar (Zmat ω) (muHat ω)) *ᵥ
        evec ω) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXtW.prodMk hevec)
  have hScaled : AEStronglyMeasurable
      (fun ω => (Fintype.card (Fin n) : ℝ)⁻¹ •
        (((Xmat ω)ᵀ * limlWeightMatrixStar (Zmat ω) (muHat ω)) *ᵥ evec ω)) μ :=
    hV.const_smul (Fintype.card (Fin n) : ℝ)⁻¹
  simpa [limlNormalizedMomentVectorStar, limlMomentVectorStar] using hScaled

omit [IsProbabilityMeasure μ] in
private theorem weakIV_limlBetaStar_aestronglyMeasurable
    {n : ℕ} {Zmat : Ω → Matrix (Fin n) l ℝ}
    {Xmat : Ω → Matrix (Fin n) k ℝ} {yvec : Ω → Fin n → ℝ}
    {muHat : Ω → ℝ}
    (hZmat : AEStronglyMeasurable Zmat μ)
    (hXmat : AEStronglyMeasurable Xmat μ)
    (hyvec : AEStronglyMeasurable yvec μ)
    (hmu : AEStronglyMeasurable muHat μ) :
    AEStronglyMeasurable
      (fun ω => limlBetaStar (Zmat ω) (Xmat ω) (yvec ω) (muHat ω)) μ := by
  have hW :=
    weakIV_limlWeightMatrixStar_aestronglyMeasurable
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
      (fun ω => ((Xmat ω)ᵀ * limlWeightMatrixStar (Zmat ω) (muHat ω) *
        Xmat ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv hM
  have hV : AEStronglyMeasurable
      (fun ω => ((Xmat ω)ᵀ * limlWeightMatrixStar (Zmat ω) (muHat ω)) *ᵥ
        yvec ω) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hXtW.prodMk hyvec)
  have hBeta : AEStronglyMeasurable
      (fun ω => ((Xmat ω)ᵀ * limlWeightMatrixStar (Zmat ω) (muHat ω) *
          Xmat ω)⁻¹ *ᵥ
        (((Xmat ω)ᵀ * limlWeightMatrixStar (Zmat ω) (muHat ω)) *ᵥ
          yvec ω)) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hMinv.prodMk hV)
  simpa [limlBetaStar, limlMomentMatrixStar, limlMomentVectorStar] using hBeta

omit [IsProbabilityMeasure μ] in
private theorem weakIV_finiteSampleMu_aestronglyMeasurable
    {limlMuHat : ℕ → Ω → ℝ}
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ) :
    ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLFiniteSampleMu limlMuHat m ω) μ := by
  intro m
  simpa [weakIVLIMLFiniteSampleMu, smul_eq_mul] using
    (hMu m).const_smul ((m : ℝ)⁻¹)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
omit [IsProbabilityMeasure μ] in
/-- Row measurability and measurability of the scaled LIML eigenvalue imply
measurability of Hansen's weak-IV-scaled LIML bread. -/
theorem weakIVLIMLWeakScaledBread_aestronglyMeasurable_of_rows
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ) :
    ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ := by
  intro m
  have hZmat : AEStronglyMeasurable
      (fun ω => stackRegressors Z m ω) μ := by
    simpa [stackRegressors] using
      (stackMatrix_aestronglyMeasurable (μ := μ) (n := m) hZ)
  have hXmat : AEStronglyMeasurable
      (fun ω => stackRegressors X m ω) μ := by
    simpa [stackRegressors] using
      (stackMatrix_aestronglyMeasurable (μ := μ) (n := m) hX)
  have hmu :=
    weakIV_finiteSampleMu_aestronglyMeasurable (μ := μ)
      (limlMuHat := limlMuHat) hMu m
  have hNorm :=
    weakIV_limlNormalizedMomentMatrixStar_aestronglyMeasurable
      (μ := μ) (Zmat := fun ω => stackRegressors Z m ω)
      (Xmat := fun ω => stackRegressors X m ω)
      (muHat := fun ω => weakIVLIMLFiniteSampleMu limlMuHat m ω)
      hZmat hXmat hmu
  simpa [weakIVLIMLWeakScaledBread] using hNorm.const_smul (m : ℝ)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
omit [IsProbabilityMeasure μ] in
/-- Row measurability and measurability of the scaled LIML eigenvalue imply
measurability of Hansen's weak-IV-scaled LIML structural-error score. -/
theorem weakIVLIMLWeakScaledScore_aestronglyMeasurable_of_rows
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ) :
    ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ := by
  intro m
  have hZmat : AEStronglyMeasurable
      (fun ω => stackRegressors Z m ω) μ := by
    simpa [stackRegressors] using
      (stackMatrix_aestronglyMeasurable (μ := μ) (n := m) hZ)
  have hXmat : AEStronglyMeasurable
      (fun ω => stackRegressors X m ω) μ := by
    simpa [stackRegressors] using
      (stackMatrix_aestronglyMeasurable (μ := μ) (n := m) hX)
  have hevec : AEStronglyMeasurable
      (fun ω => stackErrors e m ω) μ := by
    simpa [stackErrors] using
      (weakIV_stackScalar_aestronglyMeasurable (μ := μ) (n := m) he)
  have hmu :=
    weakIV_finiteSampleMu_aestronglyMeasurable (μ := μ)
      (limlMuHat := limlMuHat) hMu m
  have hNorm :=
    weakIV_limlNormalizedMomentVectorStar_aestronglyMeasurable
      (μ := μ) (Zmat := fun ω => stackRegressors Z m ω)
      (Xmat := fun ω => stackRegressors X m ω)
      (evec := fun ω => stackErrors e m ω)
      (muHat := fun ω => weakIVLIMLFiniteSampleMu limlMuHat m ω)
      hZmat hXmat hevec hmu
  simpa [weakIVLIMLWeakScaledScore] using hNorm.const_smul (m : ℝ)

omit [IsProbabilityMeasure μ] in
/-- Row measurability and measurability of the scaled LIML eigenvalue imply
measurability of the finite-sample LIML Star estimator used in Theorem 12.18. -/
theorem weakIVLIMLBetaStar_aestronglyMeasurable_of_rows
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (hY : ∀ i, AEStronglyMeasurable (Y i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ) :
    ∀ m, AEStronglyMeasurable
      (fun ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      μ := by
  intro m
  have hZmat : AEStronglyMeasurable
      (fun ω => stackRegressors Z m ω) μ := by
    simpa [stackRegressors] using
      (stackMatrix_aestronglyMeasurable (μ := μ) (n := m) hZ)
  have hXmat : AEStronglyMeasurable
      (fun ω => stackRegressors X m ω) μ := by
    simpa [stackRegressors] using
      (stackMatrix_aestronglyMeasurable (μ := μ) (n := m) hX)
  have hYvec : AEStronglyMeasurable
      (fun ω => stackOutcomes Y m ω) μ := by
    simpa [stackOutcomes] using
      (weakIV_stackScalar_aestronglyMeasurable (μ := μ) (n := m) hY)
  have hmu :=
    weakIV_finiteSampleMu_aestronglyMeasurable (μ := μ)
      (limlMuHat := limlMuHat) hMu m
  exact
    weakIV_limlBetaStar_aestronglyMeasurable
      (μ := μ) (Zmat := fun ω => stackRegressors Z m ω)
      (Xmat := fun ω => stackRegressors X m ω)
      (yvec := fun ω => stackOutcomes Y m ω)
      (muHat := fun ω => weakIVLIMLFiniteSampleMu limlMuHat m ω)
      hZmat hXmat hYvec hmu

end FiniteSampleWeakIVMeasurability

/-- Random weak-IV LIML bread limit,
`(Q_ZZ C + Ξ₂)' Q_ZZ^{-1} (Q_ZZ C + Ξ₂) - μ*Σ₂₂`. -/
noncomputable def weakIVLIMLLimitBread
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ)
    (mustar : ℝ) (Sigma22 : Matrix k k ℝ) : Matrix k k ℝ :=
  weakIV2SLSLimitBread QZZ C Xi2 - mustar • Sigma22

/-- Random weak-IV LIML structural-error score limit,
`(Q_ZZ C + Ξ₂)' Q_ZZ^{-1} ξ_e - μ*Σ₂e`. -/
noncomputable def weakIVLIMLLimitScore
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ) (xie : l → ℝ)
    (mustar : ℝ) (Sigma2e : k → ℝ) : k → ℝ :=
  weakIV2SLSLimitScore QZZ C Xi2 xie - mustar • Sigma2e

/-- Root-scaled reduced-form projected moment for the weak-IV LIML Rayleigh
problem.

The first column is `n^{-1/2}Z'Y = (n^{-1/2}Z'X)β + n^{-1/2}Z'e`; the right
block is `n^{-1/2}Z'X`.  This is the sample counterpart of Hansen's
`Q_Z C β + ξ`, expressed through the structural-error limit object `ξe`. -/
noncomputable def weakIVRootReducedFormProjectedMoment
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (β : k → ℝ) (m : ℕ) (ω : Ω) : Matrix l (Sum Unit k) ℝ
  | i, Sum.inl _ =>
      (weakIV2SLSRootScaledFirstStage Z X m ω *ᵥ β) i +
        weakIV2SLSRootScaledInstrumentScore Z e m ω i
  | i, Sum.inr j => weakIV2SLSRootScaledFirstStage Z X m ω i j

/-- Reduced-form weak-IV Gaussian/local-to-zero limit matrix entering Hansen's
LIML Rayleigh problem.

The first column is `(Q_ZZ C + Ξ₂)β + ξe`, so the full `µ*` surface records the
structural-error Gaussian component rather than only the first-stage block. -/
noncomputable def weakIVReducedFormLimit
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ)
    (xie : l → ℝ) (β : k → ℝ) : Matrix l (Sum Unit k) ℝ
  | i, Sum.inl _ => (weakIVFirstStageLimit QZZ C Xi2 *ᵥ β) i + xie i
  | i, Sum.inr j => weakIVFirstStageLimit QZZ C Xi2 i j

/-- Full reduced-form Rayleigh numerator matrix for Hansen's `µ*`, based on
the limit matrix `Q_ZZ C β + ξ`. -/
noncomputable def weakIVReducedFormRayleighMatrix
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ)
    (xie : l → ℝ) (β : k → ℝ) : Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  limlRayleighMatrix QZZ (weakIVReducedFormLimit QZZ C Xi2 xie β)

/-- Full reduced-form Rayleigh quotient for Hansen's `µ*`.  The denominator
uses the reduced-form covariance matrix for `(u₁,u₂)`. -/
noncomputable def weakIVReducedFormRayleighQuotient
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ)
    (xie : l → ℝ) (β : k → ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ)
    (γ : Sum Unit k → ℝ) : ℝ :=
  limlRayleighQuotient
    (weakIVReducedFormRayleighMatrix QZZ C Xi2 xie β) Sigma γ

/-- Sample primitive pair for the reduced-form LIML Rayleigh problem:
`(Q̂_ZZ, n^{-1/2}Z'[Y X])`. -/
noncomputable def weakIVReducedFormRayleighPrimitive
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (β : k → ℝ) (m : ℕ) (ω : Ω) :
    Matrix l l ℝ × Matrix l (Sum Unit k) ℝ :=
  (sampleQZZ (stackRegressors Z m ω),
    weakIVRootReducedFormProjectedMoment Z X e β m ω)

/-- Limit primitive pair for the reduced-form LIML Rayleigh problem:
`(Q_ZZ, Q_ZZ C β + ξ)`. -/
noncomputable def weakIVReducedFormRayleighLimitPrimitive
    (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (β : k → ℝ) (η : Ωlim) :
    Matrix l l ℝ × Matrix l (Sum Unit k) ℝ :=
  (QZZ, weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β)

/-- Reduced-form LIML Rayleigh matrix assembled from a primitive weak-IV
first-stage/score pair `(A, s_Ze)`.

The first column is `Aβ + s_Ze`; the remaining columns are `A`.  This is the
common deterministic surface behind both the sample primitive
`(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)` and its local-to-zero Gaussian limit. -/
noncomputable def weakIVReducedFormProjectedMomentFromPrimitive
    (A : Matrix l k ℝ) (zScore : l → ℝ) (β : k → ℝ) :
    Matrix l (Sum Unit k) ℝ
  | i, Sum.inl _ => (A *ᵥ β) i + zScore i
  | i, Sum.inr j => A i j

/-- Primitive-to-reduced-form bridge for the LIML Rayleigh problem. -/
noncomputable def weakIVReducedFormRayleighPrimitiveFromRootPrimitive
    (β : k → ℝ) (p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) :
    Matrix l l ℝ × Matrix l (Sum Unit k) ℝ :=
  (p.1, weakIVReducedFormProjectedMomentFromPrimitive p.2.1 p.2.2 β)

omit [Fintype l] [DecidableEq k] [DecidableEq l] [MeasurableSpace Ω] in
/-- The generic reduced-form primitive bridge specializes to the sample
Rayleigh primitive used for Hansen's finite-sample LIML eigenvalue. -/
theorem weakIVReducedFormRayleighPrimitiveFromRootPrimitive_sample_eq
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (β : k → ℝ) (m : ℕ) (ω : Ω) :
    weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
        (weakIV2SLSRootPrimitiveMoments Z X e m ω) =
      weakIVReducedFormRayleighPrimitive Z X e β m ω := by
  rfl

omit [DecidableEq k] [DecidableEq l] [MeasurableSpace Ωlim] in
/-- The generic reduced-form primitive bridge specializes to Hansen's limiting
reduced-form Rayleigh primitive. -/
theorem weakIVReducedFormRayleighPrimitiveFromRootPrimitive_limit_eq
    (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (β : k → ℝ) (η : Ωlim) :
    weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
        (weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η) =
      weakIVReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η := by
  rfl

/-- Joint primitive surface for the LIML root-assembly CMT:
root-scaled 2SLS primitive moments together with the OLS bread/score pair. -/
noncomputable def weakIVLIMLRootOLSPrimitiveMoments
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (m : ℕ) (ω : Ω) :
    (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) × (Matrix k k ℝ × (k → ℝ)) :=
  (weakIV2SLSRootPrimitiveMoments Z X e m ω,
    (weakIVOLSNormalizedBread X m ω, weakIVOLSNormalizedScore X e m ω))

/-- Joint primitive limit for the LIML root-assembly CMT. -/
noncomputable def weakIVLIMLRootOLSPrimitiveLimit
    (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) (η : Ωlim) :
    (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) × (Matrix k k ℝ × (k → ℝ)) :=
  (weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η, (Sigma22, Sigma2e))

/-- Continuous-map target from primitive root/OLS moments and a Rayleigh
selector to the root-assembly tuple used by the weak-IV LIML moment CMT. -/
noncomputable def weakIVLIMLRootAssemblyFromPrimitiveRayleighMap
    (β : k → ℝ)
    (muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ)
    (p :
      (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
        (Matrix k k ℝ × (k → ℝ))) :
    ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ :=
  ((weakIV2SLSProjectedBreadScoreFromPrimitive p.1, p.2),
    muSelector (weakIVReducedFormRayleighPrimitiveFromRootPrimitive β p.1))

omit [DecidableEq k] in
/-- Continuous-mapping bridge from the sample reduced-form Rayleigh problem to
Hansen's limiting LIML eigenvalue adjustment.

The hypothesis `muSelector` is the continuous argmin/eigenvalue selector for
the reduced-form Rayleigh primitive `(Q, R)`.  The sample and limit minimizer
certificates keep the theorem tied to the LIML Rayleigh problem; the CMT part
then derives `µ̂_n ⇒ µ*` without using the estimator limit as an assumption. -/
theorem weakIV_limlMuHat_tendstoInDistribution_of_reducedForm_rayleigh_argmin
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hprimitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l (Sum Unit k) ℝ) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        weakIVReducedFormRayleighPrimitive Z X e β m ω)
      atTop
      (fun η => weakIVReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)
      (fun _ => μ) ν)
    (hselector_cont : Continuous muSelector)
    (hliml_selector : ∀ m ω,
      limlMuHat m ω =
        muSelector (weakIVReducedFormRayleighPrimitive Z X e β m ω))
    (hmustar_selector : ∀ η,
      mustar η =
        muSelector (weakIVReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η))
    (hsample_minimizer : ∀ m ω,
      LIMLRayleighMinimizer
        (limlRayleighMatrix
          (sampleQZZ (stackRegressors Z m ω))
          (weakIVRootReducedFormProjectedMoment Z X e β m ω))
        Sigma (limlMuHat m ω))
    (hlimit_minimizer : ∀ η,
      LIMLRayleighMinimizer
        (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
        Sigma (mustar η)) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) => limlMuHat m ω)
      atTop mustar (fun _ => μ) ν ∧
    (∀ m ω,
      LIMLRayleighMinimizer
        (limlRayleighMatrix
          (sampleQZZ (stackRegressors Z m ω))
          (weakIVRootReducedFormProjectedMoment Z X e β m ω))
        Sigma (limlMuHat m ω)) ∧
    (∀ η,
      LIMLRayleighMinimizer
        (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
        Sigma (mustar η)) := by
  have hraw := hprimitive.continuous_comp hselector_cont
  have hconv : TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) => limlMuHat m ω)
      atTop mustar (fun _ => μ) ν := by
    refine TendstoInDistribution.congr ?_ ?_ hraw
    · intro m
      exact ae_of_all μ (fun ω => by
        simp [hliml_selector m ω])
    · exact ae_of_all ν (fun η => by
        simp [hmustar_selector η])
  exact ⟨hconv, hsample_minimizer, hlimit_minimizer⟩

/-- Root-assembled LIML bread for the weak-IV limit:
`(n^{-1/2}X'Z)Q̂_ZZ^{-1}(n^{-1/2}Z'X) - μ̂ n^{-1}X'X`.

This is the CMT-facing surface obtained from the root 2SLS projected bread,
the OLS bread, and the scaled LIML eigenvalue adjustment. -/
noncomputable def weakIVLIMLRootAssembledBread
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (limlMuHat : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : Matrix k k ℝ :=
  weakIV2SLSRootScaledBread Z X m ω -
    limlMuHat m ω • weakIVOLSNormalizedBread X m ω

/-- Root-assembled LIML structural-error score:
`(n^{-1/2}X'Z)Q̂_ZZ^{-1}(n^{-1/2}Z'e) - μ̂ n^{-1}X'e`. -/
noncomputable def weakIVLIMLRootAssembledScore
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (limlMuHat : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : k → ℝ :=
  weakIV2SLSRootScaledScore Z X e m ω -
    limlMuHat m ω • weakIVOLSNormalizedScore X e m ω

/-- Continuous assembly map from root 2SLS bread/score, OLS bread/score, and
the scaled LIML eigenvalue adjustment to the LIML bread/score pair. -/
noncomputable def weakIVLIMLRootAssembledBreadScoreMap
    (p :
      ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ) :
    Matrix k k ℝ × (k → ℝ) :=
  let rootPair := p.1.1
  let olsPair := p.1.2
  let mu := p.2
  (rootPair.1 - mu • olsPair.1, rootPair.2 - mu • olsPair.2)

/-- The 2SLS weak-IV drift is the inverse-bread times score form. -/
theorem weakIV2SLSBias_eq_limitBread_inv_mul_score
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ) (xie : l → ℝ) :
    weakIV2SLSBias QZZ C Xi2 xie =
      (weakIV2SLSLimitBread QZZ C Xi2)⁻¹ *ᵥ
        weakIV2SLSLimitScore QZZ C Xi2 xie := by
  simp [weakIV2SLSBias, weakIV2SLSLimitBread, weakIV2SLSLimitScore]

/-- The LIML weak-IV drift is the inverse limiting LIML bread times the
limiting LIML structural-error score. -/
theorem weakIVLIMLBias_eq_limitBread_inv_mul_score
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ) (xie : l → ℝ)
    (mustar : ℝ) (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) :
    weakIVLIMLBias QZZ C Xi2 xie mustar Sigma22 Sigma2e =
      (weakIVLIMLLimitBread QZZ C Xi2 mustar Sigma22)⁻¹ *ᵥ
        weakIVLIMLLimitScore QZZ C Xi2 xie mustar Sigma2e := by
  simp [weakIVLIMLBias, weakIVLIMLLimitBread, weakIVLIMLLimitScore,
    weakIV2SLSLimitBread, weakIV2SLSLimitScore]

omit [DecidableEq k] in
/-- LIML root-assembly CMT for Hansen Theorem 12.18.

Joint convergence of the root 2SLS bread/score pair, the OLS bread/score pair,
and the scaled LIML eigenvalue adjustment implies joint convergence of the
root-assembled LIML bread/score pair.  The limiting score contains Hansen's
`ξe` through `weakIV2SLSLimitScore`. -/
theorem weakIV_liml_root_assembled_bread_score_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hjoint : TendstoInDistribution
      (E := ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ)
      (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        ((((weakIV2SLSRootScaledBread Z X m ω,
            weakIV2SLSRootScaledScore Z X e m ω),
           (weakIVOLSNormalizedBread X m ω,
            weakIVOLSNormalizedScore X e m ω)),
          limlMuHat m ω) :
          ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ))
      atTop
      (fun η =>
        ((((weakIV2SLSLimitBread QZZ C (Xi2 η),
            weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)),
           (Sigma22, Sigma2e)),
          mustar η) :
          ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ))
      (fun _ => μ) ν) :
    TendstoInDistribution
      (E := Matrix k k ℝ × (k → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        ((weakIVLIMLRootAssembledBread Z X limlMuHat m ω,
          weakIVLIMLRootAssembledScore Z X e limlMuHat m ω) :
          Matrix k k ℝ × (k → ℝ)))
      atTop
      (fun η =>
        ((weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22,
          weakIVLIMLLimitScore QZZ C (Xi2 η) (xie η) (mustar η) Sigma2e) :
          Matrix k k ℝ × (k → ℝ)))
      (fun _ => μ) ν := by
  have hcont :
      Continuous
        (weakIVLIMLRootAssembledBreadScoreMap (k := k)) := by
    unfold weakIVLIMLRootAssembledBreadScoreMap
    fun_prop
  have hraw := hjoint.continuous_comp hcont
  simpa [weakIVLIMLRootAssembledBreadScoreMap,
    weakIVLIMLRootAssembledBread, weakIVLIMLRootAssembledScore,
    weakIVLIMLLimitBread, weakIVLIMLLimitScore] using hraw

omit [DecidableEq k] in
private theorem weakIV_twoSLS_primitive_qzz_singular_measurable :
    MeasurableSet
      {p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) | ¬ IsUnit (p.1).det} := by
  have hdet : Measurable
      (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) => (p.1).det) :=
    (Continuous.matrix_det continuous_fst).measurable
  rw [show {p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) | ¬ IsUnit (p.1).det} =
      (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) => (p.1).det) ⁻¹' {0} by
        ext p
        simp [isUnit_iff_ne_zero]]
  exact hdet (measurableSet_singleton (0 : ℝ))

omit [DecidableEq k] in
private theorem weakIV_twoSLS_projected_bread_score_map_measurable :
    Measurable
      (weakIV2SLSProjectedBreadScoreFromPrimitive
        (k := k) (l := l)) := by
  have hQdet : Measurable
      (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) => (p.1).det) :=
    (Continuous.matrix_det continuous_fst).measurable
  have hQadj : Measurable
      (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) => (p.1).adjugate) :=
    (Continuous.matrix_adjugate continuous_fst).measurable
  have hQinv_det : Measurable
      (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) =>
        Ring.inverse (p.1).det) := by
    have heq :
        (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) =>
          Ring.inverse (p.1).det) =
          (fun p => ((p.1).det)⁻¹) := by
      funext p
      exact Ring.inverse_eq_inv _
    rw [heq]
    exact measurable_inv.comp hQdet
  have hQinv : Measurable
      (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) => p.1⁻¹) := by
    have heq :
        (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) => p.1⁻¹) =
          (fun p => Ring.inverse (p.1).det • (p.1).adjugate) := by
      funext p
      exact Matrix.inv_def p.1
    rw [heq]
    exact hQinv_det.smul hQadj
  have hQZX : Measurable
      (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) => p.2.1) :=
    (continuous_fst.comp continuous_snd).measurable
  have hQZXt : Measurable
      (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) => (p.2.1)ᵀ) :=
    ((continuous_fst.comp continuous_snd).matrix_transpose).measurable
  have hzScore : Measurable
      (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) => p.2.2) :=
    (continuous_snd.comp continuous_snd).measurable
  have hleft : Measurable
      (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) =>
        (p.2.1)ᵀ * p.1⁻¹) :=
    (Continuous.matrix_mul continuous_fst continuous_snd).measurable.comp
      (hQZXt.prodMk hQinv)
  have hbread : Measurable
      (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) =>
        (p.2.1)ᵀ * p.1⁻¹ * p.2.1) :=
    (Continuous.matrix_mul continuous_fst continuous_snd).measurable.comp
      (hleft.prodMk hQZX)
  have hscore : Measurable
      (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) =>
        ((p.2.1)ᵀ * p.1⁻¹) *ᵥ p.2.2) :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp
      (hleft.prodMk hzScore)
  exact hbread.prodMk hscore

omit [Fintype k] [DecidableEq k] in
private theorem weakIV_twoSLS_projected_bread_score_map_continuousAt_of_qzz_nonsingular
    (p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ))
    (hp : IsUnit (p.1).det) :
    ContinuousAt
      (weakIV2SLSProjectedBreadScoreFromPrimitive
        (k := k) (l := l)) p := by
  have hQinv : ContinuousAt
      (fun q : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) => q.1⁻¹) p := by
    have hInv : ContinuousAt (fun A : Matrix l l ℝ => A⁻¹) p.1 := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hp.ne_zero
    exact hInv.comp continuousAt_fst
  have hQZX : ContinuousAt
      (fun q : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) => q.2.1) p :=
    (continuous_fst.comp continuous_snd).continuousAt
  have hQZXt : ContinuousAt
      (fun q : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) => (q.2.1)ᵀ) p :=
    ((continuous_fst.comp continuous_snd).matrix_transpose).continuousAt
  have hzScore : ContinuousAt
      (fun q : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) => q.2.2) p :=
    (continuous_snd.comp continuous_snd).continuousAt
  have hleft : ContinuousAt
      (fun q : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) =>
        (q.2.1)ᵀ * q.1⁻¹) p :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hQZXt.prodMk hQinv)
  have hbread : ContinuousAt
      (fun q : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) =>
        (q.2.1)ᵀ * q.1⁻¹ * q.2.1) p :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hleft.prodMk hQZX)
  have hscore : ContinuousAt
      (fun q : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) =>
        ((q.2.1)ᵀ * q.1⁻¹) *ᵥ q.2.2) p :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).continuousAt.comp
      (hleft.prodMk hzScore)
  exact hbread.prodMk hscore

omit [DecidableEq k] in
/-- Primitive first-stage/score CMT for Hansen Theorem 12.18.

If the lower-level weak-IV moments `(Q̂_ZZ, Q̂_ZX, n⁻¹ Z'e)` converge jointly to
`(Q_ZZ, Q_ZZ C + Ξ₂, ξ_e)` and the fixed `Q_ZZ` limit is nonsingular, then the
projected 2SLS bread and projected structural-error score converge jointly to
Hansen's random 2SLS bread/score limit. -/
theorem weakIV_twoSLS_projected_bread_score_tendstoInDistribution_of_primitive
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    (hPrimitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det) :
    TendstoInDistribution
      (E := Matrix k k ℝ × (k → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        ((weakIV2SLSNormalizedBread Z X m ω,
          weakIV2SLSNormalizedScore Z X e m ω) :
          Matrix k k ℝ × (k → ℝ)))
      atTop
      (fun η =>
        ((weakIV2SLSLimitBread QZZ C (Xi2 η),
          weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)) :
          Matrix k k ℝ × (k → ℝ)))
      (fun _ => μ) ν := by
  let D : Set (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) :=
    {p | ¬ IsUnit (p.1).det}
  have hD_meas : MeasurableSet D := by
    simpa [D] using
      (weakIV_twoSLS_primitive_qzz_singular_measurable (k := k) (l := l))
  have hD_null :
      (ν.map (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)) D = 0 := by
    rw [Measure.map_apply_of_aemeasurable hPrimitive.aemeasurable_limit hD_meas]
    have hQZZ_ne : QZZ.det ≠ 0 := hQZZ.ne_zero
    have hpre_empty :
        (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η) ⁻¹' D =
          (∅ : Set Ωlim) := by
      ext η
      simp [D, weakIV2SLSPrimitiveLimit, isUnit_iff_ne_zero, hQZZ_ne]
    rw [hpre_empty]
    simp
  have hcont :
      ∀ p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ), p ∉ D →
        ContinuousAt
          (weakIV2SLSProjectedBreadScoreFromPrimitive (k := k) (l := l)) p := by
    intro p hp
    have hpunit : IsUnit (p.1).det := by
      simpa [D] using hp
    exact
      weakIV_twoSLS_projected_bread_score_map_continuousAt_of_qzz_nonsingular
        (k := k) (l := l) p hpunit
  have hraw := tendstoInDistribution_ae_continuous_comp
    (X := fun (m : ℕ) (ω : Ω) => weakIV2SLSPrimitiveMoments Z X e m ω)
    (Z := fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
    hPrimitive
    (weakIV_twoSLS_projected_bread_score_map_measurable (k := k) (l := l))
    hD_null hcont
  simpa [weakIV2SLSProjectedBreadScoreFromPrimitive, weakIV2SLSPrimitiveMoments,
    weakIV2SLSPrimitiveLimit, weakIV2SLSNormalizedBread, weakIV2SLSNormalizedScore,
    weakIV2SLSLimitBread, weakIV2SLSLimitScore, sampleQXZ, twoSLSBread,
    Matrix.mul_assoc] using hraw

omit [DecidableEq k] in
/-- Root-scaled primitive first-stage/score CMT for Hansen Theorem 12.18.

This is the faithful local-to-zero version of
`weakIV_twoSLS_projected_bread_score_tendstoInDistribution_of_primitive`: the
sample primitive moments are `(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)`, so the
projected bread and score are Hansen's weak-IV objects without an extra
normalization mismatch. -/
theorem weakIV_twoSLS_root_projected_bread_score_tendstoInDistribution_of_primitive
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    (hPrimitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det) :
    TendstoInDistribution
      (E := Matrix k k ℝ × (k → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        ((weakIV2SLSRootScaledBread Z X m ω,
          weakIV2SLSRootScaledScore Z X e m ω) :
          Matrix k k ℝ × (k → ℝ)))
      atTop
      (fun η =>
        ((weakIV2SLSLimitBread QZZ C (Xi2 η),
          weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)) :
          Matrix k k ℝ × (k → ℝ)))
      (fun _ => μ) ν := by
  let D : Set (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) :=
    {p | ¬ IsUnit (p.1).det}
  have hD_meas : MeasurableSet D := by
    simpa [D] using
      (weakIV_twoSLS_primitive_qzz_singular_measurable (k := k) (l := l))
  have hD_null :
      (ν.map (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)) D = 0 := by
    rw [Measure.map_apply_of_aemeasurable hPrimitive.aemeasurable_limit hD_meas]
    have hQZZ_ne : QZZ.det ≠ 0 := hQZZ.ne_zero
    have hpre_empty :
        (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η) ⁻¹' D =
          (∅ : Set Ωlim) := by
      ext η
      simp [D, weakIV2SLSPrimitiveLimit, isUnit_iff_ne_zero, hQZZ_ne]
    rw [hpre_empty]
    simp
  have hcont :
      ∀ p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ), p ∉ D →
        ContinuousAt
          (weakIV2SLSProjectedBreadScoreFromPrimitive (k := k) (l := l)) p := by
    intro p hp
    have hpunit : IsUnit (p.1).det := by
      simpa [D] using hp
    exact
      weakIV_twoSLS_projected_bread_score_map_continuousAt_of_qzz_nonsingular
        (k := k) (l := l) p hpunit
  have hraw := tendstoInDistribution_ae_continuous_comp
    (X := fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
    (Z := fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
    hPrimitive
    (weakIV_twoSLS_projected_bread_score_map_measurable (k := k) (l := l))
    hD_null hcont
  simpa [weakIV2SLSProjectedBreadScoreFromRootPrimitive_eq,
    weakIV2SLSProjectedBreadScoreFromPrimitive, weakIV2SLSRootPrimitiveMoments,
    weakIV2SLSRootScaledBread, weakIV2SLSRootScaledScore,
    weakIV2SLSPrimitiveLimit, weakIV2SLSLimitBread, weakIV2SLSLimitScore,
    Matrix.mul_assoc] using hraw

omit [Fintype l] [DecidableEq k] [DecidableEq l] in
private theorem weakIV_reducedForm_rayleigh_primitive_from_root_continuous
    (β : k → ℝ) :
    Continuous
      (weakIVReducedFormRayleighPrimitiveFromRootPrimitive
        (k := k) (l := l) β) := by
  have hmat : Continuous
      (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) =>
        weakIVReducedFormProjectedMomentFromPrimitive p.2.1 p.2.2 β) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    cases j with
    | inl u =>
        simpa [weakIVReducedFormProjectedMomentFromPrimitive] using
          (by fun_prop :
            Continuous
              (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) =>
                (p.2.1 *ᵥ β) i + p.2.2 i))
    | inr j =>
        simpa [weakIVReducedFormProjectedMomentFromPrimitive] using
          (by fun_prop :
            Continuous
              (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) =>
                p.2.1 i j))
  change Continuous
    (fun p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ) =>
      (p.1, weakIVReducedFormProjectedMomentFromPrimitive p.2.1 p.2.2 β))
  exact continuous_fst.prodMk hmat

omit [DecidableEq k] [DecidableEq l] in
/-- Reduced-form Rayleigh primitive convergence from Hansen's root primitive
local-to-zero first-stage/score convergence.

This is the continuous bridge from
`(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)` to the reduced-form LIML Rayleigh primitive
`(Q̂_ZZ, n^{-1/2}Z'[Y X])` used by the `µ̂_n` selector in Hansen Theorem
12.18. -/
theorem weakIV_reducedForm_rayleigh_primitive_tendstoInDistribution_of_root_primitive
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {β : k → ℝ} {QZZ : Matrix l l ℝ}
    {C : Matrix l k ℝ} {Xi2 : Ωlim → Matrix l k ℝ}
    {xie : Ωlim → l → ℝ}
    (hPrimitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν) :
    TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l (Sum Unit k) ℝ) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        weakIVReducedFormRayleighPrimitive Z X e β m ω)
      atTop
      (fun η => weakIVReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)
      (fun _ => μ) ν := by
  have hraw := hPrimitive.continuous_comp
    (weakIV_reducedForm_rayleigh_primitive_from_root_continuous
      (k := k) (l := l) β)
  refine TendstoInDistribution.congr ?_ ?_ hraw
  · intro m
    exact ae_of_all μ (fun ω => by
      simpa using
        (weakIVReducedFormRayleighPrimitiveFromRootPrimitive_sample_eq
          (k := k) (l := l) Z X e β m ω))
  · exact ae_of_all ν (fun η => by
      simpa using
        (weakIVReducedFormRayleighPrimitiveFromRootPrimitive_limit_eq
          (k := k) (l := l) QZZ C Xi2 xie β η))

omit [DecidableEq k] in
private theorem weakIV_liml_rootAssembly_from_primitive_rayleigh_map_measurable
    (β : k → ℝ)
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hselector_cont : Continuous muSelector) :
    Measurable
      (weakIVLIMLRootAssemblyFromPrimitiveRayleighMap
        (k := k) (l := l) β muSelector) := by
  have hroot : Measurable
      (fun p :
          (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
            (Matrix k k ℝ × (k → ℝ)) =>
        weakIV2SLSProjectedBreadScoreFromPrimitive (k := k) (l := l) p.1) :=
    (weakIV_twoSLS_projected_bread_score_map_measurable (k := k) (l := l)).comp
      measurable_fst
  have hols : Measurable
      (fun p :
          (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
            (Matrix k k ℝ × (k → ℝ)) => p.2) :=
    measurable_snd
  have hmu : Measurable
      (fun p :
          (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
            (Matrix k k ℝ × (k → ℝ)) =>
        muSelector (weakIVReducedFormRayleighPrimitiveFromRootPrimitive β p.1)) :=
    hselector_cont.measurable.comp
      ((weakIV_reducedForm_rayleigh_primitive_from_root_continuous
        (k := k) (l := l) β).measurable.comp measurable_fst)
  simpa [weakIVLIMLRootAssemblyFromPrimitiveRayleighMap] using
    (hroot.prodMk hols).prodMk hmu

omit [DecidableEq k] in
private theorem weakIV_liml_rootAssembly_from_primitive_rayleigh_map_continuousAt_of_qzz_nonsingular
    (β : k → ℝ)
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hselector_cont : Continuous muSelector)
    (p :
      (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
        (Matrix k k ℝ × (k → ℝ)))
    (hp : IsUnit (p.1.1).det) :
    ContinuousAt
      (weakIVLIMLRootAssemblyFromPrimitiveRayleighMap
        (k := k) (l := l) β muSelector) p := by
  have hroot : ContinuousAt
      (fun q :
          (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
            (Matrix k k ℝ × (k → ℝ)) =>
        weakIV2SLSProjectedBreadScoreFromPrimitive (k := k) (l := l) q.1) p :=
    (weakIV_twoSLS_projected_bread_score_map_continuousAt_of_qzz_nonsingular
      (k := k) (l := l) p.1 hp).comp continuousAt_fst
  have hols : ContinuousAt
      (fun q :
          (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
            (Matrix k k ℝ × (k → ℝ)) => q.2) p :=
    continuousAt_snd
  have hmu : ContinuousAt
      (fun q :
          (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
            (Matrix k k ℝ × (k → ℝ)) =>
        muSelector (weakIVReducedFormRayleighPrimitiveFromRootPrimitive β q.1)) p :=
    hselector_cont.continuousAt.comp
      ((weakIV_reducedForm_rayleigh_primitive_from_root_continuous
        (k := k) (l := l) β).continuousAt.comp continuousAt_fst)
  simpa [weakIVLIMLRootAssemblyFromPrimitiveRayleighMap] using
    (hroot.prodMk hols).prodMk hmu

omit [DecidableEq k] in
/-- Primitive root/OLS/Rayleigh-selector CMT for the LIML face of Hansen
Theorem 12.18.

This is the theorem-facing bridge from the primitive local-to-zero moments and
the continuous reduced-form Rayleigh selector to the joint
`((B₂SLS,S₂SLS),(Σ₂₂,Σ₂e),µ̂)` assembly required by the weak-scaled LIML moment
CMT.  The only discontinuity is the usual `Q̂_ZZ` inverse, handled off the
nonsingular `Q_ZZ` limit. -/
theorem weakIV_liml_root_assembly_joint_tendstoInDistribution_of_primitive_rayleigh_selector
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hprimitive : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η =>
        weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hselector_cont : Continuous muSelector)
    (hliml_selector : ∀ m ω,
      limlMuHat m ω =
        muSelector (weakIVReducedFormRayleighPrimitive Z X e β m ω))
    (hmustar_selector : ∀ η,
      mustar η =
        muSelector (weakIVReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)) :
    TendstoInDistribution
      (E := ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ)
      (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        ((((weakIV2SLSRootScaledBread Z X m ω,
            weakIV2SLSRootScaledScore Z X e m ω),
           (weakIVOLSNormalizedBread X m ω,
            weakIVOLSNormalizedScore X e m ω)),
          limlMuHat m ω) :
          ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ))
      atTop
      (fun η =>
        ((((weakIV2SLSLimitBread QZZ C (Xi2 η),
            weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)),
           (Sigma22, Sigma2e)),
          mustar η) :
          ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ))
      (fun _ => μ) ν := by
  let D : Set
      ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
        (Matrix k k ℝ × (k → ℝ))) :=
    {p | ¬ IsUnit (p.1.1).det}
  have hD_meas : MeasurableSet D := by
    have hdet : Measurable
        (fun p :
            (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
              (Matrix k k ℝ × (k → ℝ)) => (p.1.1).det) :=
      (Continuous.matrix_det (continuous_fst.comp continuous_fst)).measurable
    rw [show D =
        (fun p :
            (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
              (Matrix k k ℝ × (k → ℝ)) => (p.1.1).det) ⁻¹' {0} by
          ext p
          simp [D, isUnit_iff_ne_zero]]
    exact hdet (measurableSet_singleton (0 : ℝ))
  have hD_null :
      (ν.map
        (fun η =>
          weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)) D = 0 := by
    rw [Measure.map_apply_of_aemeasurable hprimitive.aemeasurable_limit hD_meas]
    have hQZZ_ne : QZZ.det ≠ 0 := hQZZ.ne_zero
    have hpre_empty :
        (fun η =>
          weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η) ⁻¹' D =
            (∅ : Set Ωlim) := by
      ext η
      simp [D, weakIVLIMLRootOLSPrimitiveLimit, weakIV2SLSPrimitiveLimit,
        isUnit_iff_ne_zero, hQZZ_ne]
    rw [hpre_empty]
    simp
  have hcont : ∀ p :
      (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
        (Matrix k k ℝ × (k → ℝ)),
      p ∉ D →
        ContinuousAt
          (weakIVLIMLRootAssemblyFromPrimitiveRayleighMap
            (k := k) (l := l) β muSelector) p := by
    intro p hp
    have hpunit : IsUnit (p.1.1).det := by
      simpa [D] using hp
    exact
      weakIV_liml_rootAssembly_from_primitive_rayleigh_map_continuousAt_of_qzz_nonsingular
        (k := k) (l := l) β hselector_cont p hpunit
  have hraw := tendstoInDistribution_ae_continuous_comp
    (X := fun (m : ℕ) (ω : Ω) =>
      weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
    (Z := fun η =>
      weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
    hprimitive
    (weakIV_liml_rootAssembly_from_primitive_rayleigh_map_measurable
      (k := k) (l := l) β hselector_cont)
    hD_null hcont
  refine TendstoInDistribution.congr ?_ ?_ hraw
  · intro m
    exact ae_of_all μ (fun ω => by
      change
        weakIVLIMLRootAssemblyFromPrimitiveRayleighMap β muSelector
          (weakIVLIMLRootOLSPrimitiveMoments Z X e m ω) =
        (((weakIV2SLSRootScaledBread Z X m ω,
            weakIV2SLSRootScaledScore Z X e m ω),
           (weakIVOLSNormalizedBread X m ω,
            weakIVOLSNormalizedScore X e m ω)),
          limlMuHat m ω)
      have hred :
        weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
              (weakIV2SLSRootPrimitiveMoments Z X e m ω) =
            weakIVReducedFormRayleighPrimitive Z X e β m ω :=
        weakIVReducedFormRayleighPrimitiveFromRootPrimitive_sample_eq Z X e β m ω
      rw [hliml_selector m ω]
      simp [weakIVLIMLRootAssemblyFromPrimitiveRayleighMap,
        weakIVLIMLRootOLSPrimitiveMoments,
        weakIV2SLSProjectedBreadScoreFromRootPrimitive_eq, hred])
  · exact ae_of_all ν (fun η => by
      change
        weakIVLIMLRootAssemblyFromPrimitiveRayleighMap β muSelector
          (weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η) =
        (((weakIV2SLSLimitBread QZZ C (Xi2 η),
            weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)),
           (Sigma22, Sigma2e)),
          mustar η)
      have hred :
          weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
              (weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η) =
            weakIVReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η :=
        weakIVReducedFormRayleighPrimitiveFromRootPrimitive_limit_eq QZZ C Xi2 xie β η
      have hred' :
          weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
              (QZZ, weakIVFirstStageLimit QZZ C (Xi2 η), xie η) =
            weakIVReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η := by
        simpa [weakIV2SLSPrimitiveLimit] using hred
      rw [hmustar_selector η]
      simp [weakIVLIMLRootAssemblyFromPrimitiveRayleighMap,
        weakIVLIMLRootOLSPrimitiveLimit,
        weakIV2SLSProjectedBreadScoreFromPrimitive,
        weakIV2SLSPrimitiveLimit, weakIV2SLSLimitBread, weakIV2SLSLimitScore,
        hred', Matrix.mul_assoc])

/-- Moment-level OLS condition package for Hansen Theorem 12.18.

The package assumes the normalized OLS bread and structural-error score limits
appearing behind Hansen's weak-instrument OLS drift.  It deliberately does not
assume the OLS estimator limit; the public constructors below derive that limit
by the project CMT and random-inverse utilities. -/
structure WeakIVOLSMomentConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (β : k → ℝ) (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) : Prop where
  linear_model : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω
  bread_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIVOLSNormalizedBread X m ω) μ
  score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIVOLSNormalizedScore X e m ω) μ
  bread_tendsto : TendstoInMeasure μ
    (fun m ω => weakIVOLSNormalizedBread X m ω)
    atTop (fun _ => Sigma22)
  score_tendsto : TendstoInMeasure μ
    (fun m ω => weakIVOLSNormalizedScore X e m ω)
    atTop (fun _ => Sigma2e)
  bread_nonsing : IsUnit Sigma22.det

/-- Build the OLS weak-IV moment package from row measurability plus the two
normalized OLS WLLNs.

This is the local constructor for the OLS component of the shared Theorem
12.18 root/OLS primitive process. -/
theorem WeakIVOLSMomentConditions.of_rows
    {X : ℕ → Ω → k → ℝ} {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : IsUnit Sigma22.det) :
    WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e where
  linear_model := hmodel
  bread_meas := weakIVOLSNormalizedBread_aestronglyMeasurable_of_rows
    (μ := μ) (X := X) hX
  score_meas := weakIVOLSNormalizedScore_aestronglyMeasurable_of_rows
    (μ := μ) (X := X) (e := e) hX he
  bread_tendsto := hbread
  score_tendsto := hscore
  bread_nonsing := hSigma22

private theorem weakIV_tendstoInMeasure_of_tendstoInDistribution_const
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E]
    [OpensMeasurableSpace E] [HasOuterApproxClosed E]
    {Ωlim : Type*} [MeasurableSpace Ωlim]
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {X : ℕ → Ω → E} {c : E}
    (h : TendstoInDistribution (E := E) (Ω := fun _ : ℕ => Ω)
      X atTop (fun _ : Ωlim => c) (fun _ => μ) ν) :
    TendstoInMeasure μ X atTop (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  let D : Set E := {x | ε ≤ dist x c}
  have hD_closed : IsClosed D := by
    simpa [D] using
      (isClosed_le continuous_const
        (continuous_id.dist continuous_const) :
        IsClosed {x : E | ε ≤ dist x c})
  have hD_null : (ν.map (fun _ : Ωlim => c)) D = 0 := by
    have hpre : (fun _ : Ωlim => c) ⁻¹' D = ∅ := by
      ext η
      simp [D, not_le_of_gt hε]
    rw [Measure.map_apply_of_aemeasurable
      (by fun_prop : AEMeasurable (fun _ : Ωlim => c) ν) hD_closed.measurableSet,
      hpre, measure_empty]
  have htendsto :=
    TendstoInDistribution.tendsto_measure_preimage_of_closed_null h hD_closed hD_null
  simpa [D] using htendsto

omit [DecidableEq l] in
/-- Build the OLS weak-IV moment package from the shared root/OLS primitive
process used by the LIML route.

The second component of `weakIVLIMLRootOLSPrimitiveMoments` is exactly
`(Q̂_XX, n⁻¹X'e)`, so joint convergence of the root local-to-zero primitive and
the OLS primitive to `(..., (Σ₂₂,Σ₂e))` implies the OLS bread and score WLLNs by
projection and the distribution-to-constant bridge. -/
theorem WeakIVOLSMomentConditions.of_root_ols_primitive
    {Ωlim : Type*} [MeasurableSpace Ωlim]
    {ν : Measure Ωlim} [IsProbabilityMeasure ν]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hbread : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVOLSNormalizedBread X m ω) μ)
    (hscore : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVOLSNormalizedScore X e m ω) μ)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hSigma22 : IsUnit Sigma22.det) :
    WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e where
  linear_model := hmodel
  bread_meas := hbread
  score_meas := hscore
  bread_tendsto := by
    have hdist := hjoint.continuous_comp
      (by fun_prop :
        Continuous
          (fun p :
            (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
              (Matrix k k ℝ × (k → ℝ)) => p.2.1))
    have hdist_const : TendstoInDistribution
        (E := Matrix k k ℝ) (Ω := fun _ : ℕ => Ω)
        (fun (m : ℕ) (ω : Ω) =>
          (weakIVLIMLRootOLSPrimitiveMoments Z X e m ω).2.1)
        atTop (fun _ : Ωlim => Sigma22) (fun _ => μ) ν := by
      simpa [weakIVLIMLRootOLSPrimitiveLimit] using hdist
    simpa [weakIVLIMLRootOLSPrimitiveMoments] using
      weakIV_tendstoInMeasure_of_tendstoInDistribution_const
        (μ := μ) (ν := ν) hdist_const
  score_tendsto := by
    have hdist := hjoint.continuous_comp
      (by fun_prop :
        Continuous
          (fun p :
            (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
              (Matrix k k ℝ × (k → ℝ)) => p.2.2))
    have hdist_const : TendstoInDistribution
        (E := k → ℝ) (Ω := fun _ : ℕ => Ω)
        (fun (m : ℕ) (ω : Ω) =>
          (weakIVLIMLRootOLSPrimitiveMoments Z X e m ω).2.2)
        atTop (fun _ : Ωlim => Sigma2e) (fun _ => μ) ν := by
      simpa [weakIVLIMLRootOLSPrimitiveLimit] using hdist
    simpa [weakIVLIMLRootOLSPrimitiveMoments] using
      weakIV_tendstoInMeasure_of_tendstoInDistribution_const
        (μ := μ) (ν := ν) hdist_const
  bread_nonsing := hSigma22

omit [DecidableEq l] in
/-- Assemble the shared root/OLS primitive convergence from Hansen's
root-local-to-zero primitive CLT and OLS WLLNs.

This is a Slutsky bridge: the random root primitive
`(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)` may have a nondegenerate weak limit, while
the OLS component `(Q̂_XX,n^{-1}X'e)` converges in probability to the constant
`(Σ₂₂,Σ₂e)`. -/
theorem weakIV_root_ols_primitive_tendstoInDistribution_of_root_primitive_ols_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e) :
    TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν := by
  have hOLS_pair : TendstoInMeasure μ
      (fun m ω =>
        ((weakIVOLSNormalizedBread X m ω,
          weakIVOLSNormalizedScore X e m ω) :
          Matrix k k ℝ × (k → ℝ)))
      atTop (fun _ => ((Sigma22, Sigma2e) : Matrix k k ℝ × (k → ℝ))) :=
    tendstoInMeasure_prodMk hOLS.bread_tendsto hOLS.score_tendsto
  have hOLS_pair_meas : ∀ m, AEMeasurable
      (fun ω =>
        ((weakIVOLSNormalizedBread X m ω,
          weakIVOLSNormalizedScore X e m ω) :
          Matrix k k ℝ × (k → ℝ))) μ :=
    fun m => (hOLS.bread_meas m).aemeasurable.prodMk
      (hOLS.score_meas m).aemeasurable
  have hjoint :=
    hroot.prodMk_of_tendstoInMeasure_const
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      (fun (m : ℕ) (ω : Ω) =>
        ((weakIVOLSNormalizedBread X m ω,
          weakIVOLSNormalizedScore X e m ω) :
          Matrix k k ℝ × (k → ℝ)))
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      hOLS_pair hOLS_pair_meas
  simpa [weakIVLIMLRootOLSPrimitiveMoments,
    weakIVLIMLRootOLSPrimitiveLimit] using hjoint

/-- Moment/CLT-level 2SLS condition package for Hansen Theorem 12.18.

The fields are the primitive weak-IV surfaces used by the 2SLS continuous
mapping argument: the normalized projected bread and structural-error score
jointly converge to Hansen's random weak-IV bread/score, and singular
finite-sample projected-bread events vanish in probability.  The package does
not assume the final 2SLS estimator limit. -/
structure WeakIV2SLSMomentConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ) : Prop where
  linear_model : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω
  estimator_meas : ∀ m, AEStronglyMeasurable
    (fun ω =>
      twoSLSBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
    μ
  bread_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIV2SLSNormalizedBread Z X m ω) μ
  score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIV2SLSNormalizedScore Z X e m ω) μ
  joint_tendsto : TendstoInDistribution
    (E := Matrix k k ℝ × (k → ℝ)) (Ω := fun _ : ℕ => Ω)
    (fun (m : ℕ) (ω : Ω) =>
      ((weakIV2SLSNormalizedBread Z X m ω,
        weakIV2SLSNormalizedScore Z X e m ω) :
        Matrix k k ℝ × (k → ℝ)))
    atTop
    (fun (η : Ωlim) =>
      ((weakIV2SLSLimitBread QZZ C (Xi2 η),
        weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)) :
        Matrix k k ℝ × (k → ℝ)))
    (fun _ => μ) ν
  limit_nonsing_ae :
    ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0
  singular_tendsto_zero : Tendsto
    (fun m => μ {ω | ¬ IsUnit (weakIV2SLSNormalizedBread Z X m ω).det})
    atTop (𝓝 0)

/-- Primitive first-stage/score package for the 2SLS face of Hansen Theorem
12.18.

This package asks for the lower-level local-to-zero first-stage CLT surface
`(Q̂_ZZ, Q̂_ZX, n⁻¹ Z'e) ⇒ (Q_ZZ, Q_ZZ C + Ξ₂, ξ_e)`.  The constructor
`WeakIV2SLSMomentConditions.of_primitive_firstStage_score` maps it to the
projected 2SLS bread/score package by the continuous-mapping theorem, so callers
do not have to assume `WeakIV2SLSMomentConditions.joint_tendsto` directly. -/
structure WeakIV2SLSPrimitiveMomentConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ) : Prop where
  linear_model : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω
  estimator_meas : ∀ m, AEStronglyMeasurable
    (fun ω =>
      twoSLSBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
    μ
  qzz_meas : ∀ m, AEStronglyMeasurable
    (fun ω => sampleQZZ (stackRegressors Z m ω)) μ
  qzx_meas : ∀ m, AEStronglyMeasurable
    (fun ω => sampleQZX (stackRegressors Z m ω) (stackRegressors X m ω)) μ
  zscore_meas : ∀ m, AEStronglyMeasurable
    (fun ω => sampleCrossMoment (stackRegressors Z m ω) (stackErrors e m ω)) μ
  primitive_joint_tendsto : TendstoInDistribution
    (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
    (fun (m : ℕ) (ω : Ω) => weakIV2SLSPrimitiveMoments Z X e m ω)
    atTop
    (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
    (fun _ => μ) ν
  qzz_nonsing : IsUnit QZZ.det
  limit_nonsing_ae :
    ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0
  singular_tendsto_zero : Tendsto
    (fun m => μ {ω | ¬ IsUnit (weakIV2SLSNormalizedBread Z X m ω).det})
    atTop (𝓝 0)

/-- Root-primitive first-stage/score package for the 2SLS face of Hansen
Theorem 12.18.

This is the faithful local-to-zero package: the primitive joint convergence is
for `(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)`, not the strong-instrument normalized
`n^{-1}` first-stage surface.  The estimator limit is derived below from this
package by the root-scaled CMT and Star-totalization remainder, so the package
does not assume the final 2SLS weak-IV limit. -/
structure WeakIV2SLSRootPrimitiveMomentConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ) : Prop where
  linear_model : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω
  estimator_meas : ∀ m, AEStronglyMeasurable
    (fun ω =>
      twoSLSBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
    μ
  root_primitive_joint_tendsto : TendstoInDistribution
    (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
    (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
    atTop
    (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
    (fun _ => μ) ν
  qzz_nonsing : IsUnit QZZ.det
  limit_nonsing_ae :
    ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0

/-- Constructor for the 2SLS root-primitive package from Hansen's
local-to-zero first-stage/score CLT.

This names the exact fields needed by the 2SLS face: the structural model,
estimator measurability, joint convergence of
`(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)`, nonsingularity of `Q_ZZ`, and a.s.
nonsingularity of the random projected bread limit. -/
theorem WeakIV2SLSRootPrimitiveMomentConditions.of_local_to_zero_clt
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hest : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ)
    (hclt : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hlimit :
      ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0) :
    WeakIV2SLSRootPrimitiveMomentConditions μ ν Z X e Y β QZZ C Xi2 xie where
  linear_model := hmodel
  estimator_meas := hest
  root_primitive_joint_tendsto := hclt
  qzz_nonsing := hQZZ
  limit_nonsing_ae := hlimit

/-- Build the 2SLS root-primitive package from the joint root/OLS primitive
surface used by the LIML assembly route.

This collapses the duplicated local-to-zero CLT input in Theorem 12.18: the
same joint convergence of
`((Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e), (Q̂_XX, n^{-1}X'e))` supplies the 2SLS
root primitive after projecting to the first component. -/
theorem WeakIV2SLSRootPrimitiveMomentConditions.of_root_ols_primitive
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hest : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hlimit :
      ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0) :
    WeakIV2SLSRootPrimitiveMomentConditions μ ν Z X e Y β QZZ C Xi2 xie where
  linear_model := hmodel
  estimator_meas := hest
  root_primitive_joint_tendsto := by
    have hraw := hjoint.continuous_comp
      (continuous_fst :
        Continuous
          (fun p :
            (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
              (Matrix k k ℝ × (k → ℝ)) => p.1))
    simpa [weakIVLIMLRootOLSPrimitiveMoments,
      weakIVLIMLRootOLSPrimitiveLimit] using hraw
  qzz_nonsing := hQZZ
  limit_nonsing_ae := hlimit

set_option maxHeartbeats 800000 in
-- Heartbeat bump: constructing both projected bread and score measurability
-- fields from primitive matrix moments has expensive finite-product synthesis.
/-- Build the projected 2SLS weak-IV moment package from Hansen's primitive
first-stage/score CLT surface.

This removes the direct projected bread/score convergence field from the
caller: `joint_tendsto` is obtained by applying the a.s.-continuous CMT to the
map `(Q̂_ZZ, Q̂_ZX, ŝ_Ze) ↦ (Q̂_ZX' Q̂_ZZ⁻¹ Q̂_ZX,
Q̂_ZX' Q̂_ZZ⁻¹ ŝ_Ze)`. -/
theorem WeakIV2SLSMomentConditions.of_primitive_firstStage_score
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    (h : WeakIV2SLSPrimitiveMomentConditions μ ν Z X e Y β QZZ C Xi2 xie) :
    WeakIV2SLSMomentConditions μ ν Z X e Y β QZZ C Xi2 xie where
  linear_model := h.linear_model
  estimator_meas := h.estimator_meas
  bread_meas := by
    intro m
    have hQinv : AEStronglyMeasurable
        (fun ω => (sampleQZZ (stackRegressors Z m ω))⁻¹) μ :=
      aestronglyMeasurable_matrix_inv (h.qzz_meas m)
    have hQZXt : AEStronglyMeasurable
        (fun ω => (sampleQZX (stackRegressors Z m ω) (stackRegressors X m ω))ᵀ) μ :=
      ((continuous_id.matrix_transpose).comp_aestronglyMeasurable (h.qzx_meas m))
    have hleft : AEStronglyMeasurable
        (fun ω =>
          (sampleQZX (stackRegressors Z m ω) (stackRegressors X m ω))ᵀ *
            (sampleQZZ (stackRegressors Z m ω))⁻¹) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hQZXt.prodMk hQinv)
    have hbread : AEStronglyMeasurable
        (fun ω =>
          (sampleQZX (stackRegressors Z m ω) (stackRegressors X m ω))ᵀ *
            (sampleQZZ (stackRegressors Z m ω))⁻¹ *
              sampleQZX (stackRegressors Z m ω) (stackRegressors X m ω)) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hleft.prodMk (h.qzx_meas m))
    simpa [weakIV2SLSNormalizedBread, sampleQXZ, twoSLSBread, Matrix.mul_assoc] using hbread
  score_meas := by
    intro m
    have hQinv : AEStronglyMeasurable
        (fun ω => (sampleQZZ (stackRegressors Z m ω))⁻¹) μ :=
      aestronglyMeasurable_matrix_inv (h.qzz_meas m)
    have hQZXt : AEStronglyMeasurable
        (fun ω => (sampleQZX (stackRegressors Z m ω) (stackRegressors X m ω))ᵀ) μ :=
      ((continuous_id.matrix_transpose).comp_aestronglyMeasurable (h.qzx_meas m))
    have hleft : AEStronglyMeasurable
        (fun ω =>
          (sampleQZX (stackRegressors Z m ω) (stackRegressors X m ω))ᵀ *
            (sampleQZZ (stackRegressors Z m ω))⁻¹) μ :=
      (Continuous.matrix_mul continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hQZXt.prodMk hQinv)
    have hscore : AEStronglyMeasurable
        (fun ω =>
          ((sampleQZX (stackRegressors Z m ω) (stackRegressors X m ω))ᵀ *
            (sampleQZZ (stackRegressors Z m ω))⁻¹) *ᵥ
              sampleCrossMoment (stackRegressors Z m ω) (stackErrors e m ω)) μ :=
      (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
        (hleft.prodMk (h.zscore_meas m))
    simpa [weakIV2SLSNormalizedScore, sampleQXZ, Matrix.mul_assoc] using hscore
  joint_tendsto :=
    weakIV_twoSLS_projected_bread_score_tendstoInDistribution_of_primitive
      h.primitive_joint_tendsto h.qzz_nonsing
  limit_nonsing_ae := h.limit_nonsing_ae
  singular_tendsto_zero := h.singular_tendsto_zero

/-- Moment/CLT-level LIML condition package for Hansen Theorem 12.18.

The fields are the weak-IV-scaled LIML bread and structural-error score joint
limit, plus the high-probability nonsingularity needed to remove Star
totalization.  The estimator itself uses the finite-sample adjustment
`µ̂_n / n`, while `limlMuHat` is the scaled eigenvalue sequence with limit
`μ*`.  The package records Hansen's Rayleigh-minimum definition of `μ*` but
does not assume the final LIML estimator limit. -/
structure WeakIVLIMLMomentConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) : Prop where
  linear_model : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω
  liml_rayleigh_minimizer : ∀ η,
    LIMLRayleighMinimizer
      (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)
  estimator_meas : ∀ m, AEStronglyMeasurable
    (fun ω =>
      limlBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
        (weakIVLIMLFiniteSampleMu limlMuHat m ω))
    μ
  bread_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ
  score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ
  joint_tendsto : TendstoInDistribution
    (E := Matrix k k ℝ × (k → ℝ)) (Ω := fun _ : ℕ => Ω)
    (fun (m : ℕ) (ω : Ω) =>
      ((weakIVLIMLWeakScaledBread Z X limlMuHat m ω,
        weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) :
        Matrix k k ℝ × (k → ℝ)))
    atTop
    (fun (η : Ωlim) =>
      ((weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22,
        weakIVLIMLLimitScore QZZ C (Xi2 η) (xie η) (mustar η) Sigma2e) :
        Matrix k k ℝ × (k → ℝ)))
    (fun _ => μ) ν
  limit_nonsing_ae :
    ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0
  singular_tendsto_zero : Tendsto
    (fun m => μ {ω | ¬ IsUnit
      (weakIVLIMLWeakScaledBread Z X limlMuHat m ω).det})
    atTop (𝓝 0)

/-- Root/OLS/`µ̂` assembly package for the LIML face of Hansen Theorem 12.18.

The main stochastic input is the joint convergence of the root 2SLS
bread/score pair, the OLS bread/score pair, and the scaled LIML eigenvalue
adjustment.  The finite-sample bridge from the weak-scaled LIML moments to the
root-assembled moments is derived by
`weakIV_liml_weak_scaled_actual_assembled_gap_tendstoInMeasure`, so this package
does not carry a separate gap field. -/
structure WeakIVLIMLRootAssemblyConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) : Prop where
  linear_model : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω
  liml_rayleigh_minimizer : ∀ η,
    LIMLRayleighMinimizer
      (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)
  estimator_meas : ∀ m, AEStronglyMeasurable
    (fun ω =>
      limlBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
        (weakIVLIMLFiniteSampleMu limlMuHat m ω))
    μ
  actual_bread_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ
  actual_score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ
  root_assembly_joint_tendsto : TendstoInDistribution
    (E := ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ)
    (Ω := fun _ : ℕ => Ω)
    (fun (m : ℕ) (ω : Ω) =>
      ((((weakIV2SLSRootScaledBread Z X m ω,
          weakIV2SLSRootScaledScore Z X e m ω),
         (weakIVOLSNormalizedBread X m ω,
          weakIVOLSNormalizedScore X e m ω)),
        limlMuHat m ω) :
        ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ))
    atTop
    (fun η =>
      ((((weakIV2SLSLimitBread QZZ C (Xi2 η),
          weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)),
         (Sigma22, Sigma2e)),
        mustar η) :
        ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ))
    (fun _ => μ) ν
  limit_nonsing_ae :
    ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0

/-- Rayleigh-selector certificate for Hansen's weak-IV LIML eigenvalue
adjustment.

This isolates the remaining eigenvalue-selection work: a continuous selector
for the reduced-form Rayleigh primitive, pointwise sample and limit selector
equations for `µ̂_n` and `µ*`, the finite-sample and reduced-form limit
minimizer certificates, and the structural `Σ₂₂` minimizer certificate used by
the LIML bias formula. -/
structure WeakIVLIMLReducedFormRayleighSelectorCertificate
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ)
    (Sigma22 : Matrix k k ℝ) : Prop where
  selector_cont : Continuous muSelector
  sample_selector_eq : ∀ m ω,
    limlMuHat m ω =
      muSelector (weakIVReducedFormRayleighPrimitive Z X e β m ω)
  limit_selector_eq : ∀ η,
    mustar η =
      muSelector (weakIVReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)
  sample_rayleigh_minimizer : ∀ m ω,
    LIMLRayleighMinimizer
      (limlRayleighMatrix
        (sampleQZZ (stackRegressors Z m ω))
        (weakIVRootReducedFormProjectedMoment Z X e β m ω))
      Sigma (limlMuHat m ω)
  reducedForm_limit_rayleigh_minimizer : ∀ η,
    LIMLRayleighMinimizer
      (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
      Sigma (mustar η)
  structural_limit_rayleigh_minimizer : ∀ η,
    LIMLRayleighMinimizer
      (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)

/-- Narrow Rayleigh-selector certificate for Hansen's weak-IV LIML eigenvalue
adjustment.

This is the theorem-facing data actually consumed by the weak-IV LIML CMT:
the finite-sample scaled eigenvalue `µ̂_n` is selected from Hansen's
reduced-form Rayleigh primitive, the limit `µ*` is selected by the same
continuous map, and `µ*` satisfies the structural Rayleigh-minimum condition
appearing in the LIML bias formula.  It deliberately omits the separate
full reduced-form minimizer certificates from
`WeakIVLIMLReducedFormRayleighSelectorCertificate`, because those are useful
audit data but are not needed to derive Theorem 12.18's LIML limit. -/
structure WeakIVLIMLStructuralRayleighSelectorCertificate
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ)
    (Sigma22 : Matrix k k ℝ) : Prop where
  selector_cont : Continuous muSelector
  sample_selector_eq : ∀ m ω,
    limlMuHat m ω =
      muSelector (weakIVReducedFormRayleighPrimitive Z X e β m ω)
  limit_selector_eq : ∀ η,
    mustar η =
      muSelector (weakIVReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)
  structural_limit_rayleigh_minimizer : ∀ η,
    LIMLRayleighMinimizer
      (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)

omit [Fintype l] [DecidableEq k] [DecidableEq l] [MeasurableSpace Ω] in
/-- Convert a selector equation stated on Hansen's literal root primitive
`(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)` into the reduced-form sample selector
equation used by the LIML Rayleigh certificate. -/
theorem weakIV_liml_selector_sample_eq_of_root_primitive
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hroot : ∀ m ω,
      limlMuHat m ω =
        muSelector
          (weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
            (weakIV2SLSRootPrimitiveMoments Z X e m ω))) :
    ∀ m ω,
      limlMuHat m ω =
        muSelector (weakIVReducedFormRayleighPrimitive Z X e β m ω) := by
  intro m ω
  simpa [weakIVReducedFormRayleighPrimitiveFromRootPrimitive_sample_eq] using
    hroot m ω

omit [DecidableEq k] [DecidableEq l] [MeasurableSpace Ωlim] in
/-- Convert a selector equation stated on the root-primitive limit
`(Q_ZZ, Q_ZZ C + Ξ₂, ξ_e)` into the reduced-form limit selector equation used
by the LIML Rayleigh certificate. -/
theorem weakIV_liml_selector_limit_eq_of_root_primitive
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ} {β : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hroot : ∀ η,
      mustar η =
        muSelector
          (weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
            (weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η))) :
    ∀ η,
      mustar η =
        muSelector (weakIVReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η) := by
  intro η
  simpa [weakIVReducedFormRayleighPrimitiveFromRootPrimitive_limit_eq] using
    hroot η

omit [Fintype l] [DecidableEq k] [DecidableEq l] [MeasurableSpace Ω] in
/-- Convert a reduced-form sample selector equation back to Hansen's root
primitive surface.

This is the reverse bridge to
`weakIV_liml_selector_sample_eq_of_root_primitive`: a spectral proof may
identify `µ̂_n` on `(Q̂_ZZ, n^{-1/2}Z'[Y X])`, while the raw theorem package
stores selector equations on `(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)`. -/
theorem weakIV_liml_selector_sample_eq_root_primitive_of_reducedForm
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hreduced : ∀ m ω,
      limlMuHat m ω =
        muSelector (weakIVReducedFormRayleighPrimitive Z X e β m ω)) :
    ∀ m ω,
      limlMuHat m ω =
        muSelector
          (weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
            (weakIV2SLSRootPrimitiveMoments Z X e m ω)) := by
  intro m ω
  simpa [weakIVReducedFormRayleighPrimitiveFromRootPrimitive_sample_eq] using
    hreduced m ω

omit [DecidableEq k] [DecidableEq l] [MeasurableSpace Ωlim] in
/-- Convert a reduced-form limit selector equation back to Hansen's
root-primitive limit surface. -/
theorem weakIV_liml_selector_limit_eq_root_primitive_of_reducedForm
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ} {β : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hreduced : ∀ η,
      mustar η =
        muSelector (weakIVReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)) :
    ∀ η,
      mustar η =
        muSelector
          (weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
            (weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)) := by
  intro η
  simpa [weakIVReducedFormRayleighPrimitiveFromRootPrimitive_limit_eq] using
    hreduced η

omit [DecidableEq k] [MeasurableSpace Ω] [MeasurableSpace Ωlim] in
/-- Build the structural Rayleigh selector certificate from selector equations
stated directly on Hansen's root primitive and its local-to-zero limit.

This is the theorem-facing bridge for the remaining finite-sample eigenvalue
work: once a continuous LIML selector has been identified on
`(Q, n^{-1/2}Z'[Y X])`, callers may prove the sample and limit equations using
the root-primitive surface instead of manually rewriting to the reduced-form
primitive. -/
theorem WeakIVLIMLStructuralRayleighSelectorCertificate.of_root_primitive_selector_equations
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hselector : Continuous muSelector)
    (hsample : ∀ m ω,
      limlMuHat m ω =
        muSelector
          (weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
            (weakIV2SLSRootPrimitiveMoments Z X e m ω)))
    (hlimit : ∀ η,
      mustar η =
        muSelector
          (weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
            (weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)))
    (hstructural : ∀ η,
      LIMLRayleighMinimizer
        (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)) :
    WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22 where
  selector_cont := hselector
  sample_selector_eq :=
    weakIV_liml_selector_sample_eq_of_root_primitive
      (k := k) (l := l) hsample
  limit_selector_eq :=
    weakIV_liml_selector_limit_eq_of_root_primitive
      (k := k) (l := l) hlimit
  structural_limit_rayleigh_minimizer := hstructural

omit [DecidableEq k] [MeasurableSpace Ω] [MeasurableSpace Ωlim] in
/-- Build the full reduced-form Rayleigh selector certificate from root
primitive selector equations plus the optional sample and reduced-form
minimizer audit fields. -/
theorem WeakIVLIMLReducedFormRayleighSelectorCertificate.of_root_primitive_selector_equations
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hselector : Continuous muSelector)
    (hsample_eq : ∀ m ω,
      limlMuHat m ω =
        muSelector
          (weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
            (weakIV2SLSRootPrimitiveMoments Z X e m ω)))
    (hlimit_eq : ∀ η,
      mustar η =
        muSelector
          (weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
            (weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)))
    (hsample_min : ∀ m ω,
      LIMLRayleighMinimizer
        (limlRayleighMatrix
          (sampleQZZ (stackRegressors Z m ω))
          (weakIVRootReducedFormProjectedMoment Z X e β m ω))
        Sigma (limlMuHat m ω))
    (hreduced_min : ∀ η,
      LIMLRayleighMinimizer
        (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
        Sigma (mustar η))
    (hstructural_min : ∀ η,
      LIMLRayleighMinimizer
        (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)) :
    WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22 where
  selector_cont := hselector
  sample_selector_eq :=
    weakIV_liml_selector_sample_eq_of_root_primitive
      (k := k) (l := l) hsample_eq
  limit_selector_eq :=
    weakIV_liml_selector_limit_eq_of_root_primitive
      (k := k) (l := l) hlimit_eq
  sample_rayleigh_minimizer := hsample_min
  reducedForm_limit_rayleigh_minimizer := hreduced_min
  structural_limit_rayleigh_minimizer := hstructural_min

/-- Finite-sample Rayleigh/eigenvalue selector certificate for Hansen's
weak-IV LIML adjustment.

This is the explicit audit surface for the remaining finite-sample eigenvalue
work.  The sample equation is stated on Hansen's literal root primitive
`(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)`, and the finite-sample Rayleigh-minimizer
field records the exact reduced-form LIML eigenvalue problem.  The structural
limit minimizer is still an input: deriving it from the finite-sample
eigenvalue problem requires a separate argmin/eigenvalue continuity theorem. -/
structure WeakIVLIMLFiniteSampleRayleighSelectorCertificate
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ)
    (Sigma22 : Matrix k k ℝ) : Prop where
  selector_cont : Continuous muSelector
  sample_selector_eq_root_primitive : ∀ m ω,
    limlMuHat m ω =
      muSelector
        (weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
          (weakIV2SLSRootPrimitiveMoments Z X e m ω))
  limit_selector_eq_root_primitive : ∀ η,
    mustar η =
      muSelector
        (weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
          (weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η))
  finite_sample_rayleigh_minimizer : ∀ m ω,
    LIMLRayleighMinimizer
      (limlRayleighMatrix
        (sampleQZZ (stackRegressors Z m ω))
        (weakIVRootReducedFormProjectedMoment Z X e β m ω))
      Sigma (limlMuHat m ω)
  structural_limit_rayleigh_minimizer : ∀ η,
    LIMLRayleighMinimizer
      (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)

/- The raw eigenvalue problem package keeps all selector and minimizer facts
together before downstream theorem packages forget the audit-only fields. -/
/-- Raw LIML eigenvalue-problem certificate for Hansen Theorem 12.18.

This is the strongest local certificate in this file: it states the continuous
selector on Hansen's root primitive, the sample and limit selector equations,
the finite-sample reduced-form Rayleigh minimizer, the full reduced-form limit
Rayleigh minimizer, and Hansen's structural Rayleigh minimizer.  The current
library still needs a separate spectral theorem to construct these fields from
the concrete finite-sample LIML eigenvalue problem. -/
structure WeakIVLIMLRawEigenvalueProblemConditions
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ)
    (Sigma22 : Matrix k k ℝ) : Prop where
  selector_cont : Continuous muSelector
  sample_selector_eq_root_primitive : ∀ m ω,
    limlMuHat m ω =
      muSelector
        (weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
          (weakIV2SLSRootPrimitiveMoments Z X e m ω))
  limit_selector_eq_root_primitive : ∀ η,
    mustar η =
      muSelector
        (weakIVReducedFormRayleighPrimitiveFromRootPrimitive β
          (weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η))
  finite_sample_rayleigh_minimizer : ∀ m ω,
    LIMLRayleighMinimizer
      (limlRayleighMatrix
        (sampleQZZ (stackRegressors Z m ω))
        (weakIVRootReducedFormProjectedMoment Z X e β m ω))
      Sigma (limlMuHat m ω)
  reducedForm_limit_rayleigh_minimizer : ∀ η,
    LIMLRayleighMinimizer
      (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
      Sigma (mustar η)
  structural_limit_rayleigh_minimizer : ∀ η,
    LIMLRayleighMinimizer
      (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)

omit [DecidableEq k] [MeasurableSpace Ω] [MeasurableSpace Ωlim] in
/-- Build the finite-sample Rayleigh certificate from selector equations stated
on the reduced-form Rayleigh primitive.

This constructor lets the finite-sample LIML spectral calculation stay in the
natural reduced-form notation `(Q̂_ZZ, n^{-1/2}Z'[Y X])`; the root-primitive
selector equations required by the theorem package are then just notation
bridges. -/
theorem WeakIVLIMLFiniteSampleRayleighSelectorCertificate.of_reducedForm_selector
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hselector : Continuous muSelector)
    (hsample_eq : ∀ m ω,
      limlMuHat m ω =
        muSelector (weakIVReducedFormRayleighPrimitive Z X e β m ω))
    (hlimit_eq : ∀ η,
      mustar η =
        muSelector (weakIVReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η))
    (hsample_min : ∀ m ω,
      LIMLRayleighMinimizer
        (limlRayleighMatrix
          (sampleQZZ (stackRegressors Z m ω))
          (weakIVRootReducedFormProjectedMoment Z X e β m ω))
        Sigma (limlMuHat m ω))
    (hstructural_min : ∀ η,
      LIMLRayleighMinimizer
        (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)) :
    WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22 where
  selector_cont := hselector
  sample_selector_eq_root_primitive :=
    weakIV_liml_selector_sample_eq_root_primitive_of_reducedForm
      (k := k) (l := l) hsample_eq
  limit_selector_eq_root_primitive :=
    weakIV_liml_selector_limit_eq_root_primitive_of_reducedForm
      (k := k) (l := l) hlimit_eq
  finite_sample_rayleigh_minimizer := hsample_min
  structural_limit_rayleigh_minimizer := hstructural_min

omit [DecidableEq k] [MeasurableSpace Ω] [MeasurableSpace Ωlim] in
/-- Build the raw LIML eigenvalue-problem certificate from the full
reduced-form Rayleigh selector certificate.

The raw package stores selector equations on Hansen's root primitive for
compatibility with the local-to-zero CLT, while the spectral minimization
problem itself is naturally stated on the reduced-form Rayleigh primitive.
This bridge keeps the estimator theorem route derived from the reduced-form
selector/minimizer facts rather than asking callers to restate them. -/
theorem WeakIVLIMLRawEigenvalueProblemConditions.of_reducedForm_rayleigh_selector
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {Sigma22 : Matrix k k ℝ}
    (h : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22) :
    WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22 where
  selector_cont := h.selector_cont
  sample_selector_eq_root_primitive :=
    weakIV_liml_selector_sample_eq_root_primitive_of_reducedForm
      (k := k) (l := l) h.sample_selector_eq
  limit_selector_eq_root_primitive :=
    weakIV_liml_selector_limit_eq_root_primitive_of_reducedForm
      (k := k) (l := l) h.limit_selector_eq
  finite_sample_rayleigh_minimizer := h.sample_rayleigh_minimizer
  reducedForm_limit_rayleigh_minimizer := h.reducedForm_limit_rayleigh_minimizer
  structural_limit_rayleigh_minimizer := h.structural_limit_rayleigh_minimizer

omit [DecidableEq k] [MeasurableSpace Ω] [MeasurableSpace Ωlim] in
/-- Forget the reduced-form limit minimizer audit field from the full
reduced-form Rayleigh selector certificate.

This is the finite-sample-Rayleigh analogue of
`WeakIVLIMLRawEigenvalueProblemConditions.of_reducedForm_rayleigh_selector`:
callers who have proved the spectral facts in Hansen's natural reduced-form
Rayleigh notation can feed the theorem-facing finite-sample package without
restating the selector equations. -/
theorem WeakIVLIMLFiniteSampleRayleighSelectorCertificate.of_reducedForm_rayleigh_selector
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {Sigma22 : Matrix k k ℝ}
    (h : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22) :
    WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22 where
  selector_cont := h.selector_cont
  sample_selector_eq_root_primitive :=
    weakIV_liml_selector_sample_eq_root_primitive_of_reducedForm
      (k := k) (l := l) h.sample_selector_eq
  limit_selector_eq_root_primitive :=
    weakIV_liml_selector_limit_eq_root_primitive_of_reducedForm
      (k := k) (l := l) h.limit_selector_eq
  finite_sample_rayleigh_minimizer := h.sample_rayleigh_minimizer
  structural_limit_rayleigh_minimizer := h.structural_limit_rayleigh_minimizer

omit [DecidableEq k] [MeasurableSpace Ω] [MeasurableSpace Ωlim] in
/-- Forget the reduced-form limit audit field from the raw eigenvalue-problem
certificate when the downstream theorem only needs the finite-sample
Rayleigh/eigenvalue package. -/
theorem WeakIVLIMLFiniteSampleRayleighSelectorCertificate.of_raw_eigenvalue_problem
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {Sigma22 : Matrix k k ℝ}
    (h : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22) :
    WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22 where
  selector_cont := h.selector_cont
  sample_selector_eq_root_primitive := h.sample_selector_eq_root_primitive
  limit_selector_eq_root_primitive := h.limit_selector_eq_root_primitive
  finite_sample_rayleigh_minimizer := h.finite_sample_rayleigh_minimizer
  structural_limit_rayleigh_minimizer := h.structural_limit_rayleigh_minimizer

omit [DecidableEq k] [MeasurableSpace Ω] [MeasurableSpace Ωlim] in
/-- Convert the raw eigenvalue-problem certificate into the full reduced-form
Rayleigh selector certificate, retaining the reduced-form limit minimizer audit
field. -/
theorem WeakIVLIMLReducedFormRayleighSelectorCertificate.of_raw_eigenvalue_problem
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {Sigma22 : Matrix k k ℝ}
    (h : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22) :
    WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22 :=
  WeakIVLIMLReducedFormRayleighSelectorCertificate.of_root_primitive_selector_equations
    (k := k) (l := l) h.selector_cont
    h.sample_selector_eq_root_primitive h.limit_selector_eq_root_primitive
    h.finite_sample_rayleigh_minimizer h.reducedForm_limit_rayleigh_minimizer
    h.structural_limit_rayleigh_minimizer

omit [DecidableEq k] [MeasurableSpace Ω] [MeasurableSpace Ωlim] in
/-- Forget the finite-sample minimizer audit field when only the structural
selector certificate is needed downstream. -/
theorem WeakIVLIMLStructuralRayleighSelectorCertificate.of_finite_sample_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {Sigma22 : Matrix k k ℝ}
    (h : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22) :
    WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22 where
  selector_cont := h.selector_cont
  sample_selector_eq :=
    weakIV_liml_selector_sample_eq_of_root_primitive
      (k := k) (l := l) h.sample_selector_eq_root_primitive
  limit_selector_eq :=
    weakIV_liml_selector_limit_eq_of_root_primitive
      (k := k) (l := l) h.limit_selector_eq_root_primitive
  structural_limit_rayleigh_minimizer := h.structural_limit_rayleigh_minimizer

omit [DecidableEq k] [MeasurableSpace Ω] [MeasurableSpace Ωlim] in
/-- Build the full reduced-form Rayleigh certificate from the finite-sample
eigenvalue certificate plus the optional reduced-form limit minimizer audit
field. -/
theorem WeakIVLIMLReducedFormRayleighSelectorCertificate.of_finite_sample_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {Sigma22 : Matrix k k ℝ}
    (h : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hreduced : ∀ η,
      LIMLRayleighMinimizer
        (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
        Sigma (mustar η)) :
    WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22 :=
  WeakIVLIMLReducedFormRayleighSelectorCertificate.of_root_primitive_selector_equations
    (k := k) (l := l) h.selector_cont
    h.sample_selector_eq_root_primitive
    h.limit_selector_eq_root_primitive
    h.finite_sample_rayleigh_minimizer
    hreduced h.structural_limit_rayleigh_minimizer

omit [DecidableEq k] [MeasurableSpace Ω] [MeasurableSpace Ωlim] in
/-- Build the raw LIML eigenvalue-problem certificate from the finite-sample
Rayleigh/eigenvalue certificate plus the reduced-form limit minimizer audit
field.

This is the direct bridge from the finite-sample spectral problem to the raw
Theorem 12.18 package.  It keeps Hansen's sample selector equations on the
root primitive, preserves the finite-sample and structural minimizer facts
already carried by `h`, and asks only for the extra reduced-form limit
minimizer field that distinguishes the raw package from the finite-sample
certificate. -/
theorem WeakIVLIMLRawEigenvalueProblemConditions.of_finite_sample_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {Sigma22 : Matrix k k ℝ}
    (h : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hreduced : ∀ η,
      LIMLRayleighMinimizer
        (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
        Sigma (mustar η)) :
    WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22 where
  selector_cont := h.selector_cont
  sample_selector_eq_root_primitive := h.sample_selector_eq_root_primitive
  limit_selector_eq_root_primitive := h.limit_selector_eq_root_primitive
  finite_sample_rayleigh_minimizer := h.finite_sample_rayleigh_minimizer
  reducedForm_limit_rayleigh_minimizer := hreduced
  structural_limit_rayleigh_minimizer := h.structural_limit_rayleigh_minimizer

omit [DecidableEq k] in
/-- Finite-sample Rayleigh/eigenvalue certificate form of the reduced-form
selector CMT for `µ̂_n`.

The certificate fields are stated on Hansen's root primitive
`(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)`.  This theorem turns those exact
finite-sample selector equations into the distributional convergence of the
scaled LIML eigenvalue adjustment. -/
theorem WeakIVLIMLFiniteSampleRayleighSelectorCertificate.muHat_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hprimitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l (Sum Unit k) ℝ) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        weakIVReducedFormRayleighPrimitive Z X e β m ω)
      atTop
      (fun η => weakIVReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)
      (fun _ => μ) ν)
    (h : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) => limlMuHat m ω)
      atTop mustar (fun _ => μ) ν := by
  let hstructural :=
    WeakIVLIMLStructuralRayleighSelectorCertificate.of_finite_sample_rayleigh
      (k := k) (l := l) h
  have hraw := hprimitive.continuous_comp hstructural.selector_cont
  refine TendstoInDistribution.congr ?_ ?_ hraw
  · intro m
    exact ae_of_all μ (fun ω => by
      simp [hstructural.sample_selector_eq m ω])
  · exact ae_of_all ν (fun η => by
      simp [hstructural.limit_selector_eq η])

omit [DecidableEq k] in
/-- Root-primitive finite-sample Rayleigh/eigenvalue certificate form of the
selector CMT for `µ̂_n`.

This composes Hansen's literal root-primitive convergence with
`WeakIVLIMLFiniteSampleRayleighSelectorCertificate.muHat_tendstoInDistribution`,
so callers do not need to first rewrite to the reduced-form Rayleigh primitive. -/
theorem
    WeakIVLIMLFiniteSampleRayleighSelectorCertificate.muHat_tendstoInDistribution_of_root_primitive
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hPrimitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (h : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) => limlMuHat m ω)
      atTop mustar (fun _ => μ) ν :=
  WeakIVLIMLFiniteSampleRayleighSelectorCertificate.muHat_tendstoInDistribution
    (μ := μ) (ν := ν)
    (weakIV_reducedForm_rayleigh_primitive_tendstoInDistribution_of_root_primitive
      (μ := μ) (ν := ν) (β := β) hPrimitive)
    h

omit [DecidableEq k] in
/-- Finite-sample Rayleigh/eigenvalue selector outputs for Hansen Theorem
12.18.

From the root-primitive local-to-zero convergence and the finite-sample
Rayleigh certificate, this returns the three selector facts used by the LIML
face: `µ̂_n ⇒ µ*`, the finite-sample reduced-form Rayleigh minimizer, and
Hansen's structural Rayleigh minimizer for `µ*`. -/
theorem weakIV_liml_finite_sample_rayleigh_selector_outputs_of_root_primitive
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hPrimitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (h : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) => limlMuHat m ω)
      atTop mustar (fun _ => μ) ν ∧
    (∀ m ω,
      LIMLRayleighMinimizer
        (limlRayleighMatrix
          (sampleQZZ (stackRegressors Z m ω))
          (weakIVRootReducedFormProjectedMoment Z X e β m ω))
        Sigma (limlMuHat m ω)) ∧
    (∀ η,
      LIMLRayleighMinimizer
        (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)) :=
  ⟨WeakIVLIMLFiniteSampleRayleighSelectorCertificate.muHat_tendstoInDistribution_of_root_primitive
        (μ := μ) (ν := ν) hPrimitive h,
    h.finite_sample_rayleigh_minimizer,
    h.structural_limit_rayleigh_minimizer⟩

omit [DecidableEq k] in
/-- Raw LIML eigenvalue-problem outputs for Hansen Theorem 12.18.

This keeps the full reduced-form limit minimizer certificate alongside the
finite-sample minimizer and structural minimizer.  The distributional
convergence of `µ̂_n` is still proved by the existing continuous-mapping
selector theorem. -/
theorem weakIV_liml_raw_eigenvalue_problem_outputs_of_root_primitive
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hPrimitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (h : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) => limlMuHat m ω)
      atTop mustar (fun _ => μ) ν ∧
    (∀ m ω,
      LIMLRayleighMinimizer
        (limlRayleighMatrix
          (sampleQZZ (stackRegressors Z m ω))
          (weakIVRootReducedFormProjectedMoment Z X e β m ω))
        Sigma (limlMuHat m ω)) ∧
    (∀ η,
      LIMLRayleighMinimizer
        (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
        Sigma (mustar η)) ∧
    (∀ η,
      LIMLRayleighMinimizer
        (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)) := by
  let hred : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22 :=
    WeakIVLIMLReducedFormRayleighSelectorCertificate.of_raw_eigenvalue_problem
      (k := k) (l := l) h
  have hout :=
    weakIV_limlMuHat_tendstoInDistribution_of_reducedForm_rayleigh_argmin
      (μ := μ) (ν := ν)
      (weakIV_reducedForm_rayleigh_primitive_tendstoInDistribution_of_root_primitive
        (μ := μ) (ν := ν) (β := β) hPrimitive)
      hred.selector_cont hred.sample_selector_eq hred.limit_selector_eq
      hred.sample_rayleigh_minimizer hred.reducedForm_limit_rayleigh_minimizer
  exact
    ⟨hout.1, hout.2.1, hout.2.2, h.structural_limit_rayleigh_minimizer⟩

omit [DecidableEq k] in
/-- Continuous-selector CMT for the scaled LIML eigenvalue adjustment using
only the structural Rayleigh-selector certificate needed downstream. -/
theorem weakIV_limlMuHat_tendstoInDistribution_of_reducedForm_structural_rayleigh_selector
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hprimitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l (Sum Unit k) ℝ) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        weakIVReducedFormRayleighPrimitive Z X e β m ω)
      atTop
      (fun η => weakIVReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)
      (fun _ => μ) ν)
    (h : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) => limlMuHat m ω)
      atTop mustar (fun _ => μ) ν := by
  have hraw := hprimitive.continuous_comp h.selector_cont
  refine TendstoInDistribution.congr ?_ ?_ hraw
  · intro m
    exact ae_of_all μ (fun ω => by
      simp [h.sample_selector_eq m ω])
  · exact ae_of_all ν (fun η => by
      simp [h.limit_selector_eq η])

omit [DecidableEq k] in
/-- Certificate method form of
`weakIV_limlMuHat_tendstoInDistribution_of_reducedForm_structural_rayleigh_selector`. -/
theorem WeakIVLIMLStructuralRayleighSelectorCertificate.muHat_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hprimitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l (Sum Unit k) ℝ) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        weakIVReducedFormRayleighPrimitive Z X e β m ω)
      atTop
      (fun η => weakIVReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)
      (fun _ => μ) ν)
    (h : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) => limlMuHat m ω)
      atTop mustar (fun _ => μ) ν :=
  weakIV_limlMuHat_tendstoInDistribution_of_reducedForm_structural_rayleigh_selector
    (μ := μ) (ν := ν) hprimitive h

omit [DecidableEq k] in
/-- Structural Rayleigh-selector CMT for `µ̂_n` from Hansen's root primitive
local-to-zero first-stage/score convergence.

This composes the root primitive bridge
`weakIV_reducedForm_rayleigh_primitive_tendstoInDistribution_of_root_primitive`
with the reduced-form selector theorem, so callers do not have to assume
reduced-form Rayleigh primitive convergence separately. -/
theorem weakIV_limlMuHat_tendstoInDistribution_of_root_primitive_structural_rayleigh_selector
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hPrimitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (h : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) => limlMuHat m ω)
      atTop mustar (fun _ => μ) ν :=
  weakIV_limlMuHat_tendstoInDistribution_of_reducedForm_structural_rayleigh_selector
    (μ := μ) (ν := ν)
    (weakIV_reducedForm_rayleigh_primitive_tendstoInDistribution_of_root_primitive
      (μ := μ) (ν := ν) (β := β) hPrimitive)
    h

omit [DecidableEq k] in
/-- Certificate method form of the root-primitive structural Rayleigh selector
CMT for `µ̂_n`. -/
theorem
    WeakIVLIMLStructuralRayleighSelectorCertificate.muHat_tendstoInDistribution_of_root_primitive
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hPrimitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (h : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) => limlMuHat m ω)
      atTop mustar (fun _ => μ) ν :=
  weakIV_limlMuHat_tendstoInDistribution_of_root_primitive_structural_rayleigh_selector
    (μ := μ) (ν := ν) hPrimitive h

omit [DecidableEq k] [MeasurableSpace Ω] [MeasurableSpace Ωlim] in
/-- The older full reduced-form certificate is recovered from the narrower
structural certificate plus the optional reduced-form minimizer audit fields. -/
theorem WeakIVLIMLReducedFormRayleighSelectorCertificate.of_structural_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {Sigma22 : Matrix k k ℝ}
    (h : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (hsample : ∀ m ω,
      LIMLRayleighMinimizer
        (limlRayleighMatrix
          (sampleQZZ (stackRegressors Z m ω))
          (weakIVRootReducedFormProjectedMoment Z X e β m ω))
        Sigma (limlMuHat m ω))
    (hreduced : ∀ η,
      LIMLRayleighMinimizer
        (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
        Sigma (mustar η)) :
    WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22 where
  selector_cont := h.selector_cont
  sample_selector_eq := h.sample_selector_eq
  limit_selector_eq := h.limit_selector_eq
  sample_rayleigh_minimizer := hsample
  reducedForm_limit_rayleigh_minimizer := hreduced
  structural_limit_rayleigh_minimizer := h.structural_limit_rayleigh_minimizer

omit [DecidableEq k] in
/-- Certificate form of the reduced-form Rayleigh selector CMT for `µ̂_n`.

This wrapper keeps the continuous selector equations and Rayleigh minimizer
certificates together, so callers do not have to pass the six fields
separately. -/
theorem WeakIVLIMLReducedFormRayleighSelectorCertificate.muHat_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hprimitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l (Sum Unit k) ℝ) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        weakIVReducedFormRayleighPrimitive Z X e β m ω)
      atTop
      (fun η => weakIVReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)
      (fun _ => μ) ν)
    (h : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) => limlMuHat m ω)
      atTop mustar (fun _ => μ) ν ∧
    (∀ m ω,
      LIMLRayleighMinimizer
        (limlRayleighMatrix
          (sampleQZZ (stackRegressors Z m ω))
          (weakIVRootReducedFormProjectedMoment Z X e β m ω))
        Sigma (limlMuHat m ω)) ∧
    (∀ η,
      LIMLRayleighMinimizer
        (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
        Sigma (mustar η)) :=
  weakIV_limlMuHat_tendstoInDistribution_of_reducedForm_rayleigh_argmin
    (μ := μ) (ν := ν) hprimitive h.selector_cont
    h.sample_selector_eq h.limit_selector_eq
    h.sample_rayleigh_minimizer h.reducedForm_limit_rayleigh_minimizer

/-- LIML root-assembly conditions built from primitive root/OLS moments and a
Rayleigh-selector certificate.

This is the non-opaque replacement for the root-assembly joint-convergence
field: callers provide the primitive joint CLT
`((Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e), (Q̂_XX, n^{-1}X'e))`, nonsingularity of
`Q_ZZ`, and the Rayleigh selector certificate for `µ̂_n`/`µ*`. -/
structure WeakIVLIMLPrimitiveRayleighRootAssemblyConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ)
    (muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) : Prop where
  linear_model : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω
  estimator_meas : ∀ m, AEStronglyMeasurable
    (fun ω =>
      limlBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
        (weakIVLIMLFiniteSampleMu limlMuHat m ω))
    μ
  actual_bread_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ
  actual_score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ
  root_ols_primitive_joint_tendsto : TendstoInDistribution
    (E :=
      (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
        (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
    (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
    atTop
    (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
    (fun _ => μ) ν
  qzz_nonsing : IsUnit QZZ.det
  rayleigh_selector :
    WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22
  limit_nonsing_ae :
    ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0

/-- Convert the primitive Rayleigh-selector LIML package into the root-assembly
package consumed by the weak-scaled LIML moment CMT. -/
theorem WeakIVLIMLRootAssemblyConditions.of_primitive_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVLIMLPrimitiveRayleighRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVLIMLRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  linear_model := h.linear_model
  liml_rayleigh_minimizer := h.rayleigh_selector.structural_limit_rayleigh_minimizer
  estimator_meas := h.estimator_meas
  actual_bread_meas := h.actual_bread_meas
  actual_score_meas := h.actual_score_meas
  root_assembly_joint_tendsto :=
    weakIV_liml_root_assembly_joint_tendstoInDistribution_of_primitive_rayleigh_selector
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector)
      h.root_ols_primitive_joint_tendsto h.qzz_nonsing
      h.rayleigh_selector.selector_cont
      h.rayleigh_selector.sample_selector_eq
      h.rayleigh_selector.limit_selector_eq
  limit_nonsing_ae := h.limit_nonsing_ae

/-- LIML root-assembly conditions from primitive root/OLS moments and the
narrow structural Rayleigh-selector certificate.

This is the smaller Theorem 12.18 LIML primitive package: compared with
`WeakIVLIMLPrimitiveRayleighRootAssemblyConditions`, it removes the separate
sample and full reduced-form Rayleigh minimizer audit fields and keeps only
the finite-sample selector equation, the limit selector equation, and Hansen's
structural Rayleigh-minimum condition for `µ*`. -/
structure WeakIVLIMLStructuralRayleighRootAssemblyConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ)
    (muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ) : Prop where
  linear_model : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω
  estimator_meas : ∀ m, AEStronglyMeasurable
    (fun ω =>
      limlBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
        (weakIVLIMLFiniteSampleMu limlMuHat m ω))
    μ
  actual_bread_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ
  actual_score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ
  root_ols_primitive_joint_tendsto : TendstoInDistribution
    (E :=
      (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
        (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
    (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
    atTop
    (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
    (fun _ => μ) ν
  qzz_nonsing : IsUnit QZZ.det
  rayleigh_selector :
    WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22
  limit_nonsing_ae :
    ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0

/-- Forget the optional reduced-form minimizer audit fields from the older
primitive Rayleigh package. -/
theorem WeakIVLIMLStructuralRayleighRootAssemblyConditions.of_primitive_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVLIMLPrimitiveRayleighRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVLIMLStructuralRayleighRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector where
  linear_model := h.linear_model
  estimator_meas := h.estimator_meas
  actual_bread_meas := h.actual_bread_meas
  actual_score_meas := h.actual_score_meas
  root_ols_primitive_joint_tendsto := h.root_ols_primitive_joint_tendsto
  qzz_nonsing := h.qzz_nonsing
  rayleigh_selector := {
    selector_cont := h.rayleigh_selector.selector_cont
    sample_selector_eq := h.rayleigh_selector.sample_selector_eq
    limit_selector_eq := h.rayleigh_selector.limit_selector_eq
    structural_limit_rayleigh_minimizer :=
      h.rayleigh_selector.structural_limit_rayleigh_minimizer }
  limit_nonsing_ae := h.limit_nonsing_ae

/-- LIML structural Rayleigh root-assembly conditions from the finite-sample
Rayleigh/eigenvalue certificate.

This constructor exposes the exact sample selector/minimizer input and then
forgets only the finite-sample minimizer audit field to recover the narrower
structural selector package consumed by the LIML CMT. -/
theorem WeakIVLIMLStructuralRayleighRootAssemblyConditions.of_finite_sample_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hest : ∀ m, AEStronglyMeasurable
      (fun ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      μ)
    (hbread : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ)
    (hscore : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hlimit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    WeakIVLIMLStructuralRayleighRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector where
  linear_model := hmodel
  estimator_meas := hest
  actual_bread_meas := hbread
  actual_score_meas := hscore
  root_ols_primitive_joint_tendsto := hjoint
  qzz_nonsing := hQZZ
  rayleigh_selector :=
    WeakIVLIMLStructuralRayleighSelectorCertificate.of_finite_sample_rayleigh
      (k := k) (l := l) hrayleigh
  limit_nonsing_ae := hlimit

/-- LIML structural Rayleigh root-assembly conditions from the raw
eigenvalue-problem certificate.

This is the lower-level constructor to use when a caller has proved the full
raw LIML spectral package, including the reduced-form limit minimizer audit
field, but the downstream LIML moment CMT only needs the structural selector
surface. -/
theorem WeakIVLIMLStructuralRayleighRootAssemblyConditions.of_raw_eigenvalue_problem
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hest : ∀ m, AEStronglyMeasurable
      (fun ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      μ)
    (hbread : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ)
    (hscore : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hrayleigh : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hlimit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    WeakIVLIMLStructuralRayleighRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector :=
  WeakIVLIMLStructuralRayleighRootAssemblyConditions.of_finite_sample_rayleigh
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hest hbread hscore hjoint hQZZ
    (WeakIVLIMLFiniteSampleRayleighSelectorCertificate.of_raw_eigenvalue_problem
      (k := k) (l := l) hrayleigh)
    hlimit

/-- Convert the narrow structural Rayleigh-selector LIML package into the
root-assembly package consumed by the weak-scaled LIML moment CMT. -/
theorem WeakIVLIMLRootAssemblyConditions.of_structural_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (h : WeakIVLIMLStructuralRayleighRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector) :
    WeakIVLIMLRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  linear_model := h.linear_model
  liml_rayleigh_minimizer := h.rayleigh_selector.structural_limit_rayleigh_minimizer
  estimator_meas := h.estimator_meas
  actual_bread_meas := h.actual_bread_meas
  actual_score_meas := h.actual_score_meas
  root_assembly_joint_tendsto :=
    weakIV_liml_root_assembly_joint_tendstoInDistribution_of_primitive_rayleigh_selector
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector)
      h.root_ols_primitive_joint_tendsto h.qzz_nonsing
      h.rayleigh_selector.selector_cont
      h.rayleigh_selector.sample_selector_eq
      h.rayleigh_selector.limit_selector_eq
  limit_nonsing_ae := h.limit_nonsing_ae

private theorem weakIV_matrix_singular_measure_tendsto_zero
    {A : ℕ → Ω → Matrix k k ℝ} {A0 : Matrix k k ℝ}
    (hA_meas : ∀ m, AEStronglyMeasurable (A m) μ)
    (hA : TendstoInMeasure μ A atTop (fun _ => A0))
    (hA0 : IsUnit A0.det) :
    Tendsto (fun m => μ {ω | ¬ IsUnit (A m ω).det}) atTop (𝓝 0) := by
  have hDet : TendstoInMeasure μ
      (fun m ω => (A m ω).det) atTop (fun _ => A0.det) :=
    tendstoInMeasure_continuous_comp hA_meas hA
      (Continuous.matrix_det continuous_id)
  have hdet_ne : A0.det ≠ 0 := hA0.ne_zero
  set ε : ℝ := |A0.det| / 2 with hε_def
  have hε_pos : 0 < ε := half_pos (abs_pos.mpr hdet_ne)
  have hε_le : ε ≤ |A0.det| := by
    rw [hε_def]
    linarith [abs_nonneg A0.det]
  have hmeas_eps := hDet (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε_pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmeas_eps
    (fun _ => zero_le _) (fun m => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq, isUnit_iff_ne_zero, not_not] at hω
  simp only [Set.mem_setOf_eq, edist_dist, Real.dist_eq]
  rw [hω]
  simp only [zero_sub, abs_neg]
  exact ENNReal.ofReal_le_ofReal hε_le

omit [IsProbabilityMeasure μ] in
private theorem weakIV_pair_bread_singular_tendsto_zero_of_joint_tendsto
    {Ωlim : Type*} [MeasurableSpace Ωlim]
    {ν : Measure Ωlim} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {B : ℕ → Ω → Matrix k k ℝ} {S : ℕ → Ω → k → ℝ}
    {B0 : Ωlim → Matrix k k ℝ} {S0 : Ωlim → k → ℝ}
    (hjoint : TendstoInDistribution
      (E := Matrix k k ℝ × (k → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => ((B m ω, S m ω) :
        Matrix k k ℝ × (k → ℝ)))
      atTop
      (fun η => ((B0 η, S0 η) : Matrix k k ℝ × (k → ℝ)))
      (fun _ => μ) ν)
    (hlimit : ν {η | ¬ IsUnit (B0 η).det} = 0) :
    Tendsto (fun m => μ {ω | ¬ IsUnit (B m ω).det}) atTop (𝓝 0) := by
  classical
  let E : Set (Matrix k k ℝ × (k → ℝ)) := {p | ¬ IsUnit p.1.det}
  have hE : IsClosed E := by
    have hcont : Continuous
        (fun p : Matrix k k ℝ × (k → ℝ) => p.1.det) :=
      (continuous_fst.matrix_det)
    simpa [E, isUnit_iff_ne_zero] using
      (isClosed_singleton.preimage hcont :
        IsClosed {p : Matrix k k ℝ × (k → ℝ) | p.1.det = 0})
  have hnull_map :
      (ν.map (fun η => ((B0 η, S0 η) : Matrix k k ℝ × (k → ℝ)))) E = 0 := by
    rw [Measure.map_apply_of_aemeasurable hjoint.aemeasurable_limit hE.measurableSet]
    simpa [E] using hlimit
  have htendsto :=
    TendstoInDistribution.tendsto_measure_preimage_of_closed_null
      hjoint hE hnull_map
  simpa [E] using htendsto

omit [IsProbabilityMeasure μ] in
/-- In the weak-IV 2SLS limit, high-probability nonsingularity of the sample
bread follows from joint bread/score convergence and a.s. nonsingularity of
the random limit bread. -/
theorem weakIV_twoSLS_singular_tendsto_zero_of_joint_tendsto
    {Ωlim : Type*} [MeasurableSpace Ωlim]
    {ν : Measure Ωlim} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    (hjoint : TendstoInDistribution
      (E := Matrix k k ℝ × (k → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        ((weakIV2SLSNormalizedBread Z X m ω,
          weakIV2SLSNormalizedScore Z X e m ω) :
          Matrix k k ℝ × (k → ℝ)))
      atTop
      (fun (η : Ωlim) =>
        ((weakIV2SLSLimitBread QZZ C (Xi2 η),
          weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)) :
          Matrix k k ℝ × (k → ℝ)))
      (fun _ => μ) ν)
    (hlimit : ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0) :
    Tendsto
      (fun m => μ {ω | ¬ IsUnit (weakIV2SLSNormalizedBread Z X m ω).det})
      atTop (𝓝 0) :=
  weakIV_pair_bread_singular_tendsto_zero_of_joint_tendsto
    (μ := μ) (ν := ν)
    (B := fun m ω => weakIV2SLSNormalizedBread Z X m ω)
    (S := fun m ω => weakIV2SLSNormalizedScore Z X e m ω)
    (B0 := fun η => weakIV2SLSLimitBread QZZ C (Xi2 η))
    (S0 := fun η => weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η))
    hjoint hlimit

omit [IsProbabilityMeasure μ] in
/-- In the weak-IV LIML limit, high-probability nonsingularity of the sample
LIML bread follows from joint bread/score convergence and a.s. nonsingularity
of the random limit bread. -/
theorem weakIV_liml_singular_tendsto_zero_of_joint_tendsto
    {Ωlim : Type*} [MeasurableSpace Ωlim]
    {ν : Measure Ωlim} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hjoint : TendstoInDistribution
      (E := Matrix k k ℝ × (k → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        ((weakIVLIMLWeakScaledBread Z X limlMuHat m ω,
          weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) :
          Matrix k k ℝ × (k → ℝ)))
      atTop
      (fun (η : Ωlim) =>
        ((weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22,
          weakIVLIMLLimitScore QZZ C (Xi2 η) (xie η) (mustar η) Sigma2e) :
          Matrix k k ℝ × (k → ℝ)))
      (fun _ => μ) ν)
    (hlimit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    Tendsto
      (fun m => μ {ω | ¬ IsUnit
        (weakIVLIMLWeakScaledBread Z X limlMuHat m ω).det})
      atTop (𝓝 0) :=
  weakIV_pair_bread_singular_tendsto_zero_of_joint_tendsto
    (μ := μ) (ν := ν)
    (B := fun m ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω)
    (S := fun m ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω)
    (B0 := fun η => weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22)
    (S0 := fun η => weakIVLIMLLimitScore QZZ C (Xi2 η) (xie η) (mustar η) Sigma2e)
    hjoint hlimit

/-- Pointwise nonsingularity of Hansen's random weak-IV 2SLS limit bread
implies the a.s. nonsingularity field used by the theorem packages. -/
theorem weakIV2SLSLimitBread_nonsing_ae_of_forall
    {Ωlim : Type*} [MeasurableSpace Ωlim] {ν : Measure Ωlim}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ}
    (hunit : ∀ η, IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det) :
    ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0 := by
  have hEmpty :
      {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} =
        (∅ : Set Ωlim) := by
    ext η
    simpa [isUnit_iff_ne_zero] using (hunit η).ne_zero
  rw [hEmpty, measure_empty]

/-- Pointwise nonsingularity of Hansen's random weak-IV LIML limit bread
implies the a.s. nonsingularity field used by the theorem packages. -/
theorem weakIVLIMLLimitBread_nonsing_ae_of_forall
    {Ωlim : Type*} [MeasurableSpace Ωlim] {ν : Measure Ωlim}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hunit : ∀ η,
      IsUnit (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det) :
    ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0 := by
  have hEmpty :
      {η | ¬ IsUnit
        (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} =
        (∅ : Set Ωlim) := by
    ext η
    simpa [isUnit_iff_ne_zero] using (hunit η).ne_zero
  rw [hEmpty, measure_empty]

/-- Pointwise positive-definiteness of Hansen's random weak-IV 2SLS limit
bread implies the a.s. nonsingularity field used by the theorem packages. -/
theorem weakIV2SLSLimitBread_nonsing_ae_of_forall_posDef
    {Ωlim : Type*} [MeasurableSpace Ωlim] {ν : Measure Ωlim}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ}
    (hpos : ∀ η, (weakIV2SLSLimitBread QZZ C (Xi2 η)).PosDef) :
    ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0 :=
  weakIV2SLSLimitBread_nonsing_ae_of_forall (ν := ν)
    (fun η => (Matrix.isUnit_iff_isUnit_det _).mp (hpos η).isUnit)

/-- Pointwise positive-definiteness of Hansen's random weak-IV LIML limit
bread implies the a.s. nonsingularity field used by the theorem packages. -/
theorem weakIVLIMLLimitBread_nonsing_ae_of_forall_posDef
    {Ωlim : Type*} [MeasurableSpace Ωlim] {ν : Measure Ωlim}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hpos : ∀ η,
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).PosDef) :
    ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0 :=
  weakIVLIMLLimitBread_nonsing_ae_of_forall (ν := ν)
    (fun η => (Matrix.isUnit_iff_isUnit_det _).mp (hpos η).isUnit)

omit [DecidableEq k] in
/-- Primitive-rank bridge for the weak-IV 2SLS random limit bread.

If `QZZ` is positive definite and the weak first-stage limit
`QZZ * C + Ξ₂` has full column rank, then the Hansen 2SLS limit bread
`(QZZ*C + Ξ₂)' QZZ⁻¹ (QZZ*C + Ξ₂)` is positive definite.  This reuses the
Chapter 12 population 2SLS bread theorem instead of reproving the quadratic
form argument. -/
theorem weakIV2SLSLimitBread_posDef_of_qzz_posDef_firstStage_rank
    {QZZ : Matrix l l ℝ} {C Xi2 : Matrix l k ℝ}
    (hQZZ : QZZ.PosDef)
    (hFirst : Function.Injective (weakIVFirstStageLimit QZZ C Xi2).mulVec) :
    (weakIV2SLSLimitBread QZZ C Xi2).PosDef := by
  simpa [weakIV2SLSLimitBread, twoSLSBread] using
    (twoSLSBread_posDef_of_qzz_posDef_rank
      (QXZ := (weakIVFirstStageLimit QZZ C Xi2)ᵀ)
      (QZZ := QZZ) (QZX := weakIVFirstStageLimit QZZ C Xi2)
      rfl hQZZ hFirst)

omit [DecidableEq k] [DecidableEq l] in
/-- Full column rank of Hansen's reduced-form LIML limit matrix implies full
column rank of its weak first-stage block.

The reduced-form matrix has columns `[Aβ + ξe, A]`, where
`A = QZZ*C + Ξ₂`.  Injectivity of the full reduced-form `mulVec` map therefore
implies injectivity after restricting to vectors supported on the right block. -/
theorem weakIVFirstStageLimit_mulVec_injective_of_reducedFormLimit_mulVec_injective
    {QZZ : Matrix l l ℝ} {C Xi2 : Matrix l k ℝ}
    {xie : l → ℝ} {β : k → ℝ}
    (hRank : Function.Injective
      (weakIVReducedFormLimit QZZ C Xi2 xie β).mulVec) :
    Function.Injective (weakIVFirstStageLimit QZZ C Xi2).mulVec := by
  intro u v huv
  let embed : (k → ℝ) → Sum Unit k → ℝ :=
    fun w s => Sum.elim (fun _ : Unit => 0) w s
  have hfull :
      (weakIVReducedFormLimit QZZ C Xi2 xie β).mulVec (embed u) =
        (weakIVReducedFormLimit QZZ C Xi2 xie β).mulVec (embed v) := by
    ext i
    simpa [embed, Matrix.mulVec, dotProduct, weakIVReducedFormLimit] using
      congrFun huv i
  have hvec := hRank hfull
  ext j
  exact congrFun hvec (Sum.inr j)

omit [DecidableEq k] [DecidableEq l] in
/-- A.e. full column rank of Hansen's full reduced-form LIML limit matrix
implies a.e. full column rank of the weak first-stage block `QZZ*C + Ξ₂`. -/
theorem weakIVFirstStageLimit_rank_ae_of_reducedFormLimit_rank_ae
    {Ωlim : Type*} [MeasurableSpace Ωlim] {ν : Measure Ωlim}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ} {β : k → ℝ}
    (hRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0) :
    ν {η | ¬ Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec} = 0 := by
  refine measure_mono_null ?_ hRank
  intro η hbad hred
  exact hbad
    (weakIVFirstStageLimit_mulVec_injective_of_reducedFormLimit_mulVec_injective
      (QZZ := QZZ) (C := C) (Xi2 := Xi2 η) (xie := xie η)
      (β := β) hred)

omit [DecidableEq k] [DecidableEq l] in
/-- Pointwise full column rank of the weak first-stage limit implies the a.e.
rank field used by the weak-IV limit-bread bridges. -/
theorem weakIVFirstStageLimit_rank_ae_of_forall
    {Ωlim : Type*} [MeasurableSpace Ωlim] {ν : Measure Ωlim}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ}
    (hRank : ∀ η, Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec) :
    ν {η | ¬ Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec} = 0 := by
  have hEmpty :
      {η | ¬ Function.Injective
        (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec} =
        (∅ : Set Ωlim) := by
    ext η
    simp [hRank η]
  rw [hEmpty, measure_empty]

/-- Pointwise full-column-rank weak first-stage limits imply the a.s.
nonsingularity field for Hansen's weak-IV 2SLS random limit bread. -/
theorem weakIV2SLSLimitBread_nonsing_ae_of_qzz_posDef_firstStage_rank
    {Ωlim : Type*} [MeasurableSpace Ωlim] {ν : Measure Ωlim}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ}
    (hQZZ : QZZ.PosDef)
    (hFirst : ∀ η, Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec) :
    ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0 :=
  weakIV2SLSLimitBread_nonsing_ae_of_forall_posDef (ν := ν)
    (fun η =>
      weakIV2SLSLimitBread_posDef_of_qzz_posDef_firstStage_rank
        hQZZ (hFirst η))

/-- A.e. full-column-rank weak first-stage limits imply the a.s.
nonsingularity field for Hansen's weak-IV 2SLS random limit bread. -/
theorem weakIV2SLSLimitBread_nonsing_ae_of_qzz_posDef_firstStage_rank_ae
    {Ωlim : Type*} [MeasurableSpace Ωlim] {ν : Measure Ωlim}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ}
    (hQZZ : QZZ.PosDef)
    (hFirst : ν {η | ¬ Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec} = 0) :
    ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0 := by
  refine measure_mono_null ?_ hFirst
  intro η hsing hfull
  exact hsing <|
    (Matrix.isUnit_iff_isUnit_det _).mp
      (weakIV2SLSLimitBread_posDef_of_qzz_posDef_firstStage_rank
        hQZZ hfull).isUnit

omit [Fintype k] [DecidableEq k] in
/-- Sufficient positive-definiteness bridge for Hansen's weak-IV LIML random
limit bread.

If the weak-IV 2SLS limit bread is positive definite, the reduced-form error
covariance `Σ₂₂` is positive semidefinite, and Hansen's random LIML root
`μ*` is nonpositive, then
`A'Q_ZZ^{-1}A - μ*Σ₂₂` is positive definite.  This turns the theorem packages'
raw LIML limit-bread condition into a concrete sign-and-covariance condition
whenever the `μ* ≤ 0` side of the Rayleigh problem has been established. -/
theorem weakIVLIMLLimitBread_posDef_of_twoSLS_posDef_mu_nonpos_sigma22_posSemidef
    {QZZ : Matrix l l ℝ} {C Xi2 : Matrix l k ℝ} {mustar : ℝ}
    {Sigma22 : Matrix k k ℝ}
    (h2SLS : (weakIV2SLSLimitBread QZZ C Xi2).PosDef)
    (hSigma22 : Sigma22.PosSemidef)
    (hmu : mustar ≤ 0) :
    (weakIVLIMLLimitBread QZZ C Xi2 mustar Sigma22).PosDef := by
  have hscale : 0 ≤ -mustar := neg_nonneg.mpr hmu
  have hscaled : ((-mustar) • Sigma22).PosSemidef := hSigma22.smul hscale
  simpa [weakIVLIMLLimitBread, sub_eq_add_neg] using h2SLS.add_posSemidef hscaled

/-- Pointwise `QZZ > 0`, weak first-stage full column rank, `Σ₂₂ ≥ 0`, and
`μ* ≤ 0` imply the a.s. nonsingularity field for Hansen's weak-IV LIML random
limit bread. -/
theorem weakIVLIMLLimitBread_nonsing_ae_of_qzz_posDef_firstStage_rank_mu_nonpos
    {Ωlim : Type*} [MeasurableSpace Ωlim] {ν : Measure Ωlim}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hQZZ : QZZ.PosDef)
    (hFirst : ∀ η, Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec)
    (hSigma22 : Sigma22.PosSemidef)
    (hmu : ∀ η, mustar η ≤ 0) :
    ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0 :=
  weakIVLIMLLimitBread_nonsing_ae_of_forall_posDef (ν := ν)
    (fun η =>
      weakIVLIMLLimitBread_posDef_of_twoSLS_posDef_mu_nonpos_sigma22_posSemidef
        (weakIV2SLSLimitBread_posDef_of_qzz_posDef_firstStage_rank
          hQZZ (hFirst η))
        hSigma22 (hmu η))

/-- A.e. weak first-stage full column rank and a.e. `μ* ≤ 0` imply the a.s.
nonsingularity field for Hansen's weak-IV LIML random limit bread, under
`QZZ > 0` and `Σ₂₂ ≥ 0`. -/
theorem weakIVLIMLLimitBread_nonsing_ae_of_qzz_posDef_firstStage_rank_mu_nonpos_ae
    {Ωlim : Type*} [MeasurableSpace Ωlim] {ν : Measure Ωlim}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hQZZ : QZZ.PosDef)
    (hFirst : ν {η | ¬ Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec} = 0)
    (hSigma22 : Sigma22.PosSemidef)
    (hmu : ν {η | ¬ mustar η ≤ 0} = 0) :
    ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0 := by
  refine measure_mono_null ?_ (measure_union_null hFirst hmu)
  intro η hsing
  by_contra hbad
  rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq] at hbad
  push Not at hbad
  exact hsing <|
    (Matrix.isUnit_iff_isUnit_det _).mp
      (weakIVLIMLLimitBread_posDef_of_twoSLS_posDef_mu_nonpos_sigma22_posSemidef
        (weakIV2SLSLimitBread_posDef_of_qzz_posDef_firstStage_rank
          hQZZ hbad.1)
        hSigma22 hbad.2).isUnit

omit [Fintype l] [DecidableEq k] [DecidableEq l] in
/-- A LIML Rayleigh minimizer is nonpositive whenever any nonzero test vector
has nonpositive Rayleigh quotient. -/
theorem LIMLRayleighMinimizer.nonpos_of_quotient_nonpos
    {A Sigma : Matrix k k ℝ} {mustar : ℝ}
    (hmin : LIMLRayleighMinimizer A Sigma mustar)
    {γ : k → ℝ} (hγ : γ ≠ 0)
    (hquot : limlRayleighQuotient A Sigma γ ≤ 0) :
    mustar ≤ 0 :=
  le_trans (hmin.lower_bound γ hγ) hquot

omit [DecidableEq k] in
/-- A.e. nonpositive structural Rayleigh quotient witnesses imply a.e.
`µ* ≤ 0` for Hansen's weak-IV LIML root.

This is a sign bridge from the Rayleigh/eigenvalue certificate to the
limit-bread nonsingularity route: the raw minimizer certificate supplies the
lower bound, while the caller supplies the nonpositive quotient witness on an
a.e. event. -/
theorem weakIV_mu_nonpos_ae_of_structural_rayleigh_witness_ae
    {Ωlim : Type*} [MeasurableSpace Ωlim] {ν : Measure Ωlim}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ}
    (hmin : ∀ η,
      LIMLRayleighMinimizer
        (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η))
    (hwitness : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    ν {η | ¬ mustar η ≤ 0} = 0 := by
  refine measure_mono_null ?_ hwitness
  intro η hbad hwit
  rcases hwit with ⟨γ, hγ, hquot⟩
  exact hbad <|
    (hmin η).nonpos_of_quotient_nonpos hγ
      (by simpa [weakIVLIMLRayleighQuotient] using hquot)

/-- Pointwise `µ* ≤ 0` implies the a.e. sign field used by the weak-IV LIML
limit-bread bridge. -/
theorem weakIV_mu_nonpos_ae_of_forall
    {Ωlim : Type*} [MeasurableSpace Ωlim] {ν : Measure Ωlim}
    {mustar : Ωlim → ℝ}
    (hmu : ∀ η, mustar η ≤ 0) :
    ν {η | ¬ mustar η ≤ 0} = 0 := by
  have hEmpty : {η | ¬ mustar η ≤ 0} = (∅ : Set Ωlim) := by
    ext η
    simp [hmu η]
  rw [hEmpty, measure_empty]

omit [DecidableEq k] [DecidableEq l] in
/-- Pointwise full column rank of Hansen's full reduced-form LIML limit matrix
implies the a.e. rank field used by the weak-IV theorem packages. -/
theorem weakIVReducedFormLimit_rank_ae_of_forall
    {Ωlim : Type*} [MeasurableSpace Ωlim] {ν : Measure Ωlim}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ} {β : k → ℝ}
    (hRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec) :
    ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0 := by
  have hEmpty :
      {η | ¬ Function.Injective
        (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} =
        (∅ : Set Ωlim) := by
    ext η
    simp [hRank η]
  rw [hEmpty, measure_empty]

omit [DecidableEq k] in
/-- Pointwise nonpositive structural Rayleigh quotient witnesses imply the
a.e. witness field used to prove `µ* ≤ 0` in the weak-IV theorem packages. -/
theorem weakIVLIMLRayleigh_nonpos_witness_ae_of_forall
    {Ωlim : Type*} [MeasurableSpace Ωlim] {ν : Measure Ωlim}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {Sigma22 : Matrix k k ℝ}
    (hWitness : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0 := by
  have hEmpty :
      {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
        weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} =
        (∅ : Set Ωlim) := by
    ext η
    simp [hWitness η]
  rw [hEmpty, measure_empty]

omit [IsProbabilityMeasure μ] in
/-- Build the 2SLS weak-IV moment package without separately assuming
high-probability nonsingularity.  The singular-event probability is derived
from the joint bread/score distributional limit and the a.s. nonsingular limit
bread. -/
theorem WeakIV2SLSMomentConditions.of_joint_tendsto_limit_nonsing
    {Ωlim : Type*} [MeasurableSpace Ωlim]
    {ν : Measure Ωlim} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hest : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ)
    (hbread : ∀ m, AEStronglyMeasurable
      (fun ω => weakIV2SLSNormalizedBread Z X m ω) μ)
    (hscore : ∀ m, AEStronglyMeasurable
      (fun ω => weakIV2SLSNormalizedScore Z X e m ω) μ)
    (hjoint : TendstoInDistribution
      (E := Matrix k k ℝ × (k → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        ((weakIV2SLSNormalizedBread Z X m ω,
          weakIV2SLSNormalizedScore Z X e m ω) :
          Matrix k k ℝ × (k → ℝ)))
      atTop
      (fun (η : Ωlim) =>
        ((weakIV2SLSLimitBread QZZ C (Xi2 η),
          weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)) :
          Matrix k k ℝ × (k → ℝ)))
      (fun _ => μ) ν)
    (hlimit : ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0) :
    WeakIV2SLSMomentConditions μ ν Z X e Y β QZZ C Xi2 xie where
  linear_model := hmodel
  estimator_meas := hest
  bread_meas := hbread
  score_meas := hscore
  joint_tendsto := hjoint
  limit_nonsing_ae := hlimit
  singular_tendsto_zero :=
    weakIV_twoSLS_singular_tendsto_zero_of_joint_tendsto
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e)
      (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      hjoint hlimit

omit [IsProbabilityMeasure μ] in
/-- Build the LIML weak-IV moment package without separately assuming
high-probability nonsingularity.  The singular-event probability is derived
from the joint LIML bread/score distributional limit and the a.s. nonsingular
limit bread. -/
theorem WeakIVLIMLMomentConditions.of_joint_tendsto_limit_nonsing
    {Ωlim : Type*} [MeasurableSpace Ωlim]
    {ν : Measure Ωlim} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hrayleigh : ∀ η,
      LIMLRayleighMinimizer
        (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η))
    (hest : ∀ m, AEStronglyMeasurable
      (fun ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      μ)
    (hbread : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ)
    (hscore : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ)
    (hjoint : TendstoInDistribution
      (E := Matrix k k ℝ × (k → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        ((weakIVLIMLWeakScaledBread Z X limlMuHat m ω,
          weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) :
          Matrix k k ℝ × (k → ℝ)))
      atTop
      (fun (η : Ωlim) =>
        ((weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22,
          weakIVLIMLLimitScore QZZ C (Xi2 η) (xie η) (mustar η) Sigma2e) :
          Matrix k k ℝ × (k → ℝ)))
      (fun _ => μ) ν)
    (hlimit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    WeakIVLIMLMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  linear_model := hmodel
  liml_rayleigh_minimizer := hrayleigh
  estimator_meas := hest
  bread_meas := hbread
  score_meas := hscore
  joint_tendsto := hjoint
  limit_nonsing_ae := hlimit
  singular_tendsto_zero :=
    weakIV_liml_singular_tendsto_zero_of_joint_tendsto
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e)
      (limlMuHat := limlMuHat)
      (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (mustar := mustar) (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      hjoint hlimit

private theorem weakIV_ols_centered_aestronglyMeasurable
    {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ} {Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e) :
    ∀ m, AEStronglyMeasurable
      (fun ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β) μ := by
  intro m
  have hInv_meas : AEStronglyMeasurable
      (fun ω => (weakIVOLSNormalizedBread X m ω)⁻¹) μ :=
    aestronglyMeasurable_matrix_inv (h.bread_meas m)
  have hYscore_meas : AEStronglyMeasurable
      (fun ω =>
        sampleCrossMoment (stackRegressors X m ω) (stackOutcomes Y m ω)) μ := by
    have hYscore_eq :
        (fun ω =>
          sampleCrossMoment (stackRegressors X m ω) (stackOutcomes Y m ω)) =
        (fun ω =>
          weakIVOLSNormalizedBread X m ω *ᵥ β +
            weakIVOLSNormalizedScore X e m ω) := by
      funext ω
      rw [sampleCrossMoment_stackOutcomes_linear_model X e Y β h.linear_model]
      simp [weakIVOLSNormalizedBread, weakIVOLSNormalizedScore]
    rw [hYscore_eq]
    exact
      ((Continuous.matrix_mulVec continuous_id continuous_const).comp_aestronglyMeasurable
          (h.bread_meas m)).add
        (h.score_meas m)
  have hBeta_meas : AEStronglyMeasurable
      (fun ω =>
        (weakIVOLSNormalizedBread X m ω)⁻¹ *ᵥ
          sampleCrossMoment (stackRegressors X m ω) (stackOutcomes Y m ω)) μ :=
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      (hInv_meas.prodMk hYscore_meas)
  have hOLS_meas : AEStronglyMeasurable
      (fun ω => olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω)) μ := by
    convert hBeta_meas using 1
    funext ω
    rw [olsBetaStar_stack_eq_sampleGramInv_sampleCrossMoment]
    simp [weakIVOLSNormalizedBread]
  exact hOLS_meas.sub aestronglyMeasurable_const

private theorem weakIV_ols_leading_score_aestronglyMeasurable
    {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ} {Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e) :
    ∀ m, AEStronglyMeasurable
      (fun ω =>
        (weakIVOLSNormalizedBread X m ω)⁻¹ *ᵥ
          weakIVOLSNormalizedScore X e m ω) μ := by
  intro m
  exact
    (Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((aestronglyMeasurable_matrix_inv (h.bread_meas m)).prodMk (h.score_meas m))

private theorem weakIV_ols_totalization_remainder_tendstoInMeasure_zero
    {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ} {Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e) :
    TendstoInMeasure μ
      (fun m ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β -
          (weakIVOLSNormalizedBread X m ω)⁻¹ *ᵥ
            weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => (0 : k → ℝ)) := by
  have hsingular := weakIV_matrix_singular_measure_tendsto_zero
    (A := fun m ω => weakIVOLSNormalizedBread X m ω)
    h.bread_meas h.bread_tendsto h.bread_nonsing
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsingular
    (fun _ => zero_le _) (fun m => ?_)
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro hunit
  have hunit' : IsUnit (sampleGram (stackRegressors X m ω)).det := by
    simpa [weakIVOLSNormalizedBread] using hunit
  have hR :
      olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β -
          (weakIVOLSNormalizedBread X m ω)⁻¹ *ᵥ
            weakIVOLSNormalizedScore X e m ω = 0 := by
    have hbase :
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β -
            (sampleGram (stackRegressors X m ω))⁻¹ *ᵥ
              sampleCrossMoment (stackRegressors X m ω) (stackErrors e m ω) = 0 := by
      rw [olsBetaStar_sub_identity X e Y β h.linear_model m ω,
        Matrix.nonsing_inv_mul _ hunit', sub_self, Matrix.zero_mulVec]
    simpa [weakIVOLSNormalizedBread, weakIVOLSNormalizedScore] using hbase
  rw [hR, edist_self] at hω
  exact absurd hω (not_le.mpr hε)

/-- Moment-level OLS constructor for Hansen Theorem 12.18.

If the normalized OLS bread converges to `Σ₂₂` and the normalized structural
score converges to `Σ₂e`, with nonsingular limiting bread, then
`β̂_ols - β ->p Σ₂₂^{-1}Σ₂e`.  This replaces the proof-facing direct OLS-limit
assumption with smaller bread/score convergence assumptions. -/
theorem weakIV_olsBetaStar_minus_beta_tendstoInMeasure_of_moments
    {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ} {Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e) :
    TendstoInMeasure μ
      (fun m ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) := by
  have hInv_meas : ∀ m, AEStronglyMeasurable
      (fun ω => (weakIVOLSNormalizedBread X m ω)⁻¹) μ :=
    fun m => aestronglyMeasurable_matrix_inv (h.bread_meas m)
  have hInv : TendstoInMeasure μ
      (fun m ω => (weakIVOLSNormalizedBread X m ω)⁻¹)
      atTop (fun _ => Sigma22⁻¹) :=
    tendstoInMeasure_matrix_inv h.bread_meas h.bread_tendsto
      (fun _ => h.bread_nonsing)
  have hLeading : TendstoInMeasure μ
      (fun m ω =>
        (weakIVOLSNormalizedBread X m ω)⁻¹ *ᵥ
          weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) := by
    simpa [weakIVOLSBias] using
      tendstoInMeasure_mulVec hInv_meas h.score_meas hInv h.score_tendsto
  have hRemainder := weakIV_ols_totalization_remainder_tendstoInMeasure_zero h
  have hCentered_meas := weakIV_ols_centered_aestronglyMeasurable h
  have hLeading_meas := weakIV_ols_leading_score_aestronglyMeasurable h
  have hRemainder_meas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β -
          (weakIVOLSNormalizedBread X m ω)⁻¹ *ᵥ
            weakIVOLSNormalizedScore X e m ω) μ :=
    fun m => (hCentered_meas m).sub (hLeading_meas m)
  have hsum := tendstoInMeasure_add hLeading_meas hRemainder_meas hLeading hRemainder
  refine TendstoInMeasure.congr ?_ ?_ hsum
  · intro m
    exact ae_of_all μ (fun ω => by
      ext i
      simp [Pi.add_apply, Pi.sub_apply])
  · exact ae_of_all μ (fun _ => by
      ext i
      simp [Pi.add_apply])

/-- Uncentered OLS constructor for Hansen Theorem 12.18 from the same
moment-level bread/score package. -/
theorem weakIV_olsBetaStar_tendstoInMeasure_of_moments
    {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ} {Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e) :
    TendstoInMeasure μ
      (fun m ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) := by
  have hCentered := weakIV_olsBetaStar_minus_beta_tendstoInMeasure_of_moments h
  have hCentered_meas := weakIV_ols_centered_aestronglyMeasurable h
  have hAdd := tendstoInMeasure_continuous_comp hCentered_meas hCentered
    (by fun_prop : Continuous fun x : k → ℝ => β + x)
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hAdd
  intro m
  exact ae_of_all μ (fun ω => by
    ext i
    simp [Pi.add_apply, Pi.sub_apply])

private theorem weakIV_twoSLS_inverse_score_map_measurable :
    Measurable
      (fun p : Matrix k k ℝ × (k → ℝ) => p.1⁻¹ *ᵥ p.2) := by
  have hdet : Measurable
      (fun p : Matrix k k ℝ × (k → ℝ) => (p.1).det) :=
    (Continuous.matrix_det continuous_fst).measurable
  have hadj : Measurable
      (fun p : Matrix k k ℝ × (k → ℝ) => (p.1).adjugate) :=
    (Continuous.matrix_adjugate continuous_fst).measurable
  have hinv_det : Measurable
      (fun p : Matrix k k ℝ × (k → ℝ) => Ring.inverse (p.1).det) := by
    have heq :
        (fun p : Matrix k k ℝ × (k → ℝ) => Ring.inverse (p.1).det) =
          (fun p => ((p.1).det)⁻¹) := by
      funext p
      exact Ring.inverse_eq_inv _
    rw [heq]
    exact measurable_inv.comp hdet
  have hmat_inv : Measurable
      (fun p : Matrix k k ℝ × (k → ℝ) => p.1⁻¹) := by
    have heq :
        (fun p : Matrix k k ℝ × (k → ℝ) => p.1⁻¹) =
          (fun p => Ring.inverse (p.1).det • (p.1).adjugate) := by
      funext p
      exact Matrix.inv_def p.1
    rw [heq]
    exact hinv_det.smul hadj
  exact (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp
    (hmat_inv.prodMk measurable_snd)

private theorem weakIV_twoSLS_singular_pair_measurable :
    MeasurableSet
      {p : Matrix k k ℝ × (k → ℝ) | ¬ IsUnit (p.1).det} := by
  have hdet : Measurable
      (fun p : Matrix k k ℝ × (k → ℝ) => (p.1).det) :=
    (Continuous.matrix_det continuous_fst).measurable
  rw [show {p : Matrix k k ℝ × (k → ℝ) | ¬ IsUnit (p.1).det} =
      (fun p : Matrix k k ℝ × (k → ℝ) => (p.1).det) ⁻¹' {0} by
        ext p
        simp [isUnit_iff_ne_zero]]
  exact hdet (measurableSet_singleton (0 : ℝ))

private theorem weakIV_twoSLS_inverse_score_continuousAt_of_nonsingular
    (p : Matrix k k ℝ × (k → ℝ))
    (hp : IsUnit (p.1).det) :
    ContinuousAt (fun q : Matrix k k ℝ × (k → ℝ) => q.1⁻¹ *ᵥ q.2) p := by
  have hInv : ContinuousAt (fun A : Matrix k k ℝ => A⁻¹) p.1 := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hp.ne_zero
  have hInvProd : ContinuousAt
      (fun q : Matrix k k ℝ × (k → ℝ) => q.1⁻¹) p :=
    hInv.comp continuousAt_fst
  exact (Continuous.matrix_mulVec continuous_fst continuous_snd).continuousAt.comp
    (hInvProd.prodMk continuousAt_snd)

omit [Fintype k] [DecidableEq k] [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Hansen's root-scaled weak-IV bread is `n` times the normalized 2SLS
bread. -/
theorem weakIV2SLSRootScaledBread_eq_card_smul_normalizedBread
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (m : ℕ) (ω : Ω) :
    weakIV2SLSRootScaledBread Z X m ω =
      (m : ℝ) • weakIV2SLSNormalizedBread Z X m ω := by
  simp [weakIV2SLSRootScaledBread, weakIV2SLSRootScaledFirstStage,
    weakIV2SLSNormalizedBread, sampleQXZ, twoSLSBread,
    Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

omit [Fintype k] [DecidableEq k] [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Hansen's root-scaled weak-IV score is `n` times the normalized 2SLS
structural-error score. -/
theorem weakIV2SLSRootScaledScore_eq_card_smul_normalizedScore
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (m : ℕ) (ω : Ω) :
    weakIV2SLSRootScaledScore Z X e m ω =
      (m : ℝ) • weakIV2SLSNormalizedScore Z X e m ω := by
  have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hsqrt :
      Real.sqrt (m : ℝ) * (m : ℝ)⁻¹ * Real.sqrt (m : ℝ) =
        (m : ℝ) * (m : ℝ)⁻¹ := by
    rw [mul_assoc, mul_comm (m : ℝ)⁻¹ (Real.sqrt (m : ℝ)), ← mul_assoc,
      ← sq, Real.sq_sqrt hm_nonneg]
  simp [weakIV2SLSRootScaledScore, weakIV2SLSRootScaledFirstStage,
    weakIV2SLSRootScaledInstrumentScore, weakIV2SLSNormalizedScore,
    sampleQXZ, Matrix.smul_mul, Matrix.smul_mulVec, Matrix.mulVec_smul,
    smul_smul, hsqrt]

omit [Fintype k] [DecidableEq k] in
private theorem weakIV_limlNormalizedMomentMatrixStar_eq_zero_sub_mu_residual
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
private theorem weakIV_limlNormalizedMomentVectorStar_eq_zero_sub_mu_residual
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq n] [DecidableEq l]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (e : n → ℝ) (muHat : ℝ) :
    limlNormalizedMomentVectorStar Z X e muHat =
      limlNormalizedMomentVectorStar Z X e 0 -
        muHat • (sampleCrossMoment X e - limlNormalizedMomentVectorStar Z X e 0) := by
  ext a
  simp [limlNormalizedMomentVectorStar, limlMomentVectorStar, limlWeightMatrixStar,
    sampleCrossMoment, Matrix.mul_sub, Matrix.sub_mulVec, Matrix.smul_mulVec]
  ring_nf

omit [Fintype k] [DecidableEq k] [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
private theorem weakIVLIMLNormalizedBread_zero_eq_twoSLSNormalizedBread
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (m : ℕ) (ω : Ω) :
    weakIVLIMLNormalizedBread Z X (fun _ _ => 0) m ω =
      weakIV2SLSNormalizedBread Z X m ω := by
  by_cases hm : m = 0
  · subst m
    simp [weakIVLIMLNormalizedBread, weakIV2SLSNormalizedBread,
      limlNormalizedMomentMatrixStar, sampleQXZ, twoSLSBread, sampleQZZ,
      sampleGram]
  · haveI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
    have h :=
      twoSLSBread_sample_eq_card_inv_smul_momentMatrixStar
        (Z := stackRegressors Z m ω) (X := stackRegressors X m ω)
    calc
      weakIVLIMLNormalizedBread Z X (fun _ _ => 0) m ω =
          (Fintype.card (Fin m) : ℝ)⁻¹ •
            twoSLSMomentMatrixStar (stackRegressors Z m ω) (stackRegressors X m ω) := by
        simp [weakIVLIMLNormalizedBread, limlNormalizedMomentMatrixStar]
      _ = weakIV2SLSNormalizedBread Z X m ω := by
        simpa [weakIV2SLSNormalizedBread] using h.symm

omit [Fintype k] [DecidableEq k] in
private theorem weakIV_twoSLSNormalizedScore_eq_card_inv_smul_momentVectorStar
    {n l : Type*} [Fintype n] [Fintype l] [DecidableEq l]
    (Z : Matrix n l ℝ) (X : Matrix n k ℝ) (e : n → ℝ) [Nonempty n] :
    (sampleQXZ Z X * (sampleQZZ Z)⁻¹) *ᵥ sampleCrossMoment Z e =
      (Fintype.card n : ℝ)⁻¹ • twoSLSMomentVectorStar Z X e := by
  have hN : (Fintype.card n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold sampleQXZ sampleQZX sampleQZZ sampleGram sampleCrossMoment
    twoSLSMomentVectorStar instrumentProjectionStar
  rw [nonsingInv_smul]
  simp [Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mulVec_smul, Matrix.mul_assoc, smul_smul, hN]

omit [Fintype k] [DecidableEq k] [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
private theorem weakIVLIMLNormalizedScore_zero_eq_twoSLSNormalizedScore
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (m : ℕ) (ω : Ω) :
    weakIVLIMLNormalizedScore Z X e (fun _ _ => 0) m ω =
      weakIV2SLSNormalizedScore Z X e m ω := by
  by_cases hm : m = 0
  · subst m
    simp [weakIVLIMLNormalizedScore, weakIV2SLSNormalizedScore,
      limlNormalizedMomentVectorStar, sampleQXZ, sampleCrossMoment, sampleQZZ,
      sampleGram]
  · haveI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
    have h :=
      weakIV_twoSLSNormalizedScore_eq_card_inv_smul_momentVectorStar
        (Z := stackRegressors Z m ω) (X := stackRegressors X m ω)
        (e := stackErrors e m ω)
    calc
      weakIVLIMLNormalizedScore Z X e (fun _ _ => 0) m ω =
          (Fintype.card (Fin m) : ℝ)⁻¹ •
            twoSLSMomentVectorStar
              (stackRegressors Z m ω) (stackRegressors X m ω) (stackErrors e m ω) := by
        simp [weakIVLIMLNormalizedScore, limlNormalizedMomentVectorStar]
      _ = weakIV2SLSNormalizedScore Z X e m ω := by
        simpa [weakIV2SLSNormalizedScore] using h.symm

omit [Fintype k] [DecidableEq k] [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Exact finite-sample weak-IV LIML bread decomposition.

The weak-scaled LIML bread, formed with finite-sample adjustment `µ̂_n/n`, is
the root-assembled LIML bread plus the small projected 2SLS remainder
`µ̂_n n^{-1}` times the root 2SLS bread. -/
theorem weakIVLIMLWeakScaledBread_eq_root_assembled_add_projected
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (limlMuHat : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) :
    weakIVLIMLWeakScaledBread Z X limlMuHat m ω =
      weakIVLIMLRootAssembledBread Z X limlMuHat m ω +
        limlMuHat m ω • weakIV2SLSNormalizedBread Z X m ω := by
  by_cases hm : m = 0
  · subst m
    ext a b
    simp [weakIVLIMLWeakScaledBread, weakIVLIMLNormalizedBread,
      weakIVLIMLRootAssembledBread, weakIV2SLSRootScaledBread,
      weakIV2SLSNormalizedBread, weakIVOLSNormalizedBread,
      weakIVLIMLFiniteSampleMu, limlNormalizedMomentMatrixStar,
      sampleQXZ, twoSLSBread, sampleQZZ, sampleGram]
  have hsplit :
      weakIVLIMLNormalizedBread Z X (weakIVLIMLFiniteSampleMu limlMuHat) m ω =
        weakIVLIMLNormalizedBread Z X (fun _ _ => 0) m ω -
          weakIVLIMLFiniteSampleMu limlMuHat m ω •
            (weakIVOLSNormalizedBread X m ω -
              weakIVLIMLNormalizedBread Z X (fun _ _ => 0) m ω) := by
    simpa [weakIVLIMLNormalizedBread, weakIVOLSNormalizedBread] using
      weakIV_limlNormalizedMomentMatrixStar_eq_zero_sub_mu_residual
        (Z := stackRegressors Z m ω) (X := stackRegressors X m ω)
        (muHat := weakIVLIMLFiniteSampleMu limlMuHat m ω)
  have hm_real : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  ext a b
  simp [weakIVLIMLWeakScaledBread, hsplit,
    weakIVLIMLNormalizedBread_zero_eq_twoSLSNormalizedBread,
    weakIV2SLSRootScaledBread_eq_card_smul_normalizedBread,
    weakIVLIMLRootAssembledBread, weakIVLIMLFiniteSampleMu]
  field_simp [hm_real]
  ring

omit [Fintype k] [DecidableEq k] [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- Exact finite-sample weak-IV LIML score decomposition. -/
theorem weakIVLIMLWeakScaledScore_eq_root_assembled_add_projected
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (limlMuHat : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) :
    weakIVLIMLWeakScaledScore Z X e limlMuHat m ω =
      weakIVLIMLRootAssembledScore Z X e limlMuHat m ω +
        limlMuHat m ω • weakIV2SLSNormalizedScore Z X e m ω := by
  by_cases hm : m = 0
  · subst m
    ext a
    simp [weakIVLIMLWeakScaledScore, weakIVLIMLNormalizedScore,
      weakIVLIMLRootAssembledScore, weakIV2SLSRootScaledScore,
      weakIV2SLSRootScaledFirstStage, weakIV2SLSRootScaledInstrumentScore,
      weakIV2SLSNormalizedScore, weakIVOLSNormalizedScore,
      weakIVLIMLFiniteSampleMu, limlNormalizedMomentVectorStar,
      sampleQXZ, sampleCrossMoment, sampleQZZ, sampleGram]
  have hsplit :
      weakIVLIMLNormalizedScore Z X e (weakIVLIMLFiniteSampleMu limlMuHat) m ω =
        weakIVLIMLNormalizedScore Z X e (fun _ _ => 0) m ω -
          weakIVLIMLFiniteSampleMu limlMuHat m ω •
            (weakIVOLSNormalizedScore X e m ω -
              weakIVLIMLNormalizedScore Z X e (fun _ _ => 0) m ω) := by
    simpa [weakIVLIMLNormalizedScore, weakIVOLSNormalizedScore] using
      weakIV_limlNormalizedMomentVectorStar_eq_zero_sub_mu_residual
        (Z := stackRegressors Z m ω) (X := stackRegressors X m ω)
        (e := stackErrors e m ω)
        (muHat := weakIVLIMLFiniteSampleMu limlMuHat m ω)
  have hm_real : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  ext a
  simp [weakIVLIMLWeakScaledScore, hsplit,
    weakIVLIMLNormalizedScore_zero_eq_twoSLSNormalizedScore,
    weakIV2SLSRootScaledScore_eq_card_smul_normalizedScore,
    weakIVLIMLRootAssembledScore, weakIVLIMLFiniteSampleMu]
  field_simp [hm_real]
  ring

/-- Continuous map sending the root/OLS/`µ̂` assembly tuple to the projected
2SLS remainder `µ̂_n (B₂ₛₗₛ, S₂ₛₗₛ)`. -/
noncomputable def weakIVLIMLRootProjectedRemainderMap
    (p :
      ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ) :
    Matrix k k ℝ × (k → ℝ) :=
  p.2 • p.1.1

omit [DecidableEq k] in
/-- The finite-sample scaled-LIML normalization differs from the
root-assembled LIML bread/score pair by an `o_p(1)` projected 2SLS remainder.

This is the exact replacement for the former proof obligation
`WeakIVLIMLRootAssemblyConditions.actual_assembled_gap`.  The proof uses the
root/OLS/`µ̂` joint distributional limit only to get tightness of
`µ̂_n (B₂ₛₗₛ, S₂ₛₗₛ)`, then multiplies by the deterministic `n⁻¹` scale. -/
theorem weakIV_liml_weak_scaled_actual_assembled_gap_tendstoInMeasure
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hjoint : TendstoInDistribution
      (E := ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ)
      (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        ((((weakIV2SLSRootScaledBread Z X m ω,
            weakIV2SLSRootScaledScore Z X e m ω),
           (weakIVOLSNormalizedBread X m ω,
            weakIVOLSNormalizedScore X e m ω)),
          limlMuHat m ω) :
          ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ))
      atTop
      (fun η =>
        ((((weakIV2SLSLimitBread QZZ C (Xi2 η),
            weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)),
           (Sigma22, Sigma2e)),
          mustar η) :
          ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ))
      (fun _ => μ) ν) :
    TendstoInMeasure μ
      (fun m ω =>
        (((weakIVLIMLWeakScaledBread Z X limlMuHat m ω,
            weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) :
            Matrix k k ℝ × (k → ℝ)) -
          ((weakIVLIMLRootAssembledBread Z X limlMuHat m ω,
            weakIVLIMLRootAssembledScore Z X e limlMuHat m ω) :
            Matrix k k ℝ × (k → ℝ))))
      atTop (fun _ => (0 : Matrix k k ℝ × (k → ℝ))) := by
  have hcont :
      Continuous (weakIVLIMLRootProjectedRemainderMap (k := k)) := by
    unfold weakIVLIMLRootProjectedRemainderMap
    fun_prop
  have hdist := hjoint.continuous_comp hcont
  have htight :
      BoundedInProbabilityNorm μ
        (fun (m : ℕ) (ω : Ω) =>
          weakIVLIMLRootProjectedRemainderMap
            ((((weakIV2SLSRootScaledBread Z X m ω,
                weakIV2SLSRootScaledScore Z X e m ω),
               (weakIVOLSNormalizedBread X m ω,
                weakIVOLSNormalizedScore X e m ω)),
              limlMuHat m ω) :
              ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ)) :=
    BoundedInProbabilityNorm.of_tendstoInDistribution hdist
  have hc : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsmall := htight.tendstoInMeasure_const_smul_zero hc
  refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hsmall
  intro m
  exact ae_of_all μ (fun ω => by
    by_cases hm : m = 0
    · subst m
      ext a b <;>
        simp [weakIVLIMLWeakScaledBread, weakIVLIMLWeakScaledScore,
          weakIVLIMLRootAssembledBread, weakIVLIMLRootAssembledScore,
          weakIV2SLSRootScaledBread, weakIV2SLSRootScaledScore,
          weakIV2SLSRootScaledFirstStage, weakIV2SLSRootScaledInstrumentScore,
          weakIVOLSNormalizedBread, weakIVOLSNormalizedScore,
          weakIVLIMLRootProjectedRemainderMap,
          sampleQZZ, sampleGram, sampleCrossMoment]
    · ext a b <;>
        simp [weakIVLIMLRootProjectedRemainderMap,
          weakIVLIMLWeakScaledBread_eq_root_assembled_add_projected,
          weakIVLIMLWeakScaledScore_eq_root_assembled_add_projected,
          weakIV2SLSRootScaledBread_eq_card_smul_normalizedBread,
          weakIV2SLSRootScaledScore_eq_card_smul_normalizedScore]
      all_goals
        field_simp [show (m : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hm]
        try ring)

/-- Build the LIML weak-IV moment package from the root/OLS/`µ̂` assembly
surface.

This constructor derives the LIML bread/score distributional field by CMT from
the root 2SLS bread/score pair, the OLS bread/score pair, and the scaled LIML
eigenvalue adjustment, then transfers from the root-assembled pair to the
weak-scaled finite-sample LIML pair using
`weakIV_liml_weak_scaled_actual_assembled_gap_tendstoInMeasure`. -/
theorem WeakIVLIMLMomentConditions.of_root_assembly
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVLIMLRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVLIMLMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e := by
  have hAssembled :=
    weakIV_liml_root_assembled_bread_score_tendstoInDistribution
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e)
      (limlMuHat := limlMuHat) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      h.root_assembly_joint_tendsto
  have hActual_meas : ∀ m, AEMeasurable
      (fun ω =>
        ((weakIVLIMLWeakScaledBread Z X limlMuHat m ω,
          weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) :
          Matrix k k ℝ × (k → ℝ))) μ :=
    fun m => (h.actual_bread_meas m).aemeasurable.prodMk
      (h.actual_score_meas m).aemeasurable
  have hGap :=
    weakIV_liml_weak_scaled_actual_assembled_gap_tendstoInMeasure
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e)
      (limlMuHat := limlMuHat) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      h.root_assembly_joint_tendsto
  have hActual_joint : TendstoInDistribution
      (E := Matrix k k ℝ × (k → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        ((weakIVLIMLWeakScaledBread Z X limlMuHat m ω,
          weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) :
          Matrix k k ℝ × (k → ℝ)))
      atTop
      (fun (η : Ωlim) =>
        ((weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22,
          weakIVLIMLLimitScore QZZ C (Xi2 η) (xie η) (mustar η) Sigma2e) :
          Matrix k k ℝ × (k → ℝ)))
      (fun _ => μ) ν :=
    tendstoInDistribution_of_tendstoInMeasure_sub
      (X := fun (m : ℕ) (ω : Ω) =>
        ((weakIVLIMLRootAssembledBread Z X limlMuHat m ω,
          weakIVLIMLRootAssembledScore Z X e limlMuHat m ω) :
          Matrix k k ℝ × (k → ℝ)))
      (Y := fun (m : ℕ) (ω : Ω) =>
        ((weakIVLIMLWeakScaledBread Z X limlMuHat m ω,
          weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) :
          Matrix k k ℝ × (k → ℝ)))
      (Z := fun (η : Ωlim) =>
        ((weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22,
          weakIVLIMLLimitScore QZZ C (Xi2 η) (xie η) (mustar η) Sigma2e) :
          Matrix k k ℝ × (k → ℝ)))
      hAssembled hGap hActual_meas
  exact
    WeakIVLIMLMomentConditions.of_joint_tendsto_limit_nonsing
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      h.linear_model h.liml_rayleigh_minimizer h.estimator_meas
      h.actual_bread_meas h.actual_score_meas hActual_joint h.limit_nonsing_ae

/-- Build the LIML weak-IV moment package from primitive root/OLS moments and
the narrow structural Rayleigh-selector certificate. -/
theorem WeakIVLIMLMomentConditions.of_structural_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (h : WeakIVLIMLStructuralRayleighRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector) :
    WeakIVLIMLMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVLIMLMomentConditions.of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVLIMLRootAssemblyConditions.of_structural_rayleigh
      (μ := μ) (ν := ν) h)

/-- Build the LIML weak-IV moment package from primitive root/OLS moments and
the finite-sample Rayleigh/eigenvalue certificate.

This is the lower-level LIML-only version of the theorem-facing finite-sample
Rayleigh route: it derives the LIML bread/score convergence package without
also carrying OLS and 2SLS theorem endpoints. -/
theorem WeakIVLIMLMomentConditions.of_finite_sample_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hest : ∀ m, AEStronglyMeasurable
      (fun ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      μ)
    (hbread : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ)
    (hscore : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hlimit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    WeakIVLIMLMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVLIMLMomentConditions.of_structural_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVLIMLStructuralRayleighRootAssemblyConditions.of_finite_sample_rayleigh
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hest hbread hscore hjoint hQZZ hrayleigh hlimit)

/-- Build the LIML weak-IV moment package from primitive root/OLS moments and
the raw LIML eigenvalue-problem certificate.

The raw certificate retains the reduced-form limit minimizer audit field; this
constructor uses it through the finite-sample Rayleigh route and does not add
any new spectral asymptotic assumption. -/
theorem WeakIVLIMLMomentConditions.of_raw_eigenvalue_problem
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hest : ∀ m, AEStronglyMeasurable
      (fun ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      μ)
    (hbread : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ)
    (hscore : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hrayleigh : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hlimit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    WeakIVLIMLMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVLIMLMomentConditions.of_finite_sample_rayleigh
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hest hbread hscore hjoint hQZZ
    (WeakIVLIMLFiniteSampleRayleighSelectorCertificate.of_raw_eigenvalue_problem
      (k := k) (l := l) hrayleigh)
    hlimit

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- On nonempty samples, the inverse-score term is invariant to Hansen's
root scaling of both the weak-IV bread and score. -/
theorem weakIV2SLSRootScaled_inverse_score_eq_normalized
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (m : ℕ) (ω : Ω) [Nonempty (Fin m)] :
    (weakIV2SLSRootScaledBread Z X m ω)⁻¹ *ᵥ
        weakIV2SLSRootScaledScore Z X e m ω =
      (weakIV2SLSNormalizedBread Z X m ω)⁻¹ *ᵥ
        weakIV2SLSNormalizedScore Z X e m ω := by
  have hm_card : (Fintype.card (Fin m) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm : (m : ℝ) ≠ 0 := by
    simpa using hm_card
  rw [weakIV2SLSRootScaledBread_eq_card_smul_normalizedBread,
    weakIV2SLSRootScaledScore_eq_card_smul_normalizedScore]
  rw [nonsingInv_smul]
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
    inv_mul_cancel₀ hm, one_smul]

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
/-- On nonempty samples, the LIML inverse-score term is invariant to multiplying
both the finite-sample LIML bread and score by Hansen's weak-IV scale `n`. -/
theorem weakIVLIMLWeakScaled_inverse_score_eq_normalized
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (limlMuHat : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) [Nonempty (Fin m)] :
    (weakIVLIMLWeakScaledBread Z X limlMuHat m ω)⁻¹ *ᵥ
        weakIVLIMLWeakScaledScore Z X e limlMuHat m ω =
      (weakIVLIMLNormalizedBread Z X (weakIVLIMLFiniteSampleMu limlMuHat) m ω)⁻¹ *ᵥ
        weakIVLIMLNormalizedScore Z X e (weakIVLIMLFiniteSampleMu limlMuHat) m ω := by
  have hm_card : (Fintype.card (Fin m) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hm : (m : ℝ) ≠ 0 := by
    simpa using hm_card
  rw [weakIVLIMLWeakScaledBread, weakIVLIMLWeakScaledScore]
  rw [nonsingInv_smul]
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul,
    inv_mul_cancel₀ hm, one_smul]

/-- Leading 2SLS weak-IV inverse-score CMT.

Joint convergence of the normalized projected bread and structural-error score
implies convergence of the inverse-bread score term to Hansen's random weak-IV
2SLS drift.  The inverse map is handled by the a.s.-continuity CMT off the
singular limiting-bread set. -/
theorem weakIV_twoSLS_leading_tendstoInDistribution_of_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    (h : WeakIV2SLSMomentConditions μ ν Z X e Y β QZZ C Xi2 xie) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        (weakIV2SLSNormalizedBread Z X m ω)⁻¹ *ᵥ
          weakIV2SLSNormalizedScore Z X e m ω)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν := by
  let D : Set (Matrix k k ℝ × (k → ℝ)) :=
    {p | ¬ IsUnit (p.1).det}
  have hD_meas : MeasurableSet D := by
    simpa [D] using (weakIV_twoSLS_singular_pair_measurable (k := k))
  have hD_null :
      (ν.map (fun η =>
        ((weakIV2SLSLimitBread QZZ C (Xi2 η),
          weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)) :
          Matrix k k ℝ × (k → ℝ)))) D = 0 := by
    rw [Measure.map_apply_of_aemeasurable h.joint_tendsto.aemeasurable_limit hD_meas]
    simpa [D] using h.limit_nonsing_ae
  have hcont : ∀ p : Matrix k k ℝ × (k → ℝ), p ∉ D →
      ContinuousAt (fun q : Matrix k k ℝ × (k → ℝ) => q.1⁻¹ *ᵥ q.2) p := by
    intro p hp
    have hpunit : IsUnit (p.1).det := by
      simpa [D] using hp
    exact weakIV_twoSLS_inverse_score_continuousAt_of_nonsingular (k := k) p hpunit
  have hraw := tendstoInDistribution_ae_continuous_comp
    (X := fun (m : ℕ) (ω : Ω) =>
      ((weakIV2SLSNormalizedBread Z X m ω,
        weakIV2SLSNormalizedScore Z X e m ω) :
        Matrix k k ℝ × (k → ℝ)))
    (Z := fun η =>
      ((weakIV2SLSLimitBread QZZ C (Xi2 η),
        weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)) :
        Matrix k k ℝ × (k → ℝ)))
    h.joint_tendsto weakIV_twoSLS_inverse_score_map_measurable hD_null hcont
  simpa [weakIV2SLSBias_eq_limitBread_inv_mul_score] using hraw

omit [IsProbabilityMeasure μ] in
/-- In the root-scaled weak-IV 2SLS limit, high-probability nonsingularity of
the sample root bread follows from joint root bread/score convergence and
a.s. nonsingularity of the random limit bread. -/
theorem weakIV_twoSLS_root_singular_tendsto_zero_of_joint_tendsto
    {Ωlim : Type*} [MeasurableSpace Ωlim]
    {ν : Measure Ωlim} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    (hjoint : TendstoInDistribution
      (E := Matrix k k ℝ × (k → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        ((weakIV2SLSRootScaledBread Z X m ω,
          weakIV2SLSRootScaledScore Z X e m ω) :
          Matrix k k ℝ × (k → ℝ)))
      atTop
      (fun (η : Ωlim) =>
        ((weakIV2SLSLimitBread QZZ C (Xi2 η),
          weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)) :
          Matrix k k ℝ × (k → ℝ)))
      (fun _ => μ) ν)
    (hlimit : ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0) :
    Tendsto
      (fun m => μ {ω | ¬ IsUnit (weakIV2SLSRootScaledBread Z X m ω).det})
      atTop (𝓝 0) :=
  weakIV_pair_bread_singular_tendsto_zero_of_joint_tendsto
    (μ := μ) (ν := ν)
    (B := fun m ω => weakIV2SLSRootScaledBread Z X m ω)
    (S := fun m ω => weakIV2SLSRootScaledScore Z X e m ω)
    (B0 := fun η => weakIV2SLSLimitBread QZZ C (Xi2 η))
    (S0 := fun η => weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η))
    hjoint hlimit

/-- Leading root-scaled 2SLS weak-IV inverse-score CMT. -/
theorem weakIV_twoSLS_root_leading_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    (hjoint : TendstoInDistribution
      (E := Matrix k k ℝ × (k → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        ((weakIV2SLSRootScaledBread Z X m ω,
          weakIV2SLSRootScaledScore Z X e m ω) :
          Matrix k k ℝ × (k → ℝ)))
      atTop
      (fun (η : Ωlim) =>
        ((weakIV2SLSLimitBread QZZ C (Xi2 η),
          weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)) :
          Matrix k k ℝ × (k → ℝ)))
      (fun _ => μ) ν)
    (hlimit : ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        (weakIV2SLSRootScaledBread Z X m ω)⁻¹ *ᵥ
          weakIV2SLSRootScaledScore Z X e m ω)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν := by
  let D : Set (Matrix k k ℝ × (k → ℝ)) :=
    {p | ¬ IsUnit (p.1).det}
  have hD_meas : MeasurableSet D := by
    simpa [D] using (weakIV_twoSLS_singular_pair_measurable (k := k))
  have hD_null :
      (ν.map (fun η =>
        ((weakIV2SLSLimitBread QZZ C (Xi2 η),
          weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)) :
          Matrix k k ℝ × (k → ℝ)))) D = 0 := by
    rw [Measure.map_apply_of_aemeasurable hjoint.aemeasurable_limit hD_meas]
    simpa [D] using hlimit
  have hcont : ∀ p : Matrix k k ℝ × (k → ℝ), p ∉ D →
      ContinuousAt (fun q : Matrix k k ℝ × (k → ℝ) => q.1⁻¹ *ᵥ q.2) p := by
    intro p hp
    have hpunit : IsUnit (p.1).det := by
      simpa [D] using hp
    exact weakIV_twoSLS_inverse_score_continuousAt_of_nonsingular (k := k) p hpunit
  have hraw := tendstoInDistribution_ae_continuous_comp
    (X := fun (m : ℕ) (ω : Ω) =>
      ((weakIV2SLSRootScaledBread Z X m ω,
        weakIV2SLSRootScaledScore Z X e m ω) :
        Matrix k k ℝ × (k → ℝ)))
    (Z := fun η =>
      ((weakIV2SLSLimitBread QZZ C (Xi2 η),
        weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)) :
        Matrix k k ℝ × (k → ℝ)))
    hjoint weakIV_twoSLS_inverse_score_map_measurable hD_null hcont
  simpa [weakIV2SLSBias_eq_limitBread_inv_mul_score] using hraw

omit [IsProbabilityMeasure μ] in
private theorem weakIV_twoSLS_leading_aemeasurable
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    (hBread : ∀ m, AEStronglyMeasurable
      (fun ω => weakIV2SLSNormalizedBread Z X m ω) μ)
    (hScore : ∀ m, AEStronglyMeasurable
      (fun ω => weakIV2SLSNormalizedScore Z X e m ω) μ) :
    ∀ m, AEMeasurable
      (fun ω =>
        (weakIV2SLSNormalizedBread Z X m ω)⁻¹ *ᵥ
          weakIV2SLSNormalizedScore Z X e m ω) μ := by
  intro m
  exact
    ((Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((aestronglyMeasurable_matrix_inv (hBread m)).prodMk (hScore m))).aemeasurable

omit [IsProbabilityMeasure μ] in
private theorem weakIV_twoSLS_root_leading_aemeasurable
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ}
    (hBread : ∀ m, AEStronglyMeasurable
      (fun ω => weakIV2SLSRootScaledBread Z X m ω) μ)
    (hScore : ∀ m, AEStronglyMeasurable
      (fun ω => weakIV2SLSRootScaledScore Z X e m ω) μ) :
    ∀ m, AEMeasurable
      (fun ω =>
        (weakIV2SLSRootScaledBread Z X m ω)⁻¹ *ᵥ
          weakIV2SLSRootScaledScore Z X e m ω) μ := by
  intro m
  exact
    ((Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((aestronglyMeasurable_matrix_inv (hBread m)).prodMk (hScore m))).aemeasurable

omit [IsProbabilityMeasure μ] in
private theorem weakIV_twoSLS_estimator_centered_aemeasurable
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y : ℕ → Ω → ℝ} {β : k → ℝ}
    (hmeas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ) :
    ∀ m, AEMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      μ := by
  intro m
  exact ((hmeas m).sub aestronglyMeasurable_const).aemeasurable

omit [IsProbabilityMeasure μ] in
private theorem weakIV_twoSLS_totalization_remainder_tendstoInMeasure_zero
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hsingular : Tendsto
      (fun m => μ {ω | ¬ IsUnit (weakIV2SLSNormalizedBread Z X m ω).det})
      atTop (𝓝 0)) :
    TendstoInMeasure μ
      (fun m ω =>
        twoSLSBetaStar
            (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) -
          β -
          (weakIV2SLSNormalizedBread Z X m ω)⁻¹ *ᵥ
            weakIV2SLSNormalizedScore Z X e m ω)
      atTop (fun _ => (0 : k → ℝ)) := by
  intro ε hε
  have hBound : ∀ᶠ m in atTop,
      μ {ω |
          edist
            (twoSLSBetaStar
                (stackRegressors Z m ω) (stackRegressors X m ω)
                (stackOutcomes Y m ω) -
              β -
              (weakIV2SLSNormalizedBread Z X m ω)⁻¹ *ᵥ
                weakIV2SLSNormalizedScore Z X e m ω)
            (0 : k → ℝ) ≥ ε} ≤
        μ {ω | ¬ IsUnit (weakIV2SLSNormalizedBread Z X m ω).det} := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    refine measure_mono ?_
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    intro hunit
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hunit' : IsUnit
        (twoSLSMomentMatrixStar
          (stackRegressors Z m ω) (stackRegressors X m ω)).det :=
      isUnit_twoSLSMomentMatrixStar_det_of_sample_bread
        (Z := stackRegressors Z m ω) (X := stackRegressors X m ω) (by
          simpa [weakIV2SLSNormalizedBread] using hunit)
    have hY :
        stackOutcomes Y m ω =
          stackRegressors X m ω *ᵥ β + stackErrors e m ω := by
      ext i
      simp [stackOutcomes, stackRegressors, stackErrors, Matrix.mulVec,
        dotProduct, hmodel]
    have hR :
        twoSLSBetaStar
            (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) -
          β -
          (weakIV2SLSNormalizedBread Z X m ω)⁻¹ *ᵥ
            weakIV2SLSNormalizedScore Z X e m ω = 0 := by
      rw [hY]
      have hbase :=
        twoSLSBetaStar_sub_eq_linearizedScore_of_nonsingular
          (Z := stackRegressors Z m ω) (X := stackRegressors X m ω)
          (β := β) (e := stackErrors e m ω) hunit'
      rw [hbase]
      simp [weakIV2SLSNormalizedBread, weakIV2SLSNormalizedScore,
        twoSLSLinearizationMatrix, Matrix.mul_assoc, Matrix.mulVec_mulVec]
    rw [hR, edist_self] at hω
    exact absurd hω (not_le.mpr hε)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsingular (Eventually.of_forall (fun _ => zero_le _)) hBound

omit [IsProbabilityMeasure μ] in
private theorem weakIV_twoSLS_root_totalization_remainder_tendstoInMeasure_zero
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {β : k → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hsingular : Tendsto
      (fun m => μ {ω | ¬ IsUnit (weakIV2SLSRootScaledBread Z X m ω).det})
      atTop (𝓝 0)) :
    TendstoInMeasure μ
      (fun m ω =>
        twoSLSBetaStar
            (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) -
          β -
          (weakIV2SLSRootScaledBread Z X m ω)⁻¹ *ᵥ
            weakIV2SLSRootScaledScore Z X e m ω)
      atTop (fun _ => (0 : k → ℝ)) := by
  intro ε hε
  have hBound : ∀ᶠ m in atTop,
      μ {ω |
          edist
            (twoSLSBetaStar
                (stackRegressors Z m ω) (stackRegressors X m ω)
                (stackOutcomes Y m ω) -
              β -
              (weakIV2SLSRootScaledBread Z X m ω)⁻¹ *ᵥ
                weakIV2SLSRootScaledScore Z X e m ω)
            (0 : k → ℝ) ≥ ε} ≤
        μ {ω | ¬ IsUnit (weakIV2SLSRootScaledBread Z X m ω).det} := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    refine measure_mono ?_
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    intro hunit
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hunit_norm : IsUnit (weakIV2SLSNormalizedBread Z X m ω).det := by
      have hroot :=
        weakIV2SLSRootScaledBread_eq_card_smul_normalizedBread Z X m ω
      have hdet_ne :
          ((m : ℝ) • weakIV2SLSNormalizedBread Z X m ω).det ≠ 0 := by
        simpa [hroot] using hunit.ne_zero
      have hnorm_ne : (weakIV2SLSNormalizedBread Z X m ω).det ≠ 0 := by
        rw [Matrix.det_smul] at hdet_ne
        exact right_ne_zero_of_mul hdet_ne
      exact isUnit_iff_ne_zero.mpr hnorm_ne
    have hunit' : IsUnit
        (twoSLSMomentMatrixStar
          (stackRegressors Z m ω) (stackRegressors X m ω)).det :=
      isUnit_twoSLSMomentMatrixStar_det_of_sample_bread
        (Z := stackRegressors Z m ω) (X := stackRegressors X m ω) (by
          simpa [weakIV2SLSNormalizedBread] using hunit_norm)
    have hY :
        stackOutcomes Y m ω =
          stackRegressors X m ω *ᵥ β + stackErrors e m ω := by
      ext i
      simp [stackOutcomes, stackRegressors, stackErrors, Matrix.mulVec,
        dotProduct, hmodel]
    have hR :
        twoSLSBetaStar
            (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) -
          β -
          (weakIV2SLSRootScaledBread Z X m ω)⁻¹ *ᵥ
            weakIV2SLSRootScaledScore Z X e m ω = 0 := by
      rw [hY]
      have hbase :=
        twoSLSBetaStar_sub_eq_linearizedScore_of_nonsingular
          (Z := stackRegressors Z m ω) (X := stackRegressors X m ω)
          (β := β) (e := stackErrors e m ω) hunit'
      rw [hbase]
      rw [weakIV2SLSRootScaled_inverse_score_eq_normalized]
      simp [weakIV2SLSNormalizedBread, weakIV2SLSNormalizedScore,
        twoSLSLinearizationMatrix, Matrix.mul_assoc, Matrix.mulVec_mulVec]
    rw [hR, edist_self] at hω
    exact absurd hω (not_le.mpr hε)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsingular (Eventually.of_forall (fun _ => zero_le _)) hBound

/-- Moment-level 2SLS constructor for Hansen Theorem 12.18.

This derives the centered 2SLS weak-IV distributional limit from the normalized
projected bread/score joint limit plus the singular-event linearization
remainder, instead of assuming the final estimator limit. -/
theorem weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution_of_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    (h : WeakIV2SLSMomentConditions μ ν Z X e Y β QZZ C Xi2 xie) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν := by
  have hLeading := weakIV_twoSLS_leading_tendstoInDistribution_of_moments h
  have hRemainder :=
    weakIV_twoSLS_totalization_remainder_tendstoInMeasure_zero
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (β := β)
      h.linear_model h.singular_tendsto_zero
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (m : ℕ) ω =>
      (weakIV2SLSNormalizedBread Z X m ω)⁻¹ *ᵥ
        weakIV2SLSNormalizedScore Z X e m ω)
    (Y := fun (m : ℕ) ω =>
      twoSLSBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
    (Z := fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
    hLeading hRemainder
    (weakIV_twoSLS_estimator_centered_aemeasurable h.estimator_meas)

/-- Root-scaled moment-level 2SLS constructor for Hansen Theorem 12.18.

This is the faithful local-to-zero route: the projected bread/score process is
formed from `(n^{-1/2}Z'X, n^{-1/2}Z'e)`, and the finite-sample 2SLS
linearization is connected to that root-scaled inverse-score term by the
scaling-invariance bridge above. -/
theorem weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution_of_root_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hest : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ)
    (hjoint : TendstoInDistribution
      (E := Matrix k k ℝ × (k → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        ((weakIV2SLSRootScaledBread Z X m ω,
          weakIV2SLSRootScaledScore Z X e m ω) :
          Matrix k k ℝ × (k → ℝ)))
      atTop
      (fun (η : Ωlim) =>
        ((weakIV2SLSLimitBread QZZ C (Xi2 η),
          weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)) :
          Matrix k k ℝ × (k → ℝ)))
      (fun _ => μ) ν)
    (hlimit : ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν := by
  have hLeading :=
    weakIV_twoSLS_root_leading_tendstoInDistribution
      (μ := μ) (ν := ν) hjoint hlimit
  have hsingular :=
    weakIV_twoSLS_root_singular_tendsto_zero_of_joint_tendsto
      (μ := μ) (ν := ν) hjoint hlimit
  have hRemainder :=
    weakIV_twoSLS_root_totalization_remainder_tendstoInMeasure_zero
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y) (β := β)
      hmodel hsingular
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (m : ℕ) ω =>
      (weakIV2SLSRootScaledBread Z X m ω)⁻¹ *ᵥ
        weakIV2SLSRootScaledScore Z X e m ω)
    (Y := fun (m : ℕ) ω =>
      twoSLSBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
    (Z := fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
    hLeading hRemainder
    (weakIV_twoSLS_estimator_centered_aemeasurable hest)

/-- Root-primitive local-to-zero constructor for the 2SLS face of Hansen
Theorem 12.18.

The assumed primitive convergence is exactly Hansen's displayed weak-IV CLT
surface `(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)`. -/
theorem weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution_of_root_primitive
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hest : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ)
    (hPrimitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hlimit : ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν := by
  have hjoint :=
    weakIV_twoSLS_root_projected_bread_score_tendstoInDistribution_of_primitive
      (μ := μ) (ν := ν) hPrimitive hQZZ
  exact
    weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution_of_root_moments
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      hmodel hest hjoint hlimit

/-- Uncentered root-primitive local-to-zero constructor for the 2SLS face of
Hansen Theorem 12.18.

This is the `β + bias` compatibility form of
`weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution_of_root_primitive`,
so callers using Hansen's primitive `(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)` CLT
do not need to detour through the older projected-moment package. -/
theorem weakIV_twoSLSBetaStar_tendstoInDistribution_of_root_primitive
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hest : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ)
    (hPrimitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hlimit : ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν := by
  have hCentered :=
    weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution_of_root_primitive
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      hmodel hest hPrimitive hQZZ hlimit
  have hAdd := hCentered.continuous_comp
    (by fun_prop : Continuous fun x : k → ℝ => β + x)
  refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hAdd
  intro m
  exact ae_of_all μ (fun ω => by
    ext i
    simp [Pi.add_apply, Pi.sub_apply])

/-- Root-primitive moment-package constructor for the centered 2SLS face of
Hansen Theorem 12.18.

This is the package form of
`weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution_of_root_primitive`,
so callers can carry Hansen's local-to-zero 2SLS assumptions as one structured
hypothesis. -/
theorem weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution_of_root_primitive_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    (h : WeakIV2SLSRootPrimitiveMomentConditions μ ν Z X e Y β QZZ C Xi2 xie) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν :=
  weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution_of_root_primitive
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (β := β) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
    h.linear_model h.estimator_meas h.root_primitive_joint_tendsto
    h.qzz_nonsing h.limit_nonsing_ae

/-- Root-primitive moment-package constructor for the uncentered 2SLS face of
Hansen Theorem 12.18. -/
theorem weakIV_twoSLSBetaStar_tendstoInDistribution_of_root_primitive_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    (h : WeakIV2SLSRootPrimitiveMomentConditions μ ν Z X e Y β QZZ C Xi2 xie) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν :=
  weakIV_twoSLSBetaStar_tendstoInDistribution_of_root_primitive
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (β := β) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
    h.linear_model h.estimator_meas h.root_primitive_joint_tendsto
    h.qzz_nonsing h.limit_nonsing_ae

/-- Uncentered 2SLS constructor from the same weak-IV bread/score package. -/
theorem weakIV_twoSLSBetaStar_tendstoInDistribution_of_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    (h : WeakIV2SLSMomentConditions μ ν Z X e Y β QZZ C Xi2 xie) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν := by
  have hCentered := weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution_of_moments h
  have hAdd := hCentered.continuous_comp
    (by fun_prop : Continuous fun x : k → ℝ => β + x)
  refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hAdd
  intro m
  exact ae_of_all μ (fun ω => by
    ext i
    simp [Pi.add_apply, Pi.sub_apply])

/-- Leading LIML weak-IV inverse-score CMT.

Joint convergence of the weak-scaled LIML bread and structural-error score
implies convergence of the inverse-bread score term to Hansen's random weak-IV
LIML drift. -/
theorem weakIV_liml_leading_tendstoInDistribution_of_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVLIMLMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        (weakIVLIMLWeakScaledBread Z X limlMuHat m ω)⁻¹ *ᵥ
          weakIVLIMLWeakScaledScore Z X e limlMuHat m ω)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν := by
  let D : Set (Matrix k k ℝ × (k → ℝ)) :=
    {p | ¬ IsUnit (p.1).det}
  have hD_meas : MeasurableSet D := by
    simpa [D] using (weakIV_twoSLS_singular_pair_measurable (k := k))
  have hD_null :
      (ν.map (fun η =>
        ((weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22,
          weakIVLIMLLimitScore QZZ C (Xi2 η) (xie η) (mustar η) Sigma2e) :
          Matrix k k ℝ × (k → ℝ)))) D = 0 := by
    rw [Measure.map_apply_of_aemeasurable h.joint_tendsto.aemeasurable_limit hD_meas]
    simpa [D] using h.limit_nonsing_ae
  have hcont : ∀ p : Matrix k k ℝ × (k → ℝ), p ∉ D →
      ContinuousAt (fun q : Matrix k k ℝ × (k → ℝ) => q.1⁻¹ *ᵥ q.2) p := by
    intro p hp
    have hpunit : IsUnit (p.1).det := by
      simpa [D] using hp
    exact weakIV_twoSLS_inverse_score_continuousAt_of_nonsingular (k := k) p hpunit
  have hraw := tendstoInDistribution_ae_continuous_comp
    (X := fun (m : ℕ) (ω : Ω) =>
      ((weakIVLIMLWeakScaledBread Z X limlMuHat m ω,
        weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) :
        Matrix k k ℝ × (k → ℝ)))
    (Z := fun η =>
      ((weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22,
        weakIVLIMLLimitScore QZZ C (Xi2 η) (xie η) (mustar η) Sigma2e) :
        Matrix k k ℝ × (k → ℝ)))
    h.joint_tendsto weakIV_twoSLS_inverse_score_map_measurable hD_null hcont
  simpa [weakIVLIMLBias_eq_limitBread_inv_mul_score] using hraw

omit [IsProbabilityMeasure μ] in
private theorem weakIV_liml_leading_aemeasurable
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    (hBread : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ)
    (hScore : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ) :
    ∀ m, AEMeasurable
      (fun ω =>
        (weakIVLIMLWeakScaledBread Z X limlMuHat m ω)⁻¹ *ᵥ
          weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ := by
  intro m
  exact
    ((Continuous.matrix_mulVec continuous_fst continuous_snd).comp_aestronglyMeasurable
      ((aestronglyMeasurable_matrix_inv (hBread m)).prodMk (hScore m))).aemeasurable

omit [IsProbabilityMeasure μ] in
private theorem weakIV_liml_estimator_centered_aemeasurable
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ} {β : k → ℝ}
    (hmeas : ∀ m, AEStronglyMeasurable
      (fun ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      μ) :
    ∀ m, AEMeasurable
      (fun ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      μ := by
  intro m
  exact ((hmeas m).sub aestronglyMeasurable_const).aemeasurable

omit [IsProbabilityMeasure μ] in
private theorem weakIV_liml_totalization_remainder_tendstoInMeasure_zero
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ} {β : k → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hsingular : Tendsto
      (fun m => μ {ω | ¬ IsUnit (weakIVLIMLWeakScaledBread Z X limlMuHat m ω).det})
      atTop (𝓝 0)) :
    TendstoInMeasure μ
      (fun m ω =>
        limlBetaStar
            (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
            (weakIVLIMLFiniteSampleMu limlMuHat m ω) -
          β -
          (weakIVLIMLWeakScaledBread Z X limlMuHat m ω)⁻¹ *ᵥ
            weakIVLIMLWeakScaledScore Z X e limlMuHat m ω)
      atTop (fun _ => (0 : k → ℝ)) := by
  intro ε hε
  have hBound : ∀ᶠ m in atTop,
      μ {ω |
          edist
            (limlBetaStar
                (stackRegressors Z m ω) (stackRegressors X m ω)
                (stackOutcomes Y m ω) (weakIVLIMLFiniteSampleMu limlMuHat m ω) -
              β -
              (weakIVLIMLWeakScaledBread Z X limlMuHat m ω)⁻¹ *ᵥ
                weakIVLIMLWeakScaledScore Z X e limlMuHat m ω)
            (0 : k → ℝ) ≥ ε} ≤
        μ {ω | ¬ IsUnit (weakIVLIMLWeakScaledBread Z X limlMuHat m ω).det} := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    refine measure_mono ?_
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    intro hunit
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hY :
        stackOutcomes Y m ω =
          stackRegressors X m ω *ᵥ β + stackErrors e m ω := by
      ext i
      simp [stackOutcomes, stackRegressors, stackErrors, Matrix.mulVec,
        dotProduct, hmodel]
    have hR :
        limlBetaStar
            (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
            (weakIVLIMLFiniteSampleMu limlMuHat m ω) -
          β -
          (weakIVLIMLWeakScaledBread Z X limlMuHat m ω)⁻¹ *ᵥ
            weakIVLIMLWeakScaledScore Z X e limlMuHat m ω = 0 := by
      rw [hY]
      have hunit_norm : IsUnit
          (weakIVLIMLNormalizedBread Z X (weakIVLIMLFiniteSampleMu limlMuHat) m ω).det := by
        have hdet_ne :
            ((m : ℝ) •
              weakIVLIMLNormalizedBread Z X (weakIVLIMLFiniteSampleMu limlMuHat) m ω).det ≠ 0 := by
          simpa [weakIVLIMLWeakScaledBread] using hunit.ne_zero
        have hnorm_ne :
            (weakIVLIMLNormalizedBread Z X
              (weakIVLIMLFiniteSampleMu limlMuHat) m ω).det ≠ 0 := by
          rw [Matrix.det_smul] at hdet_ne
          exact right_ne_zero_of_mul hdet_ne
        exact isUnit_iff_ne_zero.mpr hnorm_ne
      rw [limlBetaStar_sub_eq_normalizedScore_of_nonsingular
        (Z := stackRegressors Z m ω) (X := stackRegressors X m ω)
        (β := β) (e := stackErrors e m ω)
        (μhat := weakIVLIMLFiniteSampleMu limlMuHat m ω)
        (by simpa [weakIVLIMLNormalizedBread] using hunit_norm)]
      rw [weakIVLIMLWeakScaled_inverse_score_eq_normalized]
      simp [weakIVLIMLNormalizedBread, weakIVLIMLNormalizedScore]
    rw [hR, edist_self] at hω
    exact absurd hω (not_le.mpr hε)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsingular (Eventually.of_forall (fun _ => zero_le _)) hBound

/-- Moment-level LIML constructor for Hansen Theorem 12.18.

This derives the centered LIML weak-IV distributional limit from normalized
LIML bread/score convergence and a Rayleigh-minimum certificate for `μ*`,
instead of assuming the final estimator limit. -/
theorem weakIV_limlBetaStar_minus_beta_tendstoInDistribution_of_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVLIMLMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν := by
  have hLeading := weakIV_liml_leading_tendstoInDistribution_of_moments h
  have hRemainder :=
    weakIV_liml_totalization_remainder_tendstoInMeasure_zero
      (μ := μ) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β)
      h.linear_model h.singular_tendsto_zero
  exact tendstoInDistribution_of_tendstoInMeasure_sub
    (X := fun (m : ℕ) ω =>
      (weakIVLIMLWeakScaledBread Z X limlMuHat m ω)⁻¹ *ᵥ
        weakIVLIMLWeakScaledScore Z X e limlMuHat m ω)
    (Y := fun (m : ℕ) ω =>
      limlBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
        (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
    (Z := fun η =>
      weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
    hLeading hRemainder
    (weakIV_liml_estimator_centered_aemeasurable h.estimator_meas)

/-- Uncentered LIML constructor from the same weak-IV bread/score package. -/
theorem weakIV_limlBetaStar_tendstoInDistribution_of_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVLIMLMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν := by
  have hCentered := weakIV_limlBetaStar_minus_beta_tendstoInDistribution_of_moments h
  have hAdd := hCentered.continuous_comp
    (by fun_prop : Continuous fun x : k → ℝ => β + x)
  refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hAdd
  intro m
  exact ae_of_all μ (fun ω => by
    ext i
    simp [Pi.add_apply, Pi.sub_apply])


/-- Proof-facing condition package for Hansen Theorem 12.18.

The fields state the three estimator limits under the weak-instrument sequence
(12.71): OLS has a deterministic inconsistent probability limit, while 2SLS
and LIML converge in distribution to Hansen's random weak-IV functionals.  The
`µ*` field records Hansen's Rayleigh-minimum definition of the limiting LIML
eigenvalue adjustment. -/
structure WeakIVTheorem1218Conditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) : Prop where
  liml_rayleigh_minimizer : ∀ η,
    LIMLRayleighMinimizer
      (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)
  ols_limit : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
    atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e)
  twoSLS_limit : TendstoInDistribution
    (fun (m : ℕ) ω =>
      twoSLSBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
    atTop
    (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
    (fun _ => μ) ν
  liml_limit : TendstoInDistribution
    (fun (m : ℕ) ω =>
      limlBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
        (weakIVLIMLFiniteSampleMu limlMuHat m ω))
    atTop
    (fun η =>
      β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
    (fun _ => μ) ν

/-- Centered proof-facing condition package for Hansen Theorem 12.18.

Primitive weak-instrument arguments usually deliver the displayed centered
limits directly.  This package keeps that surface separate from the uncentered
compatibility wrapper above while still recording Hansen's Rayleigh-minimum
definition of `µ*`. -/
structure WeakIVTheorem1218CenteredConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) : Prop where
  liml_rayleigh_minimizer : ∀ η,
    LIMLRayleighMinimizer
      (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)
  ols_centered : TendstoInMeasure μ
    (fun (m : ℕ) ω =>
      olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
    atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e)
  twoSLS_centered : TendstoInDistribution
    (fun (m : ℕ) ω =>
      twoSLSBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
    atTop
    (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
    (fun _ => μ) ν
  liml_centered : TendstoInDistribution
    (fun (m : ℕ) ω =>
      limlBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
        (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
    atTop
    (fun η =>
      weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
    (fun _ => μ) ν

/-- The theorem-facing local-to-zero moment package for Hansen Theorem 12.18.

This is the bundled surface closest to the current formalized proof route.  It
does not assume any of the three estimator limits directly: OLS is supplied by
normalized bread/score moments, 2SLS by the root-primitive local-to-zero
first-stage/score package, and LIML by weak-scaled LIML bread/score moments
plus the Rayleigh-minimum certificate for `µ*`. -/
structure WeakIVTheorem1218LocalToZeroMomentConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) : Prop where
  ols_moments : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e
  twoSLS_root_primitive :
    WeakIV2SLSRootPrimitiveMomentConditions μ ν Z X e Y β QZZ C Xi2 xie
  liml_moments : WeakIVLIMLMomentConditions
    μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e

/-- Preferred theorem-facing primitive package for Hansen Theorem 12.18.

Compared with `WeakIVTheorem1218LocalToZeroMomentConditions`, this package
does not assume the LIML bread/score limit package directly.  It carries OLS
moments, Hansen's root-primitive 2SLS local-to-zero CLT package, and the LIML
root/OLS/`µ̂` assembly package. -/
structure WeakIVTheorem1218RootAssemblyConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) : Prop where
  ols_moments : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e
  twoSLS_root_primitive :
    WeakIV2SLSRootPrimitiveMomentConditions μ ν Z X e Y β QZZ C Xi2 xie
  liml_root_assembly : WeakIVLIMLRootAssemblyConditions
    μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e

/-- Strongest currently formalized theorem-facing primitive package for Hansen
Theorem 12.18.

OLS is supplied by normalized bread/score moments, 2SLS by the root-primitive
local-to-zero CLT package, and LIML by a primitive root/OLS joint CLT plus the
reduced-form Rayleigh selector certificate for `µ̂_n` and `µ*`.  No estimator
limit is assumed directly. -/
structure WeakIVTheorem1218PrimitiveRayleighConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ)
    (muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) : Prop where
  ols_moments : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e
  twoSLS_root_primitive :
    WeakIV2SLSRootPrimitiveMomentConditions μ ν Z X e Y β QZZ C Xi2 xie
  liml_primitive_rayleigh :
    WeakIVLIMLPrimitiveRayleighRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma

/-- Theorem-facing primitive package for Hansen Theorem 12.18 using the
narrow structural Rayleigh selector.

This has the same OLS and 2SLS primitive inputs as
`WeakIVTheorem1218PrimitiveRayleighConditions`, but its LIML face only asks
for the continuous finite-sample/limit selector equations and Hansen's
structural Rayleigh-minimum certificate for `µ*`. -/
structure WeakIVTheorem1218StructuralRayleighConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ)
    (muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ) : Prop where
  ols_moments : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e
  twoSLS_root_primitive :
    WeakIV2SLSRootPrimitiveMomentConditions μ ν Z X e Y β QZZ C Xi2 xie
  liml_structural_rayleigh : WeakIVLIMLStructuralRayleighRootAssemblyConditions
    μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
    muSelector

/-- Theorem-facing finite-sample Rayleigh/eigenvalue package for Hansen
Theorem 12.18.

The package uses one shared root/OLS primitive convergence field for both the
2SLS root-primitive CMT and the LIML root assembly.  The LIML eigenvalue input
is not opaque: `rayleigh_selector` records the continuous selector, its sample
and limit equations on the root primitive, and the finite-sample Rayleigh
minimizer certificate generated by the LIML eigenvalue problem. -/
structure WeakIVTheorem1218FiniteSampleRayleighConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ)
    (muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) : Prop where
  ols_moments : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e
  twoSLS_estimator_meas : ∀ m, AEStronglyMeasurable
    (fun ω =>
      twoSLSBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
    μ
  liml_estimator_meas : ∀ m, AEStronglyMeasurable
    (fun ω =>
      limlBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
        (weakIVLIMLFiniteSampleMu limlMuHat m ω))
    μ
  liml_actual_bread_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ
  liml_actual_score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ
  root_ols_primitive_joint_tendsto : TendstoInDistribution
    (E :=
      (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
        (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
    (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
    atTop
    (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
    (fun _ => μ) ν
  qzz_nonsing : IsUnit QZZ.det
  rayleigh_selector : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
    Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22
  twoSLS_limit_nonsing_ae :
    ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0
  liml_limit_nonsing_ae :
    ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0

/-- Theorem-facing raw LIML eigenvalue-problem package for Hansen Theorem
12.18.

This strengthens `WeakIVTheorem1218FiniteSampleRayleighConditions` by retaining
the full reduced-form limit Rayleigh minimizer certificate from the raw
eigenvalue problem.  The downstream estimator theorem only needs the
finite-sample package, but this package is the one to cite when auditing
faithfulness to Hansen's `µ*` construction. -/
structure WeakIVTheorem1218RawEigenvalueProblemConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e : ℕ → Ω → ℝ) (Y : ℕ → Ω → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ)
    (muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) : Prop where
  ols_moments : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e
  twoSLS_estimator_meas : ∀ m, AEStronglyMeasurable
    (fun ω =>
      twoSLSBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
    μ
  liml_estimator_meas : ∀ m, AEStronglyMeasurable
    (fun ω =>
      limlBetaStar
        (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
        (weakIVLIMLFiniteSampleMu limlMuHat m ω))
    μ
  liml_actual_bread_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ
  liml_actual_score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ
  root_ols_primitive_joint_tendsto : TendstoInDistribution
    (E :=
      (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
        (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
    (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
    atTop
    (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
    (fun _ => μ) ν
  qzz_nonsing : IsUnit QZZ.det
  raw_eigenvalue_problem : WeakIVLIMLRawEigenvalueProblemConditions
    Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22
  twoSLS_limit_nonsing_ae :
    ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0
  liml_limit_nonsing_ae :
    ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0

/-- Finite-sample Rayleigh theorem package with the OLS WLLNs derived from the
shared root/OLS primitive convergence.

This is the preferred constructor when the local-to-zero CLT has already been
proved jointly for
`((Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e), (Q̂_XX, n^{-1}X'e))`.  The OLS
`WeakIVOLSMomentConditions` field is assembled by projecting that joint limit to
its OLS component, so callers no longer provide separate OLS bread/score WLLNs. -/
theorem WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOLS_bread : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVOLSNormalizedBread X m ω) μ)
    (hOLS_score : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVOLSNormalizedScore X e m ω) μ)
    (hSigma22 : IsUnit Sigma22.det)
    (h2SLS_est : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ)
    (hLIML_est : ∀ m, AEStronglyMeasurable
      (fun ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      μ)
    (hLIML_bread : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ)
    (hLIML_score : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    WeakIVTheorem1218FiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma where
  ols_moments :=
    WeakIVOLSMomentConditions.of_root_ols_primitive
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      hmodel hOLS_bread hOLS_score hjoint hSigma22
  twoSLS_estimator_meas := h2SLS_est
  liml_estimator_meas := hLIML_est
  liml_actual_bread_meas := hLIML_bread
  liml_actual_score_meas := hLIML_score
  root_ols_primitive_joint_tendsto := hjoint
  qzz_nonsing := hQZZ
  rayleigh_selector := hrayleigh
  twoSLS_limit_nonsing_ae := h2SLS_limit
  liml_limit_nonsing_ae := hLIML_limit

/-- Finite-sample Rayleigh theorem package from a root-primitive CLT plus OLS
moment WLLNs.

This constructor avoids assuming the full shared root/OLS primitive convergence
as one primitive.  It builds that joint convergence by Slutsky from
`(Q̂_ZZ,n^{-1/2}Z'X,n^{-1/2}Z'e) ⇒ (QZZ,QZZ*C+Ξ₂,ξe)` and the OLS
moment package. -/
theorem WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_primitive_ols_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e)
    (h2SLS_est : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ)
    (hLIML_est : ∀ m, AEStronglyMeasurable
      (fun ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      μ)
    (hLIML_bread : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ)
    (hLIML_score : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    WeakIVTheorem1218FiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hOLS.linear_model hOLS.bread_meas hOLS.score_meas hOLS.bread_nonsing
    h2SLS_est hLIML_est hLIML_bread hLIML_score
    (weakIV_root_ols_primitive_tendstoInDistribution_of_root_primitive_ols_moments
      (μ := μ) (ν := ν) hroot hOLS)
    hQZZ hrayleigh h2SLS_limit hLIML_limit

/-- Finite-sample Rayleigh theorem package with finite-sample measurability
derived from row-level measurability.

Compared with `of_root_ols_primitive`, this constructor removes the separate
OLS bread/score, 2SLS estimator, LIML estimator, and weak-scaled LIML
bread/score measurability inputs.  They are all deterministic measurable
functions of row-measurable `Z`, `X`, `e`, the structural equation for `Y`, and
the scaled LIML eigenvalue sequence `µ̂_n`. -/
theorem WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive_rows
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : IsUnit Sigma22.det)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    WeakIVTheorem1218FiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma := by
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model β hX he hmodel
  have h2SLS_est : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ := by
    intro m
    simpa [stackRegressors, stackOutcomes] using
      (twoSLSBetaStar_aestronglyMeasurable_of_rows
        (μ := μ) (n := m) (Z := Z) (X := X) (Y := Y) hZ hX hY)
  exact
    WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel
      (weakIVOLSNormalizedBread_aestronglyMeasurable_of_rows
        (μ := μ) (X := X) hX)
      (weakIVOLSNormalizedScore_aestronglyMeasurable_of_rows
        (μ := μ) (X := X) (e := e) hX he)
      hSigma22 h2SLS_est
      (weakIVLIMLBetaStar_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y) (limlMuHat := limlMuHat)
        hZ hX hY hMu)
      (weakIVLIMLWeakScaledBread_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (limlMuHat := limlMuHat) hZ hX hMu)
      (weakIVLIMLWeakScaledScore_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (e := e) (limlMuHat := limlMuHat)
        hZ hX he hMu)
      hjoint hQZZ hrayleigh h2SLS_limit hLIML_limit

/-- Row-measurable finite-sample Rayleigh package from a root-primitive CLT and
separate OLS bread/score WLLNs.

This is the row-level version of
`WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_primitive_ols_moments`:
all finite-sample measurability fields are derived from row measurability, and
the shared root/OLS primitive convergence is assembled internally by Slutsky. -/
theorem
    WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : IsUnit Sigma22.det)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    WeakIVTheorem1218FiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma := by
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model β hX he hmodel
  have hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e :=
    WeakIVOLSMomentConditions.of_rows
      (μ := μ) hmodel hX he hbread hscore hSigma22
  have h2SLS_est : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ := by
    intro m
    simpa [stackRegressors, stackOutcomes] using
      (twoSLSBetaStar_aestronglyMeasurable_of_rows
        (μ := μ) (n := m) (Z := Z) (X := X) (Y := Y) hZ hX hY)
  exact
    WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_primitive_ols_moments
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hOLS h2SLS_est
      (weakIVLIMLBetaStar_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y) (limlMuHat := limlMuHat)
        hZ hX hY hMu)
      (weakIVLIMLWeakScaledBread_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (limlMuHat := limlMuHat) hZ hX hMu)
      (weakIVLIMLWeakScaledScore_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (e := e) (limlMuHat := limlMuHat)
        hZ hX he hMu)
      hroot hQZZ hrayleigh h2SLS_limit hLIML_limit

set_option linter.style.longLine false in
/-- Finite-sample Rayleigh theorem package from row-measurable primitive
fields, with random limit-bread nonsingularity discharged from reduced-form
rank and structural Rayleigh sign witnesses.

This is the finite-sample-Rayleigh analogue of
`WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae`.
It does not require the raw package's full reduced-form limit minimizer audit
field: the existing finite-sample Rayleigh certificate already carries the
structural LIML minimizer needed to derive `µ* ≤ 0` from the supplied
nonpositive Rayleigh witnesses. -/
theorem
    WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    WeakIVTheorem1218FiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive_rows
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu
    ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
    hjoint ((Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ.isUnit)
    hrayleigh
    (weakIV2SLSLimitBread_nonsing_ae_of_qzz_posDef_firstStage_rank_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) hQZZ
      (weakIVFirstStageLimit_rank_ae_of_reducedFormLimit_rank_ae
        (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
        (β := β) hReducedRank))
    (weakIVLIMLLimitBread_nonsing_ae_of_qzz_posDef_firstStage_rank_mu_nonpos_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
      (mustar := mustar) (Sigma22 := Sigma22)
      hQZZ
      (weakIVFirstStageLimit_rank_ae_of_reducedFormLimit_rank_ae
        (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
        (β := β) hReducedRank)
      hSigma22.posSemidef
      (weakIV_mu_nonpos_ae_of_structural_rayleigh_witness_ae
        (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
        (mustar := mustar) (Sigma22 := Sigma22)
        hrayleigh.structural_limit_rayleigh_minimizer hRayleighNonpos))

set_option linter.style.longLine false in
/-- Pointwise-support variant of
`WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae`.

Pointwise full rank of Hansen's reduced-form limit matrix and pointwise
nonpositive structural Rayleigh witnesses are converted internally to the a.e.
rank/sign fields used for limit-bread nonsingularity. -/
theorem
    WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    WeakIVTheorem1218FiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
    (weakIVReducedFormLimit_rank_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (β := β) hReducedRank)
    (weakIVLIMLRayleigh_nonpos_witness_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
      (Sigma22 := Sigma22) hRayleighNonpos)

set_option linter.style.longLine false in
/-- Row-measurable finite-sample Rayleigh package from a root-primitive CLT,
OLS bread/score WLLNs, and a.e. reduced-form rank/Rayleigh-witness inputs.

This is the split-primitive version of
`WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae`:
the shared root/OLS primitive convergence is assembled internally by Slutsky. -/
theorem
    WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    WeakIVTheorem1218FiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hbread hscore
    ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
    hroot ((Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ.isUnit)
    hrayleigh
    (weakIV2SLSLimitBread_nonsing_ae_of_qzz_posDef_firstStage_rank_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) hQZZ
      (weakIVFirstStageLimit_rank_ae_of_reducedFormLimit_rank_ae
        (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
        (β := β) hReducedRank))
    (weakIVLIMLLimitBread_nonsing_ae_of_qzz_posDef_firstStage_rank_mu_nonpos_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
      (mustar := mustar) (Sigma22 := Sigma22)
      hQZZ
      (weakIVFirstStageLimit_rank_ae_of_reducedFormLimit_rank_ae
        (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
        (β := β) hReducedRank)
      hSigma22.posSemidef
      (weakIV_mu_nonpos_ae_of_structural_rayleigh_witness_ae
        (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
        (mustar := mustar) (Sigma22 := Sigma22)
        hrayleigh.structural_limit_rayleigh_minimizer hRayleighNonpos))

set_option linter.style.longLine false in
/-- Pointwise-support variant of
`WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae`. -/
theorem
    WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    WeakIVTheorem1218FiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ hrayleigh
    (weakIVReducedFormLimit_rank_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (β := β) hReducedRank)
    (weakIVLIMLRayleigh_nonpos_witness_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
      (Sigma22 := Sigma22) hRayleighNonpos)

/-- Raw eigenvalue-problem theorem package with OLS moments derived from the
shared root/OLS primitive convergence.

Compared with the structure literal, this constructor removes the independent
`WeakIVOLSMomentConditions` input.  The remaining primitive inputs are exactly
the shared local-to-zero root/OLS process, the raw LIML spectral certificate,
measurability fields, `QZZ` nonsingularity, and a.s. nonsingularity of the
random 2SLS/LIML limit breads. -/
theorem WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hOLS_bread : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVOLSNormalizedBread X m ω) μ)
    (hOLS_score : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVOLSNormalizedScore X e m ω) μ)
    (hSigma22 : IsUnit Sigma22.det)
    (h2SLS_est : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ)
    (hLIML_est : ∀ m, AEStronglyMeasurable
      (fun ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      μ)
    (hLIML_bread : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ)
    (hLIML_score : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma where
  ols_moments :=
    WeakIVOLSMomentConditions.of_root_ols_primitive
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      hmodel hOLS_bread hOLS_score hjoint hSigma22
  twoSLS_estimator_meas := h2SLS_est
  liml_estimator_meas := hLIML_est
  liml_actual_bread_meas := hLIML_bread
  liml_actual_score_meas := hLIML_score
  root_ols_primitive_joint_tendsto := hjoint
  qzz_nonsing := hQZZ
  raw_eigenvalue_problem := hraw
  twoSLS_limit_nonsing_ae := h2SLS_limit
  liml_limit_nonsing_ae := hLIML_limit

/-- Raw eigenvalue-problem theorem package from a root-primitive CLT plus OLS
moment WLLNs.

This constructor avoids assuming the full shared root/OLS primitive convergence
as one primitive.  It assembles that joint convergence by Slutsky from
`(Q̂_ZZ,n^{-1/2}Z'X,n^{-1/2}Z'e) ⇒ (QZZ,QZZ*C+Ξ₂,ξe)` and the OLS
moment package, while retaining the raw LIML eigenvalue audit fields. -/
theorem WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e)
    (h2SLS_est : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ)
    (hLIML_est : ∀ m, AEStronglyMeasurable
      (fun ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      μ)
    (hLIML_bread : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledBread Z X limlMuHat m ω) μ)
    (hLIML_score : ∀ m, AEStronglyMeasurable
      (fun ω => weakIVLIMLWeakScaledScore Z X e limlMuHat m ω) μ)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hOLS.linear_model hOLS.bread_meas hOLS.score_meas hOLS.bread_nonsing
    h2SLS_est hLIML_est hLIML_bread hLIML_score
    (weakIV_root_ols_primitive_tendstoInDistribution_of_root_primitive_ols_moments
      (μ := μ) (ν := ν) hroot hOLS)
    hQZZ hraw h2SLS_limit hLIML_limit

/-- Raw eigenvalue-problem theorem package with finite-sample measurability
derived from row-level measurability.

This is the row-measurable analogue of `of_root_ols_primitive`: the remaining
primitive inputs are the shared root/OLS local-to-zero process, `QZZ`
nonsingularity, the raw LIML eigenvalue-problem certificate, the nonsingular
random limit-bread events, and row measurability of `Z`, `X`, `e`, and `µ̂_n`. -/
theorem WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : IsUnit Sigma22.det)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma := by
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model β hX he hmodel
  have h2SLS_est : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ := by
    intro m
    simpa [stackRegressors, stackOutcomes] using
      (twoSLSBetaStar_aestronglyMeasurable_of_rows
        (μ := μ) (n := m) (Z := Z) (X := X) (Y := Y) hZ hX hY)
  exact
    WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel
      (weakIVOLSNormalizedBread_aestronglyMeasurable_of_rows
        (μ := μ) (X := X) hX)
      (weakIVOLSNormalizedScore_aestronglyMeasurable_of_rows
        (μ := μ) (X := X) (e := e) hX he)
      hSigma22 h2SLS_est
      (weakIVLIMLBetaStar_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y) (limlMuHat := limlMuHat)
        hZ hX hY hMu)
      (weakIVLIMLWeakScaledBread_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (limlMuHat := limlMuHat) hZ hX hMu)
      (weakIVLIMLWeakScaledScore_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (e := e) (limlMuHat := limlMuHat)
        hZ hX he hMu)
      hjoint hQZZ hraw h2SLS_limit hLIML_limit

/-- Row-measurable raw eigenvalue-problem package from a root-primitive CLT and
separate OLS bread/score WLLNs.

This is the raw analogue of
`WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows`:
finite-sample measurability is derived from rows, and the shared root/OLS
primitive convergence is assembled internally by Slutsky. -/
theorem
    WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : IsUnit Sigma22.det)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma := by
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model β hX he hmodel
  have hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e :=
    WeakIVOLSMomentConditions.of_rows
      (μ := μ) hmodel hX he hbread hscore hSigma22
  have h2SLS_est : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ := by
    intro m
    simpa [stackRegressors, stackOutcomes] using
      (twoSLSBetaStar_aestronglyMeasurable_of_rows
        (μ := μ) (n := m) (Z := Z) (X := X) (Y := Y) hZ hX hY)
  exact
    WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_moments
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hOLS h2SLS_est
      (weakIVLIMLBetaStar_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (Y := Y) (limlMuHat := limlMuHat)
        hZ hX hY hMu)
      (weakIVLIMLWeakScaledBread_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (limlMuHat := limlMuHat) hZ hX hMu)
      (weakIVLIMLWeakScaledScore_aestronglyMeasurable_of_rows
        (μ := μ) (Z := Z) (X := X) (e := e) (limlMuHat := limlMuHat)
        hZ hX he hMu)
      hroot hQZZ hraw h2SLS_limit hLIML_limit

set_option linter.style.longLine false in
/-- Split-primitive raw eigenvalue-problem package with random limit-bread
nonsingularity discharged from a.e. weak first-stage rank and `µ* ≤ 0`. -/
theorem
    WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_firstStage_rank_mu_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hFirst : ν {η | ¬ Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec} = 0)
    (hmu : ν {η | ¬ mustar η ≤ 0} = 0) :
    WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hbread hscore
    ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
    hroot ((Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ.isUnit)
    hraw
    (weakIV2SLSLimitBread_nonsing_ae_of_qzz_posDef_firstStage_rank_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) hQZZ hFirst)
    (weakIVLIMLLimitBread_nonsing_ae_of_qzz_posDef_firstStage_rank_mu_nonpos_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
      (mustar := mustar) (Sigma22 := Sigma22)
      hQZZ hFirst hSigma22.posSemidef hmu)

set_option linter.style.longLine false in
/-- Split-primitive raw eigenvalue-problem package with rank/sign inputs stated
on Hansen's reduced-form Rayleigh problem. -/
theorem
    WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_firstStage_rank_mu_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ hraw
    (weakIVFirstStageLimit_rank_ae_of_reducedFormLimit_rank_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (β := β) hReducedRank)
    (weakIV_mu_nonpos_ae_of_structural_rayleigh_witness_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
      (mustar := mustar) (Sigma22 := Sigma22)
      hraw.structural_limit_rayleigh_minimizer hRayleighNonpos)

set_option linter.style.longLine false in
/-- Pointwise-support variant of
`WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae`. -/
theorem
    WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ hraw
    (weakIVReducedFormLimit_rank_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (β := β) hReducedRank)
    (weakIVLIMLRayleigh_nonpos_witness_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
      (Sigma22 := Sigma22) hRayleighNonpos)

set_option linter.style.longLine false in
/-- Split-primitive raw theorem package directly from the full reduced-form
Rayleigh selector certificate, with a.e. reduced-form rank/Rayleigh-witness
sign inputs. -/
theorem
    WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
    (WeakIVLIMLRawEigenvalueProblemConditions.of_reducedForm_rayleigh_selector
      (k := k) (l := l) hrayleigh)
    hReducedRank hRayleighNonpos

set_option linter.style.longLine false in
/-- Pointwise-support variant of
`WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae`. -/
theorem
    WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ hrayleigh
    (weakIVReducedFormLimit_rank_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (β := β) hReducedRank)
    (weakIVLIMLRayleigh_nonpos_witness_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
      (Sigma22 := Sigma22) hRayleighNonpos)

set_option linter.style.longLine false in
/-- Raw eigenvalue-problem theorem package from row-measurable primitive
fields, with random limit-bread nonsingularity discharged from a.e. primitive
rank and sign conditions.

This removes the two explicit a.s. nonsingularity premises from
`WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows`.
The 2SLS limit bread is nonsingular a.e. from `QZZ > 0` and a.e. full column
rank of the weak first-stage limit `QZZ*C + Ξ₂`; the LIML limit bread is
nonsingular a.e. from the same rank condition, `Σ₂₂ ≥ 0`, and `µ* ≤ 0` a.e. -/
theorem
    WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hFirst : ν {η | ¬ Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec} = 0)
    (hmu : ν {η | ¬ mustar η ≤ 0} = 0) :
    WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu
    ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
    hjoint ((Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ.isUnit)
    hraw
    (weakIV2SLSLimitBread_nonsing_ae_of_qzz_posDef_firstStage_rank_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) hQZZ hFirst)
    (weakIVLIMLLimitBread_nonsing_ae_of_qzz_posDef_firstStage_rank_mu_nonpos_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
      (mustar := mustar) (Sigma22 := Sigma22)
      hQZZ hFirst hSigma22.posSemidef hmu)

set_option linter.style.longLine false in
/-- Raw eigenvalue-problem theorem package from row-measurable primitive
fields, with the rank condition stated on Hansen's reduced-form limit matrix
and the sign condition stated directly as `µ* ≤ 0` a.e.

This narrows
`WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae`:
the caller no longer supplies full rank of the weak first-stage block
`QZZ*C + Ξ₂` directly.  It is derived by restricting the full reduced-form
matrix `[Aβ + ξe, A]` to its right block. -/
theorem
    WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hmu : ν {η | ¬ mustar η ≤ 0} = 0) :
    WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw
    (weakIVFirstStageLimit_rank_ae_of_reducedFormLimit_rank_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (β := β) hReducedRank)
    hmu

set_option linter.style.longLine false in
/-- Pointwise-support variant of
`WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos_ae`. -/
theorem
    WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hmu : ∀ η, mustar η ≤ 0) :
    WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw
    (weakIVReducedFormLimit_rank_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (β := β) hReducedRank)
    (weakIV_mu_nonpos_ae_of_forall (ν := ν) hmu)

set_option linter.style.longLine false in
/-- Raw eigenvalue-problem theorem package from row-measurable primitive
fields, with rank/sign inputs stated on the reduced-form Rayleigh problem.

This is a more primitive variant of
`of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae`: a.e. full rank is
assumed for the full reduced-form limit matrix `[Aβ + ξe, A]`, then restricted
to the first-stage block `A = QZZ*C + Ξ₂`; the sign condition `µ* ≤ 0` is
derived from a.e. nonpositive structural Rayleigh quotient witnesses and the
raw structural minimizer certificate. -/
theorem
    WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw
    (weakIVFirstStageLimit_rank_ae_of_reducedFormLimit_rank_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (β := β) hReducedRank)
    (weakIV_mu_nonpos_ae_of_structural_rayleigh_witness_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
      (mustar := mustar) (Sigma22 := Sigma22)
      hraw.structural_limit_rayleigh_minimizer hRayleighNonpos)

set_option linter.style.longLine false in
/-- Raw eigenvalue-problem theorem package from row-measurable primitive
fields, with pointwise reduced-form rank and Rayleigh-witness inputs.

This is the deterministic-support variant of
`of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae`: the a.e.
rank and sign fields are derived internally from pointwise Hansen reduced-form
rank and nonpositive structural Rayleigh witnesses. -/
theorem
    WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw
    (weakIVReducedFormLimit_rank_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (β := β) hReducedRank)
    (weakIVLIMLRayleigh_nonpos_witness_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
      (Sigma22 := Sigma22) hRayleighNonpos)

set_option linter.style.longLine false in
/-- Raw theorem package directly from the full reduced-form Rayleigh selector
certificate, with a.e. reduced-form rank and Rayleigh-witness sign inputs.

This is the selector-facing version of
`WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae`:
the continuous selector, sample selector equation, limit selector equation,
finite-sample Rayleigh minimizer, reduced-form limit minimizer, and structural
limit minimizer are supplied in Hansen's reduced-form notation and converted to
the raw eigenvalue-problem package internally. -/
theorem
    WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ
    (WeakIVLIMLRawEigenvalueProblemConditions.of_reducedForm_rayleigh_selector
      (k := k) (l := l) hrayleigh)
    hReducedRank hRayleighNonpos

set_option linter.style.longLine false in
/-- Raw theorem package directly from the full reduced-form Rayleigh selector
certificate, with pointwise reduced-form rank and Rayleigh-witness sign inputs.

This deterministic-support variant derives the a.e. primitive rank and sign
fields internally before applying the selector-facing a.e. constructor. -/
theorem
    WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
    (weakIVReducedFormLimit_rank_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (β := β) hReducedRank)
    (weakIVLIMLRayleigh_nonpos_witness_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
      (Sigma22 := Sigma22) hRayleighNonpos)

/-- Forget the reduced-form limit Rayleigh audit field when applying the
existing finite-sample theorem route. -/
theorem WeakIVTheorem1218FiniteSampleRayleighConditions.of_raw_eigenvalue_problem
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVTheorem1218FiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma where
  ols_moments := h.ols_moments
  twoSLS_estimator_meas := h.twoSLS_estimator_meas
  liml_estimator_meas := h.liml_estimator_meas
  liml_actual_bread_meas := h.liml_actual_bread_meas
  liml_actual_score_meas := h.liml_actual_score_meas
  root_ols_primitive_joint_tendsto := h.root_ols_primitive_joint_tendsto
  qzz_nonsing := h.qzz_nonsing
  rayleigh_selector :=
    WeakIVLIMLFiniteSampleRayleighSelectorCertificate.of_raw_eigenvalue_problem
      (k := k) (l := l) h.raw_eigenvalue_problem
  twoSLS_limit_nonsing_ae := h.twoSLS_limit_nonsing_ae
  liml_limit_nonsing_ae := h.liml_limit_nonsing_ae

/-- Forget the optional reduced-form minimizer audit fields from the stronger
primitive Rayleigh theorem package. -/
theorem WeakIVTheorem1218StructuralRayleighConditions.of_primitive_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218PrimitiveRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVTheorem1218StructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector where
  ols_moments := h.ols_moments
  twoSLS_root_primitive := h.twoSLS_root_primitive
  liml_structural_rayleigh :=
    WeakIVLIMLStructuralRayleighRootAssemblyConditions.of_primitive_rayleigh
      (μ := μ) (ν := ν) h.liml_primitive_rayleigh

/-- Structural Rayleigh theorem package with finite-sample measurability derived
from row-level measurability.

This is the row-measurable analogue of the structural Rayleigh theorem package:
it derives the OLS bread/score, 2SLS estimator, LIML estimator, and weak-scaled
LIML bread/score measurability from rows, while keeping the shared root/OLS
primitive convergence and the structural Rayleigh selector as the substantive
inputs. -/
theorem WeakIVTheorem1218StructuralRayleighConditions.of_root_ols_primitive_rows
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : IsUnit Sigma22.det)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    WeakIVTheorem1218StructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector := by
  have hY : ∀ i, AEStronglyMeasurable (Y i) μ :=
    outcome_aestronglyMeasurable_of_linear_model β hX he hmodel
  have h2SLS_est : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ := by
    intro m
    simpa [stackRegressors, stackOutcomes] using
      (twoSLSBetaStar_aestronglyMeasurable_of_rows
        (μ := μ) (n := m) (Z := Z) (X := X) (Y := Y) hZ hX hY)
  exact
    { ols_moments :=
        WeakIVOLSMomentConditions.of_root_ols_primitive
          (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
          (β := β) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
          (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
          hmodel
          (weakIVOLSNormalizedBread_aestronglyMeasurable_of_rows
            (μ := μ) (X := X) hX)
          (weakIVOLSNormalizedScore_aestronglyMeasurable_of_rows
            (μ := μ) (X := X) (e := e) hX he)
          hjoint hSigma22
      twoSLS_root_primitive :=
        WeakIV2SLSRootPrimitiveMomentConditions.of_root_ols_primitive
          (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
          (β := β) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
          (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
          hmodel h2SLS_est hjoint hQZZ h2SLS_limit
      liml_structural_rayleigh :=
        { linear_model := hmodel
          estimator_meas :=
            weakIVLIMLBetaStar_aestronglyMeasurable_of_rows
              (μ := μ) (Z := Z) (X := X) (Y := Y) (limlMuHat := limlMuHat)
              hZ hX hY hMu
          actual_bread_meas :=
            weakIVLIMLWeakScaledBread_aestronglyMeasurable_of_rows
              (μ := μ) (Z := Z) (X := X) (limlMuHat := limlMuHat) hZ hX hMu
          actual_score_meas :=
            weakIVLIMLWeakScaledScore_aestronglyMeasurable_of_rows
              (μ := μ) (Z := Z) (X := X) (e := e) (limlMuHat := limlMuHat)
              hZ hX he hMu
          root_ols_primitive_joint_tendsto := hjoint
          qzz_nonsing := hQZZ
          rayleigh_selector := hrayleigh
          limit_nonsing_ae := hLIML_limit } }

set_option linter.style.longLine false in
/-- Structural Rayleigh theorem package from row-measurable primitive fields,
with random limit-bread nonsingularity discharged from a.e. first-stage rank
and a.e. `µ* ≤ 0`.

This narrows `WeakIVTheorem1218StructuralRayleighConditions.of_root_ols_primitive_rows`:
the caller supplies the structural Rayleigh selector and primitive rank/sign
inputs, while the 2SLS and LIML random limit-bread nonsingularity fields are
derived by the existing positive-definite bridges. -/
theorem
    WeakIVTheorem1218StructuralRayleighConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (hFirst : ν {η | ¬ Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec} = 0)
    (hmu : ν {η | ¬ mustar η ≤ 0} = 0) :
    WeakIVTheorem1218StructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector :=
  WeakIVTheorem1218StructuralRayleighConditions.of_root_ols_primitive_rows
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector)
    hmodel hZ hX he hMu
    ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
    hjoint ((Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ.isUnit)
    hrayleigh
    (weakIV2SLSLimitBread_nonsing_ae_of_qzz_posDef_firstStage_rank_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) hQZZ hFirst)
    (weakIVLIMLLimitBread_nonsing_ae_of_qzz_posDef_firstStage_rank_mu_nonpos_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
      (mustar := mustar) (Sigma22 := Sigma22)
      hQZZ hFirst hSigma22.posSemidef hmu)

set_option linter.style.longLine false in
/-- Pointwise-support variant of
`WeakIVTheorem1218StructuralRayleighConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae`. -/
theorem
    WeakIVTheorem1218StructuralRayleighConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (hFirst : ∀ η, Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec)
    (hmu : ∀ η, mustar η ≤ 0) :
    WeakIVTheorem1218StructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector :=
  WeakIVTheorem1218StructuralRayleighConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
    (weakIVFirstStageLimit_rank_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) hFirst)
    (weakIV_mu_nonpos_ae_of_forall (ν := ν) hmu)

set_option linter.style.longLine false in
/-- Structural Rayleigh theorem package from row-measurable primitive fields,
with rank/sign inputs stated on Hansen's reduced-form limit problem.

The reduced-form full-rank field is restricted to the weak first-stage block,
and the a.e. nonpositive Rayleigh quotient witnesses imply `µ* ≤ 0` through
the structural minimizer in the selector certificate. -/
theorem
    WeakIVTheorem1218StructuralRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    WeakIVTheorem1218StructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector :=
  WeakIVTheorem1218StructuralRayleighConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
    (weakIVFirstStageLimit_rank_ae_of_reducedFormLimit_rank_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (β := β) hReducedRank)
    (weakIV_mu_nonpos_ae_of_structural_rayleigh_witness_ae
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
      (mustar := mustar) (Sigma22 := Sigma22)
      hrayleigh.structural_limit_rayleigh_minimizer hRayleighNonpos)

set_option linter.style.longLine false in
/-- Pointwise-support variant of
`WeakIVTheorem1218StructuralRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae`. -/
theorem
    WeakIVTheorem1218StructuralRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    WeakIVTheorem1218StructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector :=
  WeakIVTheorem1218StructuralRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
    (weakIVReducedFormLimit_rank_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (β := β) hReducedRank)
    (weakIVLIMLRayleigh_nonpos_witness_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
      (Sigma22 := Sigma22) hRayleighNonpos)

set_option linter.style.longLine false in
/-- Structural Rayleigh theorem package from split primitive stochastic inputs,
with rank/sign inputs stated on Hansen's reduced-form limit problem.

This is the structural-selector analogue of the finite-sample/raw split
constructors: the shared root/OLS primitive process is assembled from Hansen's
root local-to-zero primitive CLT and the two normalized OLS WLLNs, while the
Rayleigh input is the narrower structural selector certificate rather than the
full reduced-form selector audit package. -/
theorem
    WeakIVTheorem1218StructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    WeakIVTheorem1218StructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector := by
  have hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e :=
    WeakIVOLSMomentConditions.of_rows
      (μ := μ) hmodel hX he hbread hscore
      ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
  have hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν :=
    weakIV_root_ols_primitive_tendstoInDistribution_of_root_primitive_ols_moments
      (μ := μ) (ν := ν) hroot hOLS
  exact
    WeakIVTheorem1218StructuralRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
      hReducedRank hRayleighNonpos

set_option linter.style.longLine false in
/-- Structural Rayleigh theorem package from split primitive stochastic inputs,
with reduced-form rank and direct a.e. `µ* ≤ 0` support.

This is the direct-sign analogue of
`WeakIVTheorem1218StructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae`.
The root/OLS primitive process is assembled from Hansen's root local-to-zero
primitive CLT and normalized OLS WLLNs, while the first-stage rank input is
derived internally from the full reduced-form limit matrix. -/
theorem
    WeakIVTheorem1218StructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hmu : ν {η | ¬ mustar η ≤ 0} = 0) :
    WeakIVTheorem1218StructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector := by
  have hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e :=
    WeakIVOLSMomentConditions.of_rows
      (μ := μ) hmodel hX he hbread hscore
      ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
  have hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν :=
    weakIV_root_ols_primitive_tendstoInDistribution_of_root_primitive_ols_moments
      (μ := μ) (ν := ν) hroot hOLS
  exact
    WeakIVTheorem1218StructuralRayleighConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
      (weakIVFirstStageLimit_rank_ae_of_reducedFormLimit_rank_ae
        (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
        (β := β) hReducedRank)
      hmu

set_option linter.style.longLine false in
/-- Pointwise-support variant of
`WeakIVTheorem1218StructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos_ae`.

Pointwise full rank of Hansen's reduced-form limit matrix and pointwise
`µ* ≤ 0` are converted internally to the a.e. fields used to discharge the
random 2SLS and LIML limit-bread nonsingularity assumptions. -/
theorem
    WeakIVTheorem1218StructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hmu : ∀ η, mustar η ≤ 0) :
    WeakIVTheorem1218StructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector :=
  WeakIVTheorem1218StructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector)
    hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ hrayleigh
    (weakIVReducedFormLimit_rank_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (β := β) hReducedRank)
    (weakIV_mu_nonpos_ae_of_forall (ν := ν) (mustar := mustar) hmu)

set_option linter.style.longLine false in
/-- Pointwise-support variant of
`WeakIVTheorem1218StructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae`. -/
theorem
    WeakIVTheorem1218StructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    WeakIVTheorem1218StructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector :=
  WeakIVTheorem1218StructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector)
    hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ hrayleigh
    (weakIVReducedFormLimit_rank_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (β := β) hReducedRank)
    (weakIVLIMLRayleigh_nonpos_witness_ae_of_forall
      (ν := ν) (QZZ := QZZ) (C := C) (Xi2 := Xi2)
      (Sigma22 := Sigma22) hRayleighNonpos)

/-- Convert the primitive Rayleigh-selector theorem package into the existing
root-assembly theorem package. -/
theorem WeakIVTheorem1218RootAssemblyConditions.of_primitive_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218PrimitiveRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVTheorem1218RootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  ols_moments := h.ols_moments
  twoSLS_root_primitive := h.twoSLS_root_primitive
  liml_root_assembly :=
    WeakIVLIMLRootAssemblyConditions.of_primitive_rayleigh
      (μ := μ) (ν := ν) h.liml_primitive_rayleigh

/-- Convert the narrow structural Rayleigh theorem package into the existing
root-assembly theorem package. -/
theorem WeakIVTheorem1218RootAssemblyConditions.of_structural_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (h : WeakIVTheorem1218StructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector) :
    WeakIVTheorem1218RootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  ols_moments := h.ols_moments
  twoSLS_root_primitive := h.twoSLS_root_primitive
  liml_root_assembly :=
    WeakIVLIMLRootAssemblyConditions.of_structural_rayleigh
      (μ := μ) (ν := ν) h.liml_structural_rayleigh

/-- Extract the LIML structural Rayleigh root-assembly package from the
finite-sample Rayleigh theorem package. -/
theorem
    WeakIVTheorem1218FiniteSampleRayleighConditions.toLIMLStructuralRayleighRootAssembly
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218FiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVLIMLStructuralRayleighRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector :=
  WeakIVLIMLStructuralRayleighRootAssemblyConditions.of_finite_sample_rayleigh
    (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    h.ols_moments.linear_model h.liml_estimator_meas
    h.liml_actual_bread_meas h.liml_actual_score_meas
    h.root_ols_primitive_joint_tendsto h.qzz_nonsing h.rayleigh_selector
    h.liml_limit_nonsing_ae

/-- Convert the finite-sample Rayleigh/eigenvalue package into the narrow
structural Rayleigh theorem package.  The 2SLS root primitive is obtained from
the same root/OLS joint local-to-zero convergence field used by LIML. -/
theorem WeakIVTheorem1218StructuralRayleighConditions.of_finite_sample_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218FiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVTheorem1218StructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector where
  ols_moments := h.ols_moments
  twoSLS_root_primitive :=
    WeakIV2SLSRootPrimitiveMomentConditions.of_root_ols_primitive
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      h.ols_moments.linear_model h.twoSLS_estimator_meas
      h.root_ols_primitive_joint_tendsto h.qzz_nonsing h.twoSLS_limit_nonsing_ae
  liml_structural_rayleigh :=
    WeakIVTheorem1218FiniteSampleRayleighConditions.toLIMLStructuralRayleighRootAssembly
      (μ := μ) (ν := ν) h

/-- Convert the finite-sample Rayleigh/eigenvalue package into the existing
RootAssembly theorem package. -/
theorem WeakIVTheorem1218RootAssemblyConditions.of_finite_sample_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218FiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVTheorem1218RootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVTheorem1218RootAssemblyConditions.of_structural_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218StructuralRayleighConditions.of_finite_sample_rayleigh
      (μ := μ) (ν := ν) h)

/-- Convert the root-assembly primitive package into the existing
local-to-zero moment package used by the Theorem 12.18 endpoints. -/
theorem WeakIVTheorem1218LocalToZeroMomentConditions.of_root_assembly
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218RootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVTheorem1218LocalToZeroMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  ols_moments := h.ols_moments
  twoSLS_root_primitive := h.twoSLS_root_primitive
  liml_moments := WeakIVLIMLMomentConditions.of_root_assembly h.liml_root_assembly

/-- Convert the primitive Rayleigh-selector theorem package into the
local-to-zero moment package consumed by the established Theorem 12.18
endpoints. -/
theorem WeakIVTheorem1218LocalToZeroMomentConditions.of_primitive_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218PrimitiveRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVTheorem1218LocalToZeroMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVTheorem1218LocalToZeroMomentConditions.of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RootAssemblyConditions.of_primitive_rayleigh
      (μ := μ) (ν := ν) h)

/-- Convert the narrow structural Rayleigh theorem package into the
local-to-zero moment package consumed by the established Theorem 12.18
endpoints. -/
theorem WeakIVTheorem1218LocalToZeroMomentConditions.of_structural_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (h : WeakIVTheorem1218StructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector) :
    WeakIVTheorem1218LocalToZeroMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVTheorem1218LocalToZeroMomentConditions.of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RootAssemblyConditions.of_structural_rayleigh
      (μ := μ) (ν := ν) h)

/-- Convert the finite-sample Rayleigh/eigenvalue theorem package into the
local-to-zero moment package consumed by the established Theorem 12.18
endpoints. -/
theorem WeakIVTheorem1218LocalToZeroMomentConditions.of_finite_sample_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218FiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVTheorem1218LocalToZeroMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVTheorem1218LocalToZeroMomentConditions.of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RootAssemblyConditions.of_finite_sample_rayleigh
      (μ := μ) (ν := ν) h)

/-- Convert the raw eigenvalue-problem theorem package into the established
root-assembly package. -/
theorem WeakIVTheorem1218RootAssemblyConditions.of_raw_eigenvalue_problem
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVTheorem1218RootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVTheorem1218RootAssemblyConditions.of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218FiniteSampleRayleighConditions.of_raw_eigenvalue_problem
      (μ := μ) (ν := ν) h)

/-- Convert the raw eigenvalue-problem theorem package into the established
local-to-zero moment package. -/
theorem WeakIVTheorem1218LocalToZeroMomentConditions.of_raw_eigenvalue_problem
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVTheorem1218LocalToZeroMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVTheorem1218LocalToZeroMomentConditions.of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RootAssemblyConditions.of_raw_eigenvalue_problem
      (μ := μ) (ν := ν) h)

/-- Centered Theorem 12.18 condition package from OLS bread/score moments.

This constructor removes the direct OLS estimator-limit assumption from the
centered package.  The 2SLS and LIML faces remain explicit estimator limits
for compatibility; use `weakIV_centeredConditions_of_ols_twoSLS_moments`
when the 2SLS bread/score package is available. -/
theorem weakIV_centeredConditions_of_ols_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e)
    (hrayleigh : ∀ η,
      LIMLRayleighMinimizer
        (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η))
    (h2 : TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν)
    (hliml : TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν) :
    WeakIVTheorem1218CenteredConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  liml_rayleigh_minimizer := hrayleigh
  ols_centered := weakIV_olsBetaStar_minus_beta_tendstoInMeasure_of_moments hOLS
  twoSLS_centered := h2
  liml_centered := hliml

/-- Centered Theorem 12.18 condition package from OLS and 2SLS moment packages.

This constructor removes both the direct OLS estimator-limit assumption and the
direct 2SLS estimator-limit assumption.  LIML remains an explicit centered
estimator limit until a caller supplies the sample eigenvalue/Rayleigh-minimizer
bridge. -/
theorem weakIV_centeredConditions_of_ols_twoSLS_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e)
    (h2SLS : WeakIV2SLSMomentConditions μ ν Z X e Y β QZZ C Xi2 xie)
    (hrayleigh : ∀ η,
      LIMLRayleighMinimizer
        (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η))
    (hliml : TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν) :
    WeakIVTheorem1218CenteredConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  liml_rayleigh_minimizer := hrayleigh
  ols_centered := weakIV_olsBetaStar_minus_beta_tendstoInMeasure_of_moments hOLS
  twoSLS_centered :=
    weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution_of_moments h2SLS
  liml_centered := hliml

/-- Centered Theorem 12.18 condition package from OLS moments and Hansen's
root-primitive 2SLS weak-IV CLT.

This is the preferred 2SLS route for the local-to-zero theorem: it uses the
primitive convergence of `(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)` instead of the
older normalized projected bread/score package. -/
theorem weakIV_centeredConditions_of_ols_twoSLS_root_primitive
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e)
    (h2SLS_est : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ)
    (h2SLS_primitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (h2SLS_limit :
      ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hrayleigh : ∀ η,
      LIMLRayleighMinimizer
        (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η))
    (hliml : TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν) :
    WeakIVTheorem1218CenteredConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  liml_rayleigh_minimizer := hrayleigh
  ols_centered := weakIV_olsBetaStar_minus_beta_tendstoInMeasure_of_moments hOLS
  twoSLS_centered :=
    weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution_of_root_primitive
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      hOLS.linear_model h2SLS_est h2SLS_primitive hQZZ h2SLS_limit
  liml_centered := hliml

/-- Centered Theorem 12.18 condition package from OLS, 2SLS, and LIML
moment packages.

This constructor derives all three centered estimator limits from lower-level
moment/CMT packages.  The LIML package still takes the sample-eigenvalue
asymptotic moment fields as inputs, but it no longer assumes the final LIML
estimator limit. -/
theorem weakIV_centeredConditions_of_ols_twoSLS_liml_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e)
    (h2SLS : WeakIV2SLSMomentConditions μ ν Z X e Y β QZZ C Xi2 xie)
    (hLIML : WeakIVLIMLMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVTheorem1218CenteredConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  liml_rayleigh_minimizer := hLIML.liml_rayleigh_minimizer
  ols_centered := weakIV_olsBetaStar_minus_beta_tendstoInMeasure_of_moments hOLS
  twoSLS_centered :=
    weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution_of_moments h2SLS
  liml_centered := weakIV_limlBetaStar_minus_beta_tendstoInDistribution_of_moments hLIML

/-- Centered Theorem 12.18 condition package from OLS moments, Hansen's
root-primitive 2SLS local-to-zero package, and LIML moment packages.

Compared with `weakIV_centeredConditions_of_ols_twoSLS_liml_moments`, this
uses the faithful root-scaled primitive 2SLS surface
`(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)` instead of the older normalized projected
bread/score package. -/
theorem weakIV_centeredConditions_of_ols_twoSLS_root_primitive_liml_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e)
    (h2SLS : WeakIV2SLSRootPrimitiveMomentConditions μ ν Z X e Y β QZZ C Xi2 xie)
    (hLIML : WeakIVLIMLMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVTheorem1218CenteredConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  liml_rayleigh_minimizer := hLIML.liml_rayleigh_minimizer
  ols_centered := weakIV_olsBetaStar_minus_beta_tendstoInMeasure_of_moments hOLS
  twoSLS_centered :=
    weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution_of_root_primitive_moments h2SLS
  liml_centered := weakIV_limlBetaStar_minus_beta_tendstoInDistribution_of_moments hLIML

/-- Convert the theorem-facing local-to-zero moment package into the centered
Theorem 12.18 condition package. -/
theorem WeakIVTheorem1218CenteredConditions.of_local_to_zero_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218LocalToZeroMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVTheorem1218CenteredConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  weakIV_centeredConditions_of_ols_twoSLS_root_primitive_liml_moments
    (μ := μ) (ν := ν) h.ols_moments h.twoSLS_root_primitive h.liml_moments

/-- Convert the root-assembly theorem package into the centered Theorem 12.18
condition package. -/
theorem WeakIVTheorem1218CenteredConditions.of_root_assembly
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218RootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVTheorem1218CenteredConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVTheorem1218CenteredConditions.of_local_to_zero_moments
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218LocalToZeroMomentConditions.of_root_assembly
      (μ := μ) (ν := ν) h)

/-- Convert the finite-sample Rayleigh/eigenvalue theorem package into the
centered Theorem 12.18 condition package. -/
theorem WeakIVTheorem1218CenteredConditions.of_finite_sample_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218FiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVTheorem1218CenteredConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVTheorem1218CenteredConditions.of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RootAssemblyConditions.of_finite_sample_rayleigh
      (μ := μ) (ν := ν) h)

/-- Convert the raw LIML eigenvalue-problem theorem package into the centered
Theorem 12.18 condition package.

This endpoint keeps the exact remaining raw input visible while deriving the
OLS, 2SLS, and LIML centered limits through the established moment and
Rayleigh-selector constructors. -/
theorem WeakIVTheorem1218CenteredConditions.of_raw_eigenvalue_problem
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVTheorem1218CenteredConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVTheorem1218CenteredConditions.of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218FiniteSampleRayleighConditions.of_raw_eigenvalue_problem
      (μ := μ) (ν := ν) h)

/-- Uncentered Theorem 12.18 condition package from OLS bread/score moments.

This is the compatibility constructor for the original `β + bias` endpoint:
it derives the OLS limit from normalized moment convergence while leaving the
2SLS and LIML estimator limits as explicit inputs. -/
theorem weakIV_conditions_of_ols_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e)
    (hrayleigh : ∀ η,
      LIMLRayleighMinimizer
        (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η))
    (h2 : TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν)
    (hliml : TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν) :
    WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  liml_rayleigh_minimizer := hrayleigh
  ols_limit := weakIV_olsBetaStar_tendstoInMeasure_of_moments hOLS
  twoSLS_limit := h2
  liml_limit := hliml

/-- Uncentered Theorem 12.18 condition package from OLS and 2SLS moments.

This is the `β + bias` compatibility constructor for the stronger
moment-level route: OLS and 2SLS estimator limits are derived from primitive
bread/score packages, while the LIML estimator limit remains explicit. -/
theorem weakIV_conditions_of_ols_twoSLS_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e)
    (h2SLS : WeakIV2SLSMomentConditions μ ν Z X e Y β QZZ C Xi2 xie)
    (hrayleigh : ∀ η,
      LIMLRayleighMinimizer
        (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η))
    (hliml : TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν) :
    WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  liml_rayleigh_minimizer := hrayleigh
  ols_limit := weakIV_olsBetaStar_tendstoInMeasure_of_moments hOLS
  twoSLS_limit := weakIV_twoSLSBetaStar_tendstoInDistribution_of_moments h2SLS
  liml_limit := hliml

/-- Uncentered Theorem 12.18 condition package from OLS moments and Hansen's
root-primitive 2SLS weak-IV CLT.

This is the `β + bias` compatibility constructor matching
`weakIV_centeredConditions_of_ols_twoSLS_root_primitive`: it derives the 2SLS
face from the literal local-to-zero primitive convergence
`(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)` instead of from the older projected
bread/score package. -/
theorem weakIV_conditions_of_ols_twoSLS_root_primitive
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e)
    (h2SLS_est : ∀ m, AEStronglyMeasurable
      (fun ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      μ)
    (h2SLS_primitive : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (h2SLS_limit :
      ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hrayleigh : ∀ η,
      LIMLRayleighMinimizer
        (weakIVLIMLRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η))
    (hliml : TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν) :
    WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  liml_rayleigh_minimizer := hrayleigh
  ols_limit := weakIV_olsBetaStar_tendstoInMeasure_of_moments hOLS
  twoSLS_limit :=
    weakIV_twoSLSBetaStar_tendstoInDistribution_of_root_primitive
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (β := β) (QZZ := QZZ) (C := C) (Xi2 := Xi2) (xie := xie)
      hOLS.linear_model h2SLS_est h2SLS_primitive hQZZ h2SLS_limit
  liml_limit := hliml

/-- Uncentered Theorem 12.18 condition package from OLS, 2SLS, and LIML
moment packages.

This is the `β + bias` compatibility constructor for the fully moment-level
route currently available in this file. -/
theorem weakIV_conditions_of_ols_twoSLS_liml_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e)
    (h2SLS : WeakIV2SLSMomentConditions μ ν Z X e Y β QZZ C Xi2 xie)
    (hLIML : WeakIVLIMLMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  liml_rayleigh_minimizer := hLIML.liml_rayleigh_minimizer
  ols_limit := weakIV_olsBetaStar_tendstoInMeasure_of_moments hOLS
  twoSLS_limit := weakIV_twoSLSBetaStar_tendstoInDistribution_of_moments h2SLS
  liml_limit := weakIV_limlBetaStar_tendstoInDistribution_of_moments hLIML

/-- Uncentered Theorem 12.18 condition package from OLS moments, Hansen's
root-primitive 2SLS local-to-zero package, and LIML moment packages. -/
theorem weakIV_conditions_of_ols_twoSLS_root_primitive_liml_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e)
    (h2SLS : WeakIV2SLSRootPrimitiveMomentConditions μ ν Z X e Y β QZZ C Xi2 xie)
    (hLIML : WeakIVLIMLMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  liml_rayleigh_minimizer := hLIML.liml_rayleigh_minimizer
  ols_limit := weakIV_olsBetaStar_tendstoInMeasure_of_moments hOLS
  twoSLS_limit :=
    weakIV_twoSLSBetaStar_tendstoInDistribution_of_root_primitive_moments h2SLS
  liml_limit := weakIV_limlBetaStar_tendstoInDistribution_of_moments hLIML

/-- Convert the theorem-facing local-to-zero moment package into the
uncentered compatibility condition package. -/
theorem WeakIVTheorem1218Conditions.of_local_to_zero_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218LocalToZeroMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  weakIV_conditions_of_ols_twoSLS_root_primitive_liml_moments
    (μ := μ) (ν := ν) h.ols_moments h.twoSLS_root_primitive h.liml_moments

/-- Convert the centered Theorem 12.18 condition package into the original
uncentered compatibility package.

The 2SLS and LIML limits are shifted by the continuous map `x ↦ β + x`; the
OLS face uses the same shift in probability.  This keeps the centered package
as the exact textbook surface while still recovering the older `β + bias`
condition package when needed. -/
theorem WeakIVTheorem1218Conditions.of_centered
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218CenteredConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β) μ) :
    WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  liml_rayleigh_minimizer := h.liml_rayleigh_minimizer
  ols_limit := by
    have hOLS := tendstoInMeasure_continuous_comp hOLS_meas h.ols_centered
      (by fun_prop : Continuous fun x : k → ℝ => β + x)
    refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hOLS
    intro m
    exact ae_of_all μ (fun ω => by
      ext i
      simp [Pi.add_apply, Pi.sub_apply])
  twoSLS_limit := by
    have h2 := h.twoSLS_centered.continuous_comp
      (by fun_prop : Continuous fun x : k → ℝ => β + x)
    refine TendstoInDistribution.congr ?_ ?_ h2
    · intro m
      exact ae_of_all μ (fun ω => by
        ext i
        simp [Pi.add_apply, Pi.sub_apply])
    · exact EventuallyEq.rfl
  liml_limit := by
    have hL := h.liml_centered.continuous_comp
      (by fun_prop : Continuous fun x : k → ℝ => β + x)
    refine TendstoInDistribution.congr ?_ ?_ hL
    · intro m
      exact ae_of_all μ (fun ω => by
        ext i
        simp [Pi.add_apply, Pi.sub_apply])
    · exact EventuallyEq.rfl

/-- The local-to-zero moment package directly exposes the centered Theorem
12.18 condition package. -/
theorem WeakIVTheorem1218LocalToZeroMomentConditions.centeredConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218LocalToZeroMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVTheorem1218CenteredConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVTheorem1218CenteredConditions.of_local_to_zero_moments
    (μ := μ) (ν := ν) h

/-- The local-to-zero moment package directly exposes the uncentered
compatibility condition package. -/
theorem WeakIVTheorem1218LocalToZeroMomentConditions.conditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218LocalToZeroMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVTheorem1218Conditions.of_local_to_zero_moments
    (μ := μ) (ν := ν) h

/-- Hansen Theorem 12.18 from the currently formalized local-to-zero moment
packages, in the exact centered form displayed in the text.

The OLS face is derived from normalized OLS bread/score convergence, the 2SLS
face is derived from Hansen's root-primitive weak-IV CLT
`(Q̂_ZZ, n^{-1/2}Z'X, n^{-1/2}Z'e)`, and the LIML face is derived from the
weak-scaled LIML bread/score package together with the Rayleigh-minimum
certificate for `µ*`. -/
theorem weakIV_estimators_minus_beta_theorem12_18_of_root_primitive_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e)
    (h2SLS : WeakIV2SLSRootPrimitiveMomentConditions μ ν Z X e Y β QZZ C Xi2 xie)
    (hLIML : WeakIVLIMLMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν := by
  let h :=
    weakIV_centeredConditions_of_ols_twoSLS_root_primitive_liml_moments
      (μ := μ) (ν := ν) hOLS h2SLS hLIML
  exact ⟨h.ols_centered, h.twoSLS_centered, h.liml_centered⟩

/-- Hansen Theorem 12.18 from one theorem-facing local-to-zero moment
package, in the exact centered form displayed in the text. -/
theorem weakIV_estimators_minus_beta_theorem12_18_of_local_to_zero_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218LocalToZeroMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_root_primitive_moments
    (μ := μ) (ν := ν) h.ols_moments h.twoSLS_root_primitive h.liml_moments

/-- Hansen Theorem 12.18 from the root-assembly primitive package, in the
centered form displayed in the text. -/
theorem weakIV_estimators_minus_beta_theorem12_18_of_root_assembly
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218RootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_local_to_zero_moments
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218LocalToZeroMomentConditions.of_root_assembly
      (μ := μ) (ν := ν) h)

/-- Hansen Theorem 12.18 from the primitive Rayleigh-selector package, in the
centered form displayed in the text. -/
theorem weakIV_estimators_minus_beta_theorem12_18_of_primitive_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218PrimitiveRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RootAssemblyConditions.of_primitive_rayleigh
      (μ := μ) (ν := ν) h)

/-- Hansen Theorem 12.18 from the narrow structural Rayleigh-selector package,
in the centered form displayed in the text. -/
theorem weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (h : WeakIVTheorem1218StructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RootAssemblyConditions.of_structural_rayleigh
      (μ := μ) (ν := ν) h)

/-- Hansen Theorem 12.18 from the finite-sample Rayleigh/eigenvalue package,
in the textbook-centered form. -/
theorem weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218FiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RootAssemblyConditions.of_finite_sample_rayleigh
      (μ := μ) (ν := ν) h)

/-- Hansen Theorem 12.18 from the raw LIML eigenvalue-problem package, in the
textbook-centered form.  This retains the reduced-form limit minimizer audit
field in the input package, then reuses the finite-sample Rayleigh route. -/
theorem weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218FiniteSampleRayleighConditions.of_raw_eigenvalue_problem
      (μ := μ) (ν := ν) h)

/-- Hansen Theorem 12.18 endpoint: under the weak-instrument local sequence,
OLS, 2SLS, and LIML have the displayed weak-IV limits. -/
theorem weakIV_estimators_theorem12_18
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  ⟨h.ols_limit, h.twoSLS_limit, h.liml_limit⟩

/-- Uncentered compatibility endpoint for Hansen Theorem 12.18 from one
theorem-facing local-to-zero moment package. -/
theorem weakIV_estimators_theorem12_18_of_local_to_zero_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218LocalToZeroMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18
    (WeakIVTheorem1218Conditions.of_local_to_zero_moments
      (μ := μ) (ν := ν) h)

/-- Uncentered compatibility endpoint for Hansen Theorem 12.18 from the
root-assembly primitive package. -/
theorem weakIV_estimators_theorem12_18_of_root_assembly
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218RootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_local_to_zero_moments
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218LocalToZeroMomentConditions.of_root_assembly
      (μ := μ) (ν := ν) h)

/-- Uncentered compatibility endpoint for Hansen Theorem 12.18 from the
primitive Rayleigh-selector package. -/
theorem weakIV_estimators_theorem12_18_of_primitive_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218PrimitiveRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RootAssemblyConditions.of_primitive_rayleigh
      (μ := μ) (ν := ν) h)

/-- Uncentered compatibility endpoint for Hansen Theorem 12.18 from the
narrow structural Rayleigh-selector package. -/
theorem weakIV_estimators_theorem12_18_of_structural_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (h : WeakIVTheorem1218StructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RootAssemblyConditions.of_structural_rayleigh
      (μ := μ) (ν := ν) h)

/-- Uncentered compatibility endpoint for Hansen Theorem 12.18 from the
finite-sample Rayleigh/eigenvalue package. -/
theorem weakIV_estimators_theorem12_18_of_finite_sample_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218FiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RootAssemblyConditions.of_finite_sample_rayleigh
      (μ := μ) (ν := ν) h)

/-- Uncentered compatibility endpoint for Hansen Theorem 12.18 from the raw
LIML eigenvalue-problem package. -/
theorem weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVTheorem1218RawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218FiniteSampleRayleighConditions.of_raw_eigenvalue_problem
      (μ := μ) (ν := ν) h)

/-- Centered Theorem 12.18 endpoint from row-measurable primitive fields and
the finite-sample Rayleigh/eigenvalue certificate.

This is the theorem-facing row wrapper around
`WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive_rows`:
callers provide row measurability, the shared root/OLS primitive convergence,
limit nonsingularity, and the finite-sample Rayleigh certificate directly. -/
theorem weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_rows
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : IsUnit Sigma22.det)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive_rows
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
      h2SLS_limit hLIML_limit)

set_option linter.style.longLine false in
/-- Centered finite-sample Rayleigh row wrapper with a.e. reduced-form rank
and Rayleigh-witness sign inputs.

This is the theorem-facing endpoint for the finite-sample Rayleigh route: it
uses `WeakIVLIMLFiniteSampleRayleighSelectorCertificate` directly, so callers
do not need the raw eigenvalue package's reduced-form limit minimizer audit
field when the reduced-form rank and structural Rayleigh nonpositivity inputs
already discharge the random limit-bread nonsingularity fields. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_rows_reducedForm_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
      hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Uncentered compatibility endpoint for the a.e. finite-sample Rayleigh
reduced-form rank and Rayleigh-witness route. -/
theorem
    weakIV_estimators_theorem12_18_of_finite_sample_rayleigh_rows_reducedForm_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
      hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Centered finite-sample Rayleigh row wrapper with pointwise reduced-form
rank and Rayleigh-witness sign inputs. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_rows_reducedForm_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
      hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Uncentered compatibility endpoint for the pointwise finite-sample
Rayleigh reduced-form rank and Rayleigh-witness route. -/
theorem
    weakIV_estimators_theorem12_18_of_finite_sample_rayleigh_rows_reducedForm_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
      hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 endpoint from split primitive stochastic inputs and
the finite-sample Rayleigh/eigenvalue certificate.

This is the split-primitive counterpart of
`weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_rows_reducedForm_rank_rayleigh_nonpos_ae`:
it assembles the shared root/OLS primitive convergence from Hansen's root
local-to-zero primitive CLT and the two normalized OLS WLLNs, then reuses the
finite-sample Rayleigh package and rank/sign bridges. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
      hrayleigh hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Uncentered Hansen Theorem 12.18 endpoint from split primitive stochastic
inputs and the finite-sample Rayleigh/eigenvalue certificate.

This is the uncentered counterpart of
`weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae`:
it keeps Hansen's `β + bias` conclusions and reuses the same finite-sample
Rayleigh condition constructor. -/
theorem
    weakIV_estimators_theorem12_18_of_finite_sample_rayleigh_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
      hrayleigh hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 endpoint from split primitive stochastic inputs,
the finite-sample Rayleigh/eigenvalue certificate, and Hansen's reduced-form
`µ*` minimizer certificate.

This keeps the finite-sample Rayleigh route as the proof engine while making
the reduced-form minimizer that Hansen uses to define `µ*` visible at the same
theorem boundary. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae_with_reducedForm_minimizer
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0)
    (hreduced : ∀ η,
      LIMLRayleighMinimizer
        (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
        Sigma (mustar η)) :
    (TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν) ∧
    (∀ η,
      LIMLRayleighMinimizer
        (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
        Sigma (mustar η)) :=
  ⟨weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
      hrayleigh hReducedRank hRayleighNonpos,
    hreduced⟩

set_option linter.style.longLine false in
/-- Uncentered Theorem 12.18 endpoint from split primitive stochastic inputs,
the finite-sample Rayleigh/eigenvalue certificate, and Hansen's reduced-form
`µ*` minimizer certificate.

This is the `β + bias` companion of
`weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae_with_reducedForm_minimizer`. -/
theorem
    weakIV_estimators_theorem12_18_of_finite_sample_rayleigh_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae_with_reducedForm_minimizer
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0)
    (hreduced : ∀ η,
      LIMLRayleighMinimizer
        (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
        Sigma (mustar η)) :
    (TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν) ∧
    (∀ η,
      LIMLRayleighMinimizer
        (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
        Sigma (mustar η)) :=
  ⟨weakIV_estimators_theorem12_18_of_finite_sample_rayleigh_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
      hrayleigh hReducedRank hRayleighNonpos,
    hreduced⟩

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 endpoint from split primitive stochastic inputs,
the finite-sample Rayleigh/eigenvalue certificate, and positive-definite
random limit breads.

This is the split root-CLT/OLS-WLLN counterpart of
`weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_rows_limitBread_posDef`.
It avoids the reduced-form rank/Rayleigh-sign shortcut when the proof supplies
positive definiteness of the random 2SLS and LIML limit breads directly. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_root_primitive_ols_wlln_rows_limitBread_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ∀ η, (weakIV2SLSLimitBread QZZ C (Xi2 η)).PosDef)
    (hLIML_limit : ∀ η,
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).PosDef) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hbread hscore
      ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
      hroot ((Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ.isUnit)
      hrayleigh
      (weakIV2SLSLimitBread_nonsing_ae_of_forall_posDef (ν := ν) h2SLS_limit)
      (weakIVLIMLLimitBread_nonsing_ae_of_forall_posDef (ν := ν) hLIML_limit))

set_option linter.style.longLine false in
/-- Uncentered Hansen Theorem 12.18 endpoint from split primitive stochastic
inputs, the finite-sample Rayleigh/eigenvalue certificate, and
positive-definite random limit breads. -/
theorem
    weakIV_estimators_theorem12_18_of_finite_sample_rayleigh_root_primitive_ols_wlln_rows_limitBread_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ∀ η, (weakIV2SLSLimitBread QZZ C (Xi2 η)).PosDef)
    (hLIML_limit : ∀ η,
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).PosDef) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hbread hscore
      ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
      hroot ((Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ.isUnit)
      hrayleigh
      (weakIV2SLSLimitBread_nonsing_ae_of_forall_posDef (ν := ν) h2SLS_limit)
      (weakIVLIMLLimitBread_nonsing_ae_of_forall_posDef (ν := ν) hLIML_limit))

set_option linter.style.longLine false in
/-- Pointwise-support centered Theorem 12.18 endpoint from split primitive
stochastic inputs and the finite-sample Rayleigh/eigenvalue certificate.

This is the pointwise rank/Rayleigh-witness analogue of
`weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae`. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
      hrayleigh hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Pointwise-support uncentered Hansen Theorem 12.18 endpoint from split
primitive stochastic inputs and the finite-sample Rayleigh/eigenvalue
certificate.

This is the uncentered counterpart of
`weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos`. -/
theorem
    weakIV_estimators_theorem12_18_of_finite_sample_rayleigh_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
      hrayleigh hReducedRank hRayleighNonpos)

/-- Centered Theorem 12.18 endpoint from row-measurable primitive fields, the
narrow structural Rayleigh selector, and pointwise nonsingularity of the random
2SLS/LIML limit breads.

Compared with the reduced-form Rayleigh row wrapper, this route does not ask
for the optional reduced-form limit minimizer audit fields. It keeps the
remaining hard inputs explicit: the shared root/OLS primitive CLT, the
structural `µ*` selector certificate, and random limit-bread nonsingularity. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh_rows_pointwise_nonsing
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : IsUnit Sigma22.det)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (h2SLS_limit : ∀ η, IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det)
    (hLIML_limit : ∀ η,
      IsUnit (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218StructuralRayleighConditions.of_root_ols_primitive_rows
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
      (weakIV2SLSLimitBread_nonsing_ae_of_forall (ν := ν) h2SLS_limit)
      (weakIVLIMLLimitBread_nonsing_ae_of_forall (ν := ν) hLIML_limit))

/-- Uncentered compatibility endpoint matching
`weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh_rows_pointwise_nonsing`. -/
theorem
    weakIV_estimators_theorem12_18_of_structural_rayleigh_rows_pointwise_nonsing
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : IsUnit Sigma22.det)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (h2SLS_limit : ∀ η, IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det)
    (hLIML_limit : ∀ η,
      IsUnit (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_structural_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218StructuralRayleighConditions.of_root_ols_primitive_rows
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
      (weakIV2SLSLimitBread_nonsing_ae_of_forall (ν := ν) h2SLS_limit)
      (weakIVLIMLLimitBread_nonsing_ae_of_forall (ν := ν) hLIML_limit))

/-- Centered Theorem 12.18 endpoint from row-measurable primitive fields and
the raw LIML eigenvalue-problem certificate.

The raw certificate still carries the exact reduced-form limit Rayleigh audit
field; this wrapper only removes the need to first assemble the theorem package
by hand. -/
theorem weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : IsUnit Sigma22.det)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw
      h2SLS_limit hLIML_limit)

/-- Centered Theorem 12.18 endpoint from row-measurable primitive fields, a
reduced-form Rayleigh selector certificate, and pointwise nonsingularity of the
random 2SLS/LIML limit breads.

This is the most reduced row-level spectral route currently available in this
file: the LIML eigenvalue facts are supplied in their natural reduced-form
Rayleigh notation, the root-primitive selector equations are derived by bridge
lemmas, and the a.s. nonsingularity fields are derived from pointwise
nonsingularity. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_rows_pointwise_nonsing
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : IsUnit Sigma22.det)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ∀ η, IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det)
    (hLIML_limit : ∀ η,
      IsUnit (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ
    (WeakIVLIMLRawEigenvalueProblemConditions.of_reducedForm_rayleigh_selector
      (k := k) (l := l) hrayleigh)
    (weakIV2SLSLimitBread_nonsing_ae_of_forall (ν := ν) h2SLS_limit)
    (weakIVLIMLLimitBread_nonsing_ae_of_forall (ν := ν) hLIML_limit)

/-- Uncentered compatibility endpoint matching
`weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_rows_pointwise_nonsing`. -/
theorem
    weakIV_estimators_theorem12_18_of_reducedForm_rayleigh_rows_pointwise_nonsing
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : IsUnit Sigma22.det)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ∀ η, IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det)
    (hLIML_limit : ∀ η,
      IsUnit (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ
      (WeakIVLIMLRawEigenvalueProblemConditions.of_reducedForm_rayleigh_selector
        (k := k) (l := l) hrayleigh)
      (weakIV2SLSLimitBread_nonsing_ae_of_forall (ν := ν) h2SLS_limit)
      (weakIVLIMLLimitBread_nonsing_ae_of_forall (ν := ν) hLIML_limit))

/-- Uncentered compatibility endpoint from row-measurable primitive fields and
the finite-sample Rayleigh/eigenvalue certificate. -/
theorem weakIV_estimators_theorem12_18_of_finite_sample_rayleigh_rows
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : IsUnit Sigma22.det)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218FiniteSampleRayleighConditions.of_root_ols_primitive_rows
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
      h2SLS_limit hLIML_limit)

/-- Uncentered compatibility endpoint from row-measurable primitive fields and
the raw LIML eigenvalue-problem certificate. -/
theorem weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem_rows
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : IsUnit Sigma22.det)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw
      h2SLS_limit hLIML_limit)

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 row wrapper with Hansen-facing positive-definite
population matrices.

This is a thin wrapper around
`weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_rows`:
positive definiteness of `Σ₂₂` and `QZZ` supplies the determinant-unit
premises used internally. -/
theorem weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_rows_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_rows
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu
    ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
    hjoint ((Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ.isUnit)
    hrayleigh h2SLS_limit hLIML_limit

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 finite-sample Rayleigh row wrapper with
positive-definite population matrices and positive-definite random limit breads.

This is the Hansen-facing positive-definite form of
`weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_rows_posDef`:
pointwise positive definiteness of the 2SLS and LIML random limit breads
supplies the a.e. nonsingularity fields used by the existing CMT endpoint. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_rows_limitBread_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ∀ η, (weakIV2SLSLimitBread QZZ C (Xi2 η)).PosDef)
    (hLIML_limit : ∀ η,
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).PosDef) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_finite_sample_rayleigh_rows_posDef
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
    (weakIV2SLSLimitBread_nonsing_ae_of_forall_posDef (ν := ν) h2SLS_limit)
    (weakIVLIMLLimitBread_nonsing_ae_of_forall_posDef (ν := ν) hLIML_limit)

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 structural Rayleigh row wrapper with
positive-definite `Σ₂₂` and `QZZ`. -/
theorem weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh_rows_pointwise_nonsing_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (h2SLS_limit : ∀ η, IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det)
    (hLIML_limit : ∀ η,
      IsUnit (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh_rows_pointwise_nonsing
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector)
    hmodel hZ hX he hMu
    ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
    hjoint ((Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ.isUnit)
    hrayleigh h2SLS_limit hLIML_limit

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 raw-eigenvalue row wrapper with positive-definite
`Σ₂₂` and `QZZ`. -/
theorem weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu
    ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
    hjoint ((Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ.isUnit)
    hraw h2SLS_limit hLIML_limit

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 reduced-form Rayleigh row wrapper with
positive-definite `Σ₂₂` and `QZZ`. -/
theorem weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_rows_pointwise_nonsing_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ∀ η, IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det)
    (hLIML_limit : ∀ η,
      IsUnit (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_rows_pointwise_nonsing
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu
    ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
    hjoint ((Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ.isUnit)
    hrayleigh h2SLS_limit hLIML_limit

set_option linter.style.longLine false in
/-- Uncentered Theorem 12.18 finite-sample Rayleigh row wrapper with
positive-definite `Σ₂₂` and `QZZ`. -/
theorem weakIV_estimators_theorem12_18_of_finite_sample_rayleigh_rows_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_finite_sample_rayleigh_rows
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu
    ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
    hjoint ((Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ.isUnit)
    hrayleigh h2SLS_limit hLIML_limit

set_option linter.style.longLine false in
/-- Uncentered Theorem 12.18 finite-sample Rayleigh row wrapper with
positive-definite population matrices and positive-definite random limit breads. -/
theorem
    weakIV_estimators_theorem12_18_of_finite_sample_rayleigh_rows_limitBread_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLFiniteSampleRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ∀ η, (weakIV2SLSLimitBread QZZ C (Xi2 η)).PosDef)
    (hLIML_limit : ∀ η,
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).PosDef) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_finite_sample_rayleigh_rows_posDef
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
    (weakIV2SLSLimitBread_nonsing_ae_of_forall_posDef (ν := ν) h2SLS_limit)
    (weakIVLIMLLimitBread_nonsing_ae_of_forall_posDef (ν := ν) hLIML_limit)

set_option linter.style.longLine false in
/-- Uncentered Theorem 12.18 structural Rayleigh row wrapper with
positive-definite `Σ₂₂` and `QZZ`. -/
theorem weakIV_estimators_theorem12_18_of_structural_rayleigh_rows_pointwise_nonsing_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (h2SLS_limit : ∀ η, IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det)
    (hLIML_limit : ∀ η,
      IsUnit (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_structural_rayleigh_rows_pointwise_nonsing
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector)
    hmodel hZ hX he hMu
    ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
    hjoint ((Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ.isUnit)
    hrayleigh h2SLS_limit hLIML_limit

set_option linter.style.longLine false in
/-- Uncentered Theorem 12.18 raw-eigenvalue row wrapper with positive-definite
`Σ₂₂` and `QZZ`. -/
theorem weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem_rows_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ν {η | ¬ IsUnit
      (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0)
    (hLIML_limit : ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem_rows
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu
    ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
    hjoint ((Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ.isUnit)
    hraw h2SLS_limit hLIML_limit

set_option linter.style.longLine false in
/-- Uncentered Theorem 12.18 reduced-form Rayleigh row wrapper with
positive-definite `Σ₂₂` and `QZZ`. -/
theorem weakIV_estimators_theorem12_18_of_reducedForm_rayleigh_rows_pointwise_nonsing_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ∀ η, IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det)
    (hLIML_limit : ∀ η,
      IsUnit (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_reducedForm_rayleigh_rows_pointwise_nonsing
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu
    ((Matrix.isUnit_iff_isUnit_det Sigma22).mp hSigma22.isUnit)
    hjoint ((Matrix.isUnit_iff_isUnit_det QZZ).mp hQZZ.isUnit)
    hrayleigh h2SLS_limit hLIML_limit

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 structural Rayleigh row wrapper with positive-definite
population matrices and positive-definite random limit breads.

This is the Hansen-facing positive-definite form of
`weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh_rows_pointwise_nonsing_posDef`.
It converts the two random limit-bread positive-definiteness assumptions into
the determinant-unit hypotheses used by the existing CMT endpoint. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh_rows_limitBread_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (h2SLS_limit : ∀ η, (weakIV2SLSLimitBread QZZ C (Xi2 η)).PosDef)
    (hLIML_limit : ∀ η,
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).PosDef) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh_rows_pointwise_nonsing_posDef
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
    (fun η => (Matrix.isUnit_iff_isUnit_det _).mp (h2SLS_limit η).isUnit)
    (fun η => (Matrix.isUnit_iff_isUnit_det _).mp (hLIML_limit η).isUnit)

set_option linter.style.longLine false in
/-- Uncentered Theorem 12.18 structural Rayleigh row wrapper with
positive-definite population matrices and positive-definite random limit breads. -/
theorem weakIV_estimators_theorem12_18_of_structural_rayleigh_rows_limitBread_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (h2SLS_limit : ∀ η, (weakIV2SLSLimitBread QZZ C (Xi2 η)).PosDef)
    (hLIML_limit : ∀ η,
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).PosDef) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_structural_rayleigh_rows_pointwise_nonsing_posDef
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
    (fun η => (Matrix.isUnit_iff_isUnit_det _).mp (h2SLS_limit η).isUnit)
    (fun η => (Matrix.isUnit_iff_isUnit_det _).mp (hLIML_limit η).isUnit)

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 reduced-form Rayleigh row wrapper with positive-definite
population matrices and positive-definite random limit breads. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_rows_limitBread_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ∀ η, (weakIV2SLSLimitBread QZZ C (Xi2 η)).PosDef)
    (hLIML_limit : ∀ η,
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).PosDef) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_rows_pointwise_nonsing_posDef
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
    (fun η => (Matrix.isUnit_iff_isUnit_det _).mp (h2SLS_limit η).isUnit)
    (fun η => (Matrix.isUnit_iff_isUnit_det _).mp (hLIML_limit η).isUnit)

set_option linter.style.longLine false in
/-- Uncentered Theorem 12.18 reduced-form Rayleigh row wrapper with
positive-definite population matrices and positive-definite random limit breads. -/
theorem weakIV_estimators_theorem12_18_of_reducedForm_rayleigh_rows_limitBread_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ∀ η, (weakIV2SLSLimitBread QZZ C (Xi2 η)).PosDef)
    (hLIML_limit : ∀ η,
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).PosDef) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_reducedForm_rayleigh_rows_pointwise_nonsing_posDef
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
    (fun η => (Matrix.isUnit_iff_isUnit_det _).mp (h2SLS_limit η).isUnit)
    (fun η => (Matrix.isUnit_iff_isUnit_det _).mp (hLIML_limit η).isUnit)

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 raw-eigenvalue row wrapper with positive-definite
population matrices and positive-definite random limit breads. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows_limitBread_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ∀ η, (weakIV2SLSLimitBread QZZ C (Xi2 η)).PosDef)
    (hLIML_limit : ∀ η,
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).PosDef) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows_posDef
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw
    (weakIV2SLSLimitBread_nonsing_ae_of_forall_posDef (ν := ν) h2SLS_limit)
    (weakIVLIMLLimitBread_nonsing_ae_of_forall_posDef (ν := ν) hLIML_limit)

set_option linter.style.longLine false in
/-- Uncentered Theorem 12.18 raw-eigenvalue row wrapper with positive-definite
population matrices and positive-definite random limit breads. -/
theorem weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem_rows_limitBread_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (h2SLS_limit : ∀ η, (weakIV2SLSLimitBread QZZ C (Xi2 η)).PosDef)
    (hLIML_limit : ∀ η,
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).PosDef) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem_rows_posDef
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw
    (weakIV2SLSLimitBread_nonsing_ae_of_forall_posDef (ν := ν) h2SLS_limit)
    (weakIVLIMLLimitBread_nonsing_ae_of_forall_posDef (ν := ν) hLIML_limit)

set_option linter.style.longLine false in
/-- Centered raw-eigenvalue row wrapper where Hansen's 2SLS limit-bread
nonsingularity is derived from `QZZ > 0` and full column rank of the weak
first-stage limit `QZZ*C + Ξ₂`.

This narrows the corresponding `..._limitBread_posDef` wrapper: the LIML
random limit bread still remains as a positive-definiteness premise, while the
2SLS random limit bread is discharged by the primitive rank bridge
`weakIV2SLSLimitBread_posDef_of_qzz_posDef_firstStage_rank`. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows_firstStage_rank_limitBread_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hFirst : ∀ η, Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec)
    (hLIML_limit : ∀ η,
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).PosDef) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows_limitBread_posDef
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw
    (fun η =>
      weakIV2SLSLimitBread_posDef_of_qzz_posDef_firstStage_rank
        (QZZ := QZZ) (C := C) (Xi2 := Xi2 η) hQZZ (hFirst η))
    hLIML_limit

set_option linter.style.longLine false in
/-- Uncentered raw-eigenvalue row wrapper where Hansen's 2SLS limit-bread
nonsingularity is derived from `QZZ > 0` and full column rank of the weak
first-stage limit `QZZ*C + Ξ₂`. -/
theorem
    weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem_rows_firstStage_rank_limitBread_posDef
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hFirst : ∀ η, Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec)
    (hLIML_limit : ∀ η,
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).PosDef) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem_rows_limitBread_posDef
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw
    (fun η =>
      weakIV2SLSLimitBread_posDef_of_qzz_posDef_firstStage_rank
        (QZZ := QZZ) (C := C) (Xi2 := Xi2 η) hQZZ (hFirst η))
    hLIML_limit

set_option linter.style.longLine false in
/-- Centered raw-eigenvalue row wrapper where both weak-IV random limit breads
are discharged from Hansen-style primitive conditions.

The 2SLS bread follows from `QZZ > 0` and full column rank of the weak
first-stage limit.  The LIML bread follows from the same 2SLS bread,
`Σ₂₂ ≥ 0`, and the Rayleigh-root sign condition `μ* ≤ 0`. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows_firstStage_rank_mu_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hFirst : ∀ η, Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec)
    (hmu : ∀ η, mustar η ≤ 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows_firstStage_rank_limitBread_posDef
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw hFirst
    (fun η =>
      weakIVLIMLLimitBread_posDef_of_twoSLS_posDef_mu_nonpos_sigma22_posSemidef
        (weakIV2SLSLimitBread_posDef_of_qzz_posDef_firstStage_rank
          (QZZ := QZZ) (C := C) (Xi2 := Xi2 η) hQZZ (hFirst η))
        hSigma22.posSemidef (hmu η))

set_option linter.style.longLine false in
/-- Uncentered raw-eigenvalue row wrapper where both weak-IV random limit
breads are discharged from `QZZ > 0`, weak first-stage full rank, `Σ₂₂ ≥ 0`,
and `μ* ≤ 0`. -/
theorem
    weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem_rows_firstStage_rank_mu_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hFirst : ∀ η, Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec)
    (hmu : ∀ η, mustar η ≤ 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem_rows_firstStage_rank_limitBread_posDef
    (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
    (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
    (Xi2 := Xi2) (xie := xie) (mustar := mustar)
    (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
    (muSelector := muSelector) (Sigma := Sigma)
    hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw hFirst
    (fun η =>
      weakIVLIMLLimitBread_posDef_of_twoSLS_posDef_mu_nonpos_sigma22_posSemidef
        (weakIV2SLSLimitBread_posDef_of_qzz_posDef_firstStage_rank
          (QZZ := QZZ) (C := C) (Xi2 := Xi2 η) hQZZ (hFirst η))
        hSigma22.posSemidef (hmu η))

set_option linter.style.longLine false in
/-- Centered raw-eigenvalue row wrapper where both weak-IV random limit breads
are discharged from a.e. Hansen-style primitive conditions.

Compared with
`weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows_firstStage_rank_mu_nonpos`,
this version only requires a.e. full column rank of the weak first-stage limit
and a.e. `µ* ≤ 0`, which is the natural probabilistic form for the random
Gaussian limit objects in Theorem 12.18. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows_firstStage_rank_mu_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hFirst : ν {η | ¬ Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec} = 0)
    (hmu : ν {η | ¬ mustar η ≤ 0} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw hFirst hmu)

set_option linter.style.longLine false in
/-- Uncentered compatibility endpoint for the a.e. first-stage-rank and
`µ* ≤ 0` raw-eigenvalue route. -/
theorem
    weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem_rows_firstStage_rank_mu_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hFirst : ν {η | ¬ Function.Injective
      (weakIVFirstStageLimit QZZ C (Xi2 η)).mulVec} = 0)
    (hmu : ν {η | ¬ mustar η ≤ 0} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw hFirst hmu)

set_option linter.style.longLine false in
/-- Centered raw-eigenvalue row wrapper with a.e. reduced-form rank and
direct `µ* ≤ 0` inputs.

This is the theorem-facing version of
`WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos_ae`:
the rank premise is stated on Hansen's full reduced-form limit matrix
`[Aβ + ξe, A]`, and the weak first-stage rank used by the 2SLS/LIML
limit-bread bridges is derived internally. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows_reducedForm_rank_mu_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hmu : ν {η | ¬ mustar η ≤ 0} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw hReducedRank hmu)

set_option linter.style.longLine false in
/-- Uncentered compatibility endpoint for the a.e. reduced-form-rank and
direct `µ* ≤ 0` raw-eigenvalue route. -/
theorem
    weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem_rows_reducedForm_rank_mu_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hmu : ν {η | ¬ mustar η ≤ 0} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw hReducedRank hmu)

set_option linter.style.longLine false in
/-- Pointwise-support variant of
`weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows_reducedForm_rank_mu_nonpos_ae`. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows_reducedForm_rank_mu_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hmu : ∀ η, mustar η ≤ 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw hReducedRank hmu)

set_option linter.style.longLine false in
/-- Uncentered compatibility endpoint for the pointwise reduced-form-rank and
direct `µ* ≤ 0` raw-eigenvalue route. -/
theorem
    weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem_rows_reducedForm_rank_mu_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hmu : ∀ η, mustar η ≤ 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw hReducedRank hmu)

set_option linter.style.longLine false in
/-- Centered raw-eigenvalue row wrapper with a.e. reduced-form rank and
Rayleigh-witness sign inputs.

This is the theorem-facing endpoint for the primitive reduced-form route: full
rank is stated on Hansen's reduced-form limit matrix `[Aβ + ξe, A]`, and the
sign condition for `µ*` is stated as a nonpositive structural Rayleigh quotient
witness on an a.e. event. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows_reducedForm_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw
      hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Uncentered compatibility endpoint for the a.e. reduced-form rank and
Rayleigh-witness sign route. -/
theorem
    weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem_rows_reducedForm_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw
      hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Centered raw-eigenvalue row wrapper with pointwise reduced-form rank and
Rayleigh-witness sign inputs.

This deterministic-support variant derives the a.e. fields in
`weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows_reducedForm_rank_rayleigh_nonpos_ae`
from pointwise full rank of Hansen's reduced-form limit matrix and pointwise
nonpositive structural Rayleigh witnesses. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem_rows_reducedForm_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw
      hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Uncentered compatibility endpoint for the pointwise reduced-form rank and
Rayleigh-witness sign route. -/
theorem
    weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem_rows_reducedForm_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hraw : WeakIVLIMLRawEigenvalueProblemConditions
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hraw
      hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 endpoint from the full reduced-form Rayleigh selector,
with a.e. reduced-form rank and Rayleigh-witness sign inputs.

This wrapper takes the raw continuous selector, sample/limit selector equations,
sample reduced-form Rayleigh certificate, reduced-form limit minimizer, and
structural Rayleigh minimizer through
`WeakIVLIMLReducedFormRayleighSelectorCertificate`; the existing rank/sign
bridges discharge the random 2SLS and LIML limit-bread nonsingularity fields. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_selector_rows_reducedForm_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
      hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Uncentered compatibility endpoint from the full reduced-form Rayleigh selector
and a.e. reduced-form rank/Rayleigh-witness sign inputs. -/
theorem
    weakIV_estimators_theorem12_18_of_reducedForm_rayleigh_selector_rows_reducedForm_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
      hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 endpoint from the full reduced-form Rayleigh selector,
with pointwise reduced-form rank and Rayleigh-witness sign inputs. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_selector_rows_reducedForm_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
      hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Uncentered compatibility endpoint from the full reduced-form Rayleigh selector
and pointwise reduced-form rank/Rayleigh-witness sign inputs. -/
theorem
    weakIV_estimators_theorem12_18_of_reducedForm_rayleigh_selector_rows_reducedForm_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hSigma22 : Sigma22.PosDef)
    (hjoint : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hSigma22 hjoint hQZZ hrayleigh
      hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 endpoint from split primitive stochastic inputs and
the narrow structural Rayleigh selector, with direct a.e. `µ* ≤ 0` support.

Compared with
`weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae`,
this wrapper takes the sign condition on Hansen's limiting LIML root `µ*`
directly.  The reduced-form full-rank condition is still stated on the same
full reduced-form limit matrix used in the theorem-facing Rayleigh route. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hmu : ν {η | ¬ mustar η ≤ 0} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218StructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector)
      hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
      hrayleigh hReducedRank hmu)

set_option linter.style.longLine false in
/-- Uncentered Theorem 12.18 endpoint from split primitive stochastic inputs and
the narrow structural Rayleigh selector, with direct a.e. `µ* ≤ 0` support. -/
theorem
    weakIV_estimators_theorem12_18_of_structural_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hmu : ν {η | ¬ mustar η ≤ 0} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_structural_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218StructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector)
      hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
      hrayleigh hReducedRank hmu)

set_option linter.style.longLine false in
/-- Pointwise-support variant of
`weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos_ae`.

This is the split-primitive direct-sign route with pointwise reduced-form rank
and pointwise `µ* ≤ 0`; the a.e. random limit-bread fields are derived by the
condition-package constructor. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hmu : ∀ η, mustar η ≤ 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218StructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector)
      hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
      hrayleigh hReducedRank hmu)

set_option linter.style.longLine false in
/-- Uncentered pointwise-support companion to
`weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos`. -/
theorem
    weakIV_estimators_theorem12_18_of_structural_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hmu : ∀ η, mustar η ≤ 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_theorem12_18_of_structural_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218StructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector)
      hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
      hrayleigh hReducedRank hmu)

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 endpoint from split primitive stochastic inputs and
the narrow structural Rayleigh selector.

Compared with
`weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae`,
this wrapper no longer requires the full reduced-form Rayleigh selector
certificate.  The remaining Rayleigh input is exactly the continuous selector
data and structural `µ*` minimizer used by the LIML limit; reduced-form
rank and Rayleigh-sign inputs still discharge random limit-bread
nonsingularity. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218StructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector)
      hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
      hrayleigh hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Pointwise-support variant of
`weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae`. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLStructuralRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_structural_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218StructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector)
      hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
      hrayleigh hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 endpoint from split primitive stochastic inputs and
the full reduced-form Rayleigh selector.

Compared with
`weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_selector_rows_reducedForm_rank_rayleigh_nonpos_ae`,
this wrapper no longer assumes the joint root/OLS primitive process directly.
It builds that joint convergence from Hansen's root local-to-zero primitive CLT
and the two normalized OLS WLLNs, then reuses the reduced-form Rayleigh selector
and a.e. reduced-form rank/sign bridges. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
      hrayleigh hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Centered Theorem 12.18 endpoint from the full reduced-form Rayleigh selector,
returning Hansen's full reduced-form `µ*` minimizer certificate alongside the
estimator limits.

This is the faithfulness wrapper for Hansen's definition of `µ*`: the estimator
proof only needs the structural Rayleigh minimizer, but Hansen's theorem defines
`µ*` by the full reduced-form Rayleigh problem.  The minimizer certificate is
already present in `WeakIVLIMLReducedFormRayleighSelectorCertificate`; this
wrapper keeps it visible in the theorem conclusion. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae_with_reducedForm_minimizer
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    (TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν) ∧
    (∀ η,
      LIMLRayleighMinimizer
        (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
        Sigma (mustar η)) :=
  ⟨weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
      (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
      hrayleigh hReducedRank hRayleighNonpos,
    hrayleigh.reducedForm_limit_rayleigh_minimizer⟩

set_option linter.style.longLine false in
/-- Uncentered Theorem 12.18 endpoint from the full reduced-form Rayleigh
selector, returning Hansen's full reduced-form `µ*` minimizer certificate
alongside the textbook `β + bias` estimator limits.

This is the uncentered companion to
`weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae_with_reducedForm_minimizer`. -/
theorem
    weakIV_estimators_theorem12_18_of_reducedForm_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae_with_reducedForm_minimizer
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ν {η | ¬ Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec} = 0)
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    (TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν) ∧
    (∀ η,
      LIMLRayleighMinimizer
        (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
        Sigma (mustar η)) :=
  ⟨weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem
      (μ := μ) (ν := ν)
      (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae
        (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
        (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
        (Xi2 := Xi2) (xie := xie) (mustar := mustar)
        (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
        (muSelector := muSelector) (Sigma := Sigma)
        hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
        hrayleigh hReducedRank hRayleighNonpos),
    hrayleigh.reducedForm_limit_rayleigh_minimizer⟩

set_option linter.style.longLine false in
/-- Pointwise-support variant of
`weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae`. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  weakIV_estimators_minus_beta_theorem12_18_of_raw_eigenvalue_problem
    (μ := μ) (ν := ν)
    (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos
      (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
      hrayleigh hReducedRank hRayleighNonpos)

set_option linter.style.longLine false in
/-- Pointwise-support centered Theorem 12.18 endpoint from the full reduced-form
Rayleigh selector, returning Hansen's reduced-form `µ*` minimizer certificate
alongside the estimator limits. -/
theorem
    weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_with_reducedForm_minimizer
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    (TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν) ∧
    (∀ η,
      LIMLRayleighMinimizer
        (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
        Sigma (mustar η)) :=
  ⟨weakIV_estimators_minus_beta_theorem12_18_of_reducedForm_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
      (μ := μ) (ν := ν) (Z := Z) (X := X) (Y := Y) (e := e)
      (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
      (Xi2 := Xi2) (xie := xie) (mustar := mustar)
      (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
      (muSelector := muSelector) (Sigma := Sigma)
      hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
      hrayleigh hReducedRank hRayleighNonpos,
    hrayleigh.reducedForm_limit_rayleigh_minimizer⟩

set_option linter.style.longLine false in
/-- Pointwise-support uncentered Theorem 12.18 endpoint from the full
reduced-form Rayleigh selector, returning Hansen's reduced-form `µ*` minimizer
certificate alongside the textbook `β + bias` estimator limits.

This is the pointwise-support companion to
`weakIV_estimators_theorem12_18_of_reducedForm_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae_with_reducedForm_minimizer`. -/
theorem
    weakIV_estimators_theorem12_18_of_reducedForm_rayleigh_selector_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_with_reducedForm_minimizer
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hX : ∀ i, AEStronglyMeasurable (X i) μ)
    (he : ∀ i, AEStronglyMeasurable (e i) μ)
    (hMu : ∀ m, AEStronglyMeasurable (fun ω => limlMuHat m ω) μ)
    (hbread : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedBread X m ω)
      atTop (fun _ => Sigma22))
    (hscore : TendstoInMeasure μ
      (fun m ω => weakIVOLSNormalizedScore X e m ω)
      atTop (fun _ => Sigma2e))
    (hSigma22 : Sigma22.PosDef)
    (hroot : TendstoInDistribution
      (E := Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIV2SLSRootPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)
      (fun _ => μ) ν)
    (hQZZ : QZZ.PosDef)
    (hrayleigh : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22)
    (hReducedRank : ∀ η, Function.Injective
      (weakIVReducedFormLimit QZZ C (Xi2 η) (xie η) β).mulVec)
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, γ ≠ 0 ∧
      weakIVLIMLRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    (TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν) ∧
    (∀ η,
      LIMLRayleighMinimizer
        (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
        Sigma (mustar η)) :=
  ⟨weakIV_estimators_theorem12_18_of_raw_eigenvalue_problem
      (μ := μ) (ν := ν)
      (WeakIVTheorem1218RawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos
        (μ := μ) (ν := ν) (Z := Z) (X := X) (e := e) (Y := Y)
        (limlMuHat := limlMuHat) (β := β) (QZZ := QZZ) (C := C)
        (Xi2 := Xi2) (xie := xie) (mustar := mustar)
        (Sigma22 := Sigma22) (Sigma2e := Sigma2e)
        (muSelector := muSelector) (Sigma := Sigma)
        hmodel hZ hX he hMu hbread hscore hSigma22 hroot hQZZ
        hrayleigh hReducedRank hRayleighNonpos),
    hrayleigh.reducedForm_limit_rayleigh_minimizer⟩

/-- Hansen Theorem 12.18 from the centered condition package, returning the
textbook-centered claims directly. -/
theorem weakIV_estimators_minus_beta_theorem12_18_of_centered
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218CenteredConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  ⟨h.ols_centered, h.twoSLS_centered, h.liml_centered⟩

/-- Uncentered compatibility wrapper from the centered weak-IV package.  This
keeps the theorem-facing centered package minimal while preserving the earlier
`β + bias` endpoint. -/
theorem weakIV_estimators_theorem12_18_of_centered
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218CenteredConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν := by
  have hOLS := tendstoInMeasure_continuous_comp hOLS_meas h.ols_centered
    (by fun_prop : Continuous fun x : k → ℝ => β + x)
  have hOLS' : TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) := by
    refine TendstoInMeasure.congr ?_ EventuallyEq.rfl hOLS
    intro m
    exact ae_of_all μ (fun ω => by
      ext i
      simp [Pi.add_apply, Pi.sub_apply])
  have h2 := h.twoSLS_centered.continuous_comp
    (by fun_prop : Continuous fun x : k → ℝ => β + x)
  have h2' : TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν := by
    refine TendstoInDistribution.congr ?_ ?_ h2
    · intro m
      exact ae_of_all μ (fun ω => by
        ext i
        simp [Pi.add_apply, Pi.sub_apply])
    · exact EventuallyEq.rfl
  have hL := h.liml_centered.continuous_comp
    (by fun_prop : Continuous fun x : k → ℝ => β + x)
  have hL' : TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν := by
    refine TendstoInDistribution.congr ?_ ?_ hL
    · intro m
      exact ae_of_all μ (fun ω => by
        ext i
        simp [Pi.add_apply, Pi.sub_apply])
    · exact EventuallyEq.rfl
  exact ⟨hOLS', h2', hL'⟩

/-- Hansen Theorem 12.18 OLS face in the textbook's exact centered form:
`β̂_ols - β ->p Σ₂₂⁻¹Σ₂e`.  The proof reuses the proof-facing probability-limit
package and the project continuous-mapping theorem. -/
theorem weakIV_olsBetaStar_minus_beta_tendstoInMeasure
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e)
    (hmeas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) := by
  have hdiff := tendstoInMeasure_continuous_comp hmeas h.ols_limit
    (by fun_prop : Continuous fun x : k → ℝ => x - β)
  refine TendstoInMeasure.congr (fun _ => EventuallyEq.rfl) ?_ hdiff
  exact ae_of_all μ (fun _ => by
    ext i
    simp [Pi.sub_apply, Pi.add_apply])

/-- Hansen Theorem 12.18 2SLS face in the textbook's exact centered form:
`β̂_2sls - β` converges in distribution to the displayed weak-IV random
functional. -/
theorem weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν := by
  have hdiff := h.twoSLS_limit.continuous_comp
    (by fun_prop : Continuous fun x : k → ℝ => x - β)
  refine TendstoInDistribution.congr ?_ ?_ hdiff
  · intro _
    exact EventuallyEq.rfl
  · exact ae_of_all ν (fun η => by
      ext i
      simp [Pi.sub_apply, Pi.add_apply])

/-- Hansen Theorem 12.18 LIML face in the textbook's exact centered form:
`β̂_liml - β` converges in distribution to the displayed weak-IV LIML random
functional. -/
theorem weakIV_limlBetaStar_minus_beta_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν := by
  have hdiff := h.liml_limit.continuous_comp
    (by fun_prop : Continuous fun x : k → ℝ => x - β)
  refine TendstoInDistribution.congr ?_ ?_ hdiff
  · intro _
    exact EventuallyEq.rfl
  · exact ae_of_all ν (fun η => by
      ext i
      simp [Pi.sub_apply, Pi.add_apply])

/-- Hansen Theorem 12.18 LIML face in k-class notation.  This is the same
centered weak-IV limit as `weakIV_limlBetaStar_minus_beta_tendstoInDistribution`,
transported through `κ = μ + 1` from `LIML.lean`. -/
theorem weakIV_limlKClassBetaStar_add_one_minus_beta_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlKClassBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω + 1) - β)
      atTop
      (fun η =>
        weakIVKClassBias QZZ C (Xi2 η) (xie η) (mustar η + 1) Sigma22 Sigma2e)
      (fun _ => μ) ν := by
  have hliml := weakIV_limlBetaStar_minus_beta_tendstoInDistribution h
  refine TendstoInDistribution.congr ?_ ?_ hliml
  · intro m
    exact ae_of_all μ (fun ω => by
      simp [limlBetaStar_eq_kClass_add_one])
  · exact ae_of_all ν (fun η => by
      simpa using
        weakIVLIMLBias_eq_kClassBias_add_one
          (QZZ := QZZ) (C := C) (Xi2 := Xi2 η) (xie := xie η)
          (mustar := mustar η) (Sigma22 := Sigma22) (Sigma2e := Sigma2e))

/-- K-class version of Hansen Theorem 12.18 for any estimator sequence `κ̂`
known pointwise to be Hansen's `μ̂ + 1`. -/
theorem weakIV_limlKClassBetaStar_kappa_minus_beta_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e)
    (hkappa : ∀ m ω, kappaHat m ω = weakIVLIMLFiniteSampleMu limlMuHat m ω + 1) :
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlKClassBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (kappaHat m ω) - β)
      atTop
      (fun η =>
        weakIVKClassBias QZZ C (Xi2 η) (xie η) (mustar η + 1) Sigma22 Sigma2e)
      (fun _ => μ) ν := by
  have hκ := weakIV_limlKClassBetaStar_add_one_minus_beta_tendstoInDistribution h
  refine TendstoInDistribution.congr ?_ ?_ hκ
  · intro m
    exact ae_of_all μ (fun ω => by
      simp [hkappa m ω])
  · exact EventuallyEq.rfl

/-- Hansen Theorem 12.18, assembled in the exact centered form used in the
textbook.  The primitive local-to-zero CLT and LIML eigenvalue-minimum
constructors are still represented by `WeakIVTheorem1218Conditions`. -/
theorem weakIV_estimators_minus_beta_theorem12_18
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e)
    (hmeas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν := by
  exact
    ⟨weakIV_olsBetaStar_minus_beta_tendstoInMeasure h hmeas,
      weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution h,
      weakIV_limlBetaStar_minus_beta_tendstoInDistribution h⟩

/-- Hansen Theorem 12.18, assembled in the exact centered form used in the
textbook with LIML written in k-class notation.  This is a theorem-facing
wrapper around `weakIV_estimators_minus_beta_theorem12_18` and the
`κ = μ + 1` bridge from `LIML.lean`. -/
theorem weakIV_estimators_minus_beta_theorem12_18_kappa
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e)
    (hkappa : ∀ m ω, kappaHat m ω = weakIVLIMLFiniteSampleMu limlMuHat m ω + 1)
    (hmeas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω)) μ) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlKClassBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (kappaHat m ω) - β)
      atTop
      (fun η =>
        weakIVKClassBias QZZ C (Xi2 η) (xie η) (mustar η + 1) Sigma22 Sigma2e)
      (fun _ => μ) ν :=
  ⟨weakIV_olsBetaStar_minus_beta_tendstoInMeasure h hmeas,
    weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution h,
    weakIV_limlKClassBetaStar_kappa_minus_beta_tendstoInDistribution h hkappa⟩

/-- Hansen Theorem 12.18 uncentered endpoint with LIML written directly in
k-class notation. -/
theorem weakIV_estimators_theorem12_18_kappa
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {limlMuHat kappaHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVTheorem1218Conditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e)
    (hkappa : ∀ m ω, kappaHat m ω = weakIVLIMLFiniteSampleMu limlMuHat m ω + 1) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop (fun _ => β + weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω))
      atTop
      (fun η => β + weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlKClassBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (kappaHat m ω))
      atTop
      (fun η =>
        β + weakIVKClassBias QZZ C (Xi2 η) (xie η) (mustar η + 1) Sigma22 Sigma2e)
      (fun _ => μ) ν := by
  have hbase := weakIV_estimators_theorem12_18 h
  have hlimlCentered :=
    weakIV_limlKClassBetaStar_kappa_minus_beta_tendstoInDistribution h hkappa
  have hliml := hlimlCentered.continuous_comp
    (by fun_prop : Continuous fun x : k → ℝ => β + x)
  refine ⟨hbase.1, hbase.2.1, ?_⟩
  refine TendstoInDistribution.congr ?_ ?_ hliml
  · intro m
    exact ae_of_all μ (fun ω => by
      ext i
      simp [Pi.add_apply, Pi.sub_apply])
  · exact EventuallyEq.rfl

end Asymptotics

end HansenEconometrics
