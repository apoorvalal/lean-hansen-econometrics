import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.AsymptoticUtils.StochasticOrder
import HansenEconometrics.Chapter6Asymptotics
import HansenEconometrics.Chapter12InstrumentalVariables.Asymptotics
import HansenEconometrics.Chapter12InstrumentalVariables.LIML
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-!
# Chapter 12 — weak instruments

This file gives the theorem surface for Hansen Theorem 12.18.  Its canonical
LIML eigenvalue primitive is the finite-sample generalized Rayleigh pair
`([Y X]'P_Z[Y X], n^{-1}[Y X]'M_Z[Y X])`; the corresponding limit pair uses
Hansen's full reduced-form Gaussian matrix and covariance `Σ`.

The canonical corrected triangular-array endpoint is
`weakIV_theorem12_18_triangular_estimators_of_raw_moments`. It derives all
three actual Star-estimator limits from raw iid moments, constructs the
generalized-pencil selector from the concrete smallest root, and states the
limiting-bread nondegeneracy assumptions omitted by the printed theorem.

Older assembly and structural-block Rayleigh interfaces are retained under
`WeakIVCompatibility`.  They are proof support only and are not canonical
statements of Hansen's LIML eigenvalue problem.
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

@[reducible]
private noncomputable def weakIVMatrixSecondCountableTopologyInst
    {ι κ : Type*} [Countable ι] [Countable κ] :
    SecondCountableTopology (Matrix ι κ ℝ) := by
  change SecondCountableTopology (ι → κ → ℝ)
  infer_instance

attribute [local instance] weakIVMatrixBorelMeasurableSpaceInst weakIVMatrixBorelSpaceInst
  weakIVMatrixSecondCountableTopologyInst

/-- OLS weak-instrument probability limit drift,
`Σ₂₂^{-1} Σ₂e`, from Hansen Theorem 12.18. -/
noncomputable def weakIVOLSBias
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) : k → ℝ :=
  Sigma22⁻¹ *ᵥ Sigma2e

/-- Weak first-stage Gaussian/local-to-zero limit matrix `Q_ZZ C + Ξ₂`. -/
noncomputable def weakIVFirstStageLimit
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ) : Matrix l k ℝ :=
  QZZ * C + Xi2

/-- X-only structural block of the weak-IV LIML limit bread,
`(Q_ZZ C + Ξ₂)' Q_ZZ^{-1} (Q_ZZ C + Ξ₂)`.

This is not Hansen's generalized-eigenvalue numerator for `µ*`, which uses
the full reduced-form matrix `[Y X]`; see `weakIVReducedFormRayleighMatrix`.
It remains public only as algebraic support for the displayed LIML bias. -/
noncomputable def weakIVStructuralRayleighMatrix
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ) : Matrix k k ℝ :=
  limlRayleighMatrix QZZ (weakIVFirstStageLimit QZZ C Xi2)

/-- X-only structural Rayleigh quotient used by legacy nonsingularity support.

This quotient does not define Hansen's `µ*`; minimizing it together with the
full reduced-form quotient is generally contradictory. -/
noncomputable def weakIVStructuralRayleighQuotient
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ)
    (Sigma22 : Matrix k k ℝ) (γ : k → ℝ) : ℝ :=
  limlRayleighQuotient (weakIVStructuralRayleighMatrix QZZ C Xi2) Sigma22 γ

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
      (stackScalar_aestronglyMeasurable (μ := μ) (n := m) he)
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
      (stackScalar_aestronglyMeasurable (μ := μ) (n := m) he)
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
      (stackScalar_aestronglyMeasurable (μ := μ) (n := m) hY)
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

/-- The finite-sample reduced-form data matrix `[Y X]` used by Hansen's LIML
generalized eigenvalue problem. -/
noncomputable def weakIVReducedFormSampleMatrix
    (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → k → ℝ)
    (m : ℕ) (ω : Ω) : Matrix (Fin m) (Sum Unit k) ℝ
  | i, Sum.inl _ => Y i.val ω
  | i, Sum.inr j => X i.val ω j

/-- The structural-equation presentation `[Xβ + e, X]` of the reduced-form
sample matrix. -/
noncomputable def weakIVReducedFormStructuralSampleMatrix
    (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ) (β : k → ℝ)
    (m : ℕ) (ω : Ω) : Matrix (Fin m) (Sum Unit k) ℝ
  | i, Sum.inl _ => (X i.val ω) ⬝ᵥ β + e i.val ω
  | i, Sum.inr j => X i.val ω j

omit [Fintype l] [DecidableEq k] [DecidableEq l] [MeasurableSpace Ω] in
/-- Under the structural equation, Hansen's observed `[Y X]` matrix is exactly
the proof-facing `[Xβ + e, X]` matrix. -/
theorem weakIVReducedFormSampleMatrix_eq_structural
    {Y : ℕ → Ω → ℝ} {X : ℕ → Ω → k → ℝ} {e : ℕ → Ω → ℝ}
    {β : k → ℝ}
    (hmodel : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (m : ℕ) (ω : Ω) :
    weakIVReducedFormSampleMatrix Y X m ω =
      weakIVReducedFormStructuralSampleMatrix X e β m ω := by
  ext i j
  cases j with
  | inl u =>
      cases u
      exact hmodel i.val ω
  | inr j => rfl

/-- Hansen's finite-sample LIML Rayleigh numerator
`[Y X]' P_Z [Y X]`.  The Star projection only totalizes singular `Z'Z`; on
the usual full-rank event it is the ordinary instrument projection. -/
noncomputable def weakIVLIMLFiniteSampleRayleighNumerator
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) :
    Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  let Zm := stackRegressors Z m ω
  let R := weakIVReducedFormSampleMatrix Y X m ω
  Rᵀ * instrumentProjectionStar Zm * R

/-- Hansen's random finite-sample residual covariance denominator
`n^{-1}[Y X]' M_Z [Y X]`, where `M_Z = I - P_Z`. -/
noncomputable def weakIVLIMLFiniteSampleResidualCovariance
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) :
    Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  let Zm := stackRegressors Z m ω
  let R := weakIVReducedFormSampleMatrix Y X m ω
  (m : ℝ)⁻¹ •
    (Rᵀ * ((1 : Matrix (Fin m) (Fin m) ℝ) - instrumentProjectionStar Zm) * R)

/-- Canonical finite-sample generalized-eigenvalue primitive for Hansen's
scaled LIML adjustment `n μhat`:
`([Y X]'P_Z[Y X], n^{-1}[Y X]'M_Z[Y X])`.

In particular, the denominator is random; replacing it by its limit `Σ` is
not an exact finite-sample eigenvalue problem. -/
noncomputable def weakIVLIMLGeneralizedEigenvalueSamplePrimitive
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) :
    Matrix (Sum Unit k) (Sum Unit k) ℝ ×
      Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  (weakIVLIMLFiniteSampleRayleighNumerator Z X Y m ω,
    weakIVLIMLFiniteSampleResidualCovariance Z X Y m ω)

/-- Canonical limit generalized-eigenvalue primitive for Hansen's `μ*`:
the full reduced-form Gaussian Rayleigh numerator paired with `Σ`. -/
noncomputable def weakIVLIMLGeneralizedEigenvalueLimitPrimitive
    (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (β : k → ℝ) (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ)
    (η : Ωlim) :
    Matrix (Sum Unit k) (Sum Unit k) ℝ ×
      Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β, Sigma)

/-- The generalized Rayleigh quotient represented by a numerator/denominator
matrix pair. -/
noncomputable def weakIVLIMLGeneralizedRayleighQuotient
    (p : Matrix (Sum Unit k) (Sum Unit k) ℝ ×
      Matrix (Sum Unit k) (Sum Unit k) ℝ)
    (γ : Sum Unit k → ℝ) : ℝ :=
  limlRayleighQuotient p.1 p.2 γ

/-- Canonical selector certificate for Hansen's finite-sample LIML
generalized eigenvalue and its weak-IV limit.

The same scalar is required to minimize only the full reduced-form quotient,
first against every regular random sample residual covariance and then against
its limit `Σ`. At `m = 0` the sample denominator is zero, so the finite-sample
minimum is required only off `selectorBad`. No X-only minimizer or
nonpositive-Rayleigh condition is present. -/
structure WeakIVLIMLGeneralizedEigenvalueSelectorCertificate
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (Y : ℕ → Ω → ℝ) (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ)
    (muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ)
    (selectorBad : Set
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ))
    (ν : Measure Ωlim) : Prop where
  selector_meas : Measurable muSelector
  selector_bad_measurable : MeasurableSet selectorBad
  selector_bad_null :
    (ν.map (fun η =>
      weakIVLIMLGeneralizedEigenvalueLimitPrimitive
        QZZ C Xi2 xie β Sigma η)) selectorBad = 0
  selector_continuous_off : ∀ p, p ∉ selectorBad → ContinuousAt muSelector p
  sample_selector_eq : ∀ m ω,
    limlMuHat m ω =
      muSelector (weakIVLIMLGeneralizedEigenvalueSamplePrimitive Z X Y m ω)
  limit_selector_eq : ∀ η,
    mustar η =
      muSelector
        (weakIVLIMLGeneralizedEigenvalueLimitPrimitive
          QZZ C Xi2 xie β Sigma η)
  finite_sample_rayleigh_minimizer_of_regular : ∀ m ω,
    let p := weakIVLIMLGeneralizedEigenvalueSamplePrimitive Z X Y m ω
    p ∉ selectorBad →
    LIMLRayleighMinimizer p.1 p.2 (limlMuHat m ω)
  limit_rayleigh_minimizer : ∀ η,
    LIMLRayleighMinimizer
      (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
      Sigma (mustar η)

omit [DecidableEq k] in
/-- The corrected generalized-eigenvalue primitive CMT derives
`n μhat ⇒ μ*` from joint convergence of both the projected numerator and the
random residual-covariance denominator. -/
theorem WeakIVLIMLGeneralizedEigenvalueSelectorCertificate.muHat_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {Y : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ}
    {selectorBad : Set
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ)}
    (hprimitive : TendstoInDistribution
      (E := Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ)
      (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        weakIVLIMLGeneralizedEigenvalueSamplePrimitive Z X Y m ω)
      atTop
      (fun η =>
        weakIVLIMLGeneralizedEigenvalueLimitPrimitive
          QZZ C Xi2 xie β Sigma η)
      (fun _ => μ) ν)
    (h : WeakIVLIMLGeneralizedEigenvalueSelectorCertificate
      Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma
      muSelector selectorBad ν) :
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) => limlMuHat m ω)
      atTop mustar (fun _ => μ) ν := by
  have hraw := tendstoInDistribution_ae_continuous_comp
    hprimitive h.selector_meas h.selector_bad_null h.selector_continuous_off
  refine TendstoInDistribution.congr ?_ ?_ hraw
  · intro m
    exact ae_of_all μ (fun ω => by
      simpa [Function.comp_def] using (h.sample_selector_eq m ω).symm)
  · exact ae_of_all ν (fun η => by
      simpa [Function.comp_def] using (h.limit_selector_eq η).symm)

/-- Numerator-only sample support pair `(Qhat_ZZ, n^{-1/2}Z'[Y X])`.

This legacy pair is useful for projected-moment CMTs but is not Hansen's
finite-sample generalized-eigenvalue primitive because it omits the random
residual covariance denominator. -/
noncomputable def weakIVCompatibilityReducedFormRayleighPrimitive
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (β : k → ℝ) (m : ℕ) (ω : Ω) :
    Matrix l l ℝ × Matrix l (Sum Unit k) ℝ :=
  (sampleQZZ (stackRegressors Z m ω),
    weakIVRootReducedFormProjectedMoment Z X e β m ω)

/-- Compatibility limit pair `(Q_ZZ, Q_ZZ C β + ξ)` for the numerator-only
selector route. -/
noncomputable def weakIVCompatibilityReducedFormRayleighLimitPrimitive
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

/-- Compatibility bridge from root moments to the numerator-only pair. -/
noncomputable def weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive
    (β : k → ℝ) (p : Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) :
    Matrix l l ℝ × Matrix l (Sum Unit k) ℝ :=
  (p.1, weakIVReducedFormProjectedMomentFromPrimitive p.2.1 p.2.2 β)

omit [Fintype l] [DecidableEq k] [DecidableEq l] [MeasurableSpace Ω] in
/-- The compatibility bridge specializes to the numerator-only sample pair.
It does not identify Hansen's finite-sample generalized eigenvalue. -/
theorem weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive_sample_eq
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (e : ℕ → Ω → ℝ)
    (β : k → ℝ) (m : ℕ) (ω : Ω) :
    weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
        (weakIV2SLSRootPrimitiveMoments Z X e m ω) =
      weakIVCompatibilityReducedFormRayleighPrimitive Z X e β m ω := by
  rfl

omit [DecidableEq k] [DecidableEq l] [MeasurableSpace Ωlim] in
/-- The compatibility bridge specializes to the numerator-only limit pair. -/
theorem weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive_limit_eq
    (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (β : k → ℝ) (η : Ωlim) :
    weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
        (weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η) =
      weakIVCompatibilityReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η := by
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

/-- Canonical joint primitive for Theorem 12.18: the root-scaled 2SLS and OLS
moments together with Hansen's full finite-sample generalized eigenvalue pair. -/
noncomputable def weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveMoments
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e Y : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) :
    ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
        (Matrix k k ℝ × (k → ℝ))) ×
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ) :=
  (weakIVLIMLRootOLSPrimitiveMoments Z X e m ω,
    weakIVLIMLGeneralizedEigenvalueSamplePrimitive Z X Y m ω)

/-- Limit of the canonical joint Theorem 12.18 primitive. -/
noncomputable def weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveLimit
    (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (β : k → ℝ) (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) (η : Ωlim) :
    ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
        (Matrix k k ℝ × (k → ℝ))) ×
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ) :=
  (weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η,
    weakIVLIMLGeneralizedEigenvalueLimitPrimitive
      QZZ C Xi2 xie β Sigma η)

/-- Map from the canonical joint primitive to the root LIML assembly tuple.
The eigenvalue coordinate is selected from the full numerator/denominator
pair, while the 2SLS coordinate reuses the projected-moment map. -/
noncomputable def weakIVLIMLGeneralizedEigenvalueRootAssemblyMap
    (muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ)
    (p :
      ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) ×
        (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
          Matrix (Sum Unit k) (Sum Unit k) ℝ)) :
    ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ :=
  ((weakIV2SLSProjectedBreadScoreFromPrimitive p.1.1, p.1.2),
    muSelector p.2)

/-- Continuous-map target from primitive root/OLS moments and a Rayleigh
selector to the root-assembly tuple used by the weak-IV LIML moment CMT. -/
noncomputable def weakIVCompatibilityLIMLRootAssemblyFromPrimitiveRayleighMap
    (β : k → ℝ)
    (muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ)
    (p :
      (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
        (Matrix k k ℝ × (k → ℝ))) :
    ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) × ℝ :=
  ((weakIV2SLSProjectedBreadScoreFromPrimitive p.1, p.2),
    muSelector (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β p.1))

omit [DecidableEq k] in
/-- Compatibility CMT from the numerator-only sample pair to a selected limit.

The hypothesis `muSelector` is the continuous argmin/eigenvalue selector for
the pair `(Q, R)`.  This theorem predates the exact random-denominator
primitive and is not the canonical finite-sample LIML eigenvalue route. -/
theorem weakIV_compatibility_limlMuHat_tendstoInDistribution_of_reducedForm_rayleigh_argmin
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
        weakIVCompatibilityReducedFormRayleighPrimitive Z X e β m ω)
      atTop
      (fun η => weakIVCompatibilityReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)
      (fun _ => μ) ν)
    (hselector_cont : Continuous muSelector)
    (hliml_selector : ∀ m ω,
      limlMuHat m ω =
        muSelector (weakIVCompatibilityReducedFormRayleighPrimitive Z X e β m ω))
    (hmustar_selector : ∀ η,
      mustar η =
        muSelector (weakIVCompatibilityReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η))
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
      (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive
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
theorem weakIV_compatibility_reducedForm_rayleigh_primitive_tendstoInDistribution_of_root_primitive
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
        weakIVCompatibilityReducedFormRayleighPrimitive Z X e β m ω)
      atTop
      (fun η => weakIVCompatibilityReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)
      (fun _ => μ) ν := by
  have hraw := hPrimitive.continuous_comp
    (weakIV_reducedForm_rayleigh_primitive_from_root_continuous
      (k := k) (l := l) β)
  refine TendstoInDistribution.congr ?_ ?_ hraw
  · intro m
    exact ae_of_all μ (fun ω => by
      simpa using
        (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive_sample_eq
          (k := k) (l := l) Z X e β m ω))
  · exact ae_of_all ν (fun η => by
      simpa using
        (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive_limit_eq
          (k := k) (l := l) QZZ C Xi2 xie β η))

omit [DecidableEq k] in
private theorem weakIV_liml_generalizedEigenvalue_rootAssembly_map_measurable
    {muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ}
    (hselector_meas : Measurable muSelector) :
    Measurable
      (weakIVLIMLGeneralizedEigenvalueRootAssemblyMap
        (k := k) (l := l) muSelector) := by
  have hroot : Measurable
      (fun p :
          ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
              (Matrix k k ℝ × (k → ℝ))) ×
            (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
              Matrix (Sum Unit k) (Sum Unit k) ℝ) =>
        weakIV2SLSProjectedBreadScoreFromPrimitive (k := k) (l := l) p.1.1) :=
    (weakIV_twoSLS_projected_bread_score_map_measurable (k := k) (l := l)).comp
      (measurable_fst.comp measurable_fst)
  have hols : Measurable
      (fun p :
          ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
              (Matrix k k ℝ × (k → ℝ))) ×
            (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
              Matrix (Sum Unit k) (Sum Unit k) ℝ) => p.1.2) :=
    measurable_snd.comp measurable_fst
  have hmu : Measurable
      (fun p :
          ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
              (Matrix k k ℝ × (k → ℝ))) ×
            (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
              Matrix (Sum Unit k) (Sum Unit k) ℝ) => muSelector p.2) :=
    hselector_meas.comp measurable_snd
  simpa [weakIVLIMLGeneralizedEigenvalueRootAssemblyMap] using
    (hroot.prodMk hols).prodMk hmu

omit [Fintype k] [DecidableEq k] in
private theorem
    weakIV_liml_generalizedEigenvalue_rootAssembly_map_continuousAt_of_qzz_nonsingular
    {muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ}
    (p :
      ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) ×
        (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
          Matrix (Sum Unit k) (Sum Unit k) ℝ))
    (hselector_cont : ContinuousAt muSelector p.2)
    (hp : IsUnit (p.1.1.1).det) :
    ContinuousAt
      (weakIVLIMLGeneralizedEigenvalueRootAssemblyMap
        (k := k) (l := l) muSelector) p := by
  have hroot_inner : ContinuousAt
      (fun q :
          (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
            (Matrix k k ℝ × (k → ℝ)) =>
        weakIV2SLSProjectedBreadScoreFromPrimitive (k := k) (l := l) q.1) p.1 :=
    (weakIV_twoSLS_projected_bread_score_map_continuousAt_of_qzz_nonsingular
      (k := k) (l := l) p.1.1 hp).comp continuousAt_fst
  have hroot : ContinuousAt
      (fun q :
          ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
              (Matrix k k ℝ × (k → ℝ))) ×
            (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
              Matrix (Sum Unit k) (Sum Unit k) ℝ) =>
        weakIV2SLSProjectedBreadScoreFromPrimitive (k := k) (l := l) q.1.1) p :=
    hroot_inner.comp continuousAt_fst
  have hols : ContinuousAt
      (fun q :
          ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
              (Matrix k k ℝ × (k → ℝ))) ×
            (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
              Matrix (Sum Unit k) (Sum Unit k) ℝ) => q.1.2) p :=
    continuousAt_snd.comp continuousAt_fst
  have hmu : ContinuousAt
      (fun q :
          ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
              (Matrix k k ℝ × (k → ℝ))) ×
            (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
              Matrix (Sum Unit k) (Sum Unit k) ℝ) => muSelector q.2) p :=
    hselector_cont.comp continuousAt_snd
  simpa [weakIVLIMLGeneralizedEigenvalueRootAssemblyMap] using
    (hroot.prodMk hols).prodMk hmu

omit [DecidableEq k] in
/-- Canonical root-assembly CMT for the LIML face of Hansen Theorem 12.18.

The input jointly contains the local-to-zero root moments, OLS moments, and
the full generalized-eigenvalue pair with random residual covariance.  Thus
the output convergence of `µ̂_n` is derived by the selector map rather than
assumed as part of an assembly package. -/
theorem weakIV_liml_root_assembly_joint_tendstoInDistribution_of_generalizedEigenvalue
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ}
    {selectorBad : Set
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ)}
    (hprimitive : TendstoInDistribution
      (E :=
        ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
            (Matrix k k ℝ × (k → ℝ))) ×
          (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
            Matrix (Sum Unit k) (Sum Unit k) ℝ))
      (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveMoments Z X e Y m ω)
      atTop
      (fun η =>
        weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveLimit
          QZZ C Xi2 xie β Sigma22 Sigma2e Sigma η)
      (fun _ => μ) ν)
    (hQZZ : IsUnit QZZ.det)
    (hselector : WeakIVLIMLGeneralizedEigenvalueSelectorCertificate
      Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma
      muSelector selectorBad ν) :
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
  let Dq : Set
      (((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) ×
        (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
          Matrix (Sum Unit k) (Sum Unit k) ℝ)) :=
    {p | ¬ IsUnit (p.1.1.1).det}
  let Ds : Set
      (((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) ×
        (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
          Matrix (Sum Unit k) (Sum Unit k) ℝ)) :=
    {p | p.2 ∈ selectorBad}
  let D := Dq ∪ Ds
  have hDq_meas : MeasurableSet Dq := by
    have hdet : Measurable
        (fun p :
            ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
                (Matrix k k ℝ × (k → ℝ))) ×
              (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
                Matrix (Sum Unit k) (Sum Unit k) ℝ) => (p.1.1.1).det) :=
      (Continuous.matrix_det
        (continuous_fst.comp (continuous_fst.comp continuous_fst))).measurable
    rw [show Dq =
        (fun p :
            ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
                (Matrix k k ℝ × (k → ℝ))) ×
              (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
                Matrix (Sum Unit k) (Sum Unit k) ℝ) => (p.1.1.1).det) ⁻¹' {0} by
          ext p
          simp [Dq, isUnit_iff_ne_zero]]
    exact hdet (measurableSet_singleton (0 : ℝ))
  have hDs_meas : MeasurableSet Ds := by
    change MeasurableSet
      ((fun p :
          ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
              (Matrix k k ℝ × (k → ℝ))) ×
            (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
              Matrix (Sum Unit k) (Sum Unit k) ℝ) => p.2) ⁻¹' selectorBad)
    exact measurable_snd hselector.selector_bad_measurable
  have hD_meas : MeasurableSet D := hDq_meas.union hDs_meas
  have hDq_null :
      (ν.map
        (fun η =>
          weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveLimit
            QZZ C Xi2 xie β Sigma22 Sigma2e Sigma η)) Dq = 0 := by
    rw [Measure.map_apply_of_aemeasurable hprimitive.aemeasurable_limit hDq_meas]
    have hQZZ_ne : QZZ.det ≠ 0 := hQZZ.ne_zero
    have hpre_empty :
        (fun η =>
          weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveLimit
            QZZ C Xi2 xie β Sigma22 Sigma2e Sigma η) ⁻¹' Dq =
            (∅ : Set Ωlim) := by
      ext η
      simp [Dq, weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveLimit,
        weakIVLIMLRootOLSPrimitiveLimit, weakIV2SLSPrimitiveLimit,
        isUnit_iff_ne_zero, hQZZ_ne]
    rw [hpre_empty]
    simp
  have hDs_null :
      (ν.map
        (fun η =>
          weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveLimit
            QZZ C Xi2 xie β Sigma22 Sigma2e Sigma η)) Ds = 0 := by
    rw [Measure.map_apply_of_aemeasurable hprimitive.aemeasurable_limit hDs_meas]
    have heigen_limit_ae : AEMeasurable
        (fun η =>
          weakIVLIMLGeneralizedEigenvalueLimitPrimitive
            QZZ C Xi2 xie β Sigma η) ν :=
      measurable_snd.comp_aemeasurable hprimitive.aemeasurable_limit
    have hbad := hselector.selector_bad_null
    rw [Measure.map_apply_of_aemeasurable heigen_limit_ae
      hselector.selector_bad_measurable] at hbad
    simpa [Ds, weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveLimit] using hbad
  have hD_null :
      (ν.map
        (fun η =>
          weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveLimit
            QZZ C Xi2 xie β Sigma22 Sigma2e Sigma η)) D = 0 := by
    simpa [D] using measure_union_null hDq_null hDs_null
  have hcont : ∀ p :
      ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) ×
        (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
          Matrix (Sum Unit k) (Sum Unit k) ℝ),
      p ∉ D →
        ContinuousAt
          (weakIVLIMLGeneralizedEigenvalueRootAssemblyMap
            (k := k) (l := l) muSelector) p := by
    intro p hp
    have hpq : p ∉ Dq := by
      intro hpq
      exact hp (by exact Or.inl hpq)
    have hps : p ∉ Ds := by
      intro hps
      exact hp (by exact Or.inr hps)
    have hpunit : IsUnit (p.1.1.1).det := by
      simpa [Dq] using hpq
    have hselector_cont : ContinuousAt muSelector p.2 :=
      hselector.selector_continuous_off p.2 (by simpa [Ds] using hps)
    exact
      weakIV_liml_generalizedEigenvalue_rootAssembly_map_continuousAt_of_qzz_nonsingular
        (k := k) (l := l) p hselector_cont hpunit
  have hraw := tendstoInDistribution_ae_continuous_comp
    hprimitive
    (weakIV_liml_generalizedEigenvalue_rootAssembly_map_measurable
      (k := k) (l := l) hselector.selector_meas)
    hD_null hcont
  refine TendstoInDistribution.congr ?_ ?_ hraw
  · intro m
    exact ae_of_all μ (fun ω => by
      change
        weakIVLIMLGeneralizedEigenvalueRootAssemblyMap muSelector
            (weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveMoments
              Z X e Y m ω) =
          (((weakIV2SLSRootScaledBread Z X m ω,
              weakIV2SLSRootScaledScore Z X e m ω),
            (weakIVOLSNormalizedBread X m ω,
              weakIVOLSNormalizedScore X e m ω)),
            limlMuHat m ω)
      simp only [weakIVLIMLGeneralizedEigenvalueRootAssemblyMap,
        weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveMoments]
      rw [← hselector.sample_selector_eq m ω]
      simp [
        weakIVLIMLRootOLSPrimitiveMoments,
        weakIV2SLSProjectedBreadScoreFromRootPrimitive_eq])
  · exact ae_of_all ν (fun η => by
      change
        weakIVLIMLGeneralizedEigenvalueRootAssemblyMap muSelector
            (weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveLimit
              QZZ C Xi2 xie β Sigma22 Sigma2e Sigma η) =
          (((weakIV2SLSLimitBread QZZ C (Xi2 η),
              weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)),
            (Sigma22, Sigma2e)),
            mustar η)
      simp only [weakIVLIMLGeneralizedEigenvalueRootAssemblyMap,
        weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveLimit]
      rw [← hselector.limit_selector_eq η]
      simp [
        weakIVLIMLRootOLSPrimitiveLimit,
        weakIV2SLSProjectedBreadScoreFromPrimitive,
        weakIV2SLSPrimitiveLimit, weakIV2SLSLimitBread, weakIV2SLSLimitScore,
        Matrix.mul_assoc])

omit [DecidableEq k] in
private theorem weakIV_liml_rootAssembly_from_primitive_rayleigh_map_measurable
    (β : k → ℝ)
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (hselector_cont : Continuous muSelector) :
    Measurable
      (weakIVCompatibilityLIMLRootAssemblyFromPrimitiveRayleighMap
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
        muSelector (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β p.1)) :=
    hselector_cont.measurable.comp
      ((weakIV_reducedForm_rayleigh_primitive_from_root_continuous
        (k := k) (l := l) β).measurable.comp measurable_fst)
  simpa [weakIVCompatibilityLIMLRootAssemblyFromPrimitiveRayleighMap] using
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
      (weakIVCompatibilityLIMLRootAssemblyFromPrimitiveRayleighMap
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
        muSelector (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β q.1)) p :=
    hselector_cont.continuousAt.comp
      ((weakIV_reducedForm_rayleigh_primitive_from_root_continuous
        (k := k) (l := l) β).continuousAt.comp continuousAt_fst)
  simpa [weakIVCompatibilityLIMLRootAssemblyFromPrimitiveRayleighMap] using
    (hroot.prodMk hols).prodMk hmu

omit [DecidableEq k] in
/-- Compatibility root/OLS/numerator-selector CMT.

This support bridge maps primitive local-to-zero moments and the continuous
numerator-only selector to the joint
`((B₂SLS,S₂SLS),(Σ₂₂,Σ₂e),µ̂)` assembly required by the weak-scaled LIML moment
CMT.  It is retained for compatibility and is not the canonical Hansen
generalized-eigenvalue derivation. -/
theorem weakIV_compatibility_root_assembly_of_numerator_selector
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
        muSelector (weakIVCompatibilityReducedFormRayleighPrimitive Z X e β m ω))
    (hmustar_selector : ∀ η,
      mustar η =
        muSelector (weakIVCompatibilityReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)) :
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
          (weakIVCompatibilityLIMLRootAssemblyFromPrimitiveRayleighMap
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
        weakIVCompatibilityLIMLRootAssemblyFromPrimitiveRayleighMap β muSelector
          (weakIVLIMLRootOLSPrimitiveMoments Z X e m ω) =
        (((weakIV2SLSRootScaledBread Z X m ω,
            weakIV2SLSRootScaledScore Z X e m ω),
           (weakIVOLSNormalizedBread X m ω,
            weakIVOLSNormalizedScore X e m ω)),
          limlMuHat m ω)
      have hred :
        weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
              (weakIV2SLSRootPrimitiveMoments Z X e m ω) =
            weakIVCompatibilityReducedFormRayleighPrimitive Z X e β m ω :=
        weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive_sample_eq Z X e β m ω
      rw [hliml_selector m ω]
      simp [weakIVCompatibilityLIMLRootAssemblyFromPrimitiveRayleighMap,
        weakIVLIMLRootOLSPrimitiveMoments,
        weakIV2SLSProjectedBreadScoreFromRootPrimitive_eq, hred])
  · exact ae_of_all ν (fun η => by
      change
        weakIVCompatibilityLIMLRootAssemblyFromPrimitiveRayleighMap β muSelector
          (weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η) =
        (((weakIV2SLSLimitBread QZZ C (Xi2 η),
            weakIV2SLSLimitScore QZZ C (Xi2 η) (xie η)),
           (Sigma22, Sigma2e)),
          mustar η)
      have hred :
          weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
              (weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η) =
            weakIVCompatibilityReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η :=
        weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive_limit_eq QZZ C Xi2 xie β η
      have hred' :
          weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
              (QZZ, weakIVFirstStageLimit QZZ C (Xi2 η), xie η) =
            weakIVCompatibilityReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η := by
        simpa [weakIV2SLSPrimitiveLimit] using hred
      rw [hmustar_selector η]
      simp [weakIVCompatibilityLIMLRootAssemblyFromPrimitiveRayleighMap,
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

/-!
## Compatibility and proof-support interfaces

The declarations in this namespace preserve the earlier assembly-oriented
proof stack.  They are not the canonical Hansen Theorem 12.18 surface:

* the historical Rayleigh certificates omit the random finite-sample residual
  covariance or additionally require an unrelated X-only minimizer;
* the `mu_nonpos` and `rayleigh_nonpos` endpoints are generally unavailable
  under the positive covariance assumptions of the generalized eigenproblem;
* root-assembly packages that already contain joint convergence with `µhat`
  are support interfaces, not derivations of Hansen's eigenvalue limit.

Use `weakIV_theorem12_18_triangular_estimators_of_raw_moments` for the
canonical corrected theorem route. The selector certificate and assembly
declarations below remain reusable proof infrastructure.
-/
namespace WeakIVCompatibility

/-- Compatibility moment/CLT-level LIML condition package.

The fields are the weak-IV-scaled LIML bread and structural-error score joint
limit, plus the high-probability nonsingularity needed to remove Star
totalization.  The estimator itself uses the finite-sample adjustment
`µ̂_n / n`, while `limlMuHat` is the scaled eigenvalue sequence with limit
`μ*`.  Eigenvalue identification belongs to the canonical generalized-
eigenvalue certificate outside this namespace. -/
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
      muSelector (weakIVCompatibilityReducedFormRayleighPrimitive Z X e β m ω)
  limit_selector_eq : ∀ η,
    mustar η =
      muSelector (weakIVCompatibilityReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)
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
      (weakIVStructuralRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)

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
      muSelector (weakIVCompatibilityReducedFormRayleighPrimitive Z X e β m ω)
  limit_selector_eq : ∀ η,
    mustar η =
      muSelector (weakIVCompatibilityReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)
  structural_limit_rayleigh_minimizer : ∀ η,
    LIMLRayleighMinimizer
      (weakIVStructuralRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)

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
          (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
            (weakIV2SLSRootPrimitiveMoments Z X e m ω))) :
    ∀ m ω,
      limlMuHat m ω =
        muSelector (weakIVCompatibilityReducedFormRayleighPrimitive Z X e β m ω) := by
  intro m ω
  simpa [weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive_sample_eq] using
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
          (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
            (weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η))) :
    ∀ η,
      mustar η =
        muSelector (weakIVCompatibilityReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η) := by
  intro η
  simpa [weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive_limit_eq] using
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
        muSelector (weakIVCompatibilityReducedFormRayleighPrimitive Z X e β m ω)) :
    ∀ m ω,
      limlMuHat m ω =
        muSelector
          (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
            (weakIV2SLSRootPrimitiveMoments Z X e m ω)) := by
  intro m ω
  simpa [weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive_sample_eq] using
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
        muSelector (weakIVCompatibilityReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)) :
    ∀ η,
      mustar η =
        muSelector
          (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
            (weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)) := by
  intro η
  simpa [weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive_limit_eq] using
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
          (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
            (weakIV2SLSRootPrimitiveMoments Z X e m ω)))
    (hlimit : ∀ η,
      mustar η =
        muSelector
          (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
            (weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η)))
    (hstructural : ∀ η,
      LIMLRayleighMinimizer
        (weakIVStructuralRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)) :
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
          (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
            (weakIV2SLSRootPrimitiveMoments Z X e m ω)))
    (hlimit_eq : ∀ η,
      mustar η =
        muSelector
          (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
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
        (weakIVStructuralRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)) :
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
        (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
          (weakIV2SLSRootPrimitiveMoments Z X e m ω))
  limit_selector_eq_root_primitive : ∀ η,
    mustar η =
      muSelector
        (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
          (weakIV2SLSPrimitiveLimit QZZ C Xi2 xie η))
  finite_sample_rayleigh_minimizer : ∀ m ω,
    LIMLRayleighMinimizer
      (limlRayleighMatrix
        (sampleQZZ (stackRegressors Z m ω))
        (weakIVRootReducedFormProjectedMoment Z X e β m ω))
      Sigma (limlMuHat m ω)
  structural_limit_rayleigh_minimizer : ∀ η,
    LIMLRayleighMinimizer
      (weakIVStructuralRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)

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
        (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
          (weakIV2SLSRootPrimitiveMoments Z X e m ω))
  limit_selector_eq_root_primitive : ∀ η,
    mustar η =
      muSelector
        (weakIVCompatibilityReducedFormRayleighPrimitiveFromRootPrimitive β
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
      (weakIVStructuralRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)

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
        muSelector (weakIVCompatibilityReducedFormRayleighPrimitive Z X e β m ω))
    (hlimit_eq : ∀ η,
      mustar η =
        muSelector (weakIVCompatibilityReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η))
    (hsample_min : ∀ m ω,
      LIMLRayleighMinimizer
        (limlRayleighMatrix
          (sampleQZZ (stackRegressors Z m ω))
          (weakIVRootReducedFormProjectedMoment Z X e β m ω))
        Sigma (limlMuHat m ω))
    (hstructural_min : ∀ η,
      LIMLRayleighMinimizer
        (weakIVStructuralRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)) :
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
        weakIVCompatibilityReducedFormRayleighPrimitive Z X e β m ω)
      atTop
      (fun η => weakIVCompatibilityReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)
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
    (weakIV_compatibility_reducedForm_rayleigh_primitive_tendstoInDistribution_of_root_primitive
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
        (weakIVStructuralRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)) :=
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
        (weakIVStructuralRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η)) := by
  let hred : WeakIVLIMLReducedFormRayleighSelectorCertificate
      Z X e limlMuHat β QZZ C Xi2 xie mustar muSelector Sigma Sigma22 :=
    WeakIVLIMLReducedFormRayleighSelectorCertificate.of_raw_eigenvalue_problem
      (k := k) (l := l) h
  have hout :=
    weakIV_compatibility_limlMuHat_tendstoInDistribution_of_reducedForm_rayleigh_argmin
      (μ := μ) (ν := ν)
      (weakIV_compatibility_reducedForm_rayleigh_primitive_tendstoInDistribution_of_root_primitive
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
        weakIVCompatibilityReducedFormRayleighPrimitive Z X e β m ω)
      atTop
      (fun η => weakIVCompatibilityReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)
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
        weakIVCompatibilityReducedFormRayleighPrimitive Z X e β m ω)
      atTop
      (fun η => weakIVCompatibilityReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)
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
`weakIV_compatibility_reducedForm_rayleigh_primitive_tendstoInDistribution_of_root_primitive`
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
    (weakIV_compatibility_reducedForm_rayleigh_primitive_tendstoInDistribution_of_root_primitive
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
        weakIVCompatibilityReducedFormRayleighPrimitive Z X e β m ω)
      atTop
      (fun η => weakIVCompatibilityReducedFormRayleighLimitPrimitive QZZ C Xi2 xie β η)
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
  weakIV_compatibility_limlMuHat_tendstoInDistribution_of_reducedForm_rayleigh_argmin
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
  estimator_meas := h.estimator_meas
  actual_bread_meas := h.actual_bread_meas
  actual_score_meas := h.actual_score_meas
  root_assembly_joint_tendsto :=
    weakIV_compatibility_root_assembly_of_numerator_selector
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
  estimator_meas := h.estimator_meas
  actual_bread_meas := h.actual_bread_meas
  actual_score_meas := h.actual_score_meas
  root_assembly_joint_tendsto :=
    weakIV_compatibility_root_assembly_of_numerator_selector
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
/-- A LIML Rayleigh minimizer is nonpositive whenever an admissible test
vector has nonpositive Rayleigh quotient. -/
theorem LIMLRayleighMinimizer.nonpos_of_quotient_nonpos
    {A Sigma : Matrix k k ℝ} {mustar : ℝ}
    (hmin : LIMLRayleighMinimizer A Sigma mustar)
    {γ : k → ℝ} (hγ : limlRayleighAdmissible Sigma γ)
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
        (weakIVStructuralRayleighMatrix QZZ C (Xi2 η)) Sigma22 (mustar η))
    (hwitness : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    ν {η | ¬ mustar η ≤ 0} = 0 := by
  refine measure_mono_null ?_ hwitness
  intro η hbad hwit
  rcases hwit with ⟨γ, hγ, hquot⟩
  exact hbad <| le_trans ((hmin η).lower_bound γ hγ)
    (by simpa [weakIVStructuralRayleighQuotient] using hquot)

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
    (hWitness : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0 := by
  have hEmpty :
      {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
        weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} =
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
  have hsingular := matrix_singular_measure_tendsto_zero_of_tendstoInMeasure
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
      limlNormalizedMomentMatrixStar_eq_zero_sub_mu_residual
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
      limlNormalizedMomentVectorStar_eq_zero_sub_mu_residual
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
      h.linear_model h.estimator_meas
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
structure WeakIVEstimatorLimitConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) : Prop where
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
structure WeakIVCenteredEstimatorLimitConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ) (Y : ℕ → Ω → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ) : Prop where
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
structure WeakIVLocalToZeroEstimatorMomentConditions
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

Compared with `WeakIVLocalToZeroEstimatorMomentConditions`, this package
does not assume the LIML bread/score limit package directly.  It carries OLS
moments, Hansen's root-primitive 2SLS local-to-zero CLT package, and the LIML
root/OLS/`µ̂` assembly package. -/
structure WeakIVEstimatorRootAssemblyConditions
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
structure WeakIVEstimatorPrimitiveRayleighConditions
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
`WeakIVEstimatorPrimitiveRayleighConditions`, but its LIML face only asks
for the continuous finite-sample/limit selector equations and Hansen's
structural Rayleigh-minimum certificate for `µ*`. -/
structure WeakIVEstimatorStructuralRayleighConditions
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
structure WeakIVEstimatorFiniteSampleRayleighConditions
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

This strengthens `WeakIVEstimatorFiniteSampleRayleighConditions` by retaining
the full reduced-form limit Rayleigh minimizer certificate from the raw
eigenvalue problem.  The downstream estimator theorem only needs the
finite-sample package, but this package is the one to cite when auditing
faithfulness to Hansen's `µ*` construction. -/
structure WeakIVEstimatorRawEigenvalueProblemConditions
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
theorem WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive
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
    WeakIVEstimatorFiniteSampleRayleighConditions
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
theorem WeakIVEstimatorFiniteSampleRayleighConditions.of_root_primitive_ols_moments
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
    WeakIVEstimatorFiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive
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
theorem WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive_rows
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
    WeakIVEstimatorFiniteSampleRayleighConditions
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
    WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive
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
`WeakIVEstimatorFiniteSampleRayleighConditions.of_root_primitive_ols_moments`:
all finite-sample measurability fields are derived from row measurability, and
the shared root/OLS primitive convergence is assembled internally by Slutsky. -/
theorem
    WeakIVEstimatorFiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows
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
    WeakIVEstimatorFiniteSampleRayleighConditions
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
    WeakIVEstimatorFiniteSampleRayleighConditions.of_root_primitive_ols_moments
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
`WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae`.
It does not require the raw package's full reduced-form limit minimizer audit
field: the existing finite-sample Rayleigh certificate already carries the
structural LIML minimizer needed to derive `µ* ≤ 0` from the supplied
nonpositive Rayleigh witnesses. -/
theorem
    WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    WeakIVEstimatorFiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive_rows
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
`WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae`.

Pointwise full rank of Hansen's reduced-form limit matrix and pointwise
nonpositive structural Rayleigh witnesses are converted internally to the a.e.
rank/sign fields used for limit-bread nonsingularity. -/
theorem
    WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    WeakIVEstimatorFiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
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
`WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae`:
the shared root/OLS primitive convergence is assembled internally by Slutsky. -/
theorem
    WeakIVEstimatorFiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    WeakIVEstimatorFiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorFiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows
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
`WeakIVEstimatorFiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae`. -/
theorem
    WeakIVEstimatorFiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    WeakIVEstimatorFiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorFiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
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
theorem WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive
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
    WeakIVEstimatorRawEigenvalueProblemConditions
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
theorem WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_moments
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
    WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive
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
theorem WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows
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
    WeakIVEstimatorRawEigenvalueProblemConditions
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
    WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive
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
`WeakIVEstimatorFiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows`:
finite-sample measurability is derived from rows, and the shared root/OLS
primitive convergence is assembled internally by Slutsky. -/
theorem
    WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows
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
    WeakIVEstimatorRawEigenvalueProblemConditions
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
    WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_moments
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
    WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_firstStage_rank_mu_nonpos_ae
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
    WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows
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
    WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_firstStage_rank_mu_nonpos_ae
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
`WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae`. -/
theorem
    WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
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
    WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
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
`WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae`. -/
theorem
    WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae
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
`WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows`.
The 2SLS limit bread is nonsingular a.e. from `QZZ > 0` and a.e. full column
rank of the weak first-stage limit `QZZ*C + Ξ₂`; the LIML limit bread is
nonsingular a.e. from the same rank condition, `Σ₂₂ ≥ 0`, and `µ* ≤ 0` a.e. -/
theorem
    WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
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
    WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows
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
`WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae`:
the caller no longer supplies full rank of the weak first-stage block
`QZZ*C + Ξ₂` directly.  It is derived by restricting the full reduced-form
matrix `[Aβ + ξe, A]` to its right block. -/
theorem
    WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos_ae
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
    WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
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
`WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos_ae`. -/
theorem
    WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos
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
    WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos_ae
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
    WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
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
    WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
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
`WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae`:
the continuous selector, sample selector equation, limit selector equation,
finite-sample Rayleigh minimizer, reduced-form limit minimizer, and structural
limit minimizer are supplied in Hansen's reduced-form notation and converted to
the raw eigenvalue-problem package internally. -/
theorem
    WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
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
    WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma :=
  WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae
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
theorem WeakIVEstimatorFiniteSampleRayleighConditions.of_raw_eigenvalue_problem
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVEstimatorFiniteSampleRayleighConditions
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
theorem WeakIVEstimatorStructuralRayleighConditions.of_primitive_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVEstimatorPrimitiveRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVEstimatorStructuralRayleighConditions
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
theorem WeakIVEstimatorStructuralRayleighConditions.of_root_ols_primitive_rows
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
    WeakIVEstimatorStructuralRayleighConditions
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

This narrows `WeakIVEstimatorStructuralRayleighConditions.of_root_ols_primitive_rows`:
the caller supplies the structural Rayleigh selector and primitive rank/sign
inputs, while the 2SLS and LIML random limit-bread nonsingularity fields are
derived by the existing positive-definite bridges. -/
theorem
    WeakIVEstimatorStructuralRayleighConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
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
    WeakIVEstimatorStructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector :=
  WeakIVEstimatorStructuralRayleighConditions.of_root_ols_primitive_rows
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
`WeakIVEstimatorStructuralRayleighConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae`. -/
theorem
    WeakIVEstimatorStructuralRayleighConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos
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
    WeakIVEstimatorStructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector :=
  WeakIVEstimatorStructuralRayleighConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
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
    WeakIVEstimatorStructuralRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    WeakIVEstimatorStructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector :=
  WeakIVEstimatorStructuralRayleighConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
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
`WeakIVEstimatorStructuralRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae`. -/
theorem
    WeakIVEstimatorStructuralRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    WeakIVEstimatorStructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector :=
  WeakIVEstimatorStructuralRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
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
    WeakIVEstimatorStructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
    WeakIVEstimatorStructuralRayleighConditions
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
    WeakIVEstimatorStructuralRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
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
`WeakIVEstimatorStructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae`.
The root/OLS primitive process is assembled from Hansen's root local-to-zero
primitive CLT and normalized OLS WLLNs, while the first-stage rank input is
derived internally from the full reduced-form limit matrix. -/
theorem
    WeakIVEstimatorStructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos_ae
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
    WeakIVEstimatorStructuralRayleighConditions
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
    WeakIVEstimatorStructuralRayleighConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
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
`WeakIVEstimatorStructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos_ae`.

Pointwise full rank of Hansen's reduced-form limit matrix and pointwise
`µ* ≤ 0` are converted internally to the a.e. fields used to discharge the
random 2SLS and LIML limit-bread nonsingularity assumptions. -/
theorem
    WeakIVEstimatorStructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos
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
    WeakIVEstimatorStructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector :=
  WeakIVEstimatorStructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos_ae
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
`WeakIVEstimatorStructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae`. -/
theorem
    WeakIVEstimatorStructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
    WeakIVEstimatorStructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector :=
  WeakIVEstimatorStructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
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
theorem WeakIVEstimatorRootAssemblyConditions.of_primitive_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVEstimatorPrimitiveRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVEstimatorRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  ols_moments := h.ols_moments
  twoSLS_root_primitive := h.twoSLS_root_primitive
  liml_root_assembly :=
    WeakIVLIMLRootAssemblyConditions.of_primitive_rayleigh
      (μ := μ) (ν := ν) h.liml_primitive_rayleigh

/-- Convert the narrow structural Rayleigh theorem package into the existing
root-assembly theorem package. -/
theorem WeakIVEstimatorRootAssemblyConditions.of_structural_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (h : WeakIVEstimatorStructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector) :
    WeakIVEstimatorRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  ols_moments := h.ols_moments
  twoSLS_root_primitive := h.twoSLS_root_primitive
  liml_root_assembly :=
    WeakIVLIMLRootAssemblyConditions.of_structural_rayleigh
      (μ := μ) (ν := ν) h.liml_structural_rayleigh

/-- Extract the LIML structural Rayleigh root-assembly package from the
finite-sample Rayleigh theorem package. -/
theorem
    WeakIVEstimatorFiniteSampleRayleighConditions.toLIMLStructuralRayleighRootAssembly
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVEstimatorFiniteSampleRayleighConditions
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
theorem WeakIVEstimatorStructuralRayleighConditions.of_finite_sample_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVEstimatorFiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVEstimatorStructuralRayleighConditions
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
    WeakIVEstimatorFiniteSampleRayleighConditions.toLIMLStructuralRayleighRootAssembly
      (μ := μ) (ν := ν) h

/-- Convert the finite-sample Rayleigh/eigenvalue package into the existing
RootAssembly theorem package. -/
theorem WeakIVEstimatorRootAssemblyConditions.of_finite_sample_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVEstimatorFiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVEstimatorRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVEstimatorRootAssemblyConditions.of_structural_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVEstimatorStructuralRayleighConditions.of_finite_sample_rayleigh
      (μ := μ) (ν := ν) h)

/-- Convert the root-assembly primitive package into the existing
local-to-zero moment package used by the Theorem 12.18 endpoints. -/
theorem WeakIVLocalToZeroEstimatorMomentConditions.of_root_assembly
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVEstimatorRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVLocalToZeroEstimatorMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  ols_moments := h.ols_moments
  twoSLS_root_primitive := h.twoSLS_root_primitive
  liml_moments := WeakIVLIMLMomentConditions.of_root_assembly h.liml_root_assembly

/-- Convert the primitive Rayleigh-selector theorem package into the
local-to-zero moment package consumed by the established Theorem 12.18
endpoints. -/
theorem WeakIVLocalToZeroEstimatorMomentConditions.of_primitive_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVEstimatorPrimitiveRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVLocalToZeroEstimatorMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVLocalToZeroEstimatorMomentConditions.of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVEstimatorRootAssemblyConditions.of_primitive_rayleigh
      (μ := μ) (ν := ν) h)

/-- Convert the narrow structural Rayleigh theorem package into the
local-to-zero moment package consumed by the established Theorem 12.18
endpoints. -/
theorem WeakIVLocalToZeroEstimatorMomentConditions.of_structural_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    (h : WeakIVEstimatorStructuralRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector) :
    WeakIVLocalToZeroEstimatorMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVLocalToZeroEstimatorMomentConditions.of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVEstimatorRootAssemblyConditions.of_structural_rayleigh
      (μ := μ) (ν := ν) h)

/-- Convert the finite-sample Rayleigh/eigenvalue theorem package into the
local-to-zero moment package consumed by the established Theorem 12.18
endpoints. -/
theorem WeakIVLocalToZeroEstimatorMomentConditions.of_finite_sample_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVEstimatorFiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVLocalToZeroEstimatorMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVLocalToZeroEstimatorMomentConditions.of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVEstimatorRootAssemblyConditions.of_finite_sample_rayleigh
      (μ := μ) (ν := ν) h)

/-- Convert the raw eigenvalue-problem theorem package into the established
root-assembly package. -/
theorem WeakIVEstimatorRootAssemblyConditions.of_raw_eigenvalue_problem
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVEstimatorRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVEstimatorRootAssemblyConditions.of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVEstimatorFiniteSampleRayleighConditions.of_raw_eigenvalue_problem
      (μ := μ) (ν := ν) h)

/-- Convert the raw eigenvalue-problem theorem package into the established
local-to-zero moment package. -/
theorem WeakIVLocalToZeroEstimatorMomentConditions.of_raw_eigenvalue_problem
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVLocalToZeroEstimatorMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVLocalToZeroEstimatorMomentConditions.of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVEstimatorRootAssemblyConditions.of_raw_eigenvalue_problem
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
    WeakIVCenteredEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
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
    (hliml : TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν) :
    WeakIVCenteredEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
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
    (hliml : TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν) :
    WeakIVCenteredEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
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
    WeakIVCenteredEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
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
    WeakIVCenteredEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  ols_centered := weakIV_olsBetaStar_minus_beta_tendstoInMeasure_of_moments hOLS
  twoSLS_centered :=
    weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution_of_root_primitive_moments h2SLS
  liml_centered := weakIV_limlBetaStar_minus_beta_tendstoInDistribution_of_moments hLIML

/-- Convert the theorem-facing local-to-zero moment package into the centered
Theorem 12.18 condition package. -/
theorem WeakIVCenteredEstimatorLimitConditions.of_local_to_zero_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVLocalToZeroEstimatorMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVCenteredEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  weakIV_centeredConditions_of_ols_twoSLS_root_primitive_liml_moments
    (μ := μ) (ν := ν) h.ols_moments h.twoSLS_root_primitive h.liml_moments

/-- Convert the root-assembly theorem package into the centered Theorem 12.18
condition package. -/
theorem WeakIVCenteredEstimatorLimitConditions.of_root_assembly
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVEstimatorRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVCenteredEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVCenteredEstimatorLimitConditions.of_local_to_zero_moments
    (μ := μ) (ν := ν)
    (WeakIVLocalToZeroEstimatorMomentConditions.of_root_assembly
      (μ := μ) (ν := ν) h)

/-- Convert the finite-sample Rayleigh/eigenvalue theorem package into the
centered Theorem 12.18 condition package. -/
theorem WeakIVCenteredEstimatorLimitConditions.of_finite_sample_rayleigh
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVEstimatorFiniteSampleRayleighConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVCenteredEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVCenteredEstimatorLimitConditions.of_root_assembly
    (μ := μ) (ν := ν)
    (WeakIVEstimatorRootAssemblyConditions.of_finite_sample_rayleigh
      (μ := μ) (ν := ν) h)

/-- Convert the raw LIML eigenvalue-problem theorem package into the centered
Theorem 12.18 condition package.

This endpoint keeps the exact remaining raw input visible while deriving the
OLS, 2SLS, and LIML centered limits through the established moment and
Rayleigh-selector constructors. -/
theorem WeakIVCenteredEstimatorLimitConditions.of_raw_eigenvalue_problem
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {muSelector : Matrix l l ℝ × Matrix l (Sum Unit k) ℝ → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (h : WeakIVEstimatorRawEigenvalueProblemConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e
      muSelector Sigma) :
    WeakIVCenteredEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVCenteredEstimatorLimitConditions.of_finite_sample_rayleigh
    (μ := μ) (ν := ν)
    (WeakIVEstimatorFiniteSampleRayleighConditions.of_raw_eigenvalue_problem
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
    WeakIVEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
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
    (hliml : TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν) :
    WeakIVEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
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
    (hliml : TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω) (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω))
      atTop
      (fun η =>
        β + weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν) :
    WeakIVEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
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
    WeakIVEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
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
    WeakIVEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
  ols_limit := weakIV_olsBetaStar_tendstoInMeasure_of_moments hOLS
  twoSLS_limit :=
    weakIV_twoSLSBetaStar_tendstoInDistribution_of_root_primitive_moments h2SLS
  liml_limit := weakIV_limlBetaStar_tendstoInDistribution_of_moments hLIML

/-- Convert the theorem-facing local-to-zero moment package into the
uncentered compatibility condition package. -/
theorem WeakIVEstimatorLimitConditions.of_local_to_zero_moments
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVLocalToZeroEstimatorMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  weakIV_conditions_of_ols_twoSLS_root_primitive_liml_moments
    (μ := μ) (ν := ν) h.ols_moments h.twoSLS_root_primitive h.liml_moments

/-- Convert the centered Theorem 12.18 condition package into the original
uncentered compatibility package.

The 2SLS and LIML limits are shifted by the continuous map `x ↦ β + x`; the
OLS face uses the same shift in probability.  This keeps the centered package
as the exact textbook surface while still recovering the older `β + bias`
condition package when needed. -/
theorem WeakIVEstimatorLimitConditions.of_centered
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVCenteredEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e)
    (hOLS_meas : ∀ m, AEStronglyMeasurable
      (fun ω => olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β) μ) :
    WeakIVEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e where
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
theorem WeakIVLocalToZeroEstimatorMomentConditions.centeredConditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVLocalToZeroEstimatorMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVCenteredEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVCenteredEstimatorLimitConditions.of_local_to_zero_moments
    (μ := μ) (ν := ν) h

/-- The local-to-zero moment package directly exposes the uncentered
compatibility condition package. -/
theorem WeakIVLocalToZeroEstimatorMomentConditions.conditions
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {e : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVLocalToZeroEstimatorMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e) :
    WeakIVEstimatorLimitConditions
      μ ν Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
  WeakIVEstimatorLimitConditions.of_local_to_zero_moments
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
    (h : WeakIVLocalToZeroEstimatorMomentConditions
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
    (h : WeakIVEstimatorRootAssemblyConditions
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
    (WeakIVLocalToZeroEstimatorMomentConditions.of_root_assembly
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
    (h : WeakIVEstimatorPrimitiveRayleighConditions
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
    (WeakIVEstimatorRootAssemblyConditions.of_primitive_rayleigh
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
    (h : WeakIVEstimatorStructuralRayleighConditions
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
    (WeakIVEstimatorRootAssemblyConditions.of_structural_rayleigh
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
    (h : WeakIVEstimatorFiniteSampleRayleighConditions
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
    (WeakIVEstimatorRootAssemblyConditions.of_finite_sample_rayleigh
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
    (h : WeakIVEstimatorRawEigenvalueProblemConditions
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
    (WeakIVEstimatorFiniteSampleRayleighConditions.of_raw_eigenvalue_problem
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
    (h : WeakIVEstimatorLimitConditions
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
    (h : WeakIVLocalToZeroEstimatorMomentConditions
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
    (WeakIVEstimatorLimitConditions.of_local_to_zero_moments
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
    (h : WeakIVEstimatorRootAssemblyConditions
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
    (WeakIVLocalToZeroEstimatorMomentConditions.of_root_assembly
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
    (h : WeakIVEstimatorPrimitiveRayleighConditions
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
    (WeakIVEstimatorRootAssemblyConditions.of_primitive_rayleigh
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
    (h : WeakIVEstimatorStructuralRayleighConditions
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
    (WeakIVEstimatorRootAssemblyConditions.of_structural_rayleigh
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
    (h : WeakIVEstimatorFiniteSampleRayleighConditions
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
    (WeakIVEstimatorRootAssemblyConditions.of_finite_sample_rayleigh
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
    (h : WeakIVEstimatorRawEigenvalueProblemConditions
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
    (WeakIVEstimatorFiniteSampleRayleighConditions.of_raw_eigenvalue_problem
      (μ := μ) (ν := ν) h)

/-- Centered Theorem 12.18 endpoint from row-measurable primitive fields and
the finite-sample Rayleigh/eigenvalue certificate.

This is the theorem-facing row wrapper around
`WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive_rows`:
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
    (WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive_rows
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
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
    (WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
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
    (WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
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
    (WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
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
    (WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
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
    (WeakIVEstimatorFiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
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
    (WeakIVEstimatorFiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0)
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0)
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
    (WeakIVEstimatorFiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows
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
    (WeakIVEstimatorFiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
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
    (WeakIVEstimatorFiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
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
    (WeakIVEstimatorFiniteSampleRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
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
    (WeakIVEstimatorStructuralRayleighConditions.of_root_ols_primitive_rows
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
    (WeakIVEstimatorStructuralRayleighConditions.of_root_ols_primitive_rows
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows
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
    (WeakIVEstimatorFiniteSampleRayleighConditions.of_root_ols_primitive_rows
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_firstStage_rank_mu_nonpos_ae
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
`WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos_ae`:
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos_ae
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos_ae
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_mu_nonpos
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rank_rayleigh_nonpos
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_ols_primitive_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos
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
    (WeakIVEstimatorStructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos_ae
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
    (WeakIVEstimatorStructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos_ae
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
    (WeakIVEstimatorStructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos
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
    (WeakIVEstimatorStructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_mu_nonpos
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
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
    (WeakIVEstimatorStructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
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
    (WeakIVEstimatorStructuralRayleighConditions.of_root_primitive_ols_wlln_rows_reducedForm_rank_rayleigh_nonpos
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
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
    (hRayleighNonpos : ν {η | ¬ ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0} = 0) :
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
      (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos_ae
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
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
    (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
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
    (hRayleighNonpos : ∀ η, ∃ γ : k → ℝ, limlRayleighAdmissible Sigma22 γ ∧
      weakIVStructuralRayleighQuotient QZZ C (Xi2 η) Sigma22 γ ≤ 0) :
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
      (WeakIVEstimatorRawEigenvalueProblemConditions.of_root_primitive_ols_wlln_rows_reducedForm_rayleigh_selector_rank_rayleigh_nonpos
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
    (h : WeakIVCenteredEstimatorLimitConditions
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
    (h : WeakIVCenteredEstimatorLimitConditions
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
    (h : WeakIVEstimatorLimitConditions
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
    (h : WeakIVEstimatorLimitConditions
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
    (h : WeakIVEstimatorLimitConditions
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
    (h : WeakIVEstimatorLimitConditions
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
    (h : WeakIVEstimatorLimitConditions
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
constructors are still represented by `WeakIVEstimatorLimitConditions`. -/
theorem weakIV_estimators_minus_beta_theorem12_18
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ} {Y : ℕ → Ω → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    (h : WeakIVEstimatorLimitConditions
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
    (h : WeakIVEstimatorLimitConditions
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
    (h : WeakIVEstimatorLimitConditions
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

end WeakIVCompatibility

open WeakIVCompatibility

/-- Canonical primitive condition package for Hansen Theorem 12.18.

The stochastic input is joint convergence of the local-to-zero root moments,
the OLS moments, and the exact finite-sample generalized-eigenvalue pair
`([Y X]'P_Z[Y X], n^{-1}[Y X]'M_Z[Y X])`.  The LIML eigenvalue is identified
only by the full reduced-form generalized Rayleigh problem.  No estimator
limit, X-only minimizer, or nonpositive-Rayleigh endpoint is assumed. -/
structure WeakIVGeneralizedEigenvalueAssemblyConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ωlim) [IsProbabilityMeasure ν]
    (Z : ℕ → Ω → l → ℝ) (X : ℕ → Ω → k → ℝ)
    (e Y : ℕ → Ω → ℝ) (limlMuHat : ℕ → Ω → ℝ)
    (β : k → ℝ) (QZZ : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi2 : Ωlim → Matrix l k ℝ) (xie : Ωlim → l → ℝ)
    (mustar : Ωlim → ℝ)
    (Sigma22 : Matrix k k ℝ) (Sigma2e : k → ℝ)
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ)
    (muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ)
    (selectorBad : Set
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ)) : Prop where
  linear_model : ∀ i ω, Y i ω = (X i ω) ⬝ᵥ β + e i ω
  ols_bread_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIVOLSNormalizedBread X m ω) μ
  ols_score_meas : ∀ m, AEStronglyMeasurable
    (fun ω => weakIVOLSNormalizedScore X e m ω) μ
  sigma22_nonsing : IsUnit Sigma22.det
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
  joint_primitive_tendsto : TendstoInDistribution
    (E :=
      ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) ×
        (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
          Matrix (Sum Unit k) (Sum Unit k) ℝ))
    (Ω := fun _ : ℕ => Ω)
    (fun (m : ℕ) (ω : Ω) =>
      weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveMoments Z X e Y m ω)
    atTop
    (fun η =>
      weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveLimit
        QZZ C Xi2 xie β Sigma22 Sigma2e Sigma η)
    (fun _ => μ) ν
  qzz_nonsing : IsUnit QZZ.det
  eigenvalue_selector : WeakIVLIMLGeneralizedEigenvalueSelectorCertificate
    Z X Y limlMuHat β QZZ C Xi2 xie mustar Sigma
    muSelector selectorBad ν
  twoSLS_limit_nonsing_ae :
    ν {η | ¬ IsUnit (weakIV2SLSLimitBread QZZ C (Xi2 η)).det} = 0
  liml_limit_nonsing_ae :
    ν {η | ¬ IsUnit
      (weakIVLIMLLimitBread QZZ C (Xi2 η) (mustar η) Sigma22).det} = 0

/-- Hansen Theorem 12.18 from the exact finite-sample LIML generalized
eigenvalue problem.

The conclusion contains the three centered estimator limits, convergence of
the scaled finite-sample LIML eigenvalue, and Hansen's full reduced-form
Rayleigh-minimizer characterization of `μ*`. -/
theorem weakIV_estimators_minus_beta_of_generalizedEigenvalueAssembly
    {Z : ℕ → Ω → l → ℝ} {X : ℕ → Ω → k → ℝ}
    {e Y : ℕ → Ω → ℝ} {limlMuHat : ℕ → Ω → ℝ}
    {β : k → ℝ} {QZZ : Matrix l l ℝ} {C : Matrix l k ℝ}
    {Xi2 : Ωlim → Matrix l k ℝ} {xie : Ωlim → l → ℝ}
    {mustar : Ωlim → ℝ}
    {Sigma22 : Matrix k k ℝ} {Sigma2e : k → ℝ}
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    {muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ}
    {selectorBad : Set
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ)}
    (h : WeakIVGeneralizedEigenvalueAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar
      Sigma22 Sigma2e Sigma muSelector selectorBad) :
    TendstoInMeasure μ
      (fun (m : ℕ) ω =>
        olsBetaStar (stackRegressors X m ω) (stackOutcomes Y m ω) - β)
      atTop (fun _ => weakIVOLSBias Sigma22 Sigma2e) ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        twoSLSBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω) - β)
      atTop
      (fun η => weakIV2SLSBias QZZ C (Xi2 η) (xie η))
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) ω =>
        limlBetaStar
          (stackRegressors Z m ω) (stackRegressors X m ω)
          (stackOutcomes Y m ω)
          (weakIVLIMLFiniteSampleMu limlMuHat m ω) - β)
      atTop
      (fun η =>
        weakIVLIMLBias QZZ C (Xi2 η) (xie η) (mustar η) Sigma22 Sigma2e)
      (fun _ => μ) ν ∧
    TendstoInDistribution
      (fun (m : ℕ) (ω : Ω) => limlMuHat m ω)
      atTop mustar (fun _ => μ) ν ∧
    (∀ η, LIMLRayleighMinimizer
      (weakIVReducedFormRayleighMatrix QZZ C (Xi2 η) (xie η) β)
      Sigma (mustar η)) := by
  have hroot_ols : TendstoInDistribution
      (E :=
        (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ)))
      (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) => weakIVLIMLRootOLSPrimitiveMoments Z X e m ω)
      atTop
      (fun η => weakIVLIMLRootOLSPrimitiveLimit QZZ C Xi2 xie Sigma22 Sigma2e η)
      (fun _ => μ) ν := by
    have hraw := h.joint_primitive_tendsto.continuous_comp
      (continuous_fst : Continuous
        (fun p :
          ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
              (Matrix k k ℝ × (k → ℝ))) ×
            (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
              Matrix (Sum Unit k) (Sum Unit k) ℝ) => p.1))
    simpa [weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveMoments,
      weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveLimit] using hraw
  have heigen_primitive : TendstoInDistribution
      (E := Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ)
      (Ω := fun _ : ℕ => Ω)
      (fun (m : ℕ) (ω : Ω) =>
        weakIVLIMLGeneralizedEigenvalueSamplePrimitive Z X Y m ω)
      atTop
      (fun η =>
        weakIVLIMLGeneralizedEigenvalueLimitPrimitive
          QZZ C Xi2 xie β Sigma η)
      (fun _ => μ) ν := by
    have hraw := h.joint_primitive_tendsto.continuous_comp
      (continuous_snd : Continuous
        (fun p :
          ((Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
              (Matrix k k ℝ × (k → ℝ))) ×
            (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
              Matrix (Sum Unit k) (Sum Unit k) ℝ) => p.2))
    simpa [weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveMoments,
      weakIVLIMLGeneralizedEigenvalueRootOLSPrimitiveLimit] using hraw
  let hOLS : WeakIVOLSMomentConditions μ X e Y β Sigma22 Sigma2e :=
    WeakIVOLSMomentConditions.of_root_ols_primitive
      h.linear_model h.ols_bread_meas h.ols_score_meas hroot_ols h.sigma22_nonsing
  let h2SLS : WeakIV2SLSRootPrimitiveMomentConditions
      μ ν Z X e Y β QZZ C Xi2 xie :=
    WeakIV2SLSRootPrimitiveMomentConditions.of_root_ols_primitive
      h.linear_model h.twoSLS_estimator_meas hroot_ols h.qzz_nonsing
      h.twoSLS_limit_nonsing_ae
  have hassembly :=
    weakIV_liml_root_assembly_joint_tendstoInDistribution_of_generalizedEigenvalue
      (μ := μ) (ν := ν) h.joint_primitive_tendsto h.qzz_nonsing
      h.eigenvalue_selector
  let hLIMLRoot : WeakIVLIMLRootAssemblyConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
    { linear_model := h.linear_model
      estimator_meas := h.liml_estimator_meas
      actual_bread_meas := h.liml_actual_bread_meas
      actual_score_meas := h.liml_actual_score_meas
      root_assembly_joint_tendsto := hassembly
      limit_nonsing_ae := h.liml_limit_nonsing_ae }
  let hLIML : WeakIVLIMLMomentConditions
      μ ν Z X e Y limlMuHat β QZZ C Xi2 xie mustar Sigma22 Sigma2e :=
    WeakIVLIMLMomentConditions.of_root_assembly hLIMLRoot
  have hOLS_limit :=
    weakIV_olsBetaStar_minus_beta_tendstoInMeasure_of_moments
      hOLS
  have h2SLS_limit :=
    weakIV_twoSLSBetaStar_minus_beta_tendstoInDistribution_of_root_primitive_moments
      h2SLS
  have hLIML_limit :=
    weakIV_limlBetaStar_minus_beta_tendstoInDistribution_of_moments hLIML
  exact
    ⟨hOLS_limit, h2SLS_limit, hLIML_limit,
      h.eigenvalue_selector.muHat_tendstoInDistribution heigen_primitive,
      h.eigenvalue_selector.limit_rayleigh_minimizer⟩

/-! ## Raw local-to-zero model

The assembly endpoint above consumes the exact finite-sample generalized
eigenvalue primitive. The declarations below record the lower raw model that
produces Hansen's Gaussian matrix and culminate in the canonical corrected
raw-moment endpoint. In particular, the sample-size argument is kept separate
from the row argument: (12.71) is a triangular array and cannot be represented
by prefixes of one fixed regressor sequence.
-/

/-- Hansen's local-to-zero first stage (12.71),
`X_{m,i} = m^{-1/2} C' Z_i + u_{2i}`. -/
noncomputable def weakIVLocalRegressorRow
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (m i : ℕ) (omega : Ω) : k → ℝ :=
  (Real.sqrt (m : ℝ))⁻¹ • (Cᵀ *ᵥ Z i omega) + fun j => u i omega (Sum.inr j)

/-- Structural error `e_i = u_{1i} - beta' u_{2i}` in Hansen's reduced form. -/
noncomputable def weakIVRawStructuralErrorRow
    (u : ℕ → Ω → Sum Unit k → ℝ) (beta : k → ℝ)
    (i : ℕ) (omega : Ω) : ℝ :=
  u i omega (Sum.inl ()) - (fun j => u i omega (Sum.inr j)) ⬝ᵥ beta

/-- The triangular-array outcome generated by the local first stage and the
structural equation `Y_{m,i} = X_{m,i}' beta + e_i`. -/
noncomputable def weakIVLocalOutcomeRow
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m i : ℕ) (omega : Ω) : ℝ :=
  weakIVLocalRegressorRow Z u C m i omega ⬝ᵥ beta +
    weakIVRawStructuralErrorRow u beta i omega

omit [DecidableEq k] [DecidableEq l] [MeasurableSpace Ω] in
/-- Equation (12.71) and the structural equation hold definitionally for the
raw triangular model. -/
theorem weakIVLocalOutcomeRow_linear_model
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m i : ℕ) (omega : Ω) :
    weakIVLocalOutcomeRow Z u C beta m i omega =
      weakIVLocalRegressorRow Z u C m i omega ⬝ᵥ beta +
        weakIVRawStructuralErrorRow u beta i omega :=
  rfl

/-! ### Triangular sample and estimator APIs

Unlike `stackRegressors`, these stacks accept a genuinely triangular array:
the sample-size index `m` is not identified with the row index `i`.
-/

/-- Stack sample `m` of a triangular regressor array. -/
def weakIVTriangularStackRegressors
    (X : ℕ → ℕ → Ω → k → ℝ) (m : ℕ) (omega : Ω) : Matrix (Fin m) k ℝ :=
  fun i j => X m i.val omega j

/-- Stack sample `m` of a triangular scalar array. -/
def weakIVTriangularStackOutcomes
    (Y : ℕ → ℕ → Ω → ℝ) (m : ℕ) (omega : Ω) : Fin m → ℝ :=
  fun i => Y m i.val omega

/-- The literal local-to-zero design matrix from (12.71). -/
noncomputable def weakIVLocalDesign
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (m : ℕ) (omega : Ω) : Matrix (Fin m) k ℝ :=
  weakIVTriangularStackRegressors (weakIVLocalRegressorRow Z u C) m omega

/-- The literal local-to-zero outcome vector generated by (12.71). -/
noncomputable def weakIVLocalOutcome
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω) : Fin m → ℝ :=
  weakIVTriangularStackOutcomes (weakIVLocalOutcomeRow Z u C beta) m omega

/-- The structural-error vector accompanying the local triangular sample. -/
noncomputable def weakIVLocalStructuralError
    (u : ℕ → Ω → Sum Unit k → ℝ) (beta : k → ℝ)
    (m : ℕ) (omega : Ω) : Fin m → ℝ :=
  fun i => weakIVRawStructuralErrorRow u beta i.val omega

omit [DecidableEq k] [DecidableEq l] [MeasurableSpace Ω] in
/-- The stacked triangular outcome satisfies the finite-sample linear model. -/
theorem weakIVLocalOutcome_eq_design_mulVec_add_error
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω) :
    weakIVLocalOutcome Z u C beta m omega =
      weakIVLocalDesign Z u C m omega *ᵥ beta +
        weakIVLocalStructuralError u beta m omega := by
  ext i
  rfl

/-- OLS computed from the literal local-to-zero triangular sample. -/
noncomputable def weakIVLocalOLSBetaStar
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω) : k → ℝ :=
  olsBetaStar (weakIVLocalDesign Z u C m omega)
    (weakIVLocalOutcome Z u C beta m omega)

/-- 2SLS computed from the literal local-to-zero triangular sample. -/
noncomputable def weakIVLocal2SLSBetaStar
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω) : k → ℝ :=
  twoSLSBetaStar (stackRegressors Z m omega)
    (weakIVLocalDesign Z u C m omega)
    (weakIVLocalOutcome Z u C beta m omega)

/-- LIML computed from the literal local-to-zero triangular sample.  The input
`limlMuHat` is the scaled generalized root `m * muHat`; the estimator receives
Hansen's finite-sample root after division by `m`. -/
noncomputable def weakIVLocalLIMLBetaStar
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (limlMuHat : ℕ → Ω → ℝ)
    (m : ℕ) (omega : Ω) : k → ℝ :=
  limlBetaStar (stackRegressors Z m omega)
    (weakIVLocalDesign Z u C m omega)
    (weakIVLocalOutcome Z u C beta m omega)
    (weakIVLIMLFiniteSampleMu limlMuHat m omega)

omit [DecidableEq l] [MeasurableSpace Ω] in
/-- Exact bridge from the triangular design/outcome to the existing OLS
estimator definition. -/
theorem weakIVLocalOLSBetaStar_eq_existing
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω) :
    weakIVLocalOLSBetaStar Z u C beta m omega =
      olsBetaStar
        (stackRegressors
          (fun i omega => weakIVLocalRegressorRow Z u C m i omega) m omega)
        (stackOutcomes
          (fun i omega => weakIVLocalOutcomeRow Z u C beta m i omega) m omega) :=
  rfl

omit [MeasurableSpace Ω] in
/-- Exact bridge from the triangular design/outcome to the existing 2SLS
estimator definition. -/
theorem weakIVLocal2SLSBetaStar_eq_existing
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω) :
    weakIVLocal2SLSBetaStar Z u C beta m omega =
      twoSLSBetaStar (stackRegressors Z m omega)
        (stackRegressors
          (fun i omega => weakIVLocalRegressorRow Z u C m i omega) m omega)
        (stackOutcomes
          (fun i omega => weakIVLocalOutcomeRow Z u C beta m i omega) m omega) :=
  rfl

omit [MeasurableSpace Ω] in
/-- Exact bridge from the triangular design/outcome to the existing LIML
estimator definition. -/
theorem weakIVLocalLIMLBetaStar_eq_existing
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (limlMuHat : ℕ → Ω → ℝ)
    (m : ℕ) (omega : Ω) :
    weakIVLocalLIMLBetaStar Z u C beta limlMuHat m omega =
      limlBetaStar (stackRegressors Z m omega)
        (stackRegressors
          (fun i omega => weakIVLocalRegressorRow Z u C m i omega) m omega)
        (stackOutcomes
          (fun i omega => weakIVLocalOutcomeRow Z u C beta m i omega) m omega)
        (weakIVLIMLFiniteSampleMu limlMuHat m omega) :=
  rfl

/-- The observed reduced-form matrix `[Y X]` for the literal triangular
local-to-zero sample. -/
noncomputable def weakIVLocalReducedFormSampleMatrix
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω) :
    Matrix (Fin m) (Sum Unit k) ℝ
  | i, Sum.inl _ => weakIVLocalOutcomeRow Z u C beta m i.val omega
  | i, Sum.inr j => weakIVLocalRegressorRow Z u C m i.val omega j

/-- The residual-covariance denominator in the literal triangular LIML
pencil. -/
noncomputable def weakIVLocalLIMLResidualCovariance
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω) :
    Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  let Zm := stackRegressors Z m omega
  let Rm := weakIVLocalReducedFormSampleMatrix Z u C beta m omega
  (m : ℝ)⁻¹ •
    (Rmᵀ * ((1 : Matrix (Fin m) (Fin m) ℝ) - instrumentProjectionStar Zm) * Rm)

/-- Exact finite-sample generalized-eigenvalue pair for the literal
local-to-zero sample. -/
noncomputable def weakIVLocalLIMLGeneralizedEigenvaluePair
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω) :
    Matrix (Sum Unit k) (Sum Unit k) ℝ ×
      Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  let Zm := stackRegressors Z m omega
  let Rm := weakIVLocalReducedFormSampleMatrix Z u C beta m omega
  (Rmᵀ * instrumentProjectionStar Zm * Rm,
    weakIVLocalLIMLResidualCovariance Z u C beta m omega)

omit [DecidableEq k] [DecidableEq l] [MeasurableSpace Ω] in
/-- The triangular reduced-form matrix is exactly `[local outcome, local
design]`, not a prefix of one fixed regressor sequence. -/
theorem weakIVLocalReducedFormSampleMatrix_apply
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω) :
    weakIVLocalReducedFormSampleMatrix Z u C beta m omega =
      weakIVReducedFormSampleMatrix
        (fun i omega => weakIVLocalOutcomeRow Z u C beta m i omega)
        (fun i omega => weakIVLocalRegressorRow Z u C m i omega) m omega :=
  rfl

omit [DecidableEq k] [MeasurableSpace Ω] in
/-- Exact bridge from the triangular sample to the existing finite-sample
residual-covariance API.  The right side deliberately fixes `m` inside both
row functions. -/
theorem weakIVLocalLIMLResidualCovariance_eq_existing
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω) :
    weakIVLocalLIMLResidualCovariance Z u C beta m omega =
      weakIVLIMLFiniteSampleResidualCovariance Z
        (fun i omega => weakIVLocalRegressorRow Z u C m i omega)
        (fun i omega => weakIVLocalOutcomeRow Z u C beta m i omega) m omega := by
  rfl

omit [DecidableEq k] [MeasurableSpace Ω] in
/-- Exact bridge from the triangular sample to the existing generalized-pair
API, with sample size kept distinct from row index. -/
theorem weakIVLocalLIMLGeneralizedEigenvaluePair_eq_existing
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω) :
    weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega =
      weakIVLIMLGeneralizedEigenvalueSamplePrimitive Z
        (fun i omega => weakIVLocalRegressorRow Z u C m i omega)
        (fun i omega => weakIVLocalOutcomeRow Z u C beta m i omega) m omega := by
  rfl

/-- One raw reduced-form score row, written as the vectorization of `Z_i u_i'`.
This is the iid summand in the CLT displayed immediately after (12.71). -/
noncomputable def weakIVRawReducedFormScoreRow
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (i : ℕ) (omega : Ω) : l × Sum Unit k → ℝ :=
  fun a => Z i omega a.1 * u i omega a.2

/-- Matrix form of `n^{-1/2} sum_i Z_i u_i'`. -/
noncomputable def weakIVRawRootReducedFormScore
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (m : ℕ) (omega : Ω) : Matrix l (Sum Unit k) ℝ :=
  fun a b => (Real.sqrt (m : ℝ))⁻¹ *
    ∑ i ∈ Finset.range m, weakIVRawReducedFormScoreRow Z u i omega (a, b)

/-- First-stage block `Xi_2` of Hansen's full Gaussian reduced-form matrix. -/
noncomputable def weakIVRawGaussianFirstStage
    (Xi : Matrix l (Sum Unit k) ℝ) : Matrix l k ℝ :=
  fun a j => Xi a (Sum.inr j)

/-- Structural-score block `xi_e = xi_1 - Xi_2 beta`. -/
noncomputable def weakIVRawGaussianStructuralScore
    (Xi : Matrix l (Sum Unit k) ℝ) (beta : k → ℝ) : l → ℝ :=
  fun a => Xi a (Sum.inl ()) - (weakIVRawGaussianFirstStage Xi *ᵥ beta) a

/-- Endogenous-error covariance block extracted from the full reduced-form
error covariance. -/
noncomputable def weakIVRawSigma22
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) : Matrix k k ℝ :=
  Sigma.submatrix Sum.inr Sum.inr

omit [Fintype k] [DecidableEq k] in
/-- Positive definiteness of the full reduced-form covariance passes to its
endogenous-error principal block. -/
private theorem weakIVRawSigma22_posDef
    [Finite k]
    {Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ}
    (hSigma : Sigma.PosDef) :
    (weakIVRawSigma22 Sigma).PosDef := by
  letI := Fintype.ofFinite k
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (hSigma.1.submatrix Sum.inr)
  intro x hx
  let y : Sum Unit k → ℝ := fun b => match b with
    | Sum.inl _ => 0
    | Sum.inr j => x j
  have hy : y ≠ 0 := by
    intro hy
    apply hx
    funext j
    have hj := congrFun hy (Sum.inr j)
    simpa [y] using hj
  have hpos := hSigma.dotProduct_mulVec_pos hy
  simpa [weakIVRawSigma22, y, Matrix.mulVec, dotProduct] using hpos

/-- Structural covariance `Sigma_2e = Sigma_21 - Sigma_22 beta` extracted
from the full reduced-form error covariance. -/
noncomputable def weakIVRawSigma2e
    (Sigma : Matrix (Sum Unit k) (Sum Unit k) ℝ) (beta : k → ℝ) : k → ℝ :=
  fun i => Sigma (Sum.inr i) (Sum.inl ()) -
    (weakIVRawSigma22 Sigma *ᵥ beta) i

/-- Structural bread/score blocks extracted from a quadratic form in the
reduced-form columns `[Y X]`. -/
private noncomputable def weakIVRawStructuralMomentPair
    (beta : k → ℝ) (A : Matrix (Sum Unit k) (Sum Unit k) ℝ) :
    Matrix k k ℝ × (k → ℝ) :=
  (weakIVRawSigma22 A, weakIVRawSigma2e A beta)

omit [DecidableEq k] in
private theorem weakIVRawStructuralMomentPair_continuous
    (beta : k → ℝ) : Continuous (weakIVRawStructuralMomentPair beta) := by
  unfold weakIVRawStructuralMomentPair weakIVRawSigma2e weakIVRawSigma22
  fun_prop

private noncomputable def weakIVStructuralReducedFormMatrix
    (X : Matrix n k ℝ) (e : n → ℝ) (beta : k → ℝ) :
    Matrix n (Sum Unit k) ℝ
  | i, Sum.inl _ => (X *ᵥ beta + e) i
  | i, Sum.inr j => X i j

omit [DecidableEq k] in
private theorem weakIVRawStructuralMomentPair_reducedForm
    {n : Type*} [Fintype n]
    (X : Matrix n k ℝ) (e : n → ℝ) (beta : k → ℝ)
    (W : Matrix n n ℝ) :
    weakIVRawStructuralMomentPair beta
        ((weakIVStructuralReducedFormMatrix X e beta)ᵀ * W *
          weakIVStructuralReducedFormMatrix X e beta) =
      (Xᵀ * W * X, (Xᵀ * W) *ᵥ e) := by
  classical
  apply Prod.ext
  · ext i j
    rfl
  · ext i
    change (((Xᵀ * W) *ᵥ (X *ᵥ beta + e)) i -
      ((Xᵀ * W * X) *ᵥ beta) i) = ((Xᵀ * W) *ᵥ e) i
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec]
    simp

omit [DecidableEq k] [DecidableEq l] [MeasurableSpace Ω] in
private theorem weakIVRawStructuralMomentPair_localReducedForm
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω)
    (W : Matrix (Fin m) (Fin m) ℝ) :
    weakIVRawStructuralMomentPair beta
        ((weakIVLocalReducedFormSampleMatrix Z u C beta m omega)ᵀ * W *
          weakIVLocalReducedFormSampleMatrix Z u C beta m omega) =
      ((weakIVLocalDesign Z u C m omega)ᵀ * W *
          weakIVLocalDesign Z u C m omega,
        ((weakIVLocalDesign Z u C m omega)ᵀ * W) *ᵥ
          weakIVLocalStructuralError u beta m omega) := by
  have hR : weakIVLocalReducedFormSampleMatrix Z u C beta m omega =
      weakIVStructuralReducedFormMatrix
        (weakIVLocalDesign Z u C m omega)
        (weakIVLocalStructuralError u beta m omega) beta := by
    ext i b
    cases b with
    | inl b => cases b; rfl
    | inr j => rfl
  rw [hR]
  exact weakIVRawStructuralMomentPair_reducedForm
    (weakIVLocalDesign Z u C m omega)
    (weakIVLocalStructuralError u beta m omega) beta W

/-- Continuous raw-moment assembly for every Gram/score block used by the OLS
and root-scaled 2SLS faces of Theorem 12.18. -/
noncomputable def weakIVRawRootOLSAssemblyMap
    (C : Matrix l k ℝ) (beta : k → ℝ)
    (p : Matrix l (Sum Unit k) ℝ ×
      (Matrix l l ℝ × Matrix (Sum Unit k) (Sum Unit k) ℝ)) :
    (Matrix l l ℝ × Matrix l k ℝ × (l → ℝ)) ×
      (Matrix k k ℝ × (k → ℝ)) :=
  ((p.2.1,
      p.2.1 * C + weakIVRawGaussianFirstStage p.1,
      weakIVRawGaussianStructuralScore p.1 beta),
    (weakIVRawSigma22 p.2.2, weakIVRawSigma2e p.2.2 beta))

omit [DecidableEq k] [DecidableEq l] in
private theorem weakIVRawRootOLSAssemblyMap_continuous
    (C : Matrix l k ℝ) (beta : k → ℝ) :
    Continuous (weakIVRawRootOLSAssemblyMap (k := k) (l := l) C beta) := by
  unfold weakIVRawRootOLSAssemblyMap
  unfold weakIVRawGaussianStructuralScore weakIVRawSigma2e
  unfold weakIVRawGaussianFirstStage weakIVRawSigma22
  fun_prop

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] [MeasurableSpace Ω] in
/-- The right block of the raw reduced-form score is exactly
`m^{-1/2} sum_i Z_i u_{2i}'`. -/
theorem weakIVRawRootReducedFormScore_firstStage_apply
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (m : ℕ) (omega : Ω) (a : l) (j : k) :
    weakIVRawGaussianFirstStage
        (weakIVRawRootReducedFormScore Z u m omega) a j =
      (Real.sqrt (m : ℝ))⁻¹ *
        ∑ i ∈ Finset.range m, Z i omega a * u i omega (Sum.inr j) :=
  rfl

omit [Fintype l] [DecidableEq k] [DecidableEq l] [MeasurableSpace Ω] in
/-- Projecting the full raw score by `(1, -beta)` is exactly Hansen's
root-scaled instrument/structural-error score `m^{-1/2} sum_i Z_i e_i`. -/
theorem weakIVRawRootReducedFormScore_structural_apply
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (beta : k → ℝ) (m : ℕ) (omega : Ω) (a : l) :
    weakIVRawGaussianStructuralScore
        (weakIVRawRootReducedFormScore Z u m omega) beta a =
      (Real.sqrt (m : ℝ))⁻¹ *
        ∑ i ∈ Finset.range m,
          Z i omega a * weakIVRawStructuralErrorRow u beta i omega := by
  classical
  simp only [weakIVRawGaussianStructuralScore, weakIVRawGaussianFirstStage,
    weakIVRawRootReducedFormScore, weakIVRawReducedFormScoreRow,
    weakIVRawStructuralErrorRow, Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.mul_sum]
  · simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l] in
private lemma weakIVRawReducedFormScoreMap_measurable :
    Measurable
      (fun p : (l → ℝ) × (Sum Unit k → ℝ) =>
        (fun a : l × Sum Unit k => p.1 a.1 * p.2 a.2)) := by
  rw [measurable_pi_iff]
  intro a
  exact ((measurable_pi_apply a.1).comp measurable_fst).mul
    ((measurable_pi_apply a.2).comp measurable_snd)

/-- Raw iid and finite-moment assumptions sufficient for the joint CLT/WLLNs
used in Hansen's derivation of Theorem 12.18.

`score_memLp_two` is the finite second moment of `vec (Z_i u_i')`, and
`score_mean_zero` is the reduced-form orthogonality condition.  These are the
moment assumptions hidden by the excerpt's phrase "by the central limit
theorem"; no convergence conclusion is stored in this package. -/
structure WeakIVRawJointMomentConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ) : Prop where
  row_aestronglyMeasurable : ∀ i,
    AEStronglyMeasurable (fun omega => (Z i omega, u i omega)) μ
  row_iIndep : iIndepFun (fun i omega => (Z i omega, u i omega)) μ
  row_identDistrib : ∀ i,
    IdentDistrib (fun omega => (Z i omega, u i omega))
      (fun omega => (Z 0 omega, u 0 omega)) μ μ
  instrument_norm_sq_integrable : Integrable (fun omega => ‖Z 0 omega‖ ^ 2) μ
  error_norm_sq_integrable : Integrable (fun omega => ‖u 0 omega‖ ^ 2) μ
  score_memLp_two : MemLp (weakIVRawReducedFormScoreRow Z u 0) 2 μ
  score_mean_zero : meanVec μ (weakIVRawReducedFormScoreRow Z u 0) = 0

namespace WeakIVRawJointMomentConditions

omit [DecidableEq k] [DecidableEq l] in
private theorem instrument_measurable
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    (h : WeakIVRawJointMomentConditions μ Z u) (i : ℕ) :
    AEStronglyMeasurable (Z i) μ :=
  continuous_fst.comp_aestronglyMeasurable (h.row_aestronglyMeasurable i)

omit [DecidableEq k] [DecidableEq l] in
private theorem error_measurable
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    (h : WeakIVRawJointMomentConditions μ Z u) (i : ℕ) :
    AEStronglyMeasurable (u i) μ :=
  continuous_snd.comp_aestronglyMeasurable (h.row_aestronglyMeasurable i)

omit [DecidableEq k] [DecidableEq l] in
private theorem score_iIndep
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    (h : WeakIVRawJointMomentConditions μ Z u) :
    iIndepFun (weakIVRawReducedFormScoreRow Z u) μ := by
  simpa [weakIVRawReducedFormScoreRow, Function.comp_def] using
    h.row_iIndep.comp
      (fun _ p => fun a : l × Sum Unit k => p.1 a.1 * p.2 a.2)
      (fun _ => weakIVRawReducedFormScoreMap_measurable (k := k) (l := l))

omit [DecidableEq k] [DecidableEq l] in
private theorem score_identDistrib
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    (h : WeakIVRawJointMomentConditions μ Z u) (i : ℕ) :
    IdentDistrib (weakIVRawReducedFormScoreRow Z u i)
      (weakIVRawReducedFormScoreRow Z u 0) μ μ := by
  simpa [weakIVRawReducedFormScoreRow, Function.comp_def] using
    (h.row_identDistrib i).comp
      (weakIVRawReducedFormScoreMap_measurable (k := k) (l := l))

omit [DecidableEq k] [DecidableEq l] in
private theorem instrument_gram_conditions
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    (h : WeakIVRawJointMomentConditions μ Z u) :
    SampleGramWLLNConditions μ Z := by
  apply SampleGramWLLNConditions.of_iid_finite_second
  · exact h.instrument_measurable
  · simpa [Function.comp_def] using
      h.row_iIndep.comp (fun _ p => p.1) (fun _ => measurable_fst)
  · intro i
    simpa [Function.comp_def] using (h.row_identDistrib i).comp measurable_fst
  · exact h.instrument_norm_sq_integrable

omit [DecidableEq k] [DecidableEq l] in
private theorem error_gram_conditions
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    (h : WeakIVRawJointMomentConditions μ Z u) :
    SampleGramWLLNConditions μ u := by
  apply SampleGramWLLNConditions.of_iid_finite_second
  · exact h.error_measurable
  · simpa [Function.comp_def] using
      h.row_iIndep.comp (fun _ p => p.2) (fun _ => measurable_snd)
  · intro i
    simpa [Function.comp_def] using (h.row_identDistrib i).comp measurable_snd
  · exact h.error_norm_sq_integrable

end WeakIVRawJointMomentConditions

/-- The raw iid model proves Hansen's full reduced-form matrix CLT.  The limit
law is exactly the multivariate Gaussian with covariance
`Cov (vec (Z_i u_i'))`; it is not an assumption of this theorem. -/
theorem weakIV_rawReducedFormScore_tendstoInDistribution_gaussian
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    (h : WeakIVRawJointMomentConditions μ Z u) :
    TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) => weakIVRawRootReducedFormScore Z u m omega)
      atTop
      (fun z : EuclideanSpace ℝ (l × Sum Unit k) =>
        (fun a b => z.ofLp (a, b) : Matrix l (Sum Unit k) ℝ))
      (fun _ => μ)
      (multivariateGaussian 0 (covMat μ (weakIVRawReducedFormScoreRow Z u 0))) := by
  have hclt := iidVectorCLT_tendstoInDistribution_multivariateGaussian
    (μ := μ) (Y := weakIVRawReducedFormScoreRow Z u)
    h.score_memLp_two h.score_iIndep h.score_identDistrib
  let curryScore : (l × Sum Unit k → ℝ) → Matrix l (Sum Unit k) ℝ :=
    fun x a b => x (a, b)
  have hcurry : Continuous curryScore := by
    apply continuous_pi
    intro a
    apply continuous_pi
    intro b
    exact continuous_apply (a, b)
  have hmap := hclt.continuous_comp
    (hcurry.comp (PiLp.continuous_ofLp 2 (fun _ : l × Sum Unit k => ℝ)))
  refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hmap
  intro m
  exact ae_of_all μ (fun omega => by
    ext a b
    simp [curryScore, weakIVRawRootReducedFormScore, h.score_mean_zero])

/-- Raw joint CLT/WLLN needed by the weak-IV continuous-mapping argument.
Besides the Gaussian reduced-form score, this proves convergence of the
instrument Gram and reduced-form-error covariance from the same iid rows. -/
theorem weakIV_rawJointMoments_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    (h : WeakIVRawJointMomentConditions μ Z u) :
    TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) =>
        (weakIVRawRootReducedFormScore Z u m omega,
          (sampleGram (stackRegressors Z m omega),
            sampleGram (stackRegressors u m omega))))
      atTop
      (fun z : EuclideanSpace ℝ (l × Sum Unit k) =>
        ((fun a b => z.ofLp (a, b) : Matrix l (Sum Unit k) ℝ),
          (popGram μ Z, popGram μ u)))
      (fun _ => μ)
      (multivariateGaussian 0 (covMat μ (weakIVRawReducedFormScoreRow Z u 0))) := by
  have hZ := sampleGram_stackRegressors_tendstoInMeasure_popGram_of_wlln
    h.instrument_gram_conditions
  have hu := sampleGram_stackRegressors_tendstoInMeasure_popGram_of_wlln
    h.error_gram_conditions
  have hgram := tendstoInMeasure_prodMk hZ hu
  have hgram_meas : ∀ m, AEMeasurable
      (fun omega =>
        (sampleGram (stackRegressors Z m omega),
          sampleGram (stackRegressors u m omega))) μ := by
    intro m
    exact
      ((sampleGram_stackRegressors_aestronglyMeasurable_of_wlln
          h.instrument_gram_conditions m).prodMk
        (sampleGram_stackRegressors_aestronglyMeasurable_of_wlln
          h.error_gram_conditions m)).aemeasurable
  exact
    (weakIV_rawReducedFormScore_tendstoInDistribution_gaussian h).prodMk_of_tendstoInMeasure_const
      (fun m omega => weakIVRawRootReducedFormScore Z u m omega)
      (fun m omega =>
        (sampleGram (stackRegressors Z m omega),
          sampleGram (stackRegressors u m omega)))
      (fun z : EuclideanSpace ℝ (l × Sum Unit k) =>
        (fun a b => z.ofLp (a, b) : Matrix l (Sum Unit k) ℝ))
      hgram hgram_meas

/-- The raw iid package derives jointly every Gram/score limit consumed by the
OLS and root-scaled 2SLS assembly.  In particular `Sigma22` and `Sigma2e` are
projections of `popGram mu u`; they are not independent assumptions. -/
theorem weakIV_rawRootOLSAssembly_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    (C : Matrix l k ℝ) (beta : k → ℝ)
    (h : WeakIVRawJointMomentConditions μ Z u) :
    TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) =>
        weakIVRawRootOLSAssemblyMap C beta
          (weakIVRawRootReducedFormScore Z u m omega,
            (sampleGram (stackRegressors Z m omega),
              sampleGram (stackRegressors u m omega))))
      atTop
      (fun z : EuclideanSpace ℝ (l × Sum Unit k) =>
        let Xi := (fun a b => z.ofLp (a, b) : Matrix l (Sum Unit k) ℝ)
        weakIVRawRootOLSAssemblyMap C beta
          (Xi, (popGram μ Z, popGram μ u)))
      (fun _ => μ)
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0))) := by
  simpa [Function.comp_def] using
    (weakIV_rawJointMoments_tendstoInDistribution h).continuous_comp
      (weakIVRawRootOLSAssemblyMap_continuous C beta)

omit [DecidableEq k] in
/-- Nonsingularity of the population instrument Gram and the raw WLLN imply
that finite-sample instrument-rank failures have probability tending to zero.
Thus instrument rank is derived, not retained in the triangular assembly
package as a separate sample-level assumption. -/
theorem weakIV_rawInstrumentGram_singular_tendsto_zero
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    (h : WeakIVRawJointMomentConditions μ Z u)
    (hQZZ : IsUnit (popGram μ Z).det) :
    Tendsto
      (fun m => μ {omega | ¬ IsUnit
        (sampleGram (stackRegressors Z m omega)).det})
      atTop (𝓝 0) := by
  classical
  have hpair : TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) =>
        (sampleGram (stackRegressors Z m omega), (0 : l → ℝ)))
      atTop
      (fun _ : EuclideanSpace ℝ (l × Sum Unit k) =>
        (popGram μ Z, (0 : l → ℝ)))
      (fun _ => μ)
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0))) := by
    have hcont : Continuous
        (fun p : Matrix l (Sum Unit k) ℝ ×
            (Matrix l l ℝ × Matrix (Sum Unit k) (Sum Unit k) ℝ) =>
          (p.2.1, (0 : l → ℝ))) := by
      fun_prop
    simpa [Function.comp_def] using
      (weakIV_rawJointMoments_tendstoInDistribution h).continuous_comp hcont
  have hlimit :
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0)))
        {z : EuclideanSpace ℝ (l × Sum Unit k) |
          ¬ IsUnit (popGram μ Z).det} = 0 := by
    have hempty :
        {z : EuclideanSpace ℝ (l × Sum Unit k) |
          ¬ IsUnit (popGram μ Z).det} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hnot => hnot hQZZ
    rw [hempty, measure_empty]
  exact weakIV_pair_bread_singular_tendsto_zero_of_joint_tendsto
    (μ := μ)
    (ν := multivariateGaussian 0
      (covMat μ (weakIVRawReducedFormScoreRow Z u 0)))
    (B := fun m omega => sampleGram (stackRegressors Z m omega))
    (S := fun _ _ => (0 : l → ℝ))
    (B0 := fun _ => popGram μ Z)
    (S0 := fun _ => (0 : l → ℝ))
    hpair hlimit

/-- Continuous block projection of the proved raw Gaussian CLT gives the joint
`(Xi_2, xi_e)` object used in all three faces of Theorem 12.18. -/
theorem weakIV_rawGaussianBlocks_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    (beta : k → ℝ) (h : WeakIVRawJointMomentConditions μ Z u) :
    TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) =>
        (weakIVRawGaussianFirstStage (weakIVRawRootReducedFormScore Z u m omega),
          weakIVRawGaussianStructuralScore
            (weakIVRawRootReducedFormScore Z u m omega) beta))
      atTop
      (fun z : EuclideanSpace ℝ (l × Sum Unit k) =>
        let Xi := (fun a b => z.ofLp (a, b) : Matrix l (Sum Unit k) ℝ)
        (weakIVRawGaussianFirstStage Xi, weakIVRawGaussianStructuralScore Xi beta))
      (fun _ => μ)
      (multivariateGaussian 0 (covMat μ (weakIVRawReducedFormScoreRow Z u 0))) := by
  have hcont : Continuous
      (fun Xi : Matrix l (Sum Unit k) ℝ =>
        (weakIVRawGaussianFirstStage Xi,
          weakIVRawGaussianStructuralScore Xi beta)) := by
    unfold weakIVRawGaussianStructuralScore weakIVRawGaussianFirstStage
    fun_prop
  simpa [Function.comp_def] using
    (weakIV_rawReducedFormScore_tendstoInDistribution_gaussian h).continuous_comp hcont

/-! ### Smallest generalized-Rayleigh selector -/

section GeneralizedRootSelector

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private noncomputable def weakIVLIMLQuadraticForm
    (B : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ (B *ᵥ x)

private noncomputable def weakIVLIMLSphereMinimum
    (B : Matrix ι ι ℝ) : ℝ :=
  sInf (weakIVLIMLQuadraticForm B '' Metric.sphere (0 : ι → ℝ) 1)

omit [DecidableEq ι] [Nonempty ι] in
private theorem weakIVLIMLQuadraticForm_continuous :
    Continuous (Function.uncurry (weakIVLIMLQuadraticForm (ι := ι))) := by
  unfold weakIVLIMLQuadraticForm Function.uncurry
  fun_prop

omit [DecidableEq ι] [Nonempty ι] in
private theorem weakIVLIMLSphereMinimum_continuous :
    Continuous (weakIVLIMLSphereMinimum (ι := ι)) := by
  letI := FiniteDimensional.proper_real (ι → ℝ)
  exact isCompact_sphere (0 : ι → ℝ) 1 |>.continuous_sInf
    weakIVLIMLQuadraticForm_continuous

omit [DecidableEq ι] [Nonempty ι] in
private theorem weakIVLIMLSphereMinimum_le
    (B : Matrix ι ι ℝ) {x : ι → ℝ}
    (hx : x ∈ Metric.sphere (0 : ι → ℝ) 1) :
    weakIVLIMLSphereMinimum B ≤ weakIVLIMLQuadraticForm B x := by
  letI := FiniteDimensional.proper_real (ι → ℝ)
  apply csInf_le
  · exact (isCompact_sphere (0 : ι → ℝ) 1).image_of_continuousOn
      ((weakIVLIMLQuadraticForm_continuous (ι := ι)).comp
        (continuous_const.prodMk continuous_id)).continuousOn |>.bddBelow
  · exact ⟨x, hx, rfl⟩

/-- Pencils whose denominator quadratic form is strictly positive in every
nonzero direction. This is open in the full matrix-pair space; no ambient
symmetry restriction is needed because a real quadratic form depends only on
the symmetric part of its matrix. -/
def weakIVLIMLPositiveDenominatorSet : Set
    (Matrix ι ι ℝ × Matrix ι ι ℝ) :=
  {p | 0 < weakIVLIMLSphereMinimum p.2}

/-- The only discontinuity set needed by the smallest generalized-root
selector: pencils whose denominator is not strictly positive. -/
def weakIVLIMLSelectorBadSet : Set
    (Matrix ι ι ℝ × Matrix ι ι ℝ) :=
  (weakIVLIMLPositiveDenominatorSet (ι := ι))ᶜ

omit [DecidableEq ι] [Nonempty ι] in
private theorem weakIVLIMLPositiveDenominatorSet_isOpen :
    IsOpen (weakIVLIMLPositiveDenominatorSet (ι := ι)) := by
  exact isOpen_Ioi.preimage
    ((weakIVLIMLSphereMinimum_continuous (ι := ι)).comp continuous_snd)

omit [DecidableEq ι] [Nonempty ι] in
theorem weakIVLIMLSelectorBadSet_measurable :
    MeasurableSet (weakIVLIMLSelectorBadSet (ι := ι)) :=
  weakIVLIMLPositiveDenominatorSet_isOpen.measurableSet.compl

omit [DecidableEq ι] [Nonempty ι] in
private theorem weakIVLIMLQuadraticForm_pos
    {p : Matrix ι ι ℝ × Matrix ι ι ℝ}
    (hp : p ∈ weakIVLIMLPositiveDenominatorSet) {x : ι → ℝ}
    (hx : x ∈ Metric.sphere (0 : ι → ℝ) 1) :
    0 < weakIVLIMLQuadraticForm p.2 x :=
  hp.trans_le (weakIVLIMLSphereMinimum_le p.2 hx)

omit [DecidableEq ι] [Nonempty ι] in
private theorem weakIVLIMLGeneralizedRayleighQuotient_smul
    (p : Matrix ι ι ℝ × Matrix ι ι ℝ) (x : ι → ℝ)
    {c : ℝ} (hc : c ≠ 0) :
    limlRayleighQuotient p.1 p.2 (c • x) =
      limlRayleighQuotient p.1 p.2 x := by
  have hquad (B : Matrix ι ι ℝ) :
      weakIVLIMLQuadraticForm B (c • x) =
        (c * c) * weakIVLIMLQuadraticForm B x := by
    unfold weakIVLIMLQuadraticForm
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
    simp only [Algebra.smul_def, Algebra.algebraMap_self_apply]
    ring
  unfold limlRayleighQuotient
  change weakIVLIMLQuadraticForm p.1 (c • x) /
      weakIVLIMLQuadraticForm p.2 (c • x) = _
  rw [hquad, hquad, mul_div_mul_left _ _ (mul_ne_zero hc hc)]
  simp [weakIVLIMLQuadraticForm]

private noncomputable def weakIVLIMLSmallestRootOnPositiveDenominator
    (p : weakIVLIMLPositiveDenominatorSet (ι := ι)) : ℝ :=
  sInf (Set.range fun x : Metric.sphere (0 : ι → ℝ) 1 =>
    limlRayleighQuotient p.1.1 p.1.2 x.1)

omit [DecidableEq ι] [Nonempty ι] in
private theorem weakIVLIMLSmallestRootOnPositiveDenominator_continuous :
    Continuous (weakIVLIMLSmallestRootOnPositiveDenominator (ι := ι)) := by
  let sphere := Metric.sphere (0 : ι → ℝ) 1
  letI := FiniteDimensional.proper_real (ι → ℝ)
  letI : CompactSpace sphere := isCompact_iff_compactSpace.mp
    (isCompact_sphere (0 : ι → ℝ) 1)
  have hf : Continuous (Function.uncurry
      (fun (p : weakIVLIMLPositiveDenominatorSet (ι := ι)) (x : sphere) =>
        limlRayleighQuotient p.1.1 p.1.2 x.1)) := by
    rw [continuous_iff_continuousAt]
    intro q
    apply ContinuousAt.div
    · exact (weakIVLIMLQuadraticForm_continuous (ι := ι)).continuousAt.comp
        (((continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk
          (continuous_subtype_val.comp continuous_snd)).continuousAt)
    · exact (weakIVLIMLQuadraticForm_continuous (ι := ι)).continuousAt.comp
        (((continuous_snd.comp (continuous_subtype_val.comp continuous_fst)).prodMk
          (continuous_subtype_val.comp continuous_snd)).continuousAt)
    · exact ne_of_gt (weakIVLIMLQuadraticForm_pos q.1.2 q.2.2)
  have h := (isCompact_univ : IsCompact (Set.univ : Set sphere)).continuous_sInf
    (show Continuous ↿(fun
        (p : weakIVLIMLPositiveDenominatorSet (ι := ι)) (x : sphere) =>
      limlRayleighQuotient p.1.1 p.1.2 x.1) from hf)
  convert h using 1
  funext p
  simp only [weakIVLIMLSmallestRootOnPositiveDenominator,
    Set.image_univ, sphere]

/-- A concrete total smallest generalized-Rayleigh root. On a pencil with a
strictly positive denominator it is the attained minimum on the unit sphere;
on the complementary singular/indefinite set it is totalized to zero. -/
noncomputable def weakIVLIMLSmallestGeneralizedRoot
    (p : Matrix ι ι ℝ × Matrix ι ι ℝ) : ℝ := by
  classical
  exact if hp : p ∈ weakIVLIMLPositiveDenominatorSet then
    weakIVLIMLSmallestRootOnPositiveDenominator ⟨p, hp⟩ else 0

omit [DecidableEq ι] [Nonempty ι] in
/-- A unit null direction puts a pencil on the concrete selector's bad set. -/
theorem weakIVLIMLSelectorBadSet_of_unit_kernel
    (p : Matrix ι ι ℝ × Matrix ι ι ℝ) (x : ι → ℝ)
    (hxnorm : ‖x‖ = 1) (hker : p.2 *ᵥ x = 0) :
    p ∈ weakIVLIMLSelectorBadSet := by
  rw [weakIVLIMLSelectorBadSet]
  intro hp
  change 0 < sInf
    ((fun y : ι → ℝ => y ⬝ᵥ (p.2 *ᵥ y)) ''
      Metric.sphere (0 : ι → ℝ) 1) at hp
  letI := FiniteDimensional.proper_real (ι → ℝ)
  have hxsphere : x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hxnorm
  have hcompact : IsCompact
      ((fun y : ι → ℝ => y ⬝ᵥ (p.2 *ᵥ y)) ''
        Metric.sphere (0 : ι → ℝ) 1) := by
    exact (isCompact_sphere (0 : ι → ℝ) 1).image_of_continuousOn (by fun_prop)
  have hzero : (0 : ℝ) ∈
      (fun y : ι → ℝ => y ⬝ᵥ (p.2 *ᵥ y)) ''
        Metric.sphere (0 : ι → ℝ) 1 := by
    refine ⟨x, hxsphere, ?_⟩
    simp [hker]
  have hle : sInf
      ((fun y : ι → ℝ => y ⬝ᵥ (p.2 *ᵥ y)) ''
        Metric.sphere (0 : ι → ℝ) 1) ≤ 0 :=
    csInf_le hcompact.bddBelow hzero
  exact (not_lt_of_ge hle) hp

omit [DecidableEq ι] [Nonempty ι] in
/-- The concrete generalized-root selector returns zero on a pencil with a
unit denominator-kernel direction. -/
theorem weakIVLIMLSmallestGeneralizedRoot_eq_zero_of_unit_kernel
    (p : Matrix ι ι ℝ × Matrix ι ι ℝ) (x : ι → ℝ)
    (hxnorm : ‖x‖ = 1) (hker : p.2 *ᵥ x = 0) :
    weakIVLIMLSmallestGeneralizedRoot p = 0 := by
  have hbad := weakIVLIMLSelectorBadSet_of_unit_kernel p x hxnorm hker
  have hnot : p ∉ weakIVLIMLPositiveDenominatorSet := by
    simpa [weakIVLIMLSelectorBadSet] using hbad
  simp [weakIVLIMLSmallestGeneralizedRoot, hnot]

omit [DecidableEq ι] [Nonempty ι] in
/-- Any nonzero denominator-kernel direction forces the concrete selector's
zero branch. -/
theorem weakIVLIMLSmallestGeneralizedRoot_eq_zero_of_nonzero_kernel
    (p : Matrix ι ι ℝ × Matrix ι ι ℝ) (x : ι → ℝ)
    (hx : x ≠ 0) (hker : p.2 *ᵥ x = 0) :
    weakIVLIMLSmallestGeneralizedRoot p = 0 := by
  let y : ι → ℝ := ‖x‖⁻¹ • x
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hynorm : ‖y‖ = 1 := by
    simp [y, norm_smul, hxnorm]
  have hyker : p.2 *ᵥ y = 0 := by
    simp [y, Matrix.mulVec_smul, hker]
  exact weakIVLIMLSmallestGeneralizedRoot_eq_zero_of_unit_kernel
    p y hynorm hyker

private def weakIVSingularCounterexampleDenominator :
    Matrix (Sum Unit Unit) (Sum Unit Unit) ℝ
  | Sum.inl _, Sum.inl _ => 1
  | _, _ => 0

private def weakIVSingularCounterexampleFirstDirection : Sum Unit Unit → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => 0

private def weakIVSingularCounterexampleKernelDirection : Sum Unit Unit → ℝ
  | Sum.inl _ => 0
  | Sum.inr _ => 1

private theorem weakIV_singularCounterexample_rayleighMinimizer :
    LIMLRayleighMinimizer
      (1 : Matrix (Sum Unit Unit) (Sum Unit Unit) ℝ)
      weakIVSingularCounterexampleDenominator 1 := by
  constructor
  · refine ⟨weakIVSingularCounterexampleFirstDirection, ?_, ?_⟩
    · norm_num [limlRayleighAdmissible, weakIVSingularCounterexampleDenominator,
        weakIVSingularCounterexampleFirstDirection, Matrix.mulVec, dotProduct]
    · norm_num [limlRayleighQuotient, weakIVSingularCounterexampleDenominator,
        weakIVSingularCounterexampleFirstDirection, Matrix.mulVec, dotProduct]
  · intro x hx
    have hpos : 0 < x (Sum.inl ()) * x (Sum.inl ()) := by
      simpa [limlRayleighAdmissible, weakIVSingularCounterexampleDenominator,
        Matrix.mulVec, dotProduct] using hx
    have hbound :
        1 ≤ (x (Sum.inl ()) * x (Sum.inl ()) +
          x (Sum.inr ()) * x (Sum.inr ())) /
            (x (Sum.inl ()) * x (Sum.inl ())) := by
      apply (le_div_iff₀ hpos).2
      nlinarith [sq_nonneg (x (Sum.inr ()))]
    simpa [limlRayleighQuotient, weakIVSingularCounterexampleDenominator,
      Matrix.mulVec, dotProduct] using hbound

private theorem weakIV_singularCounterexample_concreteRoot_eq_zero :
    weakIVLIMLSmallestGeneralizedRoot
      ((1 : Matrix (Sum Unit Unit) (Sum Unit Unit) ℝ),
        weakIVSingularCounterexampleDenominator) = 0 := by
  apply weakIVLIMLSmallestGeneralizedRoot_eq_zero_of_nonzero_kernel _
    weakIVSingularCounterexampleKernelDirection
  · intro h
    have hh := congrFun h (Sum.inr ())
    simp [weakIVSingularCounterexampleKernelDirection] at hh
  · ext i
    cases i <;>
      simp [weakIVSingularCounterexampleDenominator,
        weakIVSingularCounterexampleKernelDirection, Matrix.mulVec, dotProduct]

/-- A singular positive-semidefinite denominator can have a genuine finite
Rayleigh minimum even though the repository's positive-definite-only concrete
selector returns zero. -/
theorem weakIVLIMLSmallestGeneralizedRoot_singular_counterexample :
    ∃ A B : Matrix (Sum Unit Unit) (Sum Unit Unit) ℝ,
      B.PosSemidef ∧ ¬ IsUnit B.det ∧
        LIMLRayleighMinimizer A B 1 ∧
        weakIVLIMLSmallestGeneralizedRoot (A, B) = 0 :=
  ⟨1, weakIVSingularCounterexampleDenominator, by
    let d : Sum Unit Unit → ℝ
      | Sum.inl _ => 1
      | Sum.inr _ => 0
    have hdiag : weakIVSingularCounterexampleDenominator = Matrix.diagonal d := by
      ext i j
      cases i <;> cases j <;>
        simp [weakIVSingularCounterexampleDenominator, d, Matrix.diagonal]
    rw [hdiag]
    exact Matrix.PosSemidef.diagonal (by
      intro i
      cases i <;> norm_num), by
    let d : Sum Unit Unit → ℝ
      | Sum.inl _ => 1
      | Sum.inr _ => 0
    have hdiag : weakIVSingularCounterexampleDenominator = Matrix.diagonal d := by
      ext i j
      cases i <;> cases j <;>
        simp [weakIVSingularCounterexampleDenominator, d, Matrix.diagonal]
    simp [hdiag, Matrix.det_diagonal, d],
    weakIV_singularCounterexample_rayleighMinimizer,
    weakIV_singularCounterexample_concreteRoot_eq_zero⟩

omit [DecidableEq ι] [Nonempty ι] in
private theorem weakIVLIMLSmallestGeneralizedRoot_continuousOn :
    ContinuousOn (weakIVLIMLSmallestGeneralizedRoot (ι := ι))
      weakIVLIMLPositiveDenominatorSet := by
  rw [continuousOn_iff_continuous_restrict]
  have h := weakIVLIMLSmallestRootOnPositiveDenominator_continuous (ι := ι)
  convert h using 1
  funext p
  simp [Set.restrict, weakIVLIMLSmallestGeneralizedRoot, p.2]

omit [DecidableEq ι] [Nonempty ι] in
theorem weakIVLIMLSmallestGeneralizedRoot_continuousAt
    {p : Matrix ι ι ℝ × Matrix ι ι ℝ}
    (hp : p ∉ weakIVLIMLSelectorBadSet) :
    ContinuousAt (weakIVLIMLSmallestGeneralizedRoot (ι := ι)) p := by
  have hgood : p ∈ weakIVLIMLPositiveDenominatorSet := by
    simpa [weakIVLIMLSelectorBadSet] using hp
  exact (weakIVLIMLSmallestGeneralizedRoot_continuousOn p hgood).continuousAt
    (weakIVLIMLPositiveDenominatorSet_isOpen.mem_nhds hgood)

omit [DecidableEq ι] [Nonempty ι] in
theorem weakIVLIMLSmallestGeneralizedRoot_measurable :
    Measurable (weakIVLIMLSmallestGeneralizedRoot (ι := ι)) := by
  classical
  have hzero : ContinuousOn
      (fun _ : Matrix ι ι ℝ × Matrix ι ι ℝ => (0 : ℝ))
      (weakIVLIMLPositiveDenominatorSet (ι := ι))ᶜ :=
    continuous_const.continuousOn
  have h := (weakIVLIMLSmallestGeneralizedRoot_continuousOn
    (ι := ι)).measurable_piecewise hzero
      weakIVLIMLPositiveDenominatorSet_isOpen.measurableSet
  convert h using 1
  funext p
  by_cases hp : p ∈ weakIVLIMLPositiveDenominatorSet
  · simp [Set.piecewise, weakIVLIMLSmallestGeneralizedRoot, hp]
  · simp [Set.piecewise, weakIVLIMLSmallestGeneralizedRoot, hp]

omit [DecidableEq ι] in
theorem weakIVLIMLPositiveDenominatorSet_of_posDef
    {p : Matrix ι ι ℝ × Matrix ι ι ℝ} (hp : p.2.PosDef) :
    p ∈ weakIVLIMLPositiveDenominatorSet := by
  letI := FiniteDimensional.proper_real (ι → ℝ)
  have hcont : ContinuousOn (weakIVLIMLQuadraticForm p.2)
      (Metric.sphere (0 : ι → ℝ) 1) :=
    ((weakIVLIMLQuadraticForm_continuous (ι := ι)).comp
      ((continuous_const : Continuous (fun _ : ι → ℝ => p.2)).prodMk
        continuous_id)).continuousOn
  obtain ⟨x, hx, hmin, _⟩ :=
    (isCompact_sphere (0 : ι → ℝ) 1).exists_sInf_image_eq_and_le
      (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont
  change 0 < sInf
    (weakIVLIMLQuadraticForm p.2 '' Metric.sphere (0 : ι → ℝ) 1)
  rw [hmin]
  simpa [weakIVLIMLQuadraticForm] using hp.dotProduct_mulVec_pos
    (ne_zero_of_mem_sphere one_ne_zero ⟨x, hx⟩)

omit [DecidableEq ι] [Nonempty ι] in
private theorem weakIVLIMLSmallestGeneralizedRoot_eq_sInf
    {p : Matrix ι ι ℝ × Matrix ι ι ℝ}
    (hp : p ∈ weakIVLIMLPositiveDenominatorSet) :
    weakIVLIMLSmallestGeneralizedRoot p =
      sInf (limlRayleighQuotient p.1 p.2 ''
        Metric.sphere (0 : ι → ℝ) 1) := by
  rw [weakIVLIMLSmallestGeneralizedRoot]
  simp only [dif_pos hp, weakIVLIMLSmallestRootOnPositiveDenominator]
  congr 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

omit [DecidableEq ι] in
/-- On every pencil with a strictly positive denominator, the concrete
selector is exactly Hansen's `mu*`: it attains the generalized Rayleigh
quotient and is a lower bound over every admissible vector. -/
theorem weakIVLIMLSmallestGeneralizedRoot_rayleighMinimizer
    {p : Matrix ι ι ℝ × Matrix ι ι ℝ}
    (hp : p ∈ weakIVLIMLPositiveDenominatorSet) :
    LIMLRayleighMinimizer p.1 p.2
      (weakIVLIMLSmallestGeneralizedRoot p) := by
  letI := FiniteDimensional.proper_real (ι → ℝ)
  let sphere := Metric.sphere (0 : ι → ℝ) 1
  have hquotient : ContinuousOn (limlRayleighQuotient p.1 p.2) sphere := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div
    · exact ((weakIVLIMLQuadraticForm_continuous (ι := ι)).comp
        (continuous_const.prodMk continuous_id)).continuousAt
    · exact ((weakIVLIMLQuadraticForm_continuous (ι := ι)).comp
        (continuous_const.prodMk continuous_id)).continuousAt
    · exact ne_of_gt (weakIVLIMLQuadraticForm_pos hp
        (by simpa [sphere] using hx))
  obtain ⟨x, hx, hvalue, hlower⟩ :=
    (isCompact_sphere (0 : ι → ℝ) 1).exists_sInf_image_eq_and_le
      (NormedSpace.sphere_nonempty.mpr zero_le_one) hquotient
  refine ⟨?_, ?_⟩
  · refine ⟨x, ?_, ?_⟩
    · simpa [limlRayleighAdmissible, weakIVLIMLQuadraticForm] using
        weakIVLIMLQuadraticForm_pos hp (by simpa [sphere] using hx)
    · rw [weakIVLIMLSmallestGeneralizedRoot_eq_sInf hp, hvalue]
  · intro y hy
    have hy0 : y ≠ 0 := hy.ne_zero
    let c : ℝ := ‖y‖⁻¹
    have hc : c ≠ 0 := by simp [c, hy0]
    have hcy : c • y ∈ sphere := by
      simp [sphere, c, norm_smul, hy0]
    rw [weakIVLIMLSmallestGeneralizedRoot_eq_sInf hp, hvalue]
    have hle := hlower (c • y) hcy
    rw [weakIVLIMLGeneralizedRayleighQuotient_smul p y hc] at hle
    exact hle

end GeneralizedRootSelector

/-! ### Corrected triangular spectral boundary

The concrete selector above closes the former spectral gap. The remaining
certificate binds that selector, or a compatible alternative, to the actual
triangular sample pair without storing an estimator limit.
-/

/-- Matrix realization of the Gaussian vector supplied by the raw CLT. -/
noncomputable def weakIVRawGaussianMatrix
    (z : EuclideanSpace ℝ (l × Sum Unit k)) : Matrix l (Sum Unit k) ℝ :=
  fun a b => z.ofLp (a, b)

/-- Limit generalized-eigenvalue pair generated by the raw local-to-zero
model. -/
noncomputable def weakIVRawLIMLGeneralizedEigenvalueLimitPair
    (μ : Measure Ω) (Z : ℕ → Ω → l → ℝ)
    (u : ℕ → Ω → Sum Unit k → ℝ) (C : Matrix l k ℝ) (beta : k → ℝ)
    (z : EuclideanSpace ℝ (l × Sum Unit k)) :
    Matrix (Sum Unit k) (Sum Unit k) ℝ ×
      Matrix (Sum Unit k) (Sum Unit k) ℝ :=
  weakIVLIMLGeneralizedEigenvalueLimitPrimitive
    (popGram μ Z) C
    (fun z => weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
    (fun z => weakIVRawGaussianStructuralScore (weakIVRawGaussianMatrix z) beta)
    beta (popGram μ u) z

/-- Canonical scaled finite-sample LIML adjustment for the literal triangular
model: the totalized smallest generalized-Rayleigh root of the actual sample
pencil. -/
noncomputable def weakIVLocalLIMLSmallestRoot
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω) : ℝ :=
  weakIVLIMLSmallestGeneralizedRoot
    (weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega)

/-- Hansen's limiting `mu*` as the concrete smallest generalized-Rayleigh
root of the full reduced-form Gaussian pencil. -/
noncomputable def weakIVRawLIMLSmallestRoot
    (μ : Measure Ω) (Z : ℕ → Ω → l → ℝ)
    (u : ℕ → Ω → Sum Unit k → ℝ) (C : Matrix l k ℝ) (beta : k → ℝ)
    (z : EuclideanSpace ℝ (l × Sum Unit k)) : ℝ :=
  weakIVLIMLSmallestGeneralizedRoot
    (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z)

omit [DecidableEq k] in
private theorem weakIVRawLIMLGeneralizedEigenvalueLimitPair_positiveDenominator
    (μ : Measure Ω) (Z : ℕ → Ω → l → ℝ)
    (u : ℕ → Ω → Sum Unit k → ℝ) (C : Matrix l k ℝ) (beta : k → ℝ)
    (hSigma : (popGram μ u).PosDef)
    (z : EuclideanSpace ℝ (l × Sum Unit k)) :
    weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z ∈
      weakIVLIMLPositiveDenominatorSet := by
  apply weakIVLIMLPositiveDenominatorSet_of_posDef
  simpa [weakIVRawLIMLGeneralizedEigenvalueLimitPair,
    weakIVLIMLGeneralizedEigenvalueLimitPrimitive] using hSigma

private abbrev WeakIVRawLIMLPencilMomentState (k l : Type*) :=
  Matrix l (Sum Unit k) ℝ ×
    (Matrix l l ℝ × Matrix (Sum Unit k) (Sum Unit k) ℝ)

private abbrev WeakIVRawLIMLPencilState (k l : Type*) :=
  WeakIVRawLIMLPencilMomentState k l × ℝ

private abbrev WeakIVRawLIMLPencil (k : Type*) :=
  Matrix (Sum Unit k) (Sum Unit k) ℝ ×
    Matrix (Sum Unit k) (Sum Unit k) ℝ

/-- Continuous-map assembly of the actual OLS, 2SLS, and LIML structural
moment pairs from the generalized pencil and inverse sample size. -/
private noncomputable def weakIVTriangularEstimatorMomentAssemblyMap
    (beta : k → ℝ)
    (muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ)
    (p : WeakIVRawLIMLPencil k × ℝ) :
    ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) ×
      (Matrix k k ℝ × (k → ℝ)) :=
  let N := p.1.1
  let D := p.1.2
  let r := p.2
  let mu := muSelector p.1
  ((weakIVRawStructuralMomentPair beta (D + r • N),
      weakIVRawStructuralMomentPair beta N),
    weakIVRawStructuralMomentPair beta (N - mu • D))

/-- Centered Star estimator represented as a totalized function of structural
bread and score.  At a nonsingular bread it simplifies to `B⁻¹S`; at a
singular bread it retains the actual Star value `-beta`. -/
private noncomputable def weakIVCenteredStarEstimatorMap
    (beta : k → ℝ) (p : Matrix k k ℝ × (k → ℝ)) : k → ℝ :=
  p.1⁻¹ *ᵥ (p.1 *ᵥ beta + p.2) - beta

/-- Apply the same Star totalization to the OLS, 2SLS, and LIML moment pairs. -/
private noncomputable def weakIVTriangularEstimatorTotalizationMap
    (beta : k → ℝ)
    (p : ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) ×
      (Matrix k k ℝ × (k → ℝ))) :
    ((k → ℝ) × (k → ℝ)) × (k → ℝ) :=
  ((weakIVCenteredStarEstimatorMap beta p.1.1,
      weakIVCenteredStarEstimatorMap beta p.1.2),
    weakIVCenteredStarEstimatorMap beta p.2)

private theorem weakIVCenteredStarEstimatorMap_eq_inverse_score_of_nonsingular
    (beta : k → ℝ) (p : Matrix k k ℝ × (k → ℝ))
    (hp : IsUnit p.1.det) :
    weakIVCenteredStarEstimatorMap beta p = p.1⁻¹ *ᵥ p.2 := by
  rw [weakIVCenteredStarEstimatorMap, Matrix.mulVec_add,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hp]
  ext i
  simp [Pi.add_apply, Pi.sub_apply]

private theorem weakIVCenteredStarEstimatorMap_ols
    (X : Matrix (Fin m) k ℝ) (e : Fin m → ℝ) (beta : k → ℝ) :
    weakIVCenteredStarEstimatorMap beta
        (sampleGram X, sampleCrossMoment X e) =
      olsBetaStar X (X *ᵥ beta + e) - beta := by
  by_cases hm : m = 0
  · subst m
    simp [weakIVCenteredStarEstimatorMap, sampleGram, sampleCrossMoment,
      olsBetaStar]
  · haveI : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
    rw [olsBetaStar_eq_sampleGramInv_sampleCrossMoment,
      sampleCrossMoment_linear_model]
    rfl

private theorem weakIVCenteredStarEstimatorMap_twoSLS
    (Z : Matrix (Fin m) l ℝ) (X : Matrix (Fin m) k ℝ)
    (e : Fin m → ℝ) (beta : k → ℝ) :
    weakIVCenteredStarEstimatorMap beta
        (twoSLSMomentMatrixStar Z X, twoSLSMomentVectorStar Z X e) =
      twoSLSBetaStar Z X (X *ᵥ beta + e) - beta := by
  rw [weakIVCenteredStarEstimatorMap, twoSLSBetaStar,
    twoSLSMomentVectorStar_linear_model]

private theorem weakIVCenteredStarEstimatorMap_liml
    (Z : Matrix (Fin m) l ℝ) (X : Matrix (Fin m) k ℝ)
    (e : Fin m → ℝ) (beta : k → ℝ) (muHat : ℝ) :
    weakIVCenteredStarEstimatorMap beta
        (limlMomentMatrixStar Z X muHat,
          limlMomentVectorStar Z X e muHat) =
      limlBetaStar Z X (X *ᵥ beta + e) muHat - beta := by
  rw [weakIVCenteredStarEstimatorMap, limlBetaStar,
    limlMomentVectorStar_linear_model]

omit [MeasurableSpace Ω] in
private theorem weakIVTriangularEstimatorTotalizationMap_sample
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ)
    (limlMuHat : ℕ → Ω → ℝ) (m : ℕ) (omega : Ω) :
    weakIVTriangularEstimatorTotalizationMap beta
        (((sampleGram (weakIVLocalDesign Z u C m omega),
            sampleCrossMoment (weakIVLocalDesign Z u C m omega)
              (weakIVLocalStructuralError u beta m omega)),
          (twoSLSMomentMatrixStar (stackRegressors Z m omega)
              (weakIVLocalDesign Z u C m omega),
            twoSLSMomentVectorStar (stackRegressors Z m omega)
              (weakIVLocalDesign Z u C m omega)
              (weakIVLocalStructuralError u beta m omega))),
          (limlMomentMatrixStar (stackRegressors Z m omega)
              (weakIVLocalDesign Z u C m omega)
              (weakIVLIMLFiniteSampleMu limlMuHat m omega),
            limlMomentVectorStar (stackRegressors Z m omega)
              (weakIVLocalDesign Z u C m omega)
              (weakIVLocalStructuralError u beta m omega)
              (weakIVLIMLFiniteSampleMu limlMuHat m omega))) =
      ((weakIVLocalOLSBetaStar Z u C beta m omega - beta,
          weakIVLocal2SLSBetaStar Z u C beta m omega - beta),
        weakIVLocalLIMLBetaStar Z u C beta limlMuHat m omega - beta) := by
  rw [weakIVTriangularEstimatorTotalizationMap,
    weakIVCenteredStarEstimatorMap_ols,
    weakIVCenteredStarEstimatorMap_twoSLS,
    weakIVCenteredStarEstimatorMap_liml]
  rw [← weakIVLocalOutcome_eq_design_mulVec_add_error Z u C beta m omega]
  rfl

omit [DecidableEq k] in
private theorem weakIVRawStructuralMomentPair_reducedFormLimit
    (QZZ : Matrix l l ℝ) (C Xi2 : Matrix l k ℝ)
    (xie : l → ℝ) (beta : k → ℝ) :
    weakIVRawStructuralMomentPair beta
        (weakIVReducedFormRayleighMatrix QZZ C Xi2 xie beta) =
      (weakIV2SLSLimitBread QZZ C Xi2,
        weakIV2SLSLimitScore QZZ C Xi2 xie) := by
  let X := weakIVFirstStageLimit QZZ C Xi2
  have hR : weakIVReducedFormLimit QZZ C Xi2 xie beta =
      weakIVStructuralReducedFormMatrix X xie beta := by
    ext i b
    cases b with
    | inl b => cases b; rfl
    | inr j => rfl
  rw [weakIVReducedFormRayleighMatrix, limlRayleighMatrix, hR]
  simpa [X, weakIV2SLSLimitBread, weakIV2SLSLimitScore] using
    (weakIVRawStructuralMomentPair_reducedForm X xie beta QZZ⁻¹)

omit [DecidableEq k] in
private theorem weakIVRawStructuralMomentPair_sub_smul
    (beta : k → ℝ) (A B : Matrix (Sum Unit k) (Sum Unit k) ℝ) (c : ℝ) :
    weakIVRawStructuralMomentPair beta (A - c • B) =
      ((weakIVRawStructuralMomentPair beta A).1 -
          c • (weakIVRawStructuralMomentPair beta B).1,
        (weakIVRawStructuralMomentPair beta A).2 -
          c • (weakIVRawStructuralMomentPair beta B).2) := by
  classical
  apply Prod.ext
  · ext i j
    simp [weakIVRawStructuralMomentPair, weakIVRawSigma22]
  · ext i
    have hsub : (A - c • B).submatrix Sum.inr Sum.inr =
        A.submatrix Sum.inr Sum.inr - c • B.submatrix Sum.inr Sum.inr := by
      ext a b
      simp
    simp only [weakIVRawStructuralMomentPair, weakIVRawSigma2e,
      weakIVRawSigma22]
    rw [hsub, Matrix.sub_mulVec, Matrix.smul_mulVec]
    change
      (A (Sum.inr i) (Sum.inl ()) - c * B (Sum.inr i) (Sum.inl ())) -
          ((A.submatrix Sum.inr Sum.inr *ᵥ beta) i -
            c * (B.submatrix Sum.inr Sum.inr *ᵥ beta) i) =
        (A (Sum.inr i) (Sum.inl ()) -
            (A.submatrix Sum.inr Sum.inr *ᵥ beta) i) -
          c * (B (Sum.inr i) (Sum.inl ()) -
            (B.submatrix Sum.inr Sum.inr *ᵥ beta) i)
    ring

omit [DecidableEq k] in
private theorem weakIVTriangularEstimatorMomentAssemblyMap_limit
    (μ : Measure Ω) (Z : ℕ → Ω → l → ℝ)
    (u : ℕ → Ω → Sum Unit k → ℝ) (C : Matrix l k ℝ) (beta : k → ℝ)
    (muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ)
    (z : EuclideanSpace ℝ (l × Sum Unit k)) :
    weakIVTriangularEstimatorMomentAssemblyMap beta muSelector
        (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z, 0) =
      (((weakIVRawSigma22 (popGram μ u),
          weakIVRawSigma2e (popGram μ u) beta),
        (weakIV2SLSLimitBread (popGram μ Z) C
            (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z)),
          weakIV2SLSLimitScore (popGram μ Z) C
            (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
            (weakIVRawGaussianStructuralScore
              (weakIVRawGaussianMatrix z) beta))),
        (weakIVLIMLLimitBread (popGram μ Z) C
            (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
            (muSelector
              (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z))
            (weakIVRawSigma22 (popGram μ u)),
          weakIVLIMLLimitScore (popGram μ Z) C
            (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
            (weakIVRawGaussianStructuralScore
              (weakIVRawGaussianMatrix z) beta)
            (muSelector
              (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z))
            (weakIVRawSigma2e (popGram μ u) beta))) := by
  rw [weakIVTriangularEstimatorMomentAssemblyMap]
  simp only [zero_smul, add_zero]
  have hroot := weakIVRawStructuralMomentPair_reducedFormLimit
    (popGram μ Z) C
    (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
    (weakIVRawGaussianStructuralScore (weakIVRawGaussianMatrix z) beta) beta
  have hliml := weakIVRawStructuralMomentPair_sub_smul beta
    (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z).1
    (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z).2
    (muSelector (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z))
  simp only [weakIVRawLIMLGeneralizedEigenvalueLimitPair,
    weakIVLIMLGeneralizedEigenvalueLimitPrimitive] at hroot hliml ⊢
  have hSigma : weakIVRawStructuralMomentPair beta (popGram μ u) =
      (weakIVRawSigma22 (popGram μ u),
        weakIVRawSigma2e (popGram μ u) beta) := rfl
  rw [hroot, hSigma] at hliml
  have hLIML :
      weakIVRawStructuralMomentPair beta
          (weakIVReducedFormRayleighMatrix (popGram μ Z) C
              (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
              (weakIVRawGaussianStructuralScore
                (weakIVRawGaussianMatrix z) beta) beta -
            muSelector
                (weakIVReducedFormRayleighMatrix (popGram μ Z) C
                    (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
                    (weakIVRawGaussianStructuralScore
                      (weakIVRawGaussianMatrix z) beta) beta,
                  popGram μ u) • popGram μ u) =
        (weakIVLIMLLimitBread (popGram μ Z) C
            (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
            (muSelector
              (weakIVReducedFormRayleighMatrix (popGram μ Z) C
                  (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
                  (weakIVRawGaussianStructuralScore
                    (weakIVRawGaussianMatrix z) beta) beta,
                popGram μ u))
            (weakIVRawSigma22 (popGram μ u)),
          weakIVLIMLLimitScore (popGram μ Z) C
            (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
            (weakIVRawGaussianStructuralScore
              (weakIVRawGaussianMatrix z) beta)
            (muSelector
              (weakIVReducedFormRayleighMatrix (popGram μ Z) C
                  (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
                  (weakIVRawGaussianStructuralScore
                    (weakIVRawGaussianMatrix z) beta) beta,
                popGram μ u))
            (weakIVRawSigma2e (popGram μ u) beta)) := by
    simpa [weakIVLIMLLimitBread, weakIVLIMLLimitScore] using hliml
  rw [hSigma, hroot, hLIML]

omit [DecidableEq k] [MeasurableSpace Ω] in
private theorem weakIVTriangularEstimatorMomentAssemblyMap_sample
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ)
    (hselector : ∀ m omega,
      limlMuHat m omega =
        muSelector (weakIVLocalLIMLGeneralizedEigenvaluePair
          Z u C beta m omega))
    (m : ℕ) (omega : Ω) :
    weakIVTriangularEstimatorMomentAssemblyMap beta muSelector
        (weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega,
          (m : ℝ)⁻¹) =
      (((sampleGram (weakIVLocalDesign Z u C m omega),
          sampleCrossMoment (weakIVLocalDesign Z u C m omega)
            (weakIVLocalStructuralError u beta m omega)),
        (twoSLSMomentMatrixStar (stackRegressors Z m omega)
            (weakIVLocalDesign Z u C m omega),
          twoSLSMomentVectorStar (stackRegressors Z m omega)
            (weakIVLocalDesign Z u C m omega)
            (weakIVLocalStructuralError u beta m omega))),
        (limlMomentMatrixStar (stackRegressors Z m omega)
            (weakIVLocalDesign Z u C m omega)
            (weakIVLIMLFiniteSampleMu limlMuHat m omega),
          limlMomentVectorStar (stackRegressors Z m omega)
            (weakIVLocalDesign Z u C m omega)
            (weakIVLocalStructuralError u beta m omega)
            (weakIVLIMLFiniteSampleMu limlMuHat m omega))) := by
  classical
  let Zm := stackRegressors Z m omega
  let Xm := weakIVLocalDesign Z u C m omega
  let em := weakIVLocalStructuralError u beta m omega
  let Rm := weakIVLocalReducedFormSampleMatrix Z u C beta m omega
  let P := instrumentProjectionStar Zm
  let r : ℝ := (m : ℝ)⁻¹
  have hN :
      (weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega).1 =
        Rmᵀ * P * Rm := by
    rfl
  have hD :
      (weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega).2 =
        Rmᵀ * (r • (1 - P)) * Rm := by
    simp [weakIVLocalLIMLGeneralizedEigenvaluePair,
      weakIVLocalLIMLResidualCovariance, Rm, Zm, P, r,
      Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
  have hOLS :
      (weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega).2 +
          r • (weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega).1 =
        Rmᵀ * (r • (1 : Matrix (Fin m) (Fin m) ℝ)) * Rm := by
    rw [hN, hD]
    calc
      Rmᵀ * (r • (1 - P)) * Rm + r • (Rmᵀ * P * Rm) =
          r • (Rmᵀ * (1 - P) * Rm) + r • (Rmᵀ * P * Rm) := by
            rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = r • (Rmᵀ * (1 - P) * Rm + Rmᵀ * P * Rm) := by rw [smul_add]
      _ = r • (Rmᵀ * Rm) := by
        congr 1
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
        abel
      _ = Rmᵀ * (r • (1 : Matrix (Fin m) (Fin m) ℝ)) * Rm := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
        simp
  have hLIML :
      (weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega).1 -
          limlMuHat m omega •
            (weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega).2 =
        Rmᵀ * limlWeightMatrixStar Zm
          (weakIVLIMLFiniteSampleMu limlMuHat m omega) * Rm := by
    rw [hN, hD]
    calc
      Rmᵀ * P * Rm - limlMuHat m omega •
          (Rmᵀ * (r • (1 - P)) * Rm) =
        Rmᵀ * (P - limlMuHat m omega • (r • (1 - P))) * Rm := by
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
          simp [Matrix.mul_smul, Matrix.smul_mul]
      _ = Rmᵀ * limlWeightMatrixStar Zm
          (weakIVLIMLFiniteSampleMu limlMuHat m omega) * Rm := by
        congr 2
        ext i j
        simp [limlWeightMatrixStar, weakIVLIMLFiniteSampleMu, r, P]
        ring
  rw [weakIVTriangularEstimatorMomentAssemblyMap, ← hselector m omega]
  simp only
  rw [hOLS, hLIML, hN]
  have hOLSBlock := weakIVRawStructuralMomentPair_localReducedForm
    Z u C beta m omega (r • (1 : Matrix (Fin m) (Fin m) ℝ))
  have h2SLSBlock := weakIVRawStructuralMomentPair_localReducedForm
    Z u C beta m omega P
  have hLIMLBlock := weakIVRawStructuralMomentPair_localReducedForm
    Z u C beta m omega
      (limlWeightMatrixStar Zm (weakIVLIMLFiniteSampleMu limlMuHat m omega))
  rw [hOLSBlock, h2SLSBlock, hLIMLBlock]
  simp [Zm, P, r, sampleGram, sampleCrossMoment,
    twoSLSMomentMatrixStar, twoSLSMomentVectorStar,
    limlMomentMatrixStar, limlMomentVectorStar,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec]

/-- The deterministic reduced-form loading `[C beta, C]` used to assemble the
literal triangular sample from its raw error matrix. -/
private noncomputable def weakIVRawReducedFormLoading
    (C : Matrix l k ℝ) (beta : k → ℝ) : Matrix l (Sum Unit k) ℝ
  | a, Sum.inl _ => (C *ᵥ beta) a
  | a, Sum.inr j => C a j

/-- Algebraic pencil formula in the raw score, instrument Gram, error Gram,
and inverse sample size. -/
private noncomputable def weakIVRawLIMLPencilFormula
    (C : Matrix l k ℝ) (beta : k → ℝ)
    (p : WeakIVRawLIMLPencilState k l) : WeakIVRawLIMLPencil k :=
  let Xi := p.1.1
  let Q := p.1.2.1
  let Sigma := p.1.2.2
  let r := p.2
  let D := weakIVRawReducedFormLoading C beta
  let A := Q * D + Xi
  let N := Aᵀ * Q⁻¹ * A
  (N, Sigma + r • (Xiᵀ * D + Dᵀ * Xi + Dᵀ * Q * D - N))

/-- Nonsingular branch of the raw pencil formula.  The zero branch is used
only to make the CMT map explicit away from its continuity set. -/
private noncomputable def weakIVRawLIMLPencilAssemblyMap
    (C : Matrix l k ℝ) (beta : k → ℝ)
    (p : WeakIVRawLIMLPencilState k l) : WeakIVRawLIMLPencil k :=
  letI : Decidable (IsUnit (p.1.2.1).det) := Classical.propDecidable _
  if IsUnit (p.1.2.1).det then weakIVRawLIMLPencilFormula C beta p else 0

private noncomputable def weakIVRawLIMLPencilSampleState
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (m : ℕ) (omega : Ω) : WeakIVRawLIMLPencilState k l :=
  ((weakIVRawRootReducedFormScore Z u m omega,
      (sampleGram (stackRegressors Z m omega),
        sampleGram (stackRegressors u m omega))),
    (m : ℝ)⁻¹)

private noncomputable def weakIVRawLIMLPencilLimitState
    (μ : Measure Ω) (Z : ℕ → Ω → l → ℝ)
    (u : ℕ → Ω → Sum Unit k → ℝ)
    (z : EuclideanSpace ℝ (l × Sum Unit k)) : WeakIVRawLIMLPencilState k l :=
  ((weakIVRawGaussianMatrix z, (popGram μ Z, popGram μ u)), 0)

omit [DecidableEq k] in
private theorem weakIVRawLIMLPencilFormula_measurable
    (C : Matrix l k ℝ) (beta : k → ℝ) :
    Measurable (weakIVRawLIMLPencilFormula C beta) := by
  let D := weakIVRawReducedFormLoading C beta
  have hXi : Measurable
      (fun p : WeakIVRawLIMLPencilState k l => p.1.1) :=
    (continuous_fst.comp continuous_fst).measurable
  have hQ : Measurable
      (fun p : WeakIVRawLIMLPencilState k l => p.1.2.1) :=
    (continuous_fst.comp (continuous_snd.comp continuous_fst)).measurable
  have hSigma : Measurable
      (fun p : WeakIVRawLIMLPencilState k l => p.1.2.2) :=
    (continuous_snd.comp (continuous_snd.comp continuous_fst)).measurable
  have hr : Measurable (fun p : WeakIVRawLIMLPencilState k l => p.2) :=
    measurable_snd
  have hQdet : Measurable
      (fun p : WeakIVRawLIMLPencilState k l => (p.1.2.1).det) :=
    (Continuous.matrix_det
      (continuous_fst.comp (continuous_snd.comp continuous_fst))).measurable
  have hQadj : Measurable
      (fun p : WeakIVRawLIMLPencilState k l => (p.1.2.1).adjugate) :=
    (Continuous.matrix_adjugate
      (continuous_fst.comp (continuous_snd.comp continuous_fst))).measurable
  have hQinvDet : Measurable
      (fun p : WeakIVRawLIMLPencilState k l => Ring.inverse (p.1.2.1).det) := by
    have heq :
        (fun p : WeakIVRawLIMLPencilState k l => Ring.inverse (p.1.2.1).det) =
          (fun p => ((p.1.2.1).det)⁻¹) := by
      funext p
      exact Ring.inverse_eq_inv _
    rw [heq]
    exact measurable_inv.comp hQdet
  have hQinv : Measurable
      (fun p : WeakIVRawLIMLPencilState k l => p.1.2.1⁻¹) := by
    have heq :
        (fun p : WeakIVRawLIMLPencilState k l => p.1.2.1⁻¹) =
          (fun p => Ring.inverse (p.1.2.1).det • (p.1.2.1).adjugate) := by
      funext p
      exact Matrix.inv_def p.1.2.1
    rw [heq]
    exact hQinvDet.smul hQadj
  have hD : Measurable
      (fun _ : WeakIVRawLIMLPencilState k l => D) := measurable_const
  have hDt : Measurable
      (fun _ : WeakIVRawLIMLPencilState k l => Dᵀ) := measurable_const
  have hQD :=
    (Continuous.matrix_mul continuous_fst continuous_snd).measurable.comp
      (hQ.prodMk hD)
  have hA := hQD.add hXi
  have hAt := (continuous_id.matrix_transpose).measurable.comp hA
  have hLeft :=
    (Continuous.matrix_mul continuous_fst continuous_snd).measurable.comp
      (hAt.prodMk hQinv)
  have hN :=
    (Continuous.matrix_mul continuous_fst continuous_snd).measurable.comp
      (hLeft.prodMk hA)
  have hXiT := (continuous_id.matrix_transpose).measurable.comp hXi
  have hXiTD :=
    (Continuous.matrix_mul continuous_fst continuous_snd).measurable.comp
      (hXiT.prodMk hD)
  have hDTXi :=
    (Continuous.matrix_mul continuous_fst continuous_snd).measurable.comp
      (hDt.prodMk hXi)
  have hDTQ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).measurable.comp
      (hDt.prodMk hQ)
  have hDTQD :=
    (Continuous.matrix_mul continuous_fst continuous_snd).measurable.comp
      (hDTQ.prodMk hD)
  have hCorrection := ((hXiTD.add hDTXi).add hDTQD).sub hN
  have hFormula := hN.prodMk (hSigma.add (hr.smul hCorrection))
  simpa only [weakIVRawLIMLPencilFormula, D, Matrix.transpose_add,
    Matrix.transpose_mul] using hFormula

omit [DecidableEq k] in
private theorem weakIVRawLIMLPencilAssemblyMap_measurable
    (C : Matrix l k ℝ) (beta : k → ℝ) :
    Measurable (weakIVRawLIMLPencilAssemblyMap C beta) := by
  classical
  have hdet : Measurable
      (fun p : WeakIVRawLIMLPencilState k l => (p.1.2.1).det) :=
    (Continuous.matrix_det
      (continuous_fst.comp (continuous_snd.comp continuous_fst))).measurable
  have hunit : MeasurableSet
      {p : WeakIVRawLIMLPencilState k l | IsUnit (p.1.2.1).det} := by
    rw [show {p : WeakIVRawLIMLPencilState k l | IsUnit (p.1.2.1).det} =
        (fun p => (p.1.2.1).det) ⁻¹' ({0}ᶜ : Set ℝ) by
      ext p
      simp [isUnit_iff_ne_zero]]
    exact hdet (measurableSet_singleton 0).compl
  change Measurable
    (fun p : WeakIVRawLIMLPencilState k l =>
      if IsUnit (p.1.2.1).det then weakIVRawLIMLPencilFormula C beta p
      else (0 : WeakIVRawLIMLPencil k))
  exact Measurable.ite hunit
    (weakIVRawLIMLPencilFormula_measurable C beta) measurable_const

omit [DecidableEq k] in
private theorem weakIVRawLIMLPencilAssemblyMap_continuousAt_of_nonsingular
    (C : Matrix l k ℝ) (beta : k → ℝ)
    (p : WeakIVRawLIMLPencilState k l) (hp : IsUnit (p.1.2.1).det) :
    ContinuousAt (weakIVRawLIMLPencilAssemblyMap C beta) p := by
  let D := weakIVRawReducedFormLoading C beta
  have hXi : ContinuousAt
      (fun q : WeakIVRawLIMLPencilState k l => q.1.1) p :=
    (continuous_fst.comp continuous_fst).continuousAt
  have hQ : ContinuousAt
      (fun q : WeakIVRawLIMLPencilState k l => q.1.2.1) p :=
    (continuous_fst.comp (continuous_snd.comp continuous_fst)).continuousAt
  have hSigma : ContinuousAt
      (fun q : WeakIVRawLIMLPencilState k l => q.1.2.2) p :=
    (continuous_snd.comp (continuous_snd.comp continuous_fst)).continuousAt
  have hr : ContinuousAt
      (fun q : WeakIVRawLIMLPencilState k l => q.2) p :=
    continuousAt_snd
  have hQinv : ContinuousAt
      (fun q : WeakIVRawLIMLPencilState k l => q.1.2.1⁻¹) p := by
    have hinv : ContinuousAt (fun A : Matrix l l ℝ => A⁻¹) p.1.2.1 := by
      refine continuousAt_matrix_inv _ ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hp.ne_zero
    let qfun : WeakIVRawLIMLPencilState k l → Matrix l l ℝ :=
      fun q => q.1.2.1
    have hcomp : ContinuousAt ((fun A : Matrix l l ℝ => A⁻¹) ∘ qfun) p :=
      ContinuousAt.comp (f := qfun) hinv hQ
    simpa only [qfun, Function.comp_apply] using hcomp
  have hD : ContinuousAt
      (fun _ : WeakIVRawLIMLPencilState k l => D) p := continuousAt_const
  have hDt : ContinuousAt
      (fun _ : WeakIVRawLIMLPencilState k l => Dᵀ) p := continuousAt_const
  have hQD :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hQ.prodMk hD)
  have hA := hQD.add hXi
  have hAt := (continuous_id.matrix_transpose).continuousAt.comp hA
  have hLeft :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hAt.prodMk hQinv)
  have hN :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hLeft.prodMk hA)
  have hXiT := (continuous_id.matrix_transpose).continuousAt.comp hXi
  have hXiTD :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hXiT.prodMk hD)
  have hDTXi :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hDt.prodMk hXi)
  have hDTQ :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hDt.prodMk hQ)
  have hDTQD :=
    (Continuous.matrix_mul continuous_fst continuous_snd).continuousAt.comp
      (hDTQ.prodMk hD)
  have hCorrection := ((hXiTD.add hDTXi).add hDTQD).sub hN
  have hFormula : ContinuousAt (weakIVRawLIMLPencilFormula C beta) p := by
    simpa only [weakIVRawLIMLPencilFormula, D, Matrix.transpose_add,
      Matrix.transpose_mul] using
      hN.prodMk (hSigma.add (hr.smul hCorrection))
  have hopen : IsOpen
      {q : WeakIVRawLIMLPencilState k l | IsUnit (q.1.2.1).det} := by
    rw [show {q : WeakIVRawLIMLPencilState k l | IsUnit (q.1.2.1).det} =
        (fun q => (q.1.2.1).det) ⁻¹' ({0}ᶜ : Set ℝ) by
      ext q
      simp [isUnit_iff_ne_zero]]
    exact isOpen_compl_singleton.preimage
      (Continuous.matrix_det
        (continuous_fst.comp (continuous_snd.comp continuous_fst)))
  have hevent : ∀ᶠ q in 𝓝 p, IsUnit (q.1.2.1).det := hopen.mem_nhds hp
  apply hFormula.congr_of_eventuallyEq
  filter_upwards [hevent] with q hq
  simp only [weakIVRawLIMLPencilAssemblyMap]
  rw [if_pos hq]

omit [DecidableEq k] [DecidableEq l] [MeasurableSpace Ω] in
private theorem weakIVLocalReducedFormSampleMatrix_eq_raw_loading
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω) :
    weakIVLocalReducedFormSampleMatrix Z u C beta m omega =
      stackRegressors u m omega +
        (Real.sqrt (m : ℝ))⁻¹ •
          (stackRegressors Z m omega * weakIVRawReducedFormLoading C beta) := by
  ext i b
  cases b with
  | inl b =>
      cases b
      simp only [weakIVLocalReducedFormSampleMatrix, weakIVLocalOutcomeRow,
        weakIVLocalRegressorRow, weakIVRawStructuralErrorRow, stackRegressors,
        weakIVRawReducedFormLoading, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.add_apply,
        Matrix.smul_apply, Matrix.of_apply, Matrix.transpose_apply]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      ring_nf
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply congrArg (fun x : ℝ => x + u i.val omega (Sum.inl ()))
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro j _
      ring
  | inr j =>
      simp only [weakIVLocalReducedFormSampleMatrix, weakIVLocalRegressorRow,
        stackRegressors, weakIVRawReducedFormLoading, Matrix.mul_apply,
        Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply]
      rw [add_comm]
      apply congrArg (fun x : ℝ => u i.val omega (Sum.inr j) + x)
      apply congrArg (fun x : ℝ => (Real.sqrt (m : ℝ))⁻¹ * x)
      apply Finset.sum_congr rfl
      intro a _
      simp only [Matrix.transpose_apply]
      ring

omit [Fintype k] [Fintype l] [DecidableEq k] [DecidableEq l]
    [MeasurableSpace Ω] in
private theorem weakIVRawRootReducedFormScore_eq_stack
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (m : ℕ) (omega : Ω) :
    weakIVRawRootReducedFormScore Z u m omega =
      (Real.sqrt (m : ℝ))⁻¹ •
        ((stackRegressors Z m omega)ᵀ * stackRegressors u m omega) := by
  ext a b
  change
    (Real.sqrt (m : ℝ))⁻¹ *
        ∑ i ∈ Finset.range m, Z i omega a * u i omega b =
      (Real.sqrt (m : ℝ))⁻¹ *
        ∑ i : Fin m, Z i.val omega a * u i.val omega b
  rw [Finset.sum_fin_eq_sum_range]
  apply congrArg (fun x : ℝ => (Real.sqrt (m : ℝ))⁻¹ * x)
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

omit [DecidableEq k] [DecidableEq l] in
private theorem weakIVReducedFormLimit_eq_raw_loading
    (Q : Matrix l l ℝ) (C : Matrix l k ℝ)
    (Xi : Matrix l (Sum Unit k) ℝ) (beta : k → ℝ) :
    weakIVReducedFormLimit Q C
        (weakIVRawGaussianFirstStage Xi)
        (weakIVRawGaussianStructuralScore Xi beta) beta =
      Q * weakIVRawReducedFormLoading C beta + Xi := by
  ext a b
  cases b with
  | inl b =>
      cases b
      simp only [weakIVReducedFormLimit, weakIVFirstStageLimit,
        weakIVRawGaussianFirstStage, weakIVRawGaussianStructuralScore,
        weakIVRawReducedFormLoading, Matrix.add_apply, Matrix.mul_apply,
        Matrix.mulVec, dotProduct]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      ring_nf
  | inr j =>
      simp [weakIVReducedFormLimit, weakIVFirstStageLimit,
        weakIVRawGaussianFirstStage, weakIVRawReducedFormLoading,
        Matrix.mul_apply]

omit [DecidableEq k] [MeasurableSpace Ω] in
private theorem weakIVLocalLIMLGeneralizedEigenvaluePair_eq_raw_formula_of_ne_zero
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω)
    (hm : m ≠ 0) :
    weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega =
      weakIVRawLIMLPencilFormula C beta
        (weakIVRawLIMLPencilSampleState Z u m omega) := by
  let Zm := stackRegressors Z m omega
  let Um := stackRegressors u m omega
  let Rm := weakIVLocalReducedFormSampleMatrix Z u C beta m omega
  let D := weakIVRawReducedFormLoading C beta
  let t : ℝ := (Real.sqrt (m : ℝ))⁻¹
  let r : ℝ := (m : ℝ)⁻¹
  have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hsqrt : Real.sqrt (m : ℝ) ≠ 0 := by positivity
  have ht_sq : t * t = r := by
    dsimp [t, r]
    field_simp
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg m : 0 ≤ (m : ℝ))]
  have hscale : t * r⁻¹ * t = 1 := by
    dsimp [t, r]
    rw [inv_inv]
    field_simp
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg m : 0 ≤ (m : ℝ))]
  have hR : Rm = Um + t • (Zm * D) := by
    simpa [Rm, Um, Zm, D, t] using
      weakIVLocalReducedFormSampleMatrix_eq_raw_loading Z u C beta m omega
  have hXi : weakIVRawRootReducedFormScore Z u m omega = t • (Zmᵀ * Um) := by
    simpa [t, Zm, Um] using weakIVRawRootReducedFormScore_eq_stack Z u m omega
  have hQ : sampleGram Zm = r • (Zmᵀ * Zm) := by
    simp [sampleGram, r]
  have hSigma : sampleGram Um = r • (Umᵀ * Um) := by
    simp [sampleGram, r]
  have hA : sampleGram Zm * D + weakIVRawRootReducedFormScore Z u m omega =
      t • (Zmᵀ * Rm) := by
    rw [hQ, hXi, hR]
    simp only [Matrix.smul_mul, Matrix.mul_add, Matrix.mul_smul,
      smul_add, smul_smul, Matrix.mul_assoc]
    rw [ht_sq]
    module
  have hN :
      (sampleGram Zm * D + weakIVRawRootReducedFormScore Z u m omega)ᵀ *
          (sampleGram Zm)⁻¹ *
          (sampleGram Zm * D + weakIVRawRootReducedFormScore Z u m omega) =
        Rmᵀ * instrumentProjectionStar Zm * Rm := by
    rw [hA, hQ, nonsingInv_smul]
    simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, Matrix.transpose_mul, transpose_transpose]
    have hscale' : t * (r⁻¹ * t) = 1 := by
      calc
        t * (r⁻¹ * t) = t * r⁻¹ * t := by ring
        _ = 1 := hscale
    rw [hscale', one_smul]
    simp [instrumentProjectionStar, Matrix.mul_assoc]
  have hGram :
      r • (Rmᵀ * Rm) =
        sampleGram Um +
          r • ((weakIVRawRootReducedFormScore Z u m omega)ᵀ * D +
            Dᵀ * weakIVRawRootReducedFormScore Z u m omega +
            Dᵀ * sampleGram Zm * D) := by
    rw [hR, hXi, hQ, hSigma]
    simp only [transpose_add, transpose_smul, transpose_mul, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
      transpose_transpose, Matrix.mul_assoc]
    rw [ht_sq]
    module
  rw [weakIVLocalLIMLGeneralizedEigenvaluePair]
  simp only [weakIVRawLIMLPencilFormula, weakIVRawLIMLPencilSampleState]
  apply Prod.ext
  · simpa [Rm, Zm, D] using hN.symm
  · change
      r • (Rmᵀ * ((1 : Matrix (Fin m) (Fin m) ℝ) -
          instrumentProjectionStar Zm) * Rm) = _
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
    rw [smul_sub, ← hN, hGram]
    dsimp [Um, Zm, D, r]
    module

omit [DecidableEq k] [MeasurableSpace Ω] in
private theorem weakIVLocalLIMLGeneralizedEigenvaluePair_eq_raw_formula
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ) (m : ℕ) (omega : Ω) :
    weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega =
      weakIVRawLIMLPencilFormula C beta
        (weakIVRawLIMLPencilSampleState Z u m omega) := by
  by_cases hm : m = 0
  · subst m
    simp [weakIVLocalLIMLGeneralizedEigenvaluePair,
      weakIVLocalLIMLResidualCovariance, weakIVRawLIMLPencilFormula,
      weakIVRawLIMLPencilSampleState, sampleGram, instrumentProjectionStar]
  · exact weakIVLocalLIMLGeneralizedEigenvaluePair_eq_raw_formula_of_ne_zero
      Z u C beta m omega hm

omit [DecidableEq k] [IsProbabilityMeasure μ] in
private theorem weakIVRawLIMLPencilAssemblyMap_limit
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ)
    (hQZZ : IsUnit (popGram μ Z).det)
    (z : EuclideanSpace ℝ (l × Sum Unit k)) :
    weakIVRawLIMLPencilAssemblyMap C beta
        (weakIVRawLIMLPencilLimitState μ Z u z) =
      weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z := by
  have hlimit := weakIVReducedFormLimit_eq_raw_loading
    (popGram μ Z) C (weakIVRawGaussianMatrix z) beta
  rw [weakIVRawLIMLPencilAssemblyMap]
  simp only [weakIVRawLIMLPencilLimitState]
  rw [if_pos hQZZ]
  simp only [weakIVRawLIMLPencilFormula,
    weakIVRawLIMLGeneralizedEigenvalueLimitPair,
    weakIVLIMLGeneralizedEigenvalueLimitPrimitive,
    weakIVReducedFormRayleighMatrix, limlRayleighMatrix]
  rw [hlimit]
  simp

omit [IsProbabilityMeasure μ] in
private theorem weakIV_tendstoInMeasure_sub_zero_of_measure_ne_tendsto_zero
    {E : Type*} [NormedAddCommGroup E]
    {X Y : ℕ → Ω → E}
    (hbad : Tendsto (fun m => μ {omega | X m omega ≠ Y m omega}) atTop (𝓝 0)) :
    TendstoInMeasure μ (Y - X) atTop (fun _ => 0) := by
  intro epsilon hepsilon
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbad
    (Eventually.of_forall fun _ => zero_le _) ?_
  exact Eventually.of_forall fun m => measure_mono (by
    intro omega homega
    simp only [Set.mem_setOf_eq, Pi.sub_apply] at homega ⊢
    intro heq
    rw [heq, sub_self, edist_self] at homega
    exact (not_le_of_gt hepsilon) homega)

/-- The literal triangular LIML generalized-eigenvalue pencil follows from
the raw reduced-form CLT/WLLNs and nonsingularity of the population instrument
Gram.  No eigenvalue selector or estimator convergence is assumed. -/
theorem weakIV_rawLIMLGeneralizedEigenvaluePair_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    (C : Matrix l k ℝ) (beta : k → ℝ)
    (h : WeakIVRawJointMomentConditions μ Z u)
    (hQZZ : IsUnit (popGram μ Z).det) :
    TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) =>
        weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega)
      atTop
      (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta)
      (fun _ => μ)
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0))) := by
  let gaussianLaw := multivariateGaussian 0
    (covMat μ (weakIVRawReducedFormScoreRow Z u 0))
  have hr : TendstoInMeasure μ
      (fun (m : ℕ) (_ : Ω) => (m : ℝ)⁻¹) atTop (fun _ => (0 : ℝ)) :=
    tendstoInMeasure_const_real (μ := μ)
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hraw := weakIV_rawJointMoments_tendstoInDistribution h
  have hstate : TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) => weakIVRawLIMLPencilSampleState Z u m omega)
      atTop
      (weakIVRawLIMLPencilLimitState μ Z u)
      (fun _ => μ) gaussianLaw := by
    have hprod := hraw.prodMk_of_tendstoInMeasure_const
      (fun (m : ℕ) (omega : Ω) =>
        (weakIVRawRootReducedFormScore Z u m omega,
          (sampleGram (stackRegressors Z m omega),
            sampleGram (stackRegressors u m omega))))
      (fun m (_ : Ω) => (m : ℝ)⁻¹)
      (fun z : EuclideanSpace ℝ (l × Sum Unit k) =>
        (weakIVRawGaussianMatrix z, (popGram μ Z, popGram μ u)))
      hr (fun _ => measurable_const.aemeasurable)
    simpa [weakIVRawLIMLPencilSampleState, weakIVRawLIMLPencilLimitState,
      weakIVRawGaussianMatrix, gaussianLaw] using hprod
  let bad : Set (WeakIVRawLIMLPencilState k l) :=
    {p | ¬ IsUnit (p.1.2.1).det}
  have hbad_meas : MeasurableSet bad := by
    have hdet : Measurable
        (fun p : WeakIVRawLIMLPencilState k l => (p.1.2.1).det) :=
      (Continuous.matrix_det
        (continuous_fst.comp (continuous_snd.comp continuous_fst))).measurable
    rw [show bad =
        (fun p : WeakIVRawLIMLPencilState k l => (p.1.2.1).det) ⁻¹' {0} by
      ext p
      simp [bad, isUnit_iff_ne_zero]]
    exact hdet (measurableSet_singleton 0)
  have hbad_null :
      (gaussianLaw.map (weakIVRawLIMLPencilLimitState μ Z u)) bad = 0 := by
    rw [Measure.map_apply_of_aemeasurable hstate.aemeasurable_limit hbad_meas]
    have hpre :
        (weakIVRawLIMLPencilLimitState μ Z u) ⁻¹' bad =
          (∅ : Set (EuclideanSpace ℝ (l × Sum Unit k))) := by
      ext z
      simp only [Set.mem_preimage, bad, Set.mem_setOf_eq,
        weakIVRawLIMLPencilLimitState, Set.mem_empty_iff_false, iff_false,
        not_not]
      exact hQZZ
    rw [hpre, measure_empty]
  have hcont : ∀ p : WeakIVRawLIMLPencilState k l, p ∉ bad →
      ContinuousAt (weakIVRawLIMLPencilAssemblyMap C beta) p := by
    intro p hp
    exact weakIVRawLIMLPencilAssemblyMap_continuousAt_of_nonsingular C beta p
      (by simpa [bad] using hp)
  have hbranch : TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) =>
        weakIVRawLIMLPencilAssemblyMap C beta
          (weakIVRawLIMLPencilSampleState Z u m omega))
      atTop
      (fun z => weakIVRawLIMLPencilAssemblyMap C beta
        (weakIVRawLIMLPencilLimitState μ Z u z))
      (fun _ => μ) gaussianLaw := by
    simpa [Function.comp_def] using tendstoInDistribution_ae_continuous_comp
      hstate (weakIVRawLIMLPencilAssemblyMap_measurable C beta)
        hbad_null hcont
  have hbranch_target : TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) =>
        weakIVRawLIMLPencilAssemblyMap C beta
          (weakIVRawLIMLPencilSampleState Z u m omega))
      atTop
      (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta)
      (fun _ => μ) gaussianLaw := by
    refine TendstoInDistribution.congr (fun _ => EventuallyEq.rfl) ?_ hbranch
    exact ae_of_all gaussianLaw fun z =>
      weakIVRawLIMLPencilAssemblyMap_limit Z u C beta hQZZ z
  have hsingular := weakIV_rawInstrumentGram_singular_tendsto_zero h hQZZ
  have heq_bad : Tendsto
      (fun m => μ {omega |
        weakIVRawLIMLPencilAssemblyMap C beta
            (weakIVRawLIMLPencilSampleState Z u m omega) ≠
          weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega})
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hsingular (Eventually.of_forall fun _ => zero_le _) ?_
    exact Eventually.of_forall fun m => measure_mono (by
      intro omega hne
      simp only [Set.mem_setOf_eq] at hne ⊢
      intro hunit
      apply hne
      simp only [weakIVRawLIMLPencilAssemblyMap,
        weakIVRawLIMLPencilSampleState]
      rw [if_pos hunit]
      simpa [weakIVRawLIMLPencilSampleState] using
        (weakIVLocalLIMLGeneralizedEigenvaluePair_eq_raw_formula
          Z u C beta m omega).symm)
  have hdiff : TendstoInMeasure μ
      ((fun (m : ℕ) (omega : Ω) =>
          weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega) -
        (fun (m : ℕ) (omega : Ω) =>
          weakIVRawLIMLPencilAssemblyMap C beta
            (weakIVRawLIMLPencilSampleState Z u m omega)))
      atTop (fun _ => 0) :=
    weakIV_tendstoInMeasure_sub_zero_of_measure_ne_tendsto_zero heq_bad
  have hpencil_meas : ∀ m, AEMeasurable
      (fun omega => weakIVLocalLIMLGeneralizedEigenvaluePair
        Z u C beta m omega) μ := by
    intro m
    have hformula :=
      (weakIVRawLIMLPencilFormula_measurable C beta).comp_aemeasurable
        (hstate.forall_aemeasurable m)
    refine hformula.congr (ae_of_all μ fun omega => ?_)
    exact (weakIVLocalLIMLGeneralizedEigenvaluePair_eq_raw_formula
      Z u C beta m omega).symm
  simpa [gaussianLaw] using tendstoInDistribution_of_tendstoInMeasure_sub
    (Y := fun (m : ℕ) (omega : Ω) =>
      weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega)
    (Z := weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta)
    hbranch_target hdiff hpencil_meas

/-- Selector certificate for the literal triangular model. The finite-sample
minimum is required on regular pencils only: at `m = 0` the denominator is
zero, so Hansen's admissible Rayleigh domain is empty and an unconditional
minimum certificate would be inconsistent. The limiting minimum remains exact
and the bad set must be null under the raw Gaussian limit law. -/
structure WeakIVTriangularSelectorCertificate
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ)
    (selectorBad : Set
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ)) : Prop where
  selector_meas : Measurable muSelector
  selector_bad_measurable : MeasurableSet selectorBad
  selector_bad_null :
    ((multivariateGaussian 0
      (covMat μ (weakIVRawReducedFormScoreRow Z u 0))).map
        (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta)) selectorBad = 0
  selector_continuous_off : ∀ p, p ∉ selectorBad → ContinuousAt muSelector p
  sample_selector_eq : ∀ m omega,
    limlMuHat m omega =
      muSelector (weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega)
  finite_sample_rayleigh_minimizer_of_regular : ∀ m omega,
    let p := weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega
    p ∉ selectorBad →
    LIMLRayleighMinimizer p.1 p.2 (limlMuHat m omega)
  limit_rayleigh_minimizer : ∀ z,
    let p := weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z
    LIMLRayleighMinimizer p.1 p.2 (muSelector p)

/-- Non-circular corrected assembly package at the current raw boundary.

The pencil field records the generalized-eigenvalue CMT and is derived from raw
moments by `WeakIVTriangularAssemblyConditions.of_raw_moments`. The
selector certificate identifies every regular finite-sample root and every
limiting root as a Rayleigh minimum. Estimator nondegeneracy assumptions are
kept at the theorem endpoint that invokes the inverse maps. -/
structure WeakIVTriangularAssemblyConditions
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → l → ℝ) (u : ℕ → Ω → Sum Unit k → ℝ)
    (C : Matrix l k ℝ) (beta : k → ℝ)
    (limlMuHat : ℕ → Ω → ℝ)
    (muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ)
    (selectorBad : Set
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ)) : Prop where
  raw_moments : WeakIVRawJointMomentConditions μ Z u
  pencil_tendsto : TendstoInDistribution
    (fun (m : ℕ) (omega : Ω) =>
      weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega)
    atTop
    (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta)
    (fun _ => μ)
    (multivariateGaussian 0
      (covMat μ (weakIVRawReducedFormScoreRow Z u 0)))
  selector : WeakIVTriangularSelectorCertificate
    μ Z u C beta limlMuHat muSelector selectorBad

/-- Build the triangular raw assembly from primitive moments, population
instrument nonsingularity, and the spectral selector certificate. In
particular, no estimator convergence is assumed. -/
theorem WeakIVTriangularAssemblyConditions.of_raw_moments
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    {C : Matrix l k ℝ} {beta : k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ}
    {selectorBad : Set
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ)}
    (raw_moments : WeakIVRawJointMomentConditions μ Z u)
    (hQZZ : IsUnit (popGram μ Z).det)
    (selector : WeakIVTriangularSelectorCertificate
      μ Z u C beta limlMuHat muSelector selectorBad) :
    WeakIVTriangularAssemblyConditions
      μ Z u C beta limlMuHat muSelector selectorBad where
  raw_moments := raw_moments
  pencil_tendsto :=
    weakIV_rawLIMLGeneralizedEigenvaluePair_tendstoInDistribution
      C beta raw_moments hQZZ
  selector := selector

/-- Build the triangular assembly directly from raw moments using the concrete
smallest generalized-Rayleigh root. Positive definiteness of the full
reduced-form error covariance is the nondegeneracy condition that makes
Hansen's limiting Rayleigh problem well posed. -/
theorem WeakIVTriangularAssemblyConditions.of_raw_moments_smallestRoot
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    {C : Matrix l k ℝ} {beta : k → ℝ}
    (raw_moments : WeakIVRawJointMomentConditions μ Z u)
    (hQZZ : IsUnit (popGram μ Z).det)
    (hSigma : (popGram μ u).PosDef) :
    WeakIVTriangularAssemblyConditions
      μ Z u C beta
      (weakIVLocalLIMLSmallestRoot Z u C beta)
      weakIVLIMLSmallestGeneralizedRoot
      weakIVLIMLSelectorBadSet := by
  have hpencil :=
    weakIV_rawLIMLGeneralizedEigenvaluePair_tendstoInDistribution
      C beta raw_moments hQZZ
  apply WeakIVTriangularAssemblyConditions.of_raw_moments
    raw_moments hQZZ
  refine
    { selector_meas := weakIVLIMLSmallestGeneralizedRoot_measurable
      selector_bad_measurable := weakIVLIMLSelectorBadSet_measurable
      selector_bad_null := ?_
      selector_continuous_off := fun p hp =>
        weakIVLIMLSmallestGeneralizedRoot_continuousAt hp
      sample_selector_eq := fun _ _ => rfl
      finite_sample_rayleigh_minimizer_of_regular := ?_
      limit_rayleigh_minimizer := ?_ }
  · rw [Measure.map_apply_of_aemeasurable hpencil.aemeasurable_limit
      weakIVLIMLSelectorBadSet_measurable]
    have hpre :
        (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta) ⁻¹'
            (weakIVLIMLSelectorBadSet (ι := Sum Unit k)) =
          (∅ : Set (EuclideanSpace ℝ (l × Sum Unit k))) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false,
        weakIVLIMLSelectorBadSet, Set.mem_compl_iff]
      simpa only [not_not] using
        (weakIVRawLIMLGeneralizedEigenvalueLimitPair_positiveDenominator
          μ Z u C beta hSigma z)
    rw [hpre, measure_empty]
  · intro m omega
    dsimp only
    intro hp
    have hgood :
        weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega ∈
          weakIVLIMLPositiveDenominatorSet := by
      simpa [weakIVLIMLSelectorBadSet] using hp
    simpa [weakIVLocalLIMLSmallestRoot] using
      (weakIVLIMLSmallestGeneralizedRoot_rayleighMinimizer hgood)
  · intro z
    apply weakIVLIMLSmallestGeneralizedRoot_rayleighMinimizer
    exact weakIVRawLIMLGeneralizedEigenvalueLimitPair_positiveDenominator
      μ Z u C beta hSigma z

omit [DecidableEq k] in
private theorem weakIVTriangularEstimatorMomentAssemblyMap_measurable
    {muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ}
    (hselector : Measurable muSelector) (beta : k → ℝ) :
    Measurable
      (weakIVTriangularEstimatorMomentAssemblyMap beta muSelector) := by
  have hOLS : Measurable
      (fun p : WeakIVRawLIMLPencil k × ℝ => p.1.2 + p.2 • p.1.1) := by
    fun_prop
  have h2SLS : Measurable
      (fun p : WeakIVRawLIMLPencil k × ℝ => p.1.1) := measurable_fst.comp measurable_fst
  have hLIML : Measurable
      (fun p : WeakIVRawLIMLPencil k × ℝ =>
        p.1.1 - muSelector p.1 • p.1.2) := by
    fun_prop
  simpa [weakIVTriangularEstimatorMomentAssemblyMap] using
    (((weakIVRawStructuralMomentPair_continuous beta).measurable.comp hOLS).prodMk
      ((weakIVRawStructuralMomentPair_continuous beta).measurable.comp h2SLS)).prodMk
    ((weakIVRawStructuralMomentPair_continuous beta).measurable.comp hLIML)

omit [DecidableEq k] in
private theorem weakIVTriangularEstimatorMomentAssemblyMap_continuousAt
    {muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ}
    (beta : k → ℝ) (p : WeakIVRawLIMLPencil k × ℝ)
    (hselector : ContinuousAt muSelector p.1) :
    ContinuousAt
      (weakIVTriangularEstimatorMomentAssemblyMap beta muSelector) p := by
  have hOLS : ContinuousAt
      (fun q : WeakIVRawLIMLPencil k × ℝ => q.1.2 + q.2 • q.1.1) p := by
    fun_prop
  have h2SLS : ContinuousAt
      (fun q : WeakIVRawLIMLPencil k × ℝ => q.1.1) p :=
    continuousAt_fst.comp continuousAt_fst
  have hLIML : ContinuousAt
      (fun q : WeakIVRawLIMLPencil k × ℝ =>
        q.1.1 - muSelector q.1 • q.1.2) p := by
    fun_prop
  simpa [weakIVTriangularEstimatorMomentAssemblyMap] using
    (((weakIVRawStructuralMomentPair_continuous beta).continuousAt.comp hOLS).prodMk
      ((weakIVRawStructuralMomentPair_continuous beta).continuousAt.comp h2SLS)).prodMk
    ((weakIVRawStructuralMomentPair_continuous beta).continuousAt.comp hLIML)

private theorem weakIVCenteredStarEstimatorMap_measurable
    (beta : k → ℝ) : Measurable (weakIVCenteredStarEstimatorMap beta) := by
  let f : Matrix k k ℝ × (k → ℝ) → Matrix k k ℝ × (k → ℝ) :=
    fun p => (p.1, p.1 *ᵥ beta + p.2)
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hraw := weakIV_twoSLS_inverse_score_map_measurable.comp hf
  simpa [weakIVCenteredStarEstimatorMap, f] using hraw.sub measurable_const

private theorem weakIVCenteredStarEstimatorMap_continuousAt_of_nonsingular
    (beta : k → ℝ) (p : Matrix k k ℝ × (k → ℝ))
    (hp : IsUnit p.1.det) :
    ContinuousAt (weakIVCenteredStarEstimatorMap beta) p := by
  let f : Matrix k k ℝ × (k → ℝ) → Matrix k k ℝ × (k → ℝ) :=
    fun q => (q.1, q.1 *ᵥ beta + q.2)
  have hf : ContinuousAt f p := by
    dsimp [f]
    fun_prop
  have hraw :=
    (weakIV_twoSLS_inverse_score_continuousAt_of_nonsingular
      (k := k) (f p) hp).comp hf
  simpa [weakIVCenteredStarEstimatorMap, f] using hraw.sub continuousAt_const

private theorem weakIVTriangularEstimatorTotalizationMap_measurable
    (beta : k → ℝ) :
    Measurable (weakIVTriangularEstimatorTotalizationMap beta) := by
  unfold weakIVTriangularEstimatorTotalizationMap
  exact
    (((weakIVCenteredStarEstimatorMap_measurable beta).comp
        (measurable_fst.comp measurable_fst)).prodMk
      ((weakIVCenteredStarEstimatorMap_measurable beta).comp
        (measurable_snd.comp measurable_fst))).prodMk
    ((weakIVCenteredStarEstimatorMap_measurable beta).comp measurable_snd)

private theorem
    weakIVTriangularEstimatorTotalizationMap_continuousAt_of_nonsingular
    (beta : k → ℝ)
    (p : ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) ×
      (Matrix k k ℝ × (k → ℝ)))
    (hOLS : IsUnit p.1.1.1.det) (h2SLS : IsUnit p.1.2.1.det)
    (hLIML : IsUnit p.2.1.det) :
    ContinuousAt (weakIVTriangularEstimatorTotalizationMap beta) p := by
  unfold weakIVTriangularEstimatorTotalizationMap
  have hpOLS : ContinuousAt
      (fun q : ((Matrix k k ℝ × (k → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) × (Matrix k k ℝ × (k → ℝ)) => q.1.1) p := by
    fun_prop
  have hp2SLS : ContinuousAt
      (fun q : ((Matrix k k ℝ × (k → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) × (Matrix k k ℝ × (k → ℝ)) => q.1.2) p := by
    fun_prop
  have hpLIML : ContinuousAt
      (fun q : ((Matrix k k ℝ × (k → ℝ)) ×
          (Matrix k k ℝ × (k → ℝ))) × (Matrix k k ℝ × (k → ℝ)) => q.2) p := by
    fun_prop
  have h1 := (weakIVCenteredStarEstimatorMap_continuousAt_of_nonsingular
    beta p.1.1 hOLS).comp continuousAt_fst |>.comp continuousAt_fst
  have h2 := (weakIVCenteredStarEstimatorMap_continuousAt_of_nonsingular
    beta p.1.2 h2SLS).comp continuousAt_snd |>.comp continuousAt_fst
  have h3 := (weakIVCenteredStarEstimatorMap_continuousAt_of_nonsingular
    beta p.2 hLIML).comp continuousAt_snd
  exact (h1.prodMk h2).prodMk h3

/-- The raw triangular model and generalized-pencil CMT jointly derive the
actual OLS, root-scaled 2SLS, and weak-scaled LIML bread/score limits.

The sample objects in this statement are the literal moment matrices used by
`weakIVLocalOLSBetaStar`, `weakIVLocal2SLSBetaStar`, and
`weakIVLocalLIMLBetaStar`; no estimator convergence is assumed. -/
theorem weakIV_triangular_actual_moments_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    {C : Matrix l k ℝ} {beta : k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ}
    {selectorBad : Set
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ)}
    (h : WeakIVTriangularAssemblyConditions
      μ Z u C beta limlMuHat muSelector selectorBad) :
    TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) =>
        (((sampleGram (weakIVLocalDesign Z u C m omega),
            sampleCrossMoment (weakIVLocalDesign Z u C m omega)
              (weakIVLocalStructuralError u beta m omega)),
          (twoSLSMomentMatrixStar (stackRegressors Z m omega)
              (weakIVLocalDesign Z u C m omega),
            twoSLSMomentVectorStar (stackRegressors Z m omega)
              (weakIVLocalDesign Z u C m omega)
              (weakIVLocalStructuralError u beta m omega))),
          (limlMomentMatrixStar (stackRegressors Z m omega)
              (weakIVLocalDesign Z u C m omega)
              (weakIVLIMLFiniteSampleMu limlMuHat m omega),
            limlMomentVectorStar (stackRegressors Z m omega)
              (weakIVLocalDesign Z u C m omega)
              (weakIVLocalStructuralError u beta m omega)
              (weakIVLIMLFiniteSampleMu limlMuHat m omega))))
      atTop
      (fun z : EuclideanSpace ℝ (l × Sum Unit k) =>
        (((weakIVRawSigma22 (popGram μ u),
            weakIVRawSigma2e (popGram μ u) beta),
          (weakIV2SLSLimitBread (popGram μ Z) C
              (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z)),
            weakIV2SLSLimitScore (popGram μ Z) C
              (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
              (weakIVRawGaussianStructuralScore
                (weakIVRawGaussianMatrix z) beta))),
          (weakIVLIMLLimitBread (popGram μ Z) C
              (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
              (muSelector
                (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z))
              (weakIVRawSigma22 (popGram μ u)),
            weakIVLIMLLimitScore (popGram μ Z) C
              (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
              (weakIVRawGaussianStructuralScore
                (weakIVRawGaussianMatrix z) beta)
              (muSelector
                (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z))
              (weakIVRawSigma2e (popGram μ u) beta))))
      (fun _ => μ)
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0))) := by
  let gaussianLaw := multivariateGaussian 0
    (covMat μ (weakIVRawReducedFormScoreRow Z u 0))
  have hr : TendstoInMeasure μ
      (fun (m : ℕ) (_ : Ω) => (m : ℝ)⁻¹) atTop (fun _ => (0 : ℝ)) :=
    tendstoInMeasure_const_real (μ := μ)
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hstate : TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) =>
        (weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega,
          (m : ℝ)⁻¹))
      atTop
      (fun z =>
        (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z, 0))
      (fun _ => μ) gaussianLaw := by
    simpa [gaussianLaw] using h.pencil_tendsto.prodMk_of_tendstoInMeasure_const
      (fun (m : ℕ) (omega : Ω) =>
        weakIVLocalLIMLGeneralizedEigenvaluePair Z u C beta m omega)
      (fun (m : ℕ) (_ : Ω) => (m : ℝ)⁻¹)
      (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta)
      hr (fun _ => measurable_const.aemeasurable)
  let D : Set (WeakIVRawLIMLPencil k × ℝ) := {p | p.1 ∈ selectorBad}
  have hD_meas : MeasurableSet D := by
    exact measurable_fst h.selector.selector_bad_measurable
  have hD_null :
      (gaussianLaw.map (fun z =>
        (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z, 0))) D = 0 := by
    rw [Measure.map_apply_of_aemeasurable hstate.aemeasurable_limit hD_meas]
    have hbad := h.selector.selector_bad_null
    rw [Measure.map_apply_of_aemeasurable
      h.pencil_tendsto.aemeasurable_limit
      h.selector.selector_bad_measurable] at hbad
    simpa [D] using hbad
  have hcont : ∀ p : WeakIVRawLIMLPencil k × ℝ, p ∉ D →
      ContinuousAt
        (weakIVTriangularEstimatorMomentAssemblyMap beta muSelector) p := by
    intro p hp
    exact weakIVTriangularEstimatorMomentAssemblyMap_continuousAt beta p
      (h.selector.selector_continuous_off p.1 (by simpa [D] using hp))
  have hmap := tendstoInDistribution_ae_continuous_comp hstate
    (weakIVTriangularEstimatorMomentAssemblyMap_measurable
      h.selector.selector_meas beta)
    hD_null hcont
  refine TendstoInDistribution.congr ?_ ?_ hmap
  · intro m
    exact ae_of_all μ fun omega =>
      (weakIVTriangularEstimatorMomentAssemblyMap_sample
        Z u C beta limlMuHat muSelector h.selector.sample_selector_eq m omega)
  · exact ae_of_all gaussianLaw fun z =>
      (weakIVTriangularEstimatorMomentAssemblyMap_limit
        μ Z u C beta muSelector z)

/-- Joint totalization CMT for the three actual triangular-array Star
estimators in Hansen Theorem 12.18.

The assumptions after the raw assembly are exactly the omitted nondegeneracy
conditions needed by the inverse maps: nonsingular `Sigma22`, and almost-sure
nonsingularity of the random 2SLS and LIML limiting breads. -/
theorem weakIV_triangular_estimators_minus_beta_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    {C : Matrix l k ℝ} {beta : k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ}
    {selectorBad : Set
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ)}
    (h : WeakIVTriangularAssemblyConditions
      μ Z u C beta limlMuHat muSelector selectorBad)
    (hSigma22 : IsUnit (weakIVRawSigma22 (popGram μ u)).det)
    (h2SLSBread :
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0)))
        {z | ¬ IsUnit
          (weakIV2SLSLimitBread (popGram μ Z) C
            (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))).det} = 0)
    (hLIMLBread :
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0)))
        {z | ¬ IsUnit
          (weakIVLIMLLimitBread (popGram μ Z) C
            (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
            (muSelector
              (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z))
            (weakIVRawSigma22 (popGram μ u))).det} = 0) :
    TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) =>
        ((weakIVLocalOLSBetaStar Z u C beta m omega - beta,
            weakIVLocal2SLSBetaStar Z u C beta m omega - beta),
          weakIVLocalLIMLBetaStar Z u C beta limlMuHat m omega - beta))
      atTop
      (fun z : EuclideanSpace ℝ (l × Sum Unit k) =>
        ((weakIVOLSBias (weakIVRawSigma22 (popGram μ u))
            (weakIVRawSigma2e (popGram μ u) beta),
          weakIV2SLSBias (popGram μ Z) C
            (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
            (weakIVRawGaussianStructuralScore
              (weakIVRawGaussianMatrix z) beta)),
          weakIVLIMLBias (popGram μ Z) C
            (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
            (weakIVRawGaussianStructuralScore
              (weakIVRawGaussianMatrix z) beta)
            (muSelector
              (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z))
            (weakIVRawSigma22 (popGram μ u))
            (weakIVRawSigma2e (popGram μ u) beta)))
      (fun _ => μ)
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0))) := by
  let gaussianLaw := multivariateGaussian 0
    (covMat μ (weakIVRawReducedFormScoreRow Z u 0))
  let limitMoments := fun z : EuclideanSpace ℝ (l × Sum Unit k) =>
    (((weakIVRawSigma22 (popGram μ u),
        weakIVRawSigma2e (popGram μ u) beta),
      (weakIV2SLSLimitBread (popGram μ Z) C
          (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z)),
        weakIV2SLSLimitScore (popGram μ Z) C
          (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
          (weakIVRawGaussianStructuralScore
            (weakIVRawGaussianMatrix z) beta))),
      (weakIVLIMLLimitBread (popGram μ Z) C
          (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
          (muSelector
            (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z))
          (weakIVRawSigma22 (popGram μ u)),
        weakIVLIMLLimitScore (popGram μ Z) C
          (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
          (weakIVRawGaussianStructuralScore
            (weakIVRawGaussianMatrix z) beta)
          (muSelector
            (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z))
          (weakIVRawSigma2e (popGram μ u) beta)))
  have hmoments := weakIV_triangular_actual_moments_tendstoInDistribution h
  let DOLS : Set
      (((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) ×
        (Matrix k k ℝ × (k → ℝ))) := {p | ¬ IsUnit p.1.1.1.det}
  let D2SLS : Set
      (((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) ×
        (Matrix k k ℝ × (k → ℝ))) := {p | ¬ IsUnit p.1.2.1.det}
  let DLIML : Set
      (((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) ×
        (Matrix k k ℝ × (k → ℝ))) := {p | ¬ IsUnit p.2.1.det}
  let D := (DOLS ∪ D2SLS) ∪ DLIML
  have hDOLS_meas : MeasurableSet DOLS := by
    change MeasurableSet
      ((fun p :
          ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) ×
            (Matrix k k ℝ × (k → ℝ)) => p.1.1) ⁻¹'
        {p : Matrix k k ℝ × (k → ℝ) | ¬ IsUnit p.1.det})
    exact (measurable_fst.comp measurable_fst)
      (weakIV_twoSLS_singular_pair_measurable (k := k))
  have hD2SLS_meas : MeasurableSet D2SLS := by
    change MeasurableSet
      ((fun p :
          ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) ×
            (Matrix k k ℝ × (k → ℝ)) => p.1.2) ⁻¹'
        {p : Matrix k k ℝ × (k → ℝ) | ¬ IsUnit p.1.det})
    exact (measurable_snd.comp measurable_fst)
      (weakIV_twoSLS_singular_pair_measurable (k := k))
  have hDLIML_meas : MeasurableSet DLIML := by
    change MeasurableSet
      ((fun p :
          ((Matrix k k ℝ × (k → ℝ)) × (Matrix k k ℝ × (k → ℝ))) ×
            (Matrix k k ℝ × (k → ℝ)) => p.2) ⁻¹'
        {p : Matrix k k ℝ × (k → ℝ) | ¬ IsUnit p.1.det})
    exact measurable_snd
      (weakIV_twoSLS_singular_pair_measurable (k := k))
  have hD_meas : MeasurableSet D :=
    (hDOLS_meas.union hD2SLS_meas).union hDLIML_meas
  have hDOLS_null : (gaussianLaw.map limitMoments) DOLS = 0 := by
    rw [Measure.map_apply_of_aemeasurable hmoments.aemeasurable_limit hDOLS_meas]
    have hempty : limitMoments ⁻¹' DOLS = ∅ := by
      ext z
      simp only [Set.mem_preimage, DOLS, Set.mem_setOf_eq, limitMoments,
        Set.mem_empty_iff_false, iff_false]
      exact fun hnot => hnot hSigma22
    rw [hempty, measure_empty]
  have hD2SLS_null : (gaussianLaw.map limitMoments) D2SLS = 0 := by
    rw [Measure.map_apply_of_aemeasurable hmoments.aemeasurable_limit hD2SLS_meas]
    simpa [gaussianLaw, limitMoments, D2SLS] using h2SLSBread
  have hDLIML_null : (gaussianLaw.map limitMoments) DLIML = 0 := by
    rw [Measure.map_apply_of_aemeasurable hmoments.aemeasurable_limit hDLIML_meas]
    simpa [gaussianLaw, limitMoments, DLIML] using hLIMLBread
  have hD_null : (gaussianLaw.map limitMoments) D = 0 := by
    simpa [D] using
      measure_union_null (measure_union_null hDOLS_null hD2SLS_null) hDLIML_null
  have hcont : ∀ p, p ∉ D →
      ContinuousAt (weakIVTriangularEstimatorTotalizationMap beta) p := by
    intro p hp
    have hpOLS : p ∉ DOLS := fun hpOLS => hp (Or.inl (Or.inl hpOLS))
    have hp2SLS : p ∉ D2SLS := fun hp2SLS => hp (Or.inl (Or.inr hp2SLS))
    have hpLIML : p ∉ DLIML := fun hpLIML => hp (Or.inr hpLIML)
    exact
      weakIVTriangularEstimatorTotalizationMap_continuousAt_of_nonsingular
        beta p (by simpa [DOLS] using hpOLS) (by simpa [D2SLS] using hp2SLS)
          (by simpa [DLIML] using hpLIML)
  have hmap := tendstoInDistribution_ae_continuous_comp
    (Z := limitMoments) hmoments
    (weakIVTriangularEstimatorTotalizationMap_measurable beta)
    hD_null hcont
  refine TendstoInDistribution.congr ?_ ?_ hmap
  · intro m
    exact ae_of_all μ fun omega =>
      (weakIVTriangularEstimatorTotalizationMap_sample
        Z u C beta limlMuHat m omega)
  · have h2ae : ∀ᵐ z ∂gaussianLaw, IsUnit
        (weakIV2SLSLimitBread (popGram μ Z) C
          (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))).det := by
      simpa [gaussianLaw, ae_iff] using h2SLSBread
    have hLae : ∀ᵐ z ∂gaussianLaw, IsUnit
        (weakIVLIMLLimitBread (popGram μ Z) C
          (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
          (muSelector
            (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z))
          (weakIVRawSigma22 (popGram μ u))).det := by
      simpa [gaussianLaw, ae_iff] using hLIMLBread
    filter_upwards [h2ae, hLae] with z h2 hL
    rw [weakIVTriangularEstimatorTotalizationMap]
    rw [weakIVCenteredStarEstimatorMap_eq_inverse_score_of_nonsingular
      beta _ hSigma22]
    rw [weakIVCenteredStarEstimatorMap_eq_inverse_score_of_nonsingular
      beta _ h2]
    rw [weakIVCenteredStarEstimatorMap_eq_inverse_score_of_nonsingular
      beta _ hL]
    simp [limitMoments, weakIVOLSBias,
      weakIV2SLSBias_eq_limitBread_inv_mul_score,
      weakIVLIMLBias_eq_limitBread_inv_mul_score]

/-- Hansen Theorem 12.18 at the literal triangular-array boundary for any
certified generalized-root selector and the mathematically necessary
limiting-bread nondegeneracy assumptions.

Unlike the historical fixed-prefix endpoints, every estimator here is the
actual estimator computed from
`X_{m,i} = m^{-1/2} C' Z_i + u_{2i}`.  The raw iid moment package derives all
CLT/WLLN and sample-rank inputs; no estimator convergence is assumed. -/
theorem weakIV_theorem12_18_triangular_estimators
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    {C : Matrix l k ℝ} {beta : k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ}
    {selectorBad : Set
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ)}
    (h : WeakIVTriangularAssemblyConditions
      μ Z u C beta limlMuHat muSelector selectorBad)
    (hSigma22 : IsUnit (weakIVRawSigma22 (popGram μ u)).det)
    (h2SLSBread :
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0)))
        {z | ¬ IsUnit
          (weakIV2SLSLimitBread (popGram μ Z) C
            (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))).det} = 0)
    (hLIMLBread :
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0)))
        {z | ¬ IsUnit
          (weakIVLIMLLimitBread (popGram μ Z) C
            (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
            (muSelector
              (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z))
            (weakIVRawSigma22 (popGram μ u))).det} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) (omega : Ω) =>
        weakIVLocalOLSBetaStar Z u C beta m omega - beta)
      atTop
      (fun _ => weakIVOLSBias (weakIVRawSigma22 (popGram μ u))
        (weakIVRawSigma2e (popGram μ u) beta)) ∧
    TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) =>
        weakIVLocal2SLSBetaStar Z u C beta m omega - beta)
      atTop
      (fun z : EuclideanSpace ℝ (l × Sum Unit k) =>
        weakIV2SLSBias (popGram μ Z) C
          (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
          (weakIVRawGaussianStructuralScore
            (weakIVRawGaussianMatrix z) beta))
      (fun _ => μ)
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0))) ∧
    TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) =>
        weakIVLocalLIMLBetaStar Z u C beta limlMuHat m omega - beta)
      atTop
      (fun z : EuclideanSpace ℝ (l × Sum Unit k) =>
        weakIVLIMLBias (popGram μ Z) C
          (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
          (weakIVRawGaussianStructuralScore
            (weakIVRawGaussianMatrix z) beta)
          (muSelector
            (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z))
          (weakIVRawSigma22 (popGram μ u))
          (weakIVRawSigma2e (popGram μ u) beta))
      (fun _ => μ)
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0))) ∧
    (∀ z,
      let p := weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z
      LIMLRayleighMinimizer p.1 p.2 (muSelector p)) := by
  have hjoint := weakIV_triangular_estimators_minus_beta_tendstoInDistribution
    h hSigma22 h2SLSBread hLIMLBread
  have hOLSdist := hjoint.continuous_comp
    (by fun_prop : Continuous
      (fun p : ((k → ℝ) × (k → ℝ)) × (k → ℝ) => p.1.1))
  have hOLSdist_const : TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) =>
        weakIVLocalOLSBetaStar Z u C beta m omega - beta)
      atTop
      (fun _ : EuclideanSpace ℝ (l × Sum Unit k) =>
        weakIVOLSBias (weakIVRawSigma22 (popGram μ u))
          (weakIVRawSigma2e (popGram μ u) beta))
      (fun _ => μ)
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0))) := by
    simpa [Function.comp_def] using hOLSdist
  have hOLS := weakIV_tendstoInMeasure_of_tendstoInDistribution_const
    (μ := μ)
    (ν := multivariateGaussian 0
      (covMat μ (weakIVRawReducedFormScoreRow Z u 0)))
    hOLSdist_const
  have h2SLS := hjoint.continuous_comp
    (by fun_prop : Continuous
      (fun p : ((k → ℝ) × (k → ℝ)) × (k → ℝ) => p.1.2))
  have hLIML := hjoint.continuous_comp
    (by fun_prop : Continuous
      (fun p : ((k → ℝ) × (k → ℝ)) × (k → ℝ) => p.2))
  refine ⟨hOLS, ?_, ?_, h.selector.limit_rayleigh_minimizer⟩
  · simpa [Function.comp_def] using h2SLS
  · simpa [Function.comp_def] using hLIML

/-- Hansen Theorem 12.18 directly from raw iid moments and the concrete
smallest generalized-Rayleigh root. No selector convergence, estimator
convergence, or Rayleigh minimizer is assumed. The remaining premises are the
population rank conditions needed by the totalized inverse maps. -/
theorem weakIV_theorem12_18_triangular_estimators_of_raw_moments
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    {C : Matrix l k ℝ} {beta : k → ℝ}
    (raw_moments : WeakIVRawJointMomentConditions μ Z u)
    (hQZZ : IsUnit (popGram μ Z).det)
    (hSigma : (popGram μ u).PosDef)
    (h2SLSBread :
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0)))
        {z | ¬ IsUnit
          (weakIV2SLSLimitBread (popGram μ Z) C
            (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))).det} = 0)
    (hLIMLBread :
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0)))
        {z | ¬ IsUnit
          (weakIVLIMLLimitBread (popGram μ Z) C
            (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
            (weakIVRawLIMLSmallestRoot μ Z u C beta z)
            (weakIVRawSigma22 (popGram μ u))).det} = 0) :
    TendstoInMeasure μ
      (fun (m : ℕ) (omega : Ω) =>
        weakIVLocalOLSBetaStar Z u C beta m omega - beta)
      atTop
      (fun _ => weakIVOLSBias (weakIVRawSigma22 (popGram μ u))
        (weakIVRawSigma2e (popGram μ u) beta)) ∧
    TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) =>
        weakIVLocal2SLSBetaStar Z u C beta m omega - beta)
      atTop
      (fun z : EuclideanSpace ℝ (l × Sum Unit k) =>
        weakIV2SLSBias (popGram μ Z) C
          (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
          (weakIVRawGaussianStructuralScore
            (weakIVRawGaussianMatrix z) beta))
      (fun _ => μ)
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0))) ∧
    TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) =>
        weakIVLocalLIMLBetaStar Z u C beta
          (weakIVLocalLIMLSmallestRoot Z u C beta) m omega - beta)
      atTop
      (fun z : EuclideanSpace ℝ (l × Sum Unit k) =>
        weakIVLIMLBias (popGram μ Z) C
          (weakIVRawGaussianFirstStage (weakIVRawGaussianMatrix z))
          (weakIVRawGaussianStructuralScore
            (weakIVRawGaussianMatrix z) beta)
          (weakIVRawLIMLSmallestRoot μ Z u C beta z)
          (weakIVRawSigma22 (popGram μ u))
          (weakIVRawSigma2e (popGram μ u) beta))
      (fun _ => μ)
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0))) ∧
    (∀ z,
      let p := weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z
      LIMLRayleighMinimizer p.1 p.2
        (weakIVRawLIMLSmallestRoot μ Z u C beta z)) := by
  have hassembly :=
    WeakIVTriangularAssemblyConditions.of_raw_moments_smallestRoot
      (C := C) (beta := beta) raw_moments hQZZ hSigma
  have hSigma22 : IsUnit (weakIVRawSigma22 (popGram μ u)).det :=
    isUnit_iff_ne_zero.mpr (weakIVRawSigma22_posDef hSigma).det_pos.ne'
  simpa [weakIVRawLIMLSmallestRoot] using
    (weakIV_theorem12_18_triangular_estimators
      hassembly hSigma22 h2SLSBread hLIMLBread)

/-- Raw-support endpoint at the literal triangular boundary.  It exposes the
joint Gram/score assembly and scaled generalized root used by
`weakIV_theorem12_18_triangular_estimators`. -/
theorem weakIV_theorem12_18_triangular_raw_assembly
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    {C : Matrix l k ℝ} {beta : k → ℝ}
    {limlMuHat : ℕ → Ω → ℝ}
    {muSelector :
      Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ → ℝ}
    {selectorBad : Set
      (Matrix (Sum Unit k) (Sum Unit k) ℝ ×
        Matrix (Sum Unit k) (Sum Unit k) ℝ)}
    (h : WeakIVTriangularAssemblyConditions
      μ Z u C beta limlMuHat muSelector selectorBad) :
    TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) =>
        weakIVRawRootOLSAssemblyMap C beta
          (weakIVRawRootReducedFormScore Z u m omega,
            (sampleGram (stackRegressors Z m omega),
              sampleGram (stackRegressors u m omega))))
      atTop
      (fun z : EuclideanSpace ℝ (l × Sum Unit k) =>
        weakIVRawRootOLSAssemblyMap C beta
          (weakIVRawGaussianMatrix z, (popGram μ Z, popGram μ u)))
      (fun _ => μ)
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0))) ∧
    TendstoInDistribution
      (fun (m : ℕ) (omega : Ω) => limlMuHat m omega)
      atTop
      (fun z => muSelector
        (weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z))
      (fun _ => μ)
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0))) ∧
    (∀ z,
      let p := weakIVRawLIMLGeneralizedEigenvalueLimitPair μ Z u C beta z
      LIMLRayleighMinimizer p.1 p.2 (muSelector p)) := by
  refine ⟨weakIV_rawRootOLSAssembly_tendstoInDistribution C beta h.raw_moments, ?_,
    h.selector.limit_rayleigh_minimizer⟩
  have hmu := tendstoInDistribution_ae_continuous_comp
    h.pencil_tendsto h.selector.selector_meas h.selector.selector_bad_null
      h.selector.selector_continuous_off
  refine TendstoInDistribution.congr ?_ EventuallyEq.rfl hmu
  intro m
  exact ae_of_all μ (fun omega => by
    simpa [Function.comp_def] using (h.selector.sample_selector_eq m omega).symm)

/-- The scaled finite-sample LIML root converges to Hansen's concrete `mu*`
directly from the raw iid moment assumptions. -/
theorem weakIVLocalLIMLSmallestRoot_tendstoInDistribution
    {Z : ℕ → Ω → l → ℝ} {u : ℕ → Ω → Sum Unit k → ℝ}
    {C : Matrix l k ℝ} {beta : k → ℝ}
    (raw_moments : WeakIVRawJointMomentConditions μ Z u)
    (hQZZ : IsUnit (popGram μ Z).det)
    (hSigma : (popGram μ u).PosDef) :
    TendstoInDistribution
      (weakIVLocalLIMLSmallestRoot Z u C beta)
      atTop
      (weakIVRawLIMLSmallestRoot μ Z u C beta)
      (fun _ => μ)
      (multivariateGaussian 0
        (covMat μ (weakIVRawReducedFormScoreRow Z u 0))) := by
  have hassembly :=
    WeakIVTriangularAssemblyConditions.of_raw_moments_smallestRoot
      (C := C) (beta := beta) raw_moments hQZZ hSigma
  have hroot := (weakIV_theorem12_18_triangular_raw_assembly hassembly).2.1
  simpa [weakIVRawLIMLSmallestRoot] using hroot

end Asymptotics

end HansenEconometrics
