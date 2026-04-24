import Mathlib
import HansenEconometrics.Basic
import HansenEconometrics.LinearAlgebraUtils
import HansenEconometrics.Chapter3LeastSquaresAlgebra
import HansenEconometrics.Chapter4LeastSquaresRegression
import HansenEconometrics.AsymptoticUtils
import HansenEconometrics.ProbabilityUtils

/-!
# Chapter 7 — Asymptotic Theory

This file formalizes Hansen's Chapter 7 (Asymptotic Theory for Least Squares)
in three layers:

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

This is the current Lean version of the beginning of Chapter 7. A separate
textbook-facing theorem for ordinary `olsBeta` still needs an interface for
handling the high-probability nonsingularity event.

## Phase 4 — First CLT bridge

`SampleCLTAssumption72` strengthens the moment-level consistency assumptions
with full independence of the score vectors `eᵢXᵢ` and square integrability of
all scalar projections. The theorem
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
`oₚ(1)`, while
`scoreProjection_olsBetaStar_tendstoInDistribution_gaussian_of_inverseGap`
reduces that remainder to the inverse-gap condition. Together these form the
Cramér-Wold/Slutsky-facing layer needed for Hansen's asymptotic-normality theorem.

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

/-- The population Gram matrix `Q := 𝔼[X Xᵀ]`. -/
noncomputable def popGram (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) : Matrix k k ℝ :=
  μ[fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)]

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

end Assumption71

section Assumption72

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.Elementwise Function Topology ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {k : Type*} [Fintype k] [DecidableEq k]

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

omit [DecidableEq k] in
/-- Move a fixed matrix multiplication from the left side of a dot product to the right side. -/
private theorem mulVec_dotProduct_right (M : Matrix k k ℝ) (v a : k → ℝ) :
    (M *ᵥ v) ⬝ᵥ a = v ⬝ᵥ (Mᵀ *ᵥ a) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose, dotProduct_comm]

/-- **Scalar-projection CLT for Hansen's score.**

For every fixed vector `a`, the projected score sum
`(1 / √n) ∑_{i<n} (eᵢXᵢ)·a` converges in distribution to the Gaussian with the
matching scalar variance. This is the one-dimensional CLT supplied by Mathlib,
specialized to the score projections that appear in OLS asymptotic normality. -/
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

/-- **CLT for scalar projections of the scaled sample score.**

This is the same CLT as `scoreProjection_sum_tendstoInDistribution_gaussian`,
rewritten in Hansen's notation as `√n · ĝₙ(e)` where
`ĝₙ(e) = n⁻¹∑ eᵢXᵢ`. -/
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

/-- **Conditional scalar-projection OLS CLT for the totalized estimator.**
Once the scalar Slutsky remainder
`√n(β̂*ₙ - β)·a - √n(Q⁻¹ ĝₙ(e))·a` is known to be `oₚ(1)`, the fixed-`Q⁻¹`
score CLT transfers to the scalar projection of the totalized OLS estimator.

The deterministic roadmap above reduces this remainder to the scaled residual
plus the random-inverse gap; the residual is already controlled, so the true
remaining mathematical target is the inverse-gap/tightness step. -/
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
and Mathlib's Slutsky theorem. The remaining non-conditional task for Hansen
Theorem 7.3 is proving the inverse-gap hypothesis itself from tightness of the
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

end Assumption72

end HansenEconometrics
