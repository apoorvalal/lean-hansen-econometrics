import Mathlib
import HansenEconometrics.Basic
import HansenEconometrics.Chapter3LeastSquaresAlgebra
import HansenEconometrics.Chapter4LeastSquaresRegression
import HansenEconometrics.AsymptoticUtils

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

## Phase 3 — Probabilistic consistency (Theorem 7.1)

`SampleAssumption71` packages Hansen Assumption 7.1 (iid regressors and
errors with finite second moments, invertible population Gram `Q`, and
orthogonality `𝔼[e X] = 0`). The chain of convergences from Theorem 7.1 is
then assembled:

* `sampleGram_stackRegressors_tendstoInMeasure_popGram` — `Q̂ₙ →ₚ Q` via WLLN.
* `sampleCrossMoment_stackRegressors_stackErrors_tendstoInMeasure_zero` —
  `ĝₙ(e) →ₚ 0` via WLLN + orthogonality.
* `sampleGramInv_mulVec_sampleCrossMoment_e_tendstoInMeasure_zero` —
  `Q̂ₙ⁻¹ *ᵥ ĝₙ(e) →ₚ 0`, combining the previous two with the matrix-inverse
  CMT and the mulVec CMT from `AsymptoticUtils`.

This last theorem is the deterministic core of Theorem 7.1: the Phase 1
identity `β̂ₙ − β = Q̂ₙ⁻¹ *ᵥ ĝₙ` is valid on the event `{Q̂ₙ invertible}`,
and the RHS converges in probability to `0`. The remaining step to the
textbook statement `β̂ₙ →ₚ β` is a probabilistic invertibility argument
(det-CMT applied to `Q̂ₙ →ₚ Q` plus a triangle bound on the complement),
documented in the crosswalk [notes/ch07/latex_links.md](../notes/ch07/latex_links.md)
as pending.

See also:
- [`AsymptoticUtils.lean`](./AsymptoticUtils.lean) — WLLN wrapper, CMT for
  convergence in measure, matrix-inverse and mulVec CMTs.
- [`Chapter3LeastSquaresAlgebra.lean`](./Chapter3LeastSquaresAlgebra.lean) —
  `olsBeta` and its total version `olsBetaStar`.
- [notes/ch07/latex_links.md](../notes/ch07/latex_links.md) — LaTeX/Lean crosswalk.
-/

open scoped Matrix

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

/-- Hansen Assumption 7.1: iid regressor/error sequence with a finite nonsingular
population Gram matrix `Q := 𝔼[X Xᵀ]` and orthogonality `𝔼[X e] = 0`. -/
structure SampleAssumption71 (μ : Measure Ω) [IsFiniteMeasure μ]
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

/-- **Hansen WLLN for the sample Gram.** Under Assumption 7.1, the sample Gram
matrix of the stacked design converges in probability to the population Gram `Q`. -/
theorem sampleGram_stackRegressors_tendstoInMeasure_popGram
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleAssumption71 μ X e) :
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

/-- **Hansen WLLN for the sample cross moment.** Under Assumption 7.1, the sample
cross moment `ĝₙ = n⁻¹ ∑ eᵢ Xᵢ` of the stacked design converges in probability to
`0`, since the population cross moment `𝔼[e X] = 0` by the orthogonality axiom. -/
theorem sampleCrossMoment_stackRegressors_stackErrors_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleAssumption71 μ X e) :
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

/-- **Hansen Theorem 7.1 core — convergence of the OLS-error transform.**
Under Assumption 7.1, the sequence `Q̂ₙ⁻¹ *ᵥ ĝₙ(e)` — which is the deterministic
RHS of the Phase 1 OLS-error identity `β̂ₙ − β = Q̂ₙ⁻¹ *ᵥ ĝₙ(e)` (valid on the
event `{Q̂ₙ invertible}`) — converges in probability to `0`.

Proof chain:
* Task 9: `Q̂ₙ →ₚ Q`.
* Task 7: composed with Task 9 and `h.Q_nonsing`, this gives `Q̂ₙ⁻¹ →ₚ Q⁻¹`.
* Task 10: `ĝₙ(e) →ₚ 0`.
* `tendstoInMeasure_mulVec` joins these to `Q̂ₙ⁻¹ *ᵥ ĝₙ(e) →ₚ Q⁻¹ *ᵥ 0 = 0`.

The remaining step to close the textbook Theorem 7.1 (`olsBetaStar →ₚ β`) is a
probabilistic invertibility argument: by CMT on `det`, `(Q̂ₙ).det →ₚ Q.det ≠ 0`,
so the event `{ω : Q̂ₙ(ω) is singular}` has measure → 0. On its complement, the
Phase 1 identity applies; off it, measure shrinks. That step is mechanical but
verbose and is left as a follow-up. -/
theorem sampleGramInv_mulVec_sampleCrossMoment_e_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleAssumption71 μ X e) :
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
Under Assumption 7.1, `μ {ω | Q̂ₙ(ω) is singular} → 0`.

Proof chain:
* Task 9: `Q̂ₙ →ₚ Q`.
* CMT on `Matrix.det` (continuous): `det Q̂ₙ →ₚ det Q`.
* `det Q ≠ 0` by `h.Q_nonsing`, so `ε := |det Q|/2 > 0`.
* On the singular event, `det Q̂ₙ(ω) = 0`, so `edist 0 (det Q) = |det Q| ≥ ε`.
* Monotonicity: `μ {singular} ≤ μ {|det Q̂ₙ − det Q| ≥ ε} → 0`. -/
theorem measure_sampleGram_singular_tendsto_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleAssumption71 μ X e) :
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

/-- **Residual convergence in probability.** Under Assumption 7.1 and the linear
model `yᵢ = Xᵢ·β + eᵢ`, the residual
`β̂ₙ − β − Q̂ₙ⁻¹ *ᵥ ĝₙ(e)` converges to `0` in probability.

On the event `{Q̂ₙ invertible}`, this residual is identically `0` by
`olsBetaStar_sub_identity` + `nonsing_inv_mul`. The complement event has
vanishing measure by `measure_sampleGram_singular_tendsto_zero` (F4). -/
theorem residual_tendstoInMeasure_zero
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleAssumption71 μ X e)
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

/-- **Hansen Theorem 7.1 — Consistency of Least Squares.**
Under Assumption 7.1 and the linear model `yᵢ = Xᵢ·β + eᵢ`, the total OLS
estimator `β̂*ₙ := (Xᵀ X)⁺ Xᵀ y` (using `Matrix.nonsingInv`) converges in
probability to `β`.

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
    (h : SampleAssumption71 μ X e)
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

end HansenEconometrics
