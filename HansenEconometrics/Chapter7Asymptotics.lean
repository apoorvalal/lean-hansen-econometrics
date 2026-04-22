import Mathlib
import HansenEconometrics.Basic
import HansenEconometrics.Chapter3LeastSquaresAlgebra
import HansenEconometrics.Chapter4LeastSquaresRegression
import HansenEconometrics.AsymptoticUtils

/-!
# Chapter 7 — Asymptotic Theory (Phase 1 deterministic scaffold)

This file lays the deterministic groundwork for Hansen's asymptotic chapter.
It introduces the finite-sample empirical moment objects

* `sampleGram X        = Xᵀ X / n`   — sample analogue of `Q := E[X Xᵀ]`
* `sampleCrossMoment X e = (Xᵀ e) / n` — sample analogue of `E[X e]`

and proves the algebraic identity that is the deterministic engine behind
Hansen Theorem 7.1 (Consistency of Least Squares):

  β̂ₙ - β = Q̂ₙ⁻¹ *ᵥ g̑ₙ.

No probabilistic infrastructure is imported here beyond what Chapter 4 already
uses. The iid-sample bridge, WLLN wrapper, and continuous-mapping steps that
upgrade this identity into `β̂ₙ →ₚ β` live in a separate module and are
scheduled for Phase 2.
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

end Stacking

section Assumption71

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix.Norms.Elementwise Function

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

end Assumption71

end HansenEconometrics
