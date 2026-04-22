# Ch 7 Phase 3: OLS Consistency (β̂ₙ →ₚ β) — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal.** Formalize Hansen Theorem 7.1 (consistency of least squares, `β̂ₙ →ₚ β` under
Assumption 7.1) by transporting the Phase-1 deterministic identity
`olsBeta_sub_eq_sampleGram_inv_mulVec_sampleCrossMoment` to the asymptotic limit via the
Phase-2 WLLN/CMT utilities. β̂ₙ is the honest OLS estimator on an explicit
`Matrix (Fin n) k ℝ` stacking of an iid regressor sequence — not a re-cooked sum-form
expression.

**Architecture.** Three layers.

1. **Algebraic stacking (no probability).** `stackRegressors`, `stackErrors`, `stackOutcomes`
   plus sum-form congruence lemmas that rewrite `sampleGram` and `sampleCrossMoment` of the
   stacked design in terms of `∑ i, vecMulVec (Xᵢ) (Xᵢ)` and `∑ i, eᵢ • Xᵢ`. Pure matrix
   algebra; proved with `Matrix.ext` + `Matrix.mul_apply` + `Matrix.vecMulVec_apply`.
2. **Asymptotic matrix machinery.** Invertibility-persistence and a CMT variant for
   matrix inversion valid when the limit is nonsingular. Lives in `AsymptoticUtils.lean`
   alongside the existing `tendstoInMeasure_continuous_comp` / `tendstoInMeasure_pi` /
   `tendstoInMeasure_wlln`.
3. **Glue.** Package Assumption 7.1 as a structure, apply WLLN coordinatewise via
   `tendstoInMeasure_pi` to get `sampleGram →ₚ Q` and `sampleCrossMoment →ₚ 0`, then compose
   with the matrix-inverse CMT + `mulVec` CMT and the B-identity.

**Tech Stack.** Lean 4, Mathlib. Key pieces relied on: `Matrix.vecMulVec` / `vecMulVec_apply`
(`Mathlib/Data/Matrix/Mul.lean:616`), `Matrix.nonsingInv` for total inversion,
`MeasureTheory.TendstoInMeasure`, `ProbabilityTheory.strong_law_ae`, the existing
`Chapter7Asymptotics` and `AsymptoticUtils` scaffolds.

**Design choices up front.**

- **Total OLS via `olsBetaStar`.** The existing `olsBeta` (`Chapter3LeastSquaresAlgebra.lean:20`)
  needs `[Invertible (Xᵀ * X)]` and so is not definable at each ω without a typeclass.
  We introduce `olsBetaStar X y := (Xᵀ * X)⁻¹ *ᵥ (Xᵀ *ᵥ y)` using Mathlib's `nonsingInv`,
  prove `olsBetaStar = olsBeta` when invertible, and state Theorem 7.1 in terms of
  `olsBetaStar`. This avoids event restrictions in the statement and lets the convergence
  claim be a clean `TendstoInMeasure`.
- **Use the X·e cross moment, not X·y.** The B-identity hands us
  `sampleCrossMoment X e` directly. Under `E[X e] = 0` the limit is zero — the cleanest
  target for WLLN + CMT.
- **`Fin n`-indexed stacking.** `stackRegressors X n ω : Matrix (Fin n) k ℝ`. The existing
  `sampleGram` is `Fintype n`-generic, so specialization is free. The ℕ-indexed WLLN sum is
  bridged by `Fin.sum_univ_eq_sum_range`.
- **Assumption 7.1 as a structure.** Pack iid + integrability + `Q` invertible +
  orthogonality once so downstream statements stay readable.

**File structure.**

- Extend `HansenEconometrics/Chapter3LeastSquaresAlgebra.lean` — add `olsBetaStar` and the
  agreement lemma. One definition + one lemma; no new file.
- Extend `HansenEconometrics/AsymptoticUtils.lean` — matrix inversion CMT and invertibility
  persistence. Stays in the existing CMT section.
- Extend `HansenEconometrics/Chapter7Asymptotics.lean` — stacking primitives, congruence
  lemmas, Assumption 7.1 structure, Theorem 7.1.
- New file `notes/ch07/latex_links.md` is **not** part of this plan; crosswalk update is a
  follow-up per the project docs policy.

Throughout this plan, "TDD step" means **write the theorem signature with `sorry`, run
`lake build` to confirm it typechecks, then fill in the proof**. That is the Lean analogue
of writing a failing test before the implementation.

---

## Task 1: `olsBetaStar` — total OLS via Mathlib `nonsingInv`

**Files:**
- Modify: `HansenEconometrics/Chapter3LeastSquaresAlgebra.lean` (add after the existing
  `olsBeta` block, around line 25)

- [ ] **Step 1: Write the definition signature with `sorry`**

```lean
/-- Total version of `olsBeta`: uses `Matrix.nonsingInv` so it is defined on *every*
design matrix, agreeing with `olsBeta` when `Xᵀ * X` is invertible and returning `0`
otherwise. Required for the Chapter 7 stochastic story, where the invertibility of
`Xᵀ * X` holds only a.s., not by typeclass. -/
noncomputable def olsBetaStar (X : Matrix n k ℝ) (y : n → ℝ) : k → ℝ :=
  (Xᵀ * X)⁻¹ *ᵥ (Xᵀ *ᵥ y)
```

- [ ] **Step 2: Typecheck**

Run: `lake build HansenEconometrics.Chapter3LeastSquaresAlgebra`
Expected: builds cleanly. If `(Xᵀ * X)⁻¹` fails to elaborate, import
`Mathlib.LinearAlgebra.Matrix.NonsingularInverse` explicitly.

- [ ] **Step 3: State the agreement lemma with `sorry`**

```lean
theorem olsBetaStar_eq_olsBeta
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    olsBetaStar X y = olsBeta X y := by
  sorry
```

- [ ] **Step 4: Prove it**

Note: `olsBeta` (`Chapter3LeastSquaresAlgebra.lean:20`) uses `⅟(Xᵀ * X)` (invOf), while
`olsBetaStar` uses `(Xᵀ * X)⁻¹` (nonsingInv). The bridge goes from `nonsingInv` to
`invOf` — the likely Mathlib name is `invOf_eq_nonsing_inv` (rewrite `⅟A = A⁻¹` when
`Invertible A`). Run `lean_hover_info` on the existing `olsBeta` symbol first to
confirm the elaborated form.

```lean
theorem olsBetaStar_eq_olsBeta
    (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
    olsBetaStar X y = olsBeta X y := by
  unfold olsBetaStar olsBeta
  rw [← invOf_eq_nonsing_inv]  -- replace invOf ↔ nonsingInv; direction may flip
```

If the expected rewrite name differs, use `lean_local_search` / `lean_leansearch`.
Candidate names to try: `invOf_eq_nonsing_inv`, `Matrix.invOf_eq_nonsing_inv`,
`Matrix.nonsing_inv_eq_invOf`, `Matrix.inv_def`.

- [ ] **Step 5: Build and commit**

```bash
lake build HansenEconometrics.Chapter3LeastSquaresAlgebra
git add HansenEconometrics/Chapter3LeastSquaresAlgebra.lean
git commit -m "Add total olsBetaStar via nonsingInv for Ch 7 stochastic story"
```

---

## Task 2: Stacking primitives

**Files:**
- Modify: `HansenEconometrics/Chapter7Asymptotics.lean` (add a new section at the end of the
  namespace, before `end HansenEconometrics`)

- [ ] **Step 1: Add module-level context for the new section**

At the top of the new section, declare:

```lean
section Stacking

variable {Ω : Type*} {k : Type*} [Fintype k] [DecidableEq k]
```

(The existing file's `variable` block uses different `n k` metas — the stacking section
uses `Fin n` explicitly, so override.)

- [ ] **Step 2: Write the three stacking definitions**

```lean
/-- Stack the first `n` observations of an `ℕ`-indexed regressor sequence into an
`Fin n`-row design matrix at a fixed sample point `ω`. -/
def stackRegressors (X : ℕ → Ω → (k → ℝ)) (n : ℕ) (ω : Ω) : Matrix (Fin n) k ℝ :=
  Matrix.of (fun i j => X i.val ω j)

/-- Stack the first `n` scalar errors into a `Fin n`-indexed vector. -/
def stackErrors (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Fin n → ℝ :=
  fun i => e i.val ω

/-- Stack the first `n` outcomes into a `Fin n`-indexed vector. -/
def stackOutcomes (y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : Fin n → ℝ :=
  fun i => y i.val ω
```

- [ ] **Step 3: Typecheck**

Run: `lake build HansenEconometrics.Chapter7Asymptotics`
Expected: builds cleanly.

- [ ] **Step 4: Commit**

```bash
git add HansenEconometrics/Chapter7Asymptotics.lean
git commit -m "Add Fin n-indexed stacking of regressor/error/outcome sequences"
```

---

## Task 3: Stacking commutes with the linear model

**Files:**
- Modify: `HansenEconometrics/Chapter7Asymptotics.lean`

- [ ] **Step 1: Write the signature with `sorry`**

```lean
theorem stack_linear_model
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (y : ℕ → Ω → ℝ) (β : k → ℝ)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω)
    (n : ℕ) (ω : Ω) :
    stackOutcomes y n ω = stackRegressors X n ω *ᵥ β + stackErrors e n ω := by
  sorry
```

- [ ] **Step 2: Prove by `funext` + `hmodel`**

```lean
  funext i
  simp [stackOutcomes, stackRegressors, stackErrors, Matrix.mulVec, Matrix.of_apply,
        dotProduct, hmodel i.val ω]
```

If `simp` leaves `∑ j, X i.val ω j * β j` vs `X i.val ω ⬝ᵥ β`, add `show _ = _` to line
them up or use `Matrix.mulVec_eq_sum` + `dotProduct`.

- [ ] **Step 3: Build and commit**

```bash
lake build HansenEconometrics.Chapter7Asymptotics
git add HansenEconometrics/Chapter7Asymptotics.lean
git commit -m "stack_linear_model: stacking commutes with y_i = X_i·β + e_i"
```

---

## Task 4: Gram matrix of stacked form = ∑ vecMulVec

**Files:**
- Modify: `HansenEconometrics/Chapter7Asymptotics.lean`

This is the algebraic heart of the stacking bridge. Purely matrix algebra — no probability.

- [ ] **Step 1: Write signature with `sorry`**

```lean
theorem stackRegressors_transpose_mul_self_eq_sum
    (X : ℕ → Ω → (k → ℝ)) (n : ℕ) (ω : Ω) :
    (stackRegressors X n ω)ᵀ * stackRegressors X n ω =
      ∑ i : Fin n, Matrix.vecMulVec (X i.val ω) (X i.val ω) := by
  sorry
```

- [ ] **Step 2: Prove via Matrix.ext + mul_apply + vecMulVec_apply**

```lean
  ext a b
  simp [stackRegressors, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
        Matrix.vecMulVec_apply, Matrix.sum_apply]
  -- goal should collapse to `∑ i : Fin n, X i.val ω a * X i.val ω b = ∑ i : Fin n, ...`
```

If the `simp` leaves a residual goal, finish with `rfl` or `ring_nf`.

- [ ] **Step 3: Write the `sampleGram` corollary**

```lean
theorem sampleGram_stackRegressors_eq_avg
    (X : ℕ → Ω → (k → ℝ)) (n : ℕ) (ω : Ω) :
    sampleGram (stackRegressors X n ω) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, Matrix.vecMulVec (X i.val ω) (X i.val ω) := by
  unfold sampleGram
  rw [stackRegressors_transpose_mul_self_eq_sum]
  simp [Fintype.card_fin]
```

(The `[NeZero n]` originally in the plan is unused — at `n = 0` both sides reduce
to `0`, so the statement holds unconditionally.)

- [ ] **Step 4: Build and commit**

```bash
lake build HansenEconometrics.Chapter7Asymptotics
git add HansenEconometrics/Chapter7Asymptotics.lean
git commit -m "sampleGram of stacked design = (1/n) ∑ vecMulVec Xᵢ Xᵢ"
```

---

## Task 5: Cross moment of stacked form = ∑ eᵢ • Xᵢ

**Files:**
- Modify: `HansenEconometrics/Chapter7Asymptotics.lean`

- [ ] **Step 1: Write signature with `sorry`**

```lean
theorem stackRegressors_transpose_mulVec_stackErrors_eq_sum
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (stackRegressors X n ω)ᵀ *ᵥ stackErrors e n ω =
      ∑ i : Fin n, e i.val ω • X i.val ω := by
  sorry
```

- [ ] **Step 2: Prove**

```lean
  funext a
  simp [stackRegressors, stackErrors, Matrix.mulVec, Matrix.transpose_apply,
        Matrix.of_apply, dotProduct, Pi.smul_apply, mul_comm]
```

- [ ] **Step 3: `sampleCrossMoment` corollary**

```lean
theorem sampleCrossMoment_stackRegressors_stackErrors_eq_avg
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) =
      (n : ℝ)⁻¹ • ∑ i : Fin n, e i.val ω • X i.val ω := by
  unfold sampleCrossMoment
  rw [stackRegressors_transpose_mulVec_stackErrors_eq_sum]
  simp [Fintype.card_fin]
```

- [ ] **Step 4: Build and commit**

```bash
lake build HansenEconometrics.Chapter7Asymptotics
git add HansenEconometrics/Chapter7Asymptotics.lean
git commit -m "sampleCrossMoment of stacked design = (1/n) ∑ eᵢ • Xᵢ"
```

---

## Task 6: Bridge `Fin n` ↔ `Finset.range n` for WLLN compatibility

**Files:**
- Modify: `HansenEconometrics/Chapter7Asymptotics.lean`

WLLN outputs `(n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f i`. Our sum-form lemmas are over
`Fin n`. Bridge once, reuse everywhere.

- [ ] **Step 1: Write the two bridge lemmas with `sorry`**

```lean
theorem sum_fin_eq_sum_range_vecMulVec
    (X : ℕ → Ω → (k → ℝ)) (n : ℕ) (ω : Ω) :
    (∑ i : Fin n, Matrix.vecMulVec (X i.val ω) (X i.val ω)) =
      ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω) := by
  sorry

theorem sum_fin_eq_sum_range_smul
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (∑ i : Fin n, e i.val ω • X i.val ω) =
      ∑ i ∈ Finset.range n, e i ω • X i ω := by
  sorry
```

- [ ] **Step 2: Prove both via `Fin.sum_univ_eq_sum_range`**

```lean
  exact Fin.sum_univ_eq_sum_range (fun i => Matrix.vecMulVec (X i ω) (X i ω)) n
-- and analogously for the second
```

If `Fin.sum_univ_eq_sum_range` has a different name in the current Mathlib, try
`Finset.sum_range_univ_fin` or search via `lean_loogle` with pattern
`?f : ℕ → ?α, ∑ i : Fin ?n, ?f i.val = ∑ i ∈ Finset.range ?n, ?f i`.

- [ ] **Step 3: Build and commit**

```bash
lake build HansenEconometrics.Chapter7Asymptotics
git add HansenEconometrics/Chapter7Asymptotics.lean
git commit -m "Bridge Fin n sums to Finset.range n for WLLN compatibility"
```

---

## Task 7: Invertibility persistence in `AsymptoticUtils`

**Files:**
- Modify: `HansenEconometrics/AsymptoticUtils.lean` (add a new section after `CMT`, before
  `WLLN`)

This is the conceptually hardest step and the most likely place to get stuck. If the
proof balloons past ~40 lines, stop and reconsider whether to factor through Mathlib's
`Matrix.GeneralLinearGroup` or its `Units` machinery.

- [ ] **Step 1: State the helper**

```lean
section MatrixInverse

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- **CMT for matrix inversion.** If `A n →ₚ A` and `A` is nonsingular, then
`(A n)⁻¹ →ₚ A⁻¹`. `nonsingInv` is continuous on the open set of nonsingular matrices,
which contains the limit; the result follows from the subsequence characterization
of `TendstoInMeasure` plus the fact that nonsingular matrices are eventually preserved
under a.s. convergence. -/
theorem tendstoInMeasure_matrix_inv
    [IsFiniteMeasure μ]
    {A : ℕ → α → Matrix k k ℝ} {A∞ : α → Matrix k k ℝ}
    (hmeas : ∀ n, AEStronglyMeasurable (A n) μ)
    (hconv : TendstoInMeasure μ A atTop A∞)
    (hinv : ∀ ω, IsUnit (A∞ ω).det) :
    TendstoInMeasure μ (fun n ω => (A n ω)⁻¹) atTop (fun ω => (A∞ ω)⁻¹) := by
  sorry
```

(Note: the `hinv` hypothesis as "pointwise invertibility of the limit" is the shape
Theorem 7.1 will want — `A∞ ω = Q` is constant and invertible by Assumption 7.1, so
`hinv` is trivial at the call site. If pointwise turns out awkward, weaken to
`∀ᵐ ω ∂μ, IsUnit (A∞ ω).det`.)

- [ ] **Step 2: Typecheck the signature**

Run: `lake build HansenEconometrics.AsymptoticUtils`
Expected: builds cleanly (with `sorry`).

- [ ] **Step 3: Prove via subsequence + continuity on `GL_k(ℝ)`**

Strategy mirrors the existing `tendstoInMeasure_continuous_comp`: use
`exists_seq_tendstoInMeasure_atTop_iff`, pass to an a.s.-convergent subsequence, and
lift via the fact that `(·)⁻¹ : Matrix k k ℝ → Matrix k k ℝ` (as `nonsingInv`) is
continuous at every nonsingular matrix. Mathlib provides
`Matrix.continuousAt_inv` (or search `continuousAt_nonsingInv` /
`nonsingInv_continuousAt`) — use `lean_leansearch` "matrix inverse continuous" to locate.

**The sketch below is schematic: the method-vs-lemma shapes are guesses.** Mathlib
tends to expose measurability of `f⁻¹` via `AEStronglyMeasurable.inv` (a method on
the measurable function), not via an iff lemma. Expect to adjust `.mp` / `.comp`
composition based on the actual signature.

```lean
  -- sketch
  have hmeas' : ∀ n, AEStronglyMeasurable (fun ω => (A n ω)⁻¹) μ := by
    intro n
    exact (Matrix.aestronglyMeasurable_inv.mp ?_).comp (hmeas n)  -- may need alt name
  rw [exists_seq_tendstoInMeasure_atTop_iff hmeas']
  intro ns hns
  obtain ⟨ns', hns', hae⟩ := (exists_seq_tendstoInMeasure_atTop_iff hmeas).mp hconv ns hns
  refine ⟨ns', hns', ?_⟩
  filter_upwards [hae] with ω hω
  exact (Matrix.continuousAt_nonsingInv (hinv ω)).tendsto.comp hω
```

If the Mathlib name doesn't match, pause and run a targeted search:
- `lean_leansearch "matrix inverse continuous"`
- `lean_loogle "ContinuousAt Matrix.nonsingInv"`
- `lean_loogle "ContinuousAt (·)⁻¹ Matrix"`

Report what you find before spending more than 15 minutes on this — if the lemma
truly isn't in Mathlib, we fall back to proving continuity from scratch via Cramer's
rule / the cofactor formula (determinant + adjugate are polynomial, hence continuous;
inversion is `adj / det` on the nonsingular set).

- [ ] **Step 4: Build and commit**

```bash
lake build HansenEconometrics.AsymptoticUtils
git add HansenEconometrics/AsymptoticUtils.lean
git commit -m "tendstoInMeasure_matrix_inv: CMT for matrix inversion at nonsingular limit"
```

- [ ] **Step 5: CHECKPOINT — pause and confirm before committing downstream tasks**

Task 7 is the highest-risk item in the plan, and Tasks 8–11 commit to its signature.
Before proceeding to Task 8:
1. Verify the committed `tendstoInMeasure_matrix_inv` actually builds (not just
   typechecks with `sorry`).
2. Confirm the finalized signature still matches what Tasks 9 and 11 call. If the
   hypothesis shape drifted (e.g. pointwise `IsUnit (A∞ ω).det` became
   `∀ᵐ ω`, or measurability packaging changed), update the downstream proof sketches
   in this plan *before* starting Task 8.

---

## Task 8: Package Assumption 7.1

**Files:**
- Modify: `HansenEconometrics/Chapter7Asymptotics.lean` (add after the stacking section)

Before writing the structure, **spot-check the exact syntax** used by the existing
`tendstoInMeasure_wlln` in `HansenEconometrics/AsymptoticUtils.lean:120` for the
pairwise-independence and ident-distrib hypotheses. A syntactic mismatch here
(e.g. `Pairwise ((· ⟂ᵢ[μ] ·) on X)` vs `iIndepFun` vs `ProbabilityTheory.iIndep`)
will force every call site in Tasks 9, 10, and 11 to be rewritten, so get it right
in this task.

- [ ] **Step 1: Declare the structure**

```lean
section Assumption71

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Hansen Assumption 7.1: iid regressor/error sequence with a finite nonsingular
population Gram matrix `Q := 𝔼[X Xᵀ]` and orthogonality `𝔼[X e] = 0`. -/
structure SampleAssumption71 (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : ℕ → Ω → (k → ℝ)) (e : ℕ → Ω → ℝ) where
  /-- Measurability of each regressor observation. -/
  meas_X : ∀ i, AEStronglyMeasurable (X i) μ
  meas_e : ∀ i, AEStronglyMeasurable (e i) μ
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
  /-- Second moments on X (so `X Xᵀ` is integrable). -/
  int_outer : Integrable (fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)) μ
  /-- First-moment integrability of `e X` (so cross moment is integrable). -/
  int_cross : Integrable (fun ω => e 0 ω • X 0 ω) μ
  /-- Population Gram matrix `Q := 𝔼[X Xᵀ]` is nonsingular. -/
  Q_nonsing : IsUnit (μ[fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)]).det
  /-- Population orthogonality `𝔼[X e] = 0`. -/
  orthogonality : μ[fun ω => e 0 ω • X 0 ω] = 0

/-- The population Gram matrix `Q := 𝔼[X Xᵀ]`. -/
noncomputable def popGram (μ : Measure Ω) (X : ℕ → Ω → (k → ℝ)) : Matrix k k ℝ :=
  μ[fun ω => Matrix.vecMulVec (X 0 ω) (X 0 ω)]

end Assumption71
```

- [ ] **Step 2: Typecheck**

Run: `lake build HansenEconometrics.Chapter7Asymptotics`
Expected: builds cleanly. If `Pairwise ((· ⟂ᵢ[μ] ·) on f)` fails to elaborate, check
the exact syntax used in the existing `tendstoInMeasure_wlln` signature and copy it.

- [ ] **Step 3: Commit**

```bash
git add HansenEconometrics/Chapter7Asymptotics.lean
git commit -m "SampleAssumption71: iid + second moments + Q invertible + orthogonality"
```

---

## Task 9: `sampleGram(stack) →ₚ Q`

**Files:**
- Modify: `HansenEconometrics/Chapter7Asymptotics.lean`

- [ ] **Step 1: Write signature with `sorry`**

```lean
theorem sampleGram_stackRegressors_tendstoInMeasure_popGram
    [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleAssumption71 μ X e) :
    TendstoInMeasure μ
      (fun n ω => sampleGram (stackRegressors X n ω))
      atTop
      (fun _ => popGram μ X) := by
  sorry
```

- [ ] **Step 2: Prove by rewriting to sum-form and applying WLLN**

Transport approach: `tendstoInMeasure_congr_left` does **not** exist in Mathlib.
Use one of these two paths instead, in order of preference:
1. **Function-level rewrite.** Use `funext`/`show` to prove the two function
   sequences are *equal* (not just pointwise-eventually equal) before applying WLLN.
   Cleanest when the rewrite is definitional modulo the established lemmas.
2. **`TendstoInMeasure.congr`.** If Mathlib exposes a congr lemma for
   `TendstoInMeasure` (search `lean_leansearch "TendstoInMeasure congr"`), use it
   with a pointwise-a.e.-equal hypothesis.

If neither fits cleanly, fall back to proving the WLLN for the stacked-form
expression directly by `convert hwlln using 2` and cleaning up the residual.

```lean
  -- 1. Rewrite sampleGram of stacked form as (1/n) ∑ vecMulVec, Finset.range version
  have hrw : ∀ n ω, sampleGram (stackRegressors X n ω) =
      (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω) := by
    intro n ω
    rw [sampleGram_stackRegressors_eq_avg, sum_fin_eq_sum_range_vecMulVec]
  -- 2. WLLN on the outer-product sequence
  have hwlln := tendstoInMeasure_wlln
    (fun i ω => Matrix.vecMulVec (X i ω) (X i ω))
    h.int_outer h.indep_outer h.ident_outer
  -- 3. Transport: two function sequences are equal via funext on `hrw`
  have hfun_eq : (fun n ω => sampleGram (stackRegressors X n ω)) =
      (fun n ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, Matrix.vecMulVec (X i ω) (X i ω)) := by
    funext n ω; exact hrw n ω
  rw [hfun_eq]
  -- 4. popGram on the right also unfolds to the WLLN limit
  convert hwlln using 1  -- clean up `popGram μ X = μ[Matrix.vecMulVec (X 0 ·) (X 0 ·)]`
```

- [ ] **Step 3: Build and commit**

```bash
lake build HansenEconometrics.Chapter7Asymptotics
git add HansenEconometrics/Chapter7Asymptotics.lean
git commit -m "sampleGram of stacked regressors →ₚ population Gram Q"
```

---

## Task 10: `sampleCrossMoment(stack) →ₚ 0`

**Files:**
- Modify: `HansenEconometrics/Chapter7Asymptotics.lean`

- [ ] **Step 1: Write signature with `sorry`**

```lean
theorem sampleCrossMoment_stackRegressors_stackErrors_tendstoInMeasure_zero
    [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ}
    (h : SampleAssumption71 μ X e) :
    TendstoInMeasure μ
      (fun n ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω))
      atTop
      (fun _ => 0) := by
  sorry
```

- [ ] **Step 2: Prove by analogy with Task 9**

Same structure: rewrite sum-form via Task 5 + Task 6, apply WLLN to the cross-product
sequence, transport. At the end, use `h.orthogonality` to identify the WLLN limit
with `0`.

- [ ] **Step 3: Build and commit**

```bash
lake build HansenEconometrics.Chapter7Asymptotics
git add HansenEconometrics/Chapter7Asymptotics.lean
git commit -m "sampleCrossMoment of stacked regressors/errors →ₚ 0 under orthogonality"
```

---

## Task 11: Theorem 7.1 — β̂ₙ →ₚ β

**Files:**
- Modify: `HansenEconometrics/Chapter7Asymptotics.lean`

This is the main theorem. All pieces are in place.

- [ ] **Step 1: Write signature with `sorry`**

```lean
/-- **Hansen Theorem 7.1 (Consistency of Least Squares).** Under Assumption 7.1, the
OLS estimator on the stacked design converges in probability to `β`. -/
theorem olsBetaStar_stack_tendstoInMeasure_beta
    [IsFiniteMeasure μ]
    {X : ℕ → Ω → (k → ℝ)} {e : ℕ → Ω → ℝ} {y : ℕ → Ω → ℝ} (β : k → ℝ)
    (h : SampleAssumption71 μ X e)
    (hmodel : ∀ i ω, y i ω = (X i ω) ⬝ᵥ β + e i ω) :
    TendstoInMeasure μ
      (fun n ω => olsBetaStar (stackRegressors X n ω) (stackOutcomes y n ω))
      atTop
      (fun _ => β) := by
  sorry
```

- [ ] **Step 2: Assemble the proof from prior tasks**

```lean
  -- (a) Substitute the linear model: β̂ₙ - β = Q̂ₙ⁻¹ *ᵥ g̑ₙ (Phase 1 identity, lifted to *Star)
  -- (b) Apply tendstoInMeasure_matrix_inv to Task 9 → sampleGram⁻¹ →ₚ Q⁻¹
  -- (c) Combine (b) with Task 10 via a product/mulVec CMT to get
  --     sampleGram⁻¹ *ᵥ sampleCrossMoment →ₚ Q⁻¹ *ᵥ 0 = 0.
  --     **If (c) runs past ~20 lines inline, STOP and extract it as a named helper
  --     `tendstoInMeasure_mulVec` in AsymptoticUtils.lean, then come back here.**
  -- (d) Transport β̂ₙ - β →ₚ 0 to β̂ₙ →ₚ β via `TendstoInMeasure.add_const` or a
  --     manual rewrite.
  sorry  -- fill in per the four bullets above
```

Expect Steps (a)–(d) to each be ~5–15 lines, with (c) being the riskiest. The
two convergences in (c) live in different ambient spaces (`Matrix k k ℝ` and
`k → ℝ`), so combining them requires either a product CMT or a bespoke construction
via `tendstoInMeasure_pi` over `Fin 2` with an explicit product-encoding. Try the
`tendstoInMeasure_continuous_comp` approach with
`h := fun (p : Matrix k k ℝ × (k → ℝ)) => p.1 *ᵥ p.2` applied to the joint
convergence first; if that requires more than one lemma of plumbing to assemble
the joint convergence, promote the whole step to a helper `tendstoInMeasure_mulVec`
in `AsymptoticUtils.lean` — it's a generally reusable fact worth naming.

- [ ] **Step 3: Build and commit**

```bash
lake build HansenEconometrics.Chapter7Asymptotics
git add HansenEconometrics/Chapter7Asymptotics.lean
git commit -m "Theorem 7.1: consistency of least squares (β̂ₙ →ₚ β)"
```

---

## Task 12: Crosswalk update and docstring polish

**Files:**
- Create: `notes/ch07/latex_links.md` (per the AGENTS.md "Crosswalk policy")
- Modify: `HansenEconometrics/Chapter7Asymptotics.lean` (top-of-file docstring)

- [ ] **Step 1: Create `notes/ch07/latex_links.md`**

Follow the structure in any existing `notes/chXX/latex_links.md` (Chapter 4 is the
closest match — one row per textbook theorem, LaTeX statement, Lean target).

- [ ] **Step 2: Update the Chapter 7 file docstring**

Replace the "Phase 2 scheduled" language with a pointer to the consistency theorem
and the Assumption 7.1 structure.

- [ ] **Step 3: Commit**

```bash
git add notes/ch07/latex_links.md HansenEconometrics/Chapter7Asymptotics.lean
git commit -m "ch7: crosswalk + docstring update for Theorem 7.1"
```

---

## Risks and fallbacks

1. **Task 7 (matrix-inverse CMT) balloons.** If Mathlib's `ContinuousAt` for matrix
   inversion is missing or hard to locate, factor through the determinant/adjugate:
   `det` and `adjugate` are both polynomial, hence `Continuous`; inversion at a point
   with `det ≠ 0` then follows from continuity of division. Budget: 45 minutes of
   search + fallback before escalating.
2. **`olsBetaStar = olsBeta` agreement (Task 1).** If the `nonsingInv`/`invOf` bridge
   lemma name is elusive, do the agreement proof by unfolding both sides to
   `(Xᵀ * X)⁻¹ *ᵥ (Xᵀ *ᵥ y)` directly and using `Matrix.inv_eq_iff_eq_mul` or a similar
   characterization.
3. **Measurability-of-stacking blocker.** If WLLN needs `stack X n` to be measurable,
   add a lemma in Task 2 or 9: `AEStronglyMeasurable (fun ω => stackRegressors X n ω) μ`
   follows from `Matrix.aestronglyMeasurable_iff_of_fintype` applied coordinatewise.
4. **Fin/ℕ bridge name drift.** If `Fin.sum_univ_eq_sum_range` has been renamed,
   use `Finset.sum_range_univ_fin` or prove inline with `Fin.sum_univ_eq_sum_range_of_mono`
   (worst case: `induction n`).

## Review checklist (before declaring Phase 3 done)

Per `AGENTS.md`:
- [ ] Does Mathlib already prove any of these results? (Especially Task 7.)
- [ ] Does any existing repo theorem already imply these?
- [ ] Is `olsBetaStar` at the right generality layer? (Should match `olsBeta`.)
- [ ] Is `SampleAssumption71` variable-facing rather than sigma-algebra facing? (Yes.)
- [ ] `notes/ch07/latex_links.md` updated? (Task 12.)
- [ ] All new markdown links relative? (Task 12.)
