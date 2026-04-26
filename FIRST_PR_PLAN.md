# Formalize Hansen Theorem 3.1: OLS as the Argmin of SSE

This ExecPlan is a living document. The sections `Progress`, `Surprises & Discoveries`,
`Decision Log`, and `Outcomes & Retrospective` must be kept up to date as work proceeds.

Maintained in accordance with [PLANS.md](./PLANS.md).

## Purpose / Big Picture

After this change, the Lean source file `HansenEconometrics/Chapter3LeastSquaresAlgebra.lean`
will contain a machine-verified proof of Hansen's Theorem 3.1: under the assumption that X'X is
invertible (equivalently, positive definite), the OLS coefficient vector `β̂ = (X'X)⁻¹ X'Y`
is the unique minimizer of the sum of squared errors `S(b) = (Y - Xb)'(Y - Xb)`.

Currently the repo proves that `β̂` satisfies the normal equations and that any solution to the
normal equations equals `β̂` (`olsBeta_eq_of_normal_equations`). What is missing is the
optimization layer: a verified statement that `β̂` globally minimizes `S(b)` over all `b ∈ Rᵏ`.

After this plan is executed, the Chapter 3 crosswalk in `inventory/ch3-inventory.md` will have
a non-blank Lean cell for Theorem 3.1, and `lake build` will succeed with no new `sorry`s.

## Progress

- [ ] Read and understand all files listed in "Context and Orientation" below.
- [ ] Add `gram_quadratic_nonneg` to `HansenEconometrics/LinearAlgebraUtils.lean`.
- [ ] Add `sumSquaredErrors_eq_linearProjectionMSE` to `HansenEconometrics/Chapter3LeastSquaresAlgebra.lean`.
- [ ] Add `olsBeta_eq_linearProjectionBeta` (or inline) to `Chapter3LeastSquaresAlgebra.lean`.
- [ ] Add `sumSquaredErrors_eq_olsBeta_add_gram_form` to `Chapter3LeastSquaresAlgebra.lean`.
- [ ] Add `sumSquaredErrors_olsBeta_le` to `Chapter3LeastSquaresAlgebra.lean`.
- [ ] Add `olsBeta_isMinOn` to `Chapter3LeastSquaresAlgebra.lean`.
- [ ] Add the `Chapter2LinearProjection` import to `Chapter3LeastSquaresAlgebra.lean` if needed.
- [ ] Update the Theorem 3.1 row in `inventory/ch3-inventory.md`.
- [ ] Run `lake build` and confirm it succeeds with zero errors and zero `sorry`s.

## Surprises & Discoveries

(Fill in as work proceeds.)

## Decision Log

- Decision: Route the completing-the-square identity through the existing
  `linearProjectionMSE_eq_at_beta_add_quadratic_form` theorem from
  `Chapter2LinearProjection.lean` rather than reproving it from scratch in Chapter 3.
  Rationale: AGENTS.md principle 2 ("reuse repo theorems before adding new ones"). The
  Chapter 2 theorem already packages exactly this algebra at the right level of generality.
  The cost is a bridge lemma connecting the two notations; the benefit is no duplicated algebra.
  Date/Author: initial plan.

- Decision: Place `gram_quadratic_nonneg` in `LinearAlgebraUtils.lean` rather than in the
  chapter file.
  Rationale: It is a pure matrix-algebra fact (the Gram matrix has nonneg quadratic form)
  that is likely to be reused in later chapters (e.g., Ch 5 chi-square bounds, Ch 7 covariance
  estimator bounds). Per AGENTS.md module-boundary policy it belongs in the shared utility layer.
  Date/Author: initial plan.

- Decision: State Theorem 3.1 both as a direct inequality `sumSquaredErrors_olsBeta_le` and as
  an `IsMinOn` wrapper `olsBeta_isMinOn`.
  Rationale: The direct inequality `∀ b, SSE(β̂) ≤ SSE(b)` is the mathematically useful form
  for downstream results. `IsMinOn` is the Mathlib-standard predicate for minimizers and will
  interoperate with Mathlib's optimization library if later results need it.
  Date/Author: initial plan.

## Outcomes & Retrospective

(Fill in after completion.)

## Context and Orientation

### What Lean 4 and Mathlib are

Lean 4 is an interactive theorem prover. You write definitions and theorem statements in a
typed functional language, then supply proofs using "tactics" — commands that transform the
current proof goal. The Lean extension in VS Code checks every line in real time: a red
underline means an error or an unfinished proof. Green (no errors) means the file compiles and
every proof is machine-verified.

Mathlib is the community library of Lean 4 mathematics. It contains a very large collection of
algebra, analysis, topology, and linear algebra theorems. When you write `import Mathlib` at
the top of a file, you get access to all of it.

### Key Lean notation used in this repo

- `X *ᵥ v` — matrix-vector multiplication (X : Matrix n k ℝ, v : k → ℝ, result : n → ℝ)
- `u ⬝ᵥ v` — dot product of two vectors of the same type (result : ℝ)
- `Xᵀ` — the transpose of matrix X
- `⅟ A` — the "invertible inverse" of A, defined when `[Invertible A]` is in scope
- `[Invertible A]` — a typeclass assumption that A is invertible; provides `⅟ A`
- `noncomputable def` — a definition whose value cannot be computed (e.g., it involves real
  inverses), but whose mathematical properties can still be proved
- `theorem` / `lemma` — differ only in convention; `lemma` signals a helper, `theorem` a main result
- `by` — begins a tactic block; the proof is a sequence of tactic steps
- `rfl` — closes a goal that holds by definitional equality
- `rw [h]` — rewrite the goal using hypothesis or lemma h
- `simp [h, ...]` — simplify the goal using a set of lemmas
- `calc` — a chain of equalities or inequalities, each step justified separately
- `linarith [h1, h2]` — close a linear arithmetic goal using hypotheses
- `sorry` — placeholder for a missing proof; a file with `sorry` still compiles but is flagged
- `exact e` — close the goal by providing a term `e` of the right type
- `unfold f` — replace `f ...` with its definition

### Key files

All file paths are relative to the repository root.

- `HansenEconometrics/Chapter3LeastSquaresAlgebra.lean` — the main Chapter 3 OLS algebra file.
  Contains `sumSquaredErrors`, `olsBeta`, `residual`, `fitted`, `normal_equations`, and
  `olsBeta_eq_of_normal_equations`. This is where Theorem 3.1 will be added.

- `HansenEconometrics/Chapter3Projections.lean` — hat matrix, annihilator matrix, and their
  properties. Contains `gram_transpose` (symmetry of X'X), `hatMatrix`, `annihilatorMatrix`,
  and related idempotence/trace/rank lemmas. Imports `Chapter3LeastSquaresAlgebra`.

- `HansenEconometrics/Chapter2LinearProjection.lean` — population linear projection algebra.
  Contains `linearProjectionBeta`, `linearProjectionMSE`, and crucially
  `linearProjectionMSE_eq_at_beta_add_quadratic_form` (the completing-the-square identity).
  This is the Chapter 2 result that we will reuse.

- `HansenEconometrics/LinearAlgebraUtils.lean` — shared matrix helper lemmas. Contains
  `vecMul_eq_mulVec_transpose` (key for converting row-vector products to column-vector form),
  `quadratic_form_eq_dotProduct_of_symm_idempotent`, and `rank_eq_natCast_trace_of_isHermitian_idempotent`.
  We will add `gram_quadratic_nonneg` here.

- `inventory/ch3-inventory.md` — the chapter crosswalk. After completion, the Theorem 3.1 row
  must be updated with the new Lean theorem names.

### The existing theorem we reuse from Chapter 2

`linearProjectionMSE_eq_at_beta_add_quadratic_form` in `Chapter2LinearProjection.lean`:

    theorem linearProjectionMSE_eq_at_beta_add_quadratic_form
        (QXX : Matrix k k ℝ) (QXY : k → ℝ) (QYY : ℝ) (b : k → ℝ)
        [Invertible QXX]
        (hQXXt : QXXᵀ = QXX) :
        linearProjectionMSE QXX QXY QYY b =
          linearProjectionMSE QXX QXY QYY (linearProjectionBeta QXX QXY) +
            (b - linearProjectionBeta QXX QXY) ⬝ᵥ
              (QXX *ᵥ (b - linearProjectionBeta QXX QXY))

where `linearProjectionMSE QXX QXY QYY b = QYY - 2 * (b ⬝ᵥ QXY) + b ⬝ᵥ (QXX *ᵥ b)`.

Setting `QXX = Xᵀ * X`, `QXY = Xᵀ *ᵥ y`, `QYY = y ⬝ᵥ y` turns this into the completing-the-square
identity for `sumSquaredErrors`, with `linearProjectionBeta (Xᵀ * X) (Xᵀ *ᵥ y)` equal to
`olsBeta X y` by definition.

### The mathematical proof

The proof of Theorem 3.1 has three steps.

Step 1 — identify the right algebraic frame. Observe that `sumSquaredErrors X y b`
(defined as `(y - X *ᵥ b) ⬝ᵥ (y - X *ᵥ b)`) equals the abstract `linearProjectionMSE`
when the moment matrices are specialized to their sample counterparts:

    sumSquaredErrors X y b = linearProjectionMSE (Xᵀ * X) (Xᵀ *ᵥ y) (y ⬝ᵥ y) b

This identity holds by dot-product algebra (expand both sides and use the fact that
`y ⬝ᵥ (X *ᵥ b) = (Xᵀ *ᵥ y) ⬝ᵥ b` and `(X *ᵥ b) ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ ((Xᵀ * X) *ᵥ b)`).

Step 2 — invoke the Chapter 2 completing-the-square identity. Since `Xᵀ * X` is symmetric
(`gram_transpose`) and the Chapter 2 theorem applies to any symmetric invertible matrix,
specializing gives:

    sumSquaredErrors X y b
      = sumSquaredErrors X y (olsBeta X y)
          + (b - olsBeta X y) ⬝ᵥ ((Xᵀ * X) *ᵥ (b - olsBeta X y))

Step 3 — nonnegativity of the Gram quadratic form. For any vector `v : k → ℝ`:

    0 ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v)

Proof: `(Xᵀ * X) *ᵥ v = Xᵀ *ᵥ (X *ᵥ v)` (by `Matrix.mulVec_mulVec`), then
`v ⬝ᵥ (Xᵀ *ᵥ w) = (X *ᵥ v) ⬝ᵥ w` (by `dotProduct_mulVec` and `vecMul_eq_mulVec_transpose`),
so the whole expression equals `(X *ᵥ v) ⬝ᵥ (X *ᵥ v) ≥ 0` (by `dotProduct_star_self_nonneg`).

Combining steps 2 and 3: `SSE(b) = SSE(β̂) + nonneg_term ≥ SSE(β̂)` for all `b`. QED.

## Plan of Work

The work touches two existing files and creates no new files.

### File 1: `HansenEconometrics/LinearAlgebraUtils.lean`

Add a single new lemma after the existing `diag_nonneg_of_symm_idempotent` (around line 68).
The lemma states that the Gram matrix `Xᵀ * X` produces a nonneg quadratic form. It depends
only on `vecMul_eq_mulVec_transpose` (already in this file) and Mathlib's
`dotProduct_star_self_nonneg`.

The new lemma lives here (not in Chapter 3) because it is a reusable matrix fact: any later
chapter that needs to bound a quadratic form involving a Gram matrix can import this lemma.

### File 2: `HansenEconometrics/Chapter3LeastSquaresAlgebra.lean`

Add four new declarations in this order, each following from the previous:

1. **Add import** (if not already present): add
   `import HansenEconometrics.Chapter2LinearProjection`
   to the header. This brings `linearProjectionMSE` and
   `linearProjectionMSE_eq_at_beta_add_quadratic_form` into scope. Check that
   `Chapter3LeastSquaresAlgebra` does not already transitively import that file (it does not;
   the current imports are `Basic`, `LinearAlgebraUtils`, and `Chapter2CondExp`). The
   `Chapter2LinearProjection` file imports only `Basic`, `LinearAlgebraUtils`, and
   `ProbabilityUtils`, so there is no circular dependency.

2. **`sumSquaredErrors_eq_linearProjectionMSE`** — a bridge lemma establishing that the
   Chapter 3 `sumSquaredErrors` function equals the Chapter 2 `linearProjectionMSE` when
   specialized to sample moments. This is proved by unfolding both definitions and using
   dot-product algebra.

3. **`sumSquaredErrors_eq_olsBeta_add_gram_form`** — the completing-the-square decomposition
   for `sumSquaredErrors`, proved by combining the bridge lemma with
   `linearProjectionMSE_eq_at_beta_add_quadratic_form` from Chapter 2 and then converting
   back via the bridge.

4. **`sumSquaredErrors_olsBeta_le`** — the minimality theorem: for all `b`, `SSE(β̂) ≤ SSE(b)`,
   proved in two lines from the decomposition and `gram_quadratic_nonneg`.

5. **`olsBeta_isMinOn`** — a thin `IsMinOn` wrapper, proved by `intro b _; exact ...`.

### File 3: `inventory/ch3-inventory.md`

Update the Theorem 3.1 row in the crosswalk table to include
`sumSquaredErrors_olsBeta_le` and `olsBeta_isMinOn` in the Lean column,
following the link format used by other rows in that table.

## Concrete Steps

Work in the repository root. All `lake` commands should be run there.

**Step 0 — Understand the environment.**

Open the repository in VS Code with the Lean 4 extension installed. Open
`HansenEconometrics/Chapter3LeastSquaresAlgebra.lean`. Wait for the blue spinner in the
bottom bar to finish (Lean is loading Mathlib; this takes several minutes the first time).
Once the spinner disappears, hovering over any theorem name shows its type, and red
underlines indicate errors. This is your feedback loop.

**Step 1 — Add `gram_quadratic_nonneg` to `LinearAlgebraUtils.lean`.**

Open `HansenEconometrics/LinearAlgebraUtils.lean`. After `diag_nonneg_of_symm_idempotent`
(currently ending around line 68) and before `quadForm_eq_sum_eigenvalues`, insert:

    /-- The Gram matrix `Xᵀ * X` generates a nonneg quadratic form. This is the
    finite-sample counterpart of positive semidefiniteness: for every vector `v`,
    `v ⬝ᵥ ((Xᵀ * X) *ᵥ v) ≥ 0`. -/
    lemma gram_quadratic_nonneg {n k : Type*} [Fintype n] [Fintype k]
        (X : Matrix n k ℝ) (v : k → ℝ) :
        0 ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          vecMul_eq_mulVec_transpose, Matrix.transpose_transpose]
      exact dotProduct_star_self_nonneg (X *ᵥ v)

Verify: save the file. The Lean server should accept this with no errors (green checkmark
or no red underline on any line of the new block).

Proof explanation for a Lean novice:
- `Matrix.mulVec_mulVec` rewrites `(Xᵀ * X) *ᵥ v` as `Xᵀ *ᵥ (X *ᵥ v)`.
- `Matrix.dotProduct_mulVec` rewrites `v ⬝ᵥ (Xᵀ *ᵥ w)` as `(Matrix.vecMul v Xᵀ) ⬝ᵥ w`.
- `vecMul_eq_mulVec_transpose` (already in this file) rewrites `Matrix.vecMul v Xᵀ` as
  `(Xᵀ)ᵀ *ᵥ v`.
- `Matrix.transpose_transpose` simplifies `(Xᵀ)ᵀ` to `X`.
- After all rewrites the goal is `0 ≤ (X *ᵥ v) ⬝ᵥ (X *ᵥ v)`, which is
  `dotProduct_star_self_nonneg`.

**Step 2 — Add the import to `Chapter3LeastSquaresAlgebra.lean`.**

Open `HansenEconometrics/Chapter3LeastSquaresAlgebra.lean`. The import block currently reads:

    import Mathlib
    import HansenEconometrics.Basic
    import HansenEconometrics.LinearAlgebraUtils
    import HansenEconometrics.Chapter2CondExp

Add one line:

    import HansenEconometrics.Chapter2LinearProjection

after the existing imports. After saving, the Lean server will reload the file (the spinner
will reappear briefly). All existing theorems should remain green.

**Step 3 — Add `sumSquaredErrors_eq_linearProjectionMSE`.**

Insert the following lemma in `Chapter3LeastSquaresAlgebra.lean` immediately before `end HansenEconometrics`:

    /-- Bridge lemma: the Chapter 3 sum-of-squared-errors equals the Chapter 2
    `linearProjectionMSE` when the moment matrices are the sample Gram matrix and
    cross-moment vector. This connects the two notations so we can reuse the
    Chapter 2 completing-the-square algebra. -/
    lemma sumSquaredErrors_eq_linearProjectionMSE
        {n k : Type*} [Fintype n] [Fintype k]
        (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) :
        sumSquaredErrors X y b =
          linearProjectionMSE (Xᵀ * X) (Xᵀ *ᵥ y) (y ⬝ᵥ y) b := by
      unfold sumSquaredErrors linearProjectionMSE
      rw [sub_dotProduct, dotProduct_sub, Matrix.dotProduct_mulVec,
          vecMul_eq_mulVec_transpose, Matrix.transpose_transpose,
          dotProduct_comm (Xᵀ *ᵥ y) b,
          ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          vecMul_eq_mulVec_transpose, Matrix.transpose_transpose]
      ring

Proof explanation: Expand `(y - X *ᵥ b) ⬝ᵥ (y - X *ᵥ b)` using `sub_dotProduct` and
`dotProduct_sub`. The cross terms involve `y ⬝ᵥ (X *ᵥ b)`, which we rewrite as
`(Xᵀ *ᵥ y) ⬝ᵥ b` using `dotProduct_mulVec` and `vecMul_eq_mulVec_transpose`. The squared
term `(X *ᵥ b) ⬝ᵥ (X *ᵥ b)` is rewritten as `b ⬝ᵥ ((Xᵀ * X) *ᵥ b)` by the same pair of
lemmas plus `mulVec_mulVec`. After all rewrites, `ring` closes the goal.

If the exact rewrite sequence does not work as written: paste the lemma with `sorry` first to
check that the statement typechecks, then fill in the proof incrementally. The VS Code Lean
infoview (Ctrl+Shift+P → "Lean 4: Focus on Infoview") shows the current proof state after each
tactic step.

**Step 4 — Add `sumSquaredErrors_eq_olsBeta_add_gram_form`.**

Insert immediately after the bridge lemma:

    /-- Completing-the-square decomposition: for any coefficient vector `b`,
    the SSE at `b` equals the SSE at `olsBeta` plus a nonneg Gram quadratic form
    in the deviation `b - olsBeta`. This is the deterministic core of Theorem 3.1. -/
    theorem sumSquaredErrors_eq_olsBeta_add_gram_form
        {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
        (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) [Invertible (Xᵀ * X)] :
        sumSquaredErrors X y b =
          sumSquaredErrors X y (olsBeta X y) +
            (b - olsBeta X y) ⬝ᵥ ((Xᵀ * X) *ᵥ (b - olsBeta X y)) := by
      rw [sumSquaredErrors_eq_linearProjectionMSE X y b,
          sumSquaredErrors_eq_linearProjectionMSE X y (olsBeta X y)]
      have hβ : olsBeta X y = linearProjectionBeta (Xᵀ * X) (Xᵀ *ᵥ y) := rfl
      rw [hβ]
      exact linearProjectionMSE_eq_at_beta_add_quadratic_form
        (Xᵀ * X) (Xᵀ *ᵥ y) (y ⬝ᵥ y) b (gram_transpose X)

Proof explanation:
- The two `rw [sumSquaredErrors_eq_linearProjectionMSE ...]` calls convert both sides of the
  goal into `linearProjectionMSE` notation.
- `hβ : olsBeta X y = linearProjectionBeta (Xᵀ * X) (Xᵀ *ᵥ y)` holds by `rfl` because
  both definitions unfold to `(⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)`.
- `gram_transpose X` provides the symmetry hypothesis `(Xᵀ * X)ᵀ = Xᵀ * X` required by
  `linearProjectionMSE_eq_at_beta_add_quadratic_form`.
- `exact linearProjectionMSE_eq_at_beta_add_quadratic_form ...` closes the goal by the
  Chapter 2 theorem.

Note on `[DecidableEq k]`: the Chapter 2 theorem requires this instance. If Lean complains that
it cannot find this instance, add `[DecidableEq k]` to the surrounding `variable` block at the
top of the file (it is already present in the existing `variable` line:
`variable [Fintype n] [Fintype k] [DecidableEq k]`).

**Step 5 — Add `sumSquaredErrors_olsBeta_le`.**

Insert immediately after `sumSquaredErrors_eq_olsBeta_add_gram_form`:

    /-- Hansen Theorem 3.1: `olsBeta X y` minimizes the sum of squared errors.
    For any coefficient vector `b`, `SSE(olsBeta X y) ≤ SSE(b)`. -/
    theorem sumSquaredErrors_olsBeta_le
        {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
        (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) [Invertible (Xᵀ * X)] :
        sumSquaredErrors X y (olsBeta X y) ≤ sumSquaredErrors X y b := by
      have h := sumSquaredErrors_eq_olsBeta_add_gram_form X y b
      linarith [gram_quadratic_nonneg X (b - olsBeta X y)]

Proof explanation: `h` says `SSE(b) = SSE(β̂) + nonneg`. `gram_quadratic_nonneg` says the
quadratic-form term is `≥ 0`. `linarith` combines these two facts to conclude `SSE(β̂) ≤ SSE(b)`.

**Step 6 — Add `olsBeta_isMinOn`.**

Insert immediately after `sumSquaredErrors_olsBeta_le`:

    /-- Hansen Theorem 3.1, packaged as `IsMinOn`: `olsBeta X y` is a global minimizer
    of `sumSquaredErrors X y` over all of `k → ℝ`. -/
    theorem olsBeta_isMinOn
        {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
        (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
        IsMinOn (sumSquaredErrors X y) Set.univ (olsBeta X y) := by
      intro b _
      exact sumSquaredErrors_olsBeta_le X y b

Proof explanation: `IsMinOn f s a` unfolds to `∀ x ∈ s, f a ≤ f x`. `intro b _` introduces
the point `b` and its (trivial) membership in `Set.univ`. `exact sumSquaredErrors_olsBeta_le X y b`
closes the goal.

**Step 7 — Update the inventory crosswalk.**

Open `inventory/ch3-inventory.md`. Find the Theorem 3.1 row in the Crosswalk table, which
currently reads:

    | Theorem 3.1 objective-level argmin statement | $\hat{\beta} = \arg\min_b (Y - X b)'(Y - X b)$ |  |

Replace the blank Lean cell with:

    | Theorem 3.1 objective-level argmin statement | $\hat{\beta} = \arg\min_b (Y - X b)'(Y - X b)$ | [sumSquaredErrors_olsBeta_le](../../HansenEconometrics/Chapter3LeastSquaresAlgebra.lean)<br>`sumSquaredErrors X y (olsBeta X y) ≤ sumSquaredErrors X y b`<br>[olsBeta_isMinOn](../../HansenEconometrics/Chapter3LeastSquaresAlgebra.lean)<br>`IsMinOn (sumSquaredErrors X y) Set.univ (olsBeta X y)` |

Also add the bridge and decomposition lemmas to a "Lean-only bridge results" subsection below
the main crosswalk table:

    ## Lean-only bridge results

    | Lean theorem | Role |
    | --- | --- |
    | `sumSquaredErrors_eq_linearProjectionMSE` | Identifies `sumSquaredErrors X y b` with `linearProjectionMSE (Xᵀ * X) (Xᵀ *ᵥ y) (y ⬝ᵥ y) b`, connecting Chapter 3 and Chapter 2 notation |
    | `sumSquaredErrors_eq_olsBeta_add_gram_form` | Completing-the-square identity: `SSE(b) = SSE(β̂) + (b - β̂)'(X'X)(b - β̂)` |
    | `gram_quadratic_nonneg` (in `LinearAlgebraUtils.lean`) | `0 ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v)` for all `v` |

**Step 8 — Final build check.**

Run from the repository root:

    lake build

Expected output: a series of compilation lines ending with no errors. If the build succeeds,
the terminal returns to the prompt with exit code 0. If there are errors, read the first error
message carefully — Lean error messages typically tell you exactly which tactic step failed and
what the current goal state is.

## Validation and Acceptance

Acceptance criteria:

1. `lake build` exits 0 with no errors and no `sorry`s (search the new code for `sorry` to
   confirm none remain).

2. In `HansenEconometrics/Chapter3LeastSquaresAlgebra.lean`, the following five declarations
   exist and are accepted by Lean (no red underlines):
   - `sumSquaredErrors_eq_linearProjectionMSE`
   - `sumSquaredErrors_eq_olsBeta_add_gram_form`
   - `sumSquaredErrors_olsBeta_le`
   - `olsBeta_isMinOn`

3. In `HansenEconometrics/LinearAlgebraUtils.lean`, `gram_quadratic_nonneg` exists and is
   accepted.

4. The Theorem 3.1 row in `inventory/ch3-inventory.md` is non-blank.

5. The `IsMinOn` statement can be checked interactively: place the cursor on `olsBeta_isMinOn`
   in VS Code and confirm the Lean infoview shows the theorem type without errors.

## Idempotence and Recovery

All steps are additive: they only add new declarations to existing files and one new row to a
Markdown table. No existing declarations are modified or deleted. If a step produces an error,
simply correct the text in place; Lean re-checks incrementally on every save.

If `lake build` fails after Step 8, the error output names the file and line number. Fix the
error, save, and re-run `lake build`.

## Artifacts and Notes

### Why `rfl` works for `olsBeta_eq_linearProjectionBeta`

`olsBeta X y` is defined as `(⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)`.
`linearProjectionBeta (Xᵀ * X) (Xᵀ *ᵥ y)` is defined as `⅟ (Xᵀ * X) *ᵥ (Xᵀ *ᵥ y)`.
These are identical up to notation, so Lean can close the goal by `rfl`. This is why no
explicit proof step is needed beyond `have hβ : ... := rfl`.

### What `dotProduct_star_self_nonneg` does

This Mathlib lemma (in `Mathlib.Algebra.Order.Star.Basic`) says
`∀ (v : α → ℝ), 0 ≤ v ⬝ᵥ v` (i.e., the dot product of a real vector with itself is
nonneg). The "star" in the name refers to the star-ring structure on ℝ where `star r = r`.
For real vectors this simplifies to the fact that a sum of squares is nonneg.

### Alternative direct proof (if the bridge approach fails)

If routing through `linearProjectionMSE_eq_at_beta_add_quadratic_form` causes difficulty
(e.g., universe-level or typeclass issues), `sumSquaredErrors_eq_olsBeta_add_gram_form` can
instead be proved directly with a `calc` block:

    theorem sumSquaredErrors_eq_olsBeta_add_gram_form ... := by
      set r := residual X y with hr_def
      set δ := b - olsBeta X y with hδ_def
      -- y - X*b = r - X*δ
      have hdecomp : y - X *ᵥ b = r - X *ᵥ δ := by
        simp [hr_def, hδ_def, residual, fitted, Matrix.mulVec_sub, sub_sub_cancel]
      -- Cross-term vanishes by normal equations
      have hcross : r ⬝ᵥ (X *ᵥ δ) = 0 := by
        rw [Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose]
        simp [normal_equations]
      -- Gram quadratic form identity
      have hgram : (X *ᵥ δ) ⬝ᵥ (X *ᵥ δ) = δ ⬝ᵥ ((Xᵀ * X) *ᵥ δ) := by
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
            vecMul_eq_mulVec_transpose, Matrix.transpose_transpose]
      -- Combine
      unfold sumSquaredErrors
      rw [hdecomp, sub_dotProduct, dotProduct_sub, hcross, hgram]
      ring

This direct proof does not require the Chapter 2 import. Use it if the bridge approach does
not typecheck.

## Interfaces and Dependencies

New declarations and their signatures after this plan is complete:

In `HansenEconometrics/LinearAlgebraUtils.lean`:

    lemma gram_quadratic_nonneg {n k : Type*} [Fintype n] [Fintype k]
        (X : Matrix n k ℝ) (v : k → ℝ) :
        0 ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v)

In `HansenEconometrics/Chapter3LeastSquaresAlgebra.lean`:

    lemma sumSquaredErrors_eq_linearProjectionMSE
        {n k : Type*} [Fintype n] [Fintype k]
        (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) :
        sumSquaredErrors X y b =
          linearProjectionMSE (Xᵀ * X) (Xᵀ *ᵥ y) (y ⬝ᵥ y) b

    theorem sumSquaredErrors_eq_olsBeta_add_gram_form
        {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
        (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) [Invertible (Xᵀ * X)] :
        sumSquaredErrors X y b =
          sumSquaredErrors X y (olsBeta X y) +
            (b - olsBeta X y) ⬝ᵥ ((Xᵀ * X) *ᵥ (b - olsBeta X y))

    theorem sumSquaredErrors_olsBeta_le
        {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
        (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) [Invertible (Xᵀ * X)] :
        sumSquaredErrors X y (olsBeta X y) ≤ sumSquaredErrors X y b

    theorem olsBeta_isMinOn
        {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]
        (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
        IsMinOn (sumSquaredErrors X y) Set.univ (olsBeta X y)

External Mathlib lemmas relied upon:
- `Matrix.mulVec_mulVec` (matrix-vector associativity: `(A * B) *ᵥ v = A *ᵥ (B *ᵥ v)`)
- `Matrix.dotProduct_mulVec` (adjoint identity: `u ⬝ᵥ (M *ᵥ v) = vecMul u M ⬝ᵥ v`)
- `Matrix.transpose_transpose` (`(Aᵀ)ᵀ = A`)
- `dotProduct_star_self_nonneg` (`0 ≤ v ⬝ᵥ v`)
- `sub_dotProduct`, `dotProduct_sub` (linearity of dot product in each argument)
- `dotProduct_comm` (symmetry: `u ⬝ᵥ v = v ⬝ᵥ u`)

Repo lemmas relied upon (new dependency):
- `gram_transpose` from `Chapter3Projections.lean`
  (`(Xᵀ * X)ᵀ = Xᵀ * X`, required by `linearProjectionMSE_eq_at_beta_add_quadratic_form`)
- `vecMul_eq_mulVec_transpose` from `LinearAlgebraUtils.lean`
- `linearProjectionMSE_eq_at_beta_add_quadratic_form` from `Chapter2LinearProjection.lean`
- `normal_equations` from `Chapter3LeastSquaresAlgebra.lean` (used in direct proof alternative)
