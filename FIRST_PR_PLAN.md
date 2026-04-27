# Formalize Hansen Theorem 3.1: OLS as a Minimizer of SSE (Existence Half)

This ExecPlan is a living document. The sections `Progress`, `Surprises & Discoveries`,
`Decision Log`, and `Outcomes & Retrospective` must be kept up to date as work proceeds.

Maintained in accordance with [PLANS.md](./PLANS.md).

## Purpose / Big Picture

After this change, the Lean source file `HansenEconometrics/Chapter3LeastSquaresAlgebra.lean`
will contain a machine-verified proof of the existence half of Hansen's Theorem 3.1: under
the assumption that X'X is invertible, the OLS coefficient vector `β̂ = (X'X)⁻¹ X'Y`
attains the minimum of the sum of squared errors `S(b) = (Y - Xb)'(Y - Xb)`.

Currently the repo proves that `β̂` satisfies the normal equations and that any solution to the
normal equations equals `β̂` (`olsBeta_eq_of_normal_equations`). What is missing is the
optimization layer: a verified statement that for every `b ∈ Rᵏ`, `S(β̂) ≤ S(b)`.

Scope note. Hansen's Theorem 3.1 is the *argmin* statement, which strictly requires
*uniqueness* of the minimizer in addition to the inequality `S(β̂) ≤ S(b)`. This plan covers
the inequality (the existence half). The uniqueness statement (`b = β̂` whenever `S(b) = S(β̂)`)
mirrors `linearProjectionBeta_eq_of_MSE_eq` from Chapter 2 and is intentionally deferred to a
follow-up PR. The reason for the split: uniqueness requires strict positive-definiteness of
`X'X` (which is implied by `[Invertible (X'X)]` plus the Gram nonneg lemma but takes a
separate proof), and keeping the first PR small simplifies review.

After this plan is executed, the Chapter 3 crosswalk in `inventory/ch3-inventory.md` will have
a non-blank Lean cell for Theorem 3.1 (with an explicit "(existence half)" annotation), and
`lake build` will succeed with no new `sorry`s.

## Progress

- [ ] Read and understand all files listed in "Context and Orientation" below.
- [ ] Move `gram_transpose` from `Chapter3Projections.lean` to `LinearAlgebraUtils.lean`.
- [ ] Add `gram_quadratic_nonneg` to `LinearAlgebraUtils.lean`.
- [ ] Add `import HansenEconometrics.Chapter2LinearProjection` to `Chapter3LeastSquaresAlgebra.lean`.
- [ ] Add `sumSquaredErrors_eq_linearProjectionMSE` to `Chapter3LeastSquaresAlgebra.lean`.
- [ ] Add `sumSquaredErrors_olsBeta_le` to `Chapter3LeastSquaresAlgebra.lean`.
- [ ] Add `olsBeta_isMinOn` to `Chapter3LeastSquaresAlgebra.lean`.
- [ ] Update the Theorem 3.1 row in `inventory/ch3-inventory.md` (with "existence half" annotation).
- [ ] Add a "Lean-only bridge results" subsection to `inventory/ch3-inventory.md` (new section).
- [ ] Run `lake build` and confirm it succeeds with zero errors and zero `sorry`s.

## Surprises & Discoveries

(Fill in as work proceeds.)

## Decision Log

- Decision: Move `gram_transpose` from `Chapter3Projections.lean` to `LinearAlgebraUtils.lean`.
  Rationale: An earlier draft of this plan tried to call `gram_transpose X` from
  `Chapter3LeastSquaresAlgebra.lean`. But `gram_transpose` lives in `Chapter3Projections.lean`,
  which already imports `Chapter3LeastSquaresAlgebra.lean`, so importing `Chapter3Projections`
  back from `Chapter3LeastSquaresAlgebra` would create a cycle. `gram_transpose` is a
  pure matrix-algebra fact (`(Xᵀ * X)ᵀ = Xᵀ * X`) with multiple downstream consumers
  (`Chapter3Projections.lean`, `Chapter4LeastSquaresRegression.lean`); per AGENTS.md
  module-boundary policy it belongs in the shared utility layer.
  Date/Author: revised plan after feedback review.

- Decision: Use `linearProjectionBeta_minimizes_MSE` (Chapter 2, line 97) directly rather
  than reproving the minimization argument by hand in Chapter 3.
  Rationale: AGENTS.md principle 2 ("reuse repo theorems before adding new ones") applies
  here. Chapter 2 already contains both the completing-the-square *identity* and the
  *inequality* derived from it; there is no need to re-derive the inequality. With the
  bridge lemma plus `gram_quadratic_nonneg` plus `gram_transpose`, the Chapter 3 minimality
  theorem reduces to a few rewrites and one `exact`. The earlier draft of this plan reused
  the identity but reproved the inequality, which violated principle 2.
  Date/Author: revised plan after feedback review.

- Decision: Drop `sumSquaredErrors_eq_olsBeta_add_gram_form` (the SSE-side completing-the-square
  decomposition) from this PR.
  Rationale: It is no longer on the critical path once the minimality proof routes through
  `linearProjectionBeta_minimizes_MSE`. Including it as dead code adds review burden without
  immediate benefit. It is a natural component of the uniqueness follow-up PR, where strict
  positive-definiteness lets us conclude `b = β̂` from `(b - β̂)' X'X (b - β̂) = 0`. Defer to
  that follow-up.
  Date/Author: revised plan after feedback review.

- Decision: Refactor `sumSquaredErrors_eq_linearProjectionMSE` into two intermediate `have`
  lemmas (`hcross` and `hquad`) plus `unfold ... ; ring`, instead of a long chain of `rw`s.
  Rationale: Multi-match `rw` patterns (`Matrix.dotProduct_mulVec` matches both cross and
  quadratic terms; `dotProduct_sub` matches twice) are brittle in Lean 4 and depend on
  syntactic occurrence order. Naming the intermediate identities makes each rewrite target
  unambiguous and the proof robust to small reformatting.
  Date/Author: revised plan after feedback review.

- Decision: Place `gram_quadratic_nonneg` in `LinearAlgebraUtils.lean`.
  Rationale: It is a pure matrix-algebra fact that is likely to be reused in later chapters
  (e.g., Ch 5 chi-square bounds, Ch 7 covariance estimator bounds). Per AGENTS.md
  module-boundary policy it belongs in the shared utility layer.
  Note: this lemma is currently specialized to ℝ. If complex matrices appear in later
  chapters (e.g., spectral decompositions), it can be generalized to fields with a star
  structure where `dotProduct_star_self_nonneg` holds.
  Date/Author: initial plan.

- Decision: State Theorem 3.1 (existence half) both as a direct inequality
  `sumSquaredErrors_olsBeta_le` and as an `IsMinOn` wrapper `olsBeta_isMinOn`.
  Rationale: The direct inequality `∀ b, SSE(β̂) ≤ SSE(b)` is the mathematically useful form
  for downstream results. `IsMinOn` is the Mathlib-standard predicate for minimizers and will
  interoperate with Mathlib's optimization library if later results need it.
  Date/Author: initial plan.

- Decision: Scope this PR to the existence half of Hansen Theorem 3.1; defer uniqueness to a
  follow-up.
  Rationale: Hansen's Theorem 3.1 is the argmin statement, which includes uniqueness. The
  inequality `S(β̂) ≤ S(b)` only needs nonneg of the Gram form; uniqueness needs strict
  positivity. Strict positivity follows from `[Invertible (Xᵀ * X)]` plus the nonneg lemma,
  but is a separate ~10-line proof analogous to `linearProjectionBeta_eq_of_MSE_eq`. Keeping
  this PR focused on a single theorem keeps review simple.
  Date/Author: revised plan after feedback review.

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
- `rw [h]` — rewrite the goal left-to-right using equation h. `rw [← h]` rewrites
  right-to-left. The direction matters: `Matrix.mulVec_mulVec : A *ᵥ (B *ᵥ v) = (A * B) *ᵥ v`
  collapses iterated `*ᵥ` in the forward direction; use `← Matrix.mulVec_mulVec` to expand.
- `simp [h, ...]` — simplify the goal using a set of lemmas
- `have h : T := proof` — introduce an intermediate fact `h` of type `T` for use later
- `linarith [h1, h2]` — close a linear arithmetic goal using hypotheses
- `sorry` — placeholder for a missing proof; a file with `sorry` still compiles but is flagged
- `exact e` — close the goal by providing a term `e` of the right type
- `unfold f` — replace `f ...` with its definition
- `ring` — close a goal that is a polynomial identity in a commutative ring

### Key files

All file paths are relative to the repository root.

- `HansenEconometrics/Chapter3LeastSquaresAlgebra.lean` — the main Chapter 3 OLS algebra file.
  Contains `sumSquaredErrors`, `olsBeta`, `residual`, `fitted`, `normal_equations`, and
  `olsBeta_eq_of_normal_equations`. This is where Theorem 3.1 (existence) will be added.
  Has a file-level `variable` block: `{n k : Type*}`, `[Fintype n]`, `[Fintype k]`,
  `[DecidableEq k]`. New theorems should inherit these rather than re-declaring them.

- `HansenEconometrics/Chapter3Projections.lean` — hat matrix, annihilator matrix, and their
  properties. Currently contains `gram_transpose` (line 16); this plan moves that lemma to
  `LinearAlgebraUtils.lean`. Also contains `inv_gram_transpose`, `hatMatrix`,
  `annihilatorMatrix`. Imports `Chapter3LeastSquaresAlgebra`.

- `HansenEconometrics/Chapter2LinearProjection.lean` — population linear projection algebra.
  Contains `linearProjectionBeta`, `linearProjectionMSE`,
  `linearProjectionMSE_eq_at_beta_add_quadratic_form` (the completing-the-square identity, line 63),
  and crucially `linearProjectionBeta_minimizes_MSE` (line 97), which packages the inequality
  `MSE(β) ≤ MSE(b)` directly. The plan reuses this last theorem rather than reproving it.

- `HansenEconometrics/LinearAlgebraUtils.lean` — shared matrix helper lemmas. Contains
  `vecMul_eq_mulVec_transpose` (key for converting row-vector products to column-vector form),
  `quadratic_form_eq_dotProduct_of_symm_idempotent`, and `rank_eq_natCast_trace_of_isHermitian_idempotent`.
  This file has no file-level `variable` block, so new lemmas here must declare their type
  parameters and instance arguments explicitly. We will add `gram_transpose` (relocated) and
  `gram_quadratic_nonneg` (new) here.

- `inventory/ch3-inventory.md` — the chapter crosswalk. After completion, the Theorem 3.1 row
  must be updated with the new Lean theorem names, and a new "Lean-only bridge results"
  subsection added.

### The existing theorem we reuse from Chapter 2

`linearProjectionBeta_minimizes_MSE` in `Chapter2LinearProjection.lean` (line 97):

    theorem linearProjectionBeta_minimizes_MSE
        (QXX : Matrix k k ℝ) (QXY : k → ℝ) (QYY : ℝ) [Invertible QXX]
        (hQXXt : QXXᵀ = QXX)
        (hQXX_nonneg : ∀ v : k → ℝ, 0 ≤ v ⬝ᵥ (QXX *ᵥ v))
        (b : k → ℝ) :
        linearProjectionMSE QXX QXY QYY (linearProjectionBeta QXX QXY) ≤
          linearProjectionMSE QXX QXY QYY b

Specializing `QXX = Xᵀ * X`, `QXY = Xᵀ *ᵥ y`, `QYY = y ⬝ᵥ y` with the hypotheses provided
by `gram_transpose X` and `gram_quadratic_nonneg X` yields exactly the SSE inequality once
`sumSquaredErrors` is rewritten in `linearProjectionMSE` form via the bridge lemma.

### The mathematical proof

The proof has three pieces, all delegated to existing or about-to-be-added repo lemmas.

Piece 1 — bridge SSE to abstract MSE. Show

    sumSquaredErrors X y b = linearProjectionMSE (Xᵀ * X) (Xᵀ *ᵥ y) (y ⬝ᵥ y) b

by dot-product algebra. The two key intermediate identities:

  - `y ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ (Xᵀ *ᵥ y)` (cross term)
  - `(X *ᵥ b) ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ ((Xᵀ * X) *ᵥ b)` (quadratic term)

Once these are isolated as named `have`s, the rest is `unfold + ring`.

Piece 2 — observe `olsBeta = linearProjectionBeta` definitionally. Both unfold to
`(⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)`, so the equality is `rfl`.

Piece 3 — apply `linearProjectionBeta_minimizes_MSE`. With `gram_transpose X` providing the
symmetry hypothesis and `gram_quadratic_nonneg X` providing the nonneg hypothesis, the
abstract minimization theorem fires and closes the inequality.

## Plan of Work

The work touches four existing files and creates no new files.

### File 1: `HansenEconometrics/LinearAlgebraUtils.lean`

Two additions:

(a) Move `gram_transpose` here from `Chapter3Projections.lean`. The proof body is unchanged.
    Place it before `vecMul_eq_mulVec_transpose` (or anywhere convenient — the file has no
    file-level `variable` block, so each lemma stands alone).

(b) Add `gram_quadratic_nonneg` after `diag_nonneg_of_symm_idempotent`. The proof uses
    `← Matrix.mulVec_mulVec` to *expand* the `(Xᵀ * X) *ᵥ v` form into `Xᵀ *ᵥ (X *ᵥ v)`,
    then `Matrix.dotProduct_mulVec` and `vecMul_eq_mulVec_transpose` to convert
    `v ⬝ᵥ (Xᵀ *ᵥ (X *ᵥ v))` into `(X *ᵥ v) ⬝ᵥ (X *ᵥ v)`, which is closed by
    `dotProduct_star_self_nonneg`.

### File 2: `HansenEconometrics/Chapter3Projections.lean`

Remove the `gram_transpose` declaration (currently lines 15–19). All downstream usages —
`inv_gram_transpose` in this file (line 33, `simpa [gram_transpose ...]`), and Chapter 4
references — continue to resolve because both files transitively import `LinearAlgebraUtils`,
which now hosts `gram_transpose` in the same `HansenEconometrics` namespace.

### File 3: `HansenEconometrics/Chapter3LeastSquaresAlgebra.lean`

Three additions:

1. Add the import `import HansenEconometrics.Chapter2LinearProjection` to the header.
   Verify no circular dependency: `Chapter2LinearProjection` imports only `Mathlib`, `Basic`,
   `LinearAlgebraUtils`, and `ProbabilityUtils`. None of those import `Chapter3LeastSquaresAlgebra`.

2. Add `sumSquaredErrors_eq_linearProjectionMSE`: a bridge lemma identifying the Chapter 3
   SSE with the abstract Chapter 2 MSE when moments are sample moments. Proof via two named
   intermediate identities (`hcross`, `hquad`) plus `unfold + ring`.

3. Add `sumSquaredErrors_olsBeta_le`: the existence half of Theorem 3.1, proved by rewriting
   both sides via the bridge lemma, observing `olsBeta = linearProjectionBeta` by `rfl`,
   and applying `linearProjectionBeta_minimizes_MSE` with `gram_transpose X` and
   `gram_quadratic_nonneg X` as hypothesis arguments.

4. Add `olsBeta_isMinOn`: the `IsMinOn` wrapper, proved by `intro b _; exact ...`.

All three new declarations inherit the file-level `variable` block (`{n k : Type*}`,
`[Fintype n]`, `[Fintype k]`, `[DecidableEq k]`) and do not redeclare those binders.

### File 4: `inventory/ch3-inventory.md`

Update the Theorem 3.1 row in the crosswalk table to point to the new Lean theorems with
an "(existence half)" annotation. Add a new "Lean-only bridge results" subsection (no such
section currently exists) listing the bridge lemma and the new utility lemma.

## Concrete Steps

Work in the repository root. All `lake` commands should be run there.

**Step 0 — Understand the environment.**

Open the repository in VS Code with the Lean 4 extension installed. Open
`HansenEconometrics/Chapter3LeastSquaresAlgebra.lean`. Wait for the blue spinner in the
bottom bar to finish (Lean is loading Mathlib; this takes several minutes the first time).
Once the spinner disappears, hovering over any theorem name shows its type, and red
underlines indicate errors. This is your feedback loop.

**Step 1 — Move `gram_transpose` to `LinearAlgebraUtils.lean`.**

(a) Open `HansenEconometrics/Chapter3Projections.lean`. Delete lines 15–19 (the
`gram_transpose` declaration). Save. The file will momentarily show errors at the call sites
of `gram_transpose` (line 36 in `inv_gram_transpose` and elsewhere); these will resolve once
step 1(b) is done and the file is rechecked.

(b) Open `HansenEconometrics/LinearAlgebraUtils.lean`. Insert near the top of the
`namespace HansenEconometrics` block (e.g., immediately before `vecMul_eq_mulVec_transpose`):

    /-- Hansen Theorem 3.3.1 helper: the Gram matrix `Xᵀ * X` is symmetric. Relocated here from
    `Chapter3Projections.lean` so that earlier files (e.g., `Chapter3LeastSquaresAlgebra.lean`)
    can use it without creating a circular import. -/
    theorem gram_transpose {n k : Type*} [Fintype n] [Fintype k]
        (X : Matrix n k ℝ) :
        (Xᵀ * X)ᵀ = Xᵀ * X := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]

Save. The Chapter 3 projections file should now turn green again.

**Step 2 — Add `gram_quadratic_nonneg` to `LinearAlgebraUtils.lean`.**

Insert after `diag_nonneg_of_symm_idempotent` (around current line 68) and before
`rank_eq_natCast_trace_of_isHermitian_idempotent`:

    /-- The Gram matrix `Xᵀ * X` generates a nonneg quadratic form. This is the
    finite-sample counterpart of positive semidefiniteness: for every vector `v`,
    `v ⬝ᵥ ((Xᵀ * X) *ᵥ v) ≥ 0`. -/
    lemma gram_quadratic_nonneg {n k : Type*} [Fintype n] [Fintype k]
        (X : Matrix n k ℝ) (v : k → ℝ) :
        0 ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          vecMul_eq_mulVec_transpose, Matrix.transpose_transpose]
      exact dotProduct_star_self_nonneg (X *ᵥ v)

Note the leading `←` on `Matrix.mulVec_mulVec`. The Mathlib lemma reads
`A *ᵥ (B *ᵥ v) = (A * B) *ᵥ v`, i.e., the forward direction *collapses* iterated `*ᵥ`. Our
goal `0 ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v)` already has the collapsed form; we want to *expand* it to
`Xᵀ *ᵥ (X *ᵥ v)`, hence `←`.

Save and verify the lemma is green.

Proof explanation for a Lean novice:
- `← Matrix.mulVec_mulVec` rewrites `(Xᵀ * X) *ᵥ v` as `Xᵀ *ᵥ (X *ᵥ v)`.
- `Matrix.dotProduct_mulVec` rewrites `v ⬝ᵥ (Xᵀ *ᵥ (X *ᵥ v))` as `(Matrix.vecMul v Xᵀ) ⬝ᵥ (X *ᵥ v)`.
- `vecMul_eq_mulVec_transpose` (already in this file) rewrites `Matrix.vecMul v Xᵀ` as
  `(Xᵀ)ᵀ *ᵥ v`.
- `Matrix.transpose_transpose` simplifies `(Xᵀ)ᵀ` to `X`.
- After all rewrites the goal is `0 ≤ (X *ᵥ v) ⬝ᵥ (X *ᵥ v)`, closed by
  `dotProduct_star_self_nonneg`.

**Step 3 — Add the import to `Chapter3LeastSquaresAlgebra.lean`.**

Open `HansenEconometrics/Chapter3LeastSquaresAlgebra.lean`. The import block currently reads:

    import Mathlib
    import HansenEconometrics.Basic
    import HansenEconometrics.LinearAlgebraUtils
    import HansenEconometrics.Chapter2CondExp

Add one line:

    import HansenEconometrics.Chapter2LinearProjection

after the existing imports. After saving, the Lean server will reload the file (the spinner
will reappear briefly). All existing theorems should remain green.

**Step 4 — Add `sumSquaredErrors_eq_linearProjectionMSE`.**

Insert in `Chapter3LeastSquaresAlgebra.lean` immediately before `end HansenEconometrics`.
Note: the surrounding file has `variable {n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]`
already declared; do NOT redeclare these in the new theorem signatures.

    /-- Bridge lemma: the Chapter 3 sum-of-squared-errors equals the Chapter 2
    `linearProjectionMSE` when the moment matrices are the sample Gram matrix and
    cross-moment vector. This connects the two notations so we can reuse the
    Chapter 2 minimization theorem. -/
    lemma sumSquaredErrors_eq_linearProjectionMSE
        (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) :
        sumSquaredErrors X y b =
          linearProjectionMSE (Xᵀ * X) (Xᵀ *ᵥ y) (y ⬝ᵥ y) b := by
      have hcross : y ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ (Xᵀ *ᵥ y) := by
        rw [Matrix.dotProduct_mulVec, vecMul_eq_mulVec_transpose, dotProduct_comm]
      have hquad : (X *ᵥ b) ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ ((Xᵀ * X) *ᵥ b) := by
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
            vecMul_eq_mulVec_transpose, Matrix.transpose_transpose,
            dotProduct_comm]
      unfold sumSquaredErrors linearProjectionMSE
      rw [sub_dotProduct, dotProduct_sub, dotProduct_sub,
          dotProduct_comm (X *ᵥ b) y, hcross, hquad]
      ring

Proof explanation: The two `have` lemmas isolate the only non-trivial dot-product moves —
the cross-term identity and the quadratic-term identity. After `unfold`, the goal is a
polynomial identity in three named scalar quantities (`y ⬝ᵥ y`, `b ⬝ᵥ (Xᵀ *ᵥ y)`,
`b ⬝ᵥ ((Xᵀ * X) *ᵥ b)`); `ring` closes it after the cross-/quadratic-term substitutions.

The named-`have` style is more robust than a long `rw` chain because each rewrite targets a
unique subterm; multi-match `rw` (where the same lemma applies to several subterms) is
brittle in Lean 4 and depends on syntactic occurrence order.

If the proof does not typecheck as written, paste it with the proof body replaced by `sorry`,
then incrementally introduce tactics while watching the Lean infoview goal state.

**Step 5 — Add `sumSquaredErrors_olsBeta_le`.**

Insert immediately after the bridge lemma:

    /-- Hansen Theorem 3.1 (existence half): `olsBeta X y` attains the minimum of the sum
    of squared errors. For any coefficient vector `b`, `SSE(olsBeta X y) ≤ SSE(b)`.

    Uniqueness — `b = olsBeta X y` whenever `SSE(b) = SSE(olsBeta X y)` — requires strict
    positive-definiteness of `Xᵀ * X` and is left to a follow-up. -/
    theorem sumSquaredErrors_olsBeta_le
        (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) [Invertible (Xᵀ * X)] :
        sumSquaredErrors X y (olsBeta X y) ≤ sumSquaredErrors X y b := by
      rw [sumSquaredErrors_eq_linearProjectionMSE X y b,
          sumSquaredErrors_eq_linearProjectionMSE X y (olsBeta X y),
          show olsBeta X y = linearProjectionBeta (Xᵀ * X) (Xᵀ *ᵥ y) from rfl]
      exact linearProjectionBeta_minimizes_MSE (Xᵀ * X) (Xᵀ *ᵥ y) (y ⬝ᵥ y)
        (gram_transpose X) (gram_quadratic_nonneg X) b

Proof explanation:
- The first two `rw`s convert both sides of the inequality from `sumSquaredErrors` to
  `linearProjectionMSE` via the bridge lemma.
- The `show ... from rfl` rewrite replaces `olsBeta X y` with
  `linearProjectionBeta (Xᵀ * X) (Xᵀ *ᵥ y)`. Both definitions unfold to
  `(⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)`, so the equality is by `rfl`.
- `exact linearProjectionBeta_minimizes_MSE ...` closes the goal. Its hypotheses are:
  - `[Invertible QXX]` — supplied by `[Invertible (Xᵀ * X)]` in scope.
  - `(QXXᵀ = QXX)` — supplied by `gram_transpose X`.
  - `(∀ v, 0 ≤ v ⬝ᵥ (QXX *ᵥ v))` — supplied by `gram_quadratic_nonneg X`.

**Step 6 — Add `olsBeta_isMinOn`.**

Insert immediately after `sumSquaredErrors_olsBeta_le`:

    /-- Hansen Theorem 3.1 (existence half), packaged as `IsMinOn`: `olsBeta X y` is a
    global minimizer of `sumSquaredErrors X y` over all of `k → ℝ`. -/
    theorem olsBeta_isMinOn
        (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
        IsMinOn (sumSquaredErrors X y) Set.univ (olsBeta X y) := by
      intro b _
      exact sumSquaredErrors_olsBeta_le X y b

Proof explanation: `IsMinOn f s a` unfolds to `∀ x ∈ s, f a ≤ f x`. `intro b _` introduces
the point `b` and discards its (trivial) membership in `Set.univ`.

**Step 7 — Update the inventory crosswalk.**

Open `inventory/ch3-inventory.md`. Find the Theorem 3.1 row in the Crosswalk table, which
currently reads:

    | Theorem 3.1 objective-level argmin statement | $\hat{\beta} = \arg\min_b (Y - X b)'(Y - X b)$ |  |

Replace the blank Lean cell with:

    | Theorem 3.1 objective-level argmin statement (existence half) | $\hat{\beta} = \arg\min_b (Y - X b)'(Y - X b)$ | [sumSquaredErrors_olsBeta_le](../../HansenEconometrics/Chapter3LeastSquaresAlgebra.lean)<br>`sumSquaredErrors X y (olsBeta X y) ≤ sumSquaredErrors X y b`<br>[olsBeta_isMinOn](../../HansenEconometrics/Chapter3LeastSquaresAlgebra.lean)<br>`IsMinOn (sumSquaredErrors X y) Set.univ (olsBeta X y)` |

Add a new section (this is a *new* section — `inventory/ch3-inventory.md` does not currently
have a "Lean-only bridge results" heading) below the main Crosswalk table:

    ## Lean-only bridge results

    | Lean theorem | Role |
    | --- | --- |
    | [sumSquaredErrors_eq_linearProjectionMSE](../../HansenEconometrics/Chapter3LeastSquaresAlgebra.lean) | Identifies `sumSquaredErrors X y b` with `linearProjectionMSE (Xᵀ * X) (Xᵀ *ᵥ y) (y ⬝ᵥ y) b`, connecting Chapter 3 and Chapter 2 notation |
    | [gram_quadratic_nonneg](../../HansenEconometrics/LinearAlgebraUtils.lean) | `0 ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v)` for all `v`; the Gram matrix is positive semidefinite |
    | [gram_transpose](../../HansenEconometrics/LinearAlgebraUtils.lean) | `(Xᵀ * X)ᵀ = Xᵀ * X` (relocated from `Chapter3Projections.lean` to break a potential circular import) |

Also update the "First-pass formalization order — Layer 1 / Status" bullet about Theorem 3.1
("Theorem 3.1 objective-level argmin statement is still pending") to record that the existence
half landed and uniqueness is the remaining gap. A single replacement bullet:

    - Theorem 3.1 existence half (β̂ attains the minimum) landed via `sumSquaredErrors_olsBeta_le`
      and `olsBeta_isMinOn`. Uniqueness (any minimizer equals β̂) is still pending, mirroring
      `linearProjectionBeta_eq_of_MSE_eq` in Chapter 2.

**Step 8 — Final build check.**

Run from the repository root:

    lake build

Expected output: a series of compilation lines ending with no errors. If the build succeeds,
the terminal returns to the prompt with exit code 0. If there are errors, read the first error
message carefully — Lean error messages typically tell you exactly which tactic step failed and
what the current goal state is.

Also run, from the repository root:

    grep -rn "sorry" HansenEconometrics/ --include="*.lean"

Expected output: nothing (empty result). If any line is returned, the corresponding proof is
incomplete.

## Validation and Acceptance

Acceptance criteria:

1. `lake build` exits 0 with no errors.

2. `grep -rn "sorry" HansenEconometrics/ --include="*.lean"` returns no results.

3. In `HansenEconometrics/LinearAlgebraUtils.lean`, both `gram_transpose` (relocated) and
   `gram_quadratic_nonneg` (new) exist and are accepted by Lean (no red underlines).

4. In `HansenEconometrics/Chapter3Projections.lean`, the original `gram_transpose` declaration
   has been removed (lines 15–19 of the original file).

5. In `HansenEconometrics/Chapter3LeastSquaresAlgebra.lean`, the following three declarations
   exist and are accepted by Lean:
   - `sumSquaredErrors_eq_linearProjectionMSE`
   - `sumSquaredErrors_olsBeta_le`
   - `olsBeta_isMinOn`

6. The Theorem 3.1 row in `inventory/ch3-inventory.md` is non-blank and includes an
   "(existence half)" annotation.

7. `inventory/ch3-inventory.md` contains a new "Lean-only bridge results" subsection.

8. Behavioral check: place the cursor on `olsBeta_isMinOn` in VS Code. The Lean infoview
   should display the theorem type
   `IsMinOn (sumSquaredErrors X y) Set.univ (olsBeta X y)` with no errors.

## Idempotence and Recovery

Steps 2, 3, 4, 5, 6 are purely additive. Step 1 is the only non-additive step: it deletes the
original `gram_transpose` from `Chapter3Projections.lean` and re-adds it to
`LinearAlgebraUtils.lean`. If you stop midway with the deletion done but the addition not yet
saved, downstream files (`Chapter3Projections.lean` line 36, `Chapter4LeastSquaresRegression.lean`
lines 80, 120, 529) will show "unknown identifier `gram_transpose`" errors. The fix is to
complete step 1(b) — adding `gram_transpose` back to `LinearAlgebraUtils.lean`. The file
is then recovered.

If `lake build` fails after Step 8, the error output names the file and line number. Fix the
error, save, and re-run `lake build`.

## Artifacts and Notes

### Why `olsBeta = linearProjectionBeta` reduces to `rfl`

`olsBeta X y` is defined as `(⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)`.
`linearProjectionBeta (Xᵀ * X) (Xᵀ *ᵥ y)` is defined as `⅟ (Xᵀ * X) *ᵥ (Xᵀ *ᵥ y)`.
These are syntactically identical (the spelled-out parentheses do not affect parsing), so
Lean closes the goal by `rfl`. This is why no separate theorem `olsBeta_eq_linearProjectionBeta`
is needed — the equality is invisible at the proof level.

### What `dotProduct_star_self_nonneg` does

This Mathlib lemma says `∀ (v : α → ℝ), 0 ≤ v ⬝ᵥ v` (i.e., the dot product of a real vector
with itself is nonneg). The "star" in the name refers to the star-ring structure on ℝ where
`star r = r`. For real vectors this simplifies to the fact that a sum of squares is nonneg.

### Direction conventions for `Matrix.mulVec_mulVec`

The Mathlib lemma is `A *ᵥ (B *ᵥ v) = (A * B) *ᵥ v`. The forward direction (used by
`rw [Matrix.mulVec_mulVec]`) collapses an iterated matrix-vector product into a single
product against a composed matrix. The reverse direction (`rw [← Matrix.mulVec_mulVec]`)
expands a single product against a composed matrix into iterated form.

To choose: look at the goal. If the goal contains `A *ᵥ (B *ᵥ v)`, use forward. If the goal
contains `(A * B) *ᵥ v` and you want to introduce `A *ᵥ (B *ᵥ v)`, use `←`. This matters
because the wrong direction produces "no progress" or "motive is not type correct" errors.

The repo conventions confirm this: `Chapter3LeastSquaresAlgebra.lean:52` uses `←` to expand,
`Chapter3LeastSquaresAlgebra.lean:75` uses forward to collapse.

### Why we drop the SSE-side decomposition lemma from this PR

An earlier draft of this plan included a Chapter-3-side analog of
`linearProjectionMSE_eq_at_beta_add_quadratic_form` named
`sumSquaredErrors_eq_olsBeta_add_gram_form`. With the minimality theorem now routed through
`linearProjectionBeta_minimizes_MSE`, that decomposition is no longer used anywhere. It is
mathematically valid and will be needed for the uniqueness follow-up (where strict
positive-definiteness lets us conclude `b = β̂` from
`(b - β̂)' X'X (b - β̂) = 0`), but adding it now would be dead code. Defer to the uniqueness
PR, where it is the natural setup.

## Interfaces and Dependencies

New declarations and their signatures after this plan is complete:

In `HansenEconometrics/LinearAlgebraUtils.lean` (relocated):

    theorem gram_transpose {n k : Type*} [Fintype n] [Fintype k]
        (X : Matrix n k ℝ) :
        (Xᵀ * X)ᵀ = Xᵀ * X

In `HansenEconometrics/LinearAlgebraUtils.lean` (new):

    lemma gram_quadratic_nonneg {n k : Type*} [Fintype n] [Fintype k]
        (X : Matrix n k ℝ) (v : k → ℝ) :
        0 ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v)

In `HansenEconometrics/Chapter3LeastSquaresAlgebra.lean` (new; type-parameter and instance
binders are inherited from the file-level `variable` block):

    lemma sumSquaredErrors_eq_linearProjectionMSE
        (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) :
        sumSquaredErrors X y b =
          linearProjectionMSE (Xᵀ * X) (Xᵀ *ᵥ y) (y ⬝ᵥ y) b

    theorem sumSquaredErrors_olsBeta_le
        (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) [Invertible (Xᵀ * X)] :
        sumSquaredErrors X y (olsBeta X y) ≤ sumSquaredErrors X y b

    theorem olsBeta_isMinOn
        (X : Matrix n k ℝ) (y : n → ℝ) [Invertible (Xᵀ * X)] :
        IsMinOn (sumSquaredErrors X y) Set.univ (olsBeta X y)

External Mathlib lemmas relied upon:
- `Matrix.mulVec_mulVec` (matrix-vector associativity: `A *ᵥ (B *ᵥ v) = (A * B) *ᵥ v`).
  Used in the reverse direction (`←`) inside `gram_quadratic_nonneg` and the `hquad` step
  of the bridge lemma.
- `Matrix.dotProduct_mulVec` (`u ⬝ᵥ (M *ᵥ v) = vecMul u M ⬝ᵥ v`).
- `Matrix.transpose_mul` (`(A * B)ᵀ = Bᵀ * Aᵀ`), used in the proof of `gram_transpose`.
- `Matrix.transpose_transpose` (`(Aᵀ)ᵀ = A`).
- `dotProduct_star_self_nonneg` (`0 ≤ v ⬝ᵥ v` for real vectors).
- `sub_dotProduct`, `dotProduct_sub` (linearity of dot product in each argument).
- `dotProduct_comm` (symmetry: `u ⬝ᵥ v = v ⬝ᵥ u`).

Repo lemmas relied upon:
- `vecMul_eq_mulVec_transpose` from `LinearAlgebraUtils.lean`
  (`Matrix.vecMul x M = Mᵀ *ᵥ x`).
- `linearProjectionMSE` (the abstract MSE function) from `Chapter2LinearProjection.lean`.
- `linearProjectionBeta` (the abstract projection coefficient) from `Chapter2LinearProjection.lean`.
- `linearProjectionBeta_minimizes_MSE` from `Chapter2LinearProjection.lean`. This is the
  primary engine: with sample-moment specialization, it directly yields the SSE inequality.
