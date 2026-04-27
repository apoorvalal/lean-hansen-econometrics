# Assessment of `FIRST_PR_PLAN.md`

This is a critical review of the plan to formalize Hansen Theorem 3.1
(`olsBeta` is the SSE argmin) by adding lemmas to
`HansenEconometrics/LinearAlgebraUtils.lean` and
`HansenEconometrics/Chapter3LeastSquaresAlgebra.lean`.

The plan is well-organized and has the right overall mathematical strategy.
However, several issues — one of them blocking — will prevent `lake build`
from succeeding, and several streamlining opportunities are left on the table.

## 1. Blocking issues

### 1.1 Circular import: `gram_transpose` is unreachable from `Chapter3LeastSquaresAlgebra.lean`

The plan's Step 4 invokes `gram_transpose X` to discharge the symmetry hypothesis
of `linearProjectionMSE_eq_at_beta_add_quadratic_form`:

```lean
exact linearProjectionMSE_eq_at_beta_add_quadratic_form
  (Xᵀ * X) (Xᵀ *ᵥ y) (y ⬝ᵥ y) b (gram_transpose X)
```

But:

- `gram_transpose` is defined only in `HansenEconometrics/Chapter3Projections.lean`
  (line 16).
- `Chapter3Projections.lean` already imports `Chapter3LeastSquaresAlgebra.lean`
  (line 4 of that file).

So adding `import HansenEconometrics.Chapter3Projections` to
`Chapter3LeastSquaresAlgebra.lean` would create a cycle, and not adding it
leaves `gram_transpose` out of scope. Either way the file will not compile as
the plan stands. The "Interfaces and Dependencies" section names this as a
"new dependency" but never resolves the cyclic-import question; Step 2 of the
plan only adds `Chapter2LinearProjection`.

**Fix (recommended).** Move `gram_transpose` into
`HansenEconometrics/LinearAlgebraUtils.lean`. It is a pure matrix-algebra
fact (`(Xᵀ * X)ᵀ = Xᵀ * X`, proved by `rw [Matrix.transpose_mul,
Matrix.transpose_transpose]`) that already has multiple downstream consumers
(`Chapter3Projections.lean`, `Chapter4LeastSquaresRegression.lean`). Per the
AGENTS.md module-boundary policy this is exactly the right home for it.

**Alternative fix.** Inline the symmetry proof at the call site:

```lean
exact linearProjectionMSE_eq_at_beta_add_quadratic_form
  (Xᵀ * X) (Xᵀ *ᵥ y) (y ⬝ᵥ y) b
  (by rw [Matrix.transpose_mul, Matrix.transpose_transpose])
```

This avoids touching `LinearAlgebraUtils.lean`/`Chapter3Projections.lean` at
the cost of duplicating a one-line proof. Acceptable but less clean.

### 1.2 `Matrix.mulVec_mulVec` rewrite direction is wrong in `gram_quadratic_nonneg`

The Mathlib lemma is

```
Matrix.mulVec_mulVec : N *ᵥ (M *ᵥ v) = (N * M) *ᵥ v
```

i.e. forward `rw` *collapses* an iterated `*ᵥ`. This is corroborated by every
other call site in the repo:

- `Chapter2LinearProjection.lean:30,48` and `Chapter3LeastSquaresAlgebra.lean:75`
  use forward `Matrix.mulVec_mulVec` to collapse `A *ᵥ (B *ᵥ v)` into
  `(A * B) *ᵥ v`.
- `Chapter3LeastSquaresAlgebra.lean:52` and `Chapter3Projections.lean:196-197`
  use `← Matrix.mulVec_mulVec` to *expand* `(A * B) *ᵥ v` into `A *ᵥ (B *ᵥ v)`.

In `gram_quadratic_nonneg` the goal `0 ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v)` already has
the *collapsed* form `(Xᵀ * X) *ᵥ v`. We need to *expand* it to
`Xᵀ *ᵥ (X *ᵥ v)`, so the first rewrite must be `← Matrix.mulVec_mulVec`,
not `Matrix.mulVec_mulVec`. As written the plan's `rw` will fail with
"motive is not type correct" or "no progress" because no `A *ᵥ (B *ᵥ v)`
pattern exists in the goal.

The plan's *prose* description of this step is correct ("`Matrix.mulVec_mulVec`
rewrites `(Xᵀ * X) *ᵥ v` as `Xᵀ *ᵥ (X *ᵥ v)`"), but the Lean code does not
match the prose. The "Alternative direct proof" later in the plan correctly
uses `← Matrix.mulVec_mulVec` for an analogous step, so the bug is local to
the main proof block.

**Fix.** Change

```lean
rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    vecMul_eq_mulVec_transpose, Matrix.transpose_transpose]
```

to

```lean
rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    vecMul_eq_mulVec_transpose, Matrix.transpose_transpose]
```

## 2. Streamlining opportunity: reuse `linearProjectionBeta_minimizes_MSE`

The plan introduces both
`sumSquaredErrors_eq_olsBeta_add_gram_form` (the decomposition) and
`sumSquaredErrors_olsBeta_le` (the inequality), then derives the latter from
the former plus `gram_quadratic_nonneg`.

But `Chapter2LinearProjection.lean` already contains
`linearProjectionBeta_minimizes_MSE` (lines 97–105):

```lean
theorem linearProjectionBeta_minimizes_MSE
    (QXX : Matrix k k ℝ) (QXY : k → ℝ) (QYY : ℝ) [Invertible QXX]
    (hQXXt : QXXᵀ = QXX)
    (hQXX_nonneg : ∀ v : k → ℝ, 0 ≤ v ⬝ᵥ (QXX *ᵥ v))
    (b : k → ℝ) :
    linearProjectionMSE QXX QXY QYY (linearProjectionBeta QXX QXY) ≤
      linearProjectionMSE QXX QXY QYY b
```

This is exactly the inequality conclusion we want, lifted to the abstract
projection layer. With the bridge lemma plus `gram_quadratic_nonneg` plus
`gram_transpose` already in hand, `sumSquaredErrors_olsBeta_le` reduces to
two `rw`s and an `exact`:

```lean
theorem sumSquaredErrors_olsBeta_le
    (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) [Invertible (Xᵀ * X)] :
    sumSquaredErrors X y (olsBeta X y) ≤ sumSquaredErrors X y b := by
  rw [sumSquaredErrors_eq_linearProjectionMSE X y b,
      sumSquaredErrors_eq_linearProjectionMSE X y (olsBeta X y),
      show olsBeta X y = linearProjectionBeta (Xᵀ * X) (Xᵀ *ᵥ y) from rfl]
  exact linearProjectionBeta_minimizes_MSE (Xᵀ * X) (Xᵀ *ᵥ y) (y ⬝ᵥ y)
    (gram_transpose X) (gram_quadratic_nonneg X) b
```

Implications:

- `sumSquaredErrors_eq_olsBeta_add_gram_form` is no longer on the critical
  path for Theorem 3.1. It is still a useful identity (e.g. for a future
  uniqueness statement via strict positive-definiteness), so it can be kept,
  but it should be flagged as a *bonus* derivation rather than a required
  step.
- The Decision Log already cites AGENTS.md principle 2 ("reuse repo theorems
  before adding new ones"). That principle applies one level higher than the
  plan currently uses it: the plan reuses
  `linearProjectionMSE_eq_at_beta_add_quadratic_form` (the decomposition)
  but reproves the minimization argument by hand, when the minimization
  argument is *also* already in the repo as
  `linearProjectionBeta_minimizes_MSE`.

**Recommendation.** State `sumSquaredErrors_olsBeta_le` directly via
`linearProjectionBeta_minimizes_MSE`, and drop
`sumSquaredErrors_eq_olsBeta_add_gram_form` from the critical path (keep it
optionally as a parallel API surface or postpone to a follow-up PR).

## 3. Bridge-lemma proof is brittle

The proof of `sumSquaredErrors_eq_linearProjectionMSE` chains 10 rewrites
ending in `ring`. Several of the rewrite targets have multiple matches in
the goal (`Matrix.dotProduct_mulVec` matches both `y ⬝ᵥ (X *ᵥ b)` and
`(X *ᵥ b) ⬝ᵥ (X *ᵥ b)`; `dotProduct_sub` matches twice after the first
`sub_dotProduct`). Lean 4's `rw` semantics on multi-match patterns are
brittle and depend on syntactic occurrence order.

It is not obvious this chain compiles as written, and the plan itself
acknowledges this with the hedge "If the exact rewrite sequence does not
work as written: paste the lemma with `sorry` first".

**Recommendation.** Refactor the proof into named intermediate `have`s so
each `rw` has an unambiguous target. The cross-term identity
`y ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ (Xᵀ *ᵥ y)` and the quadratic-form identity
`(X *ᵥ b) ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ ((Xᵀ * X) *ᵥ b)` are the only two non-trivial
moves; once they are isolated as `have`s, the rest is `unfold` plus `ring`.
A sketch:

```lean
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
```

This is more robust to small differences in `rw` matching order.

## 4. Variable-block / signature redundancy

`Chapter3LeastSquaresAlgebra.lean` declares at the top:

```lean
variable {n k : Type*}
variable [Fintype n] [Fintype k] [DecidableEq k]
```

The existing theorems in the file (`normal_equations`, `olsBeta_eq_of_normal_equations`,
`fitted_add_residual`, …) inherit these and do not repeat them in their
signatures. The new theorems in the plan re-declare `{n k : Type*}` and
`[Fintype n] [Fintype k]` (and sometimes `[DecidableEq k]`) in each signature,
which is inconsistent with the file's existing style.

**Recommendation.** Drop the explicit binders. Match the file's existing
convention:

```lean
theorem sumSquaredErrors_olsBeta_le
    (X : Matrix n k ℝ) (y : n → ℝ) (b : k → ℝ) [Invertible (Xᵀ * X)] :
    sumSquaredErrors X y (olsBeta X y) ≤ sumSquaredErrors X y b := ...
```

For `gram_quadratic_nonneg` in `LinearAlgebraUtils.lean`, the explicit
`{n k : Type*} [Fintype n] [Fintype k]` *is* needed, because that file
has no file-level `variable` block for those parameters. The plan handles
this correctly.

Note: `gram_quadratic_nonneg` does **not** require `[DecidableEq k]`
(matrix multiplication and `*ᵥ` only need finiteness). The plan correctly
omits it. Worth keeping that omission deliberate.

## 5. Correctness nits

- **Acceptance criterion 2** says "the following five declarations" but
  lists only four (`sumSquaredErrors_eq_linearProjectionMSE`,
  `sumSquaredErrors_eq_olsBeta_add_gram_form`, `sumSquaredErrors_olsBeta_le`,
  `olsBeta_isMinOn`). Either the count is wrong or
  `olsBeta_eq_linearProjectionBeta` (mentioned in Progress and the Artifacts
  section but not in the actual concrete steps) was meant to be a fifth
  declaration. The plan resolves it as `have hβ : ... := rfl` inside Step 4,
  so the count should read "four". The unticked Progress entry
  "Add `olsBeta_eq_linearProjectionBeta` (or inline)" is similarly ambiguous
  and should be rewritten as "inline `olsBeta = linearProjectionBeta` via
  `rfl` in Step 4" to match what actually happens.

- **`olsBeta = linearProjectionBeta` by `rfl`** is asserted in the plan and
  in the Artifacts note. I checked: `olsBeta X y` unfolds to
  `(⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)` and
  `linearProjectionBeta (Xᵀ * X) (Xᵀ *ᵥ y)` unfolds to
  `⅟ (Xᵀ * X) *ᵥ (Xᵀ *ᵥ y)`. These are syntactically identical, so `rfl`
  is correct. ✓

- **`IsMinOn` namespace.** `IsMinOn` lives in `Mathlib.Order.MinMax` /
  `Mathlib.Analysis.Convex` machinery; since the file does
  `import Mathlib` it is available without a further import. The plan's
  use of `Set.univ` and the `intro b _` pattern is standard. ✓

- **Crosswalk subsection.** The plan adds a new "Lean-only bridge results"
  subsection to `inventory/ch3-inventory.md`. The chapter currently has
  no such section; the AGENTS.md crosswalk policy explicitly authorizes
  this pattern, so the addition is appropriate. The plan should mention
  this is a *new* section so the reviewer doesn't look for an existing one
  to extend.

## 6. Strategic comment: where does the Gram-form-nonneg fact really belong?

The plan places `gram_quadratic_nonneg` in `LinearAlgebraUtils.lean`,
arguing that downstream chapters (Ch 5 chi-square bounds, Ch 7 covariance
estimator bounds) will benefit. This is the right call.

One stronger refinement: the lemma generalises immediately to any field with
a star structure where `dotProduct_star_self_nonneg` holds. For now real
matrices are the only client, so specialising to ℝ is fine; just be aware
that if/when complex matrices appear (e.g. spectral decompositions in Ch 7
or beyond), the lemma will need to be generalised or duplicated.

Not a blocker — just a flag.

## 7. Docstring / inventory hygiene

- The plan's docstring for `sumSquaredErrors_olsBeta_le` says "Hansen
  Theorem 3.1", but Hansen Theorem 3.1 is the *argmin* statement
  (`β̂ = argmin_b S(b)`), which strictly requires *uniqueness* of the
  minimizer — not just that `β̂` attains the min. With only positive
  *semi*-definiteness of `Xᵀ * X` (which is what the plan proves), `β̂`
  is *a* minimum but not provably *the* minimum. Under the
  `[Invertible (Xᵀ * X)]` hypothesis we additionally have strict
  positive-definiteness, so uniqueness *does* hold and a follow-up
  `olsBeta_eq_of_minimizer` analogous to
  `linearProjectionBeta_eq_of_MSE_eq` (Chapter 2 line 120) would close
  the gap. The plan does not include this and could either:
  - widen scope to include uniqueness (one extra theorem, mirrors
    `linearProjectionBeta_eq_of_MSE_eq` directly via the bridge), or
  - narrow the docstring to "Hansen Theorem 3.1 (existence half)" and
    leave uniqueness to a follow-up PR.

  Either is fine, but the current plan claims the full Theorem 3.1 with
  only the existence half formalised. Worth an explicit decision.

- The Progress checklist contains the entry "Add `olsBeta_eq_linearProjectionBeta`
  (or inline)". As noted above this is a defensible-by-`rfl` step that
  the plan inlines. The bullet should be edited to reflect that, otherwise
  it reads as a deliverable that never gets checked off.

## 8. Summary of recommended edits

1. **Move `gram_transpose` from `Chapter3Projections.lean` to
   `LinearAlgebraUtils.lean`** (or inline its trivial proof at the call
   site). Without this, `Chapter3LeastSquaresAlgebra.lean` cannot reach
   `gram_transpose` without a circular import. **(blocker)**

2. **Change `Matrix.mulVec_mulVec` to `← Matrix.mulVec_mulVec`** in the
   first rewrite of `gram_quadratic_nonneg`. **(blocker)**

3. **Replace `sumSquaredErrors_olsBeta_le`'s manual-decomposition proof**
   with a direct call to `linearProjectionBeta_minimizes_MSE`, removing
   the dependency on `sumSquaredErrors_eq_olsBeta_add_gram_form` from
   the critical path. The decomposition lemma can stay as a parallel
   API but is no longer required. *(streamlining)*

4. **Refactor `sumSquaredErrors_eq_linearProjectionMSE`** into two
   intermediate `have` lemmas plus `unfold ... ; ring`. This is
   resilient to the brittleness of multi-match `rw`. *(robustness)*

5. **Drop redundant `{n k : Type*} [Fintype n] [Fintype k] [DecidableEq k]`
   binders** from new theorem signatures in `Chapter3LeastSquaresAlgebra.lean`;
   inherit from the file-level `variable` block instead. *(consistency)*

6. **Decide and document** whether this PR closes "Hansen Theorem 3.1
   in full" (requires also formalising uniqueness via
   strict positive-definiteness, mirroring `linearProjectionBeta_eq_of_MSE_eq`)
   or only the existence half. Update the docstring and inventory cell
   accordingly.

7. **Fix the "five declarations" / `olsBeta_eq_linearProjectionBeta`
   inconsistency** in the Progress checklist and acceptance criteria.

After (1) and (2), `lake build` should succeed; (3)–(7) are improvements
in line with AGENTS.md principles 1–4.
