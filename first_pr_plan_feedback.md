# Updated assessment of `FIRST_PR_PLAN.md` (round 2)

This supersedes the round-1 assessment. The round-1 feedback raised two
blockers, one streamlining miss, three robustness/clarity concerns, and a
scope decision. The response file confirms all of these were adopted and the
plan was edited accordingly. I verified each change against the updated
`FIRST_PR_PLAN.md` and the current state of the repo.

**Verdict.** The plan is now substantially closer to landable. Both
blockers are resolved on paper, the streamlining is in place, scope is
explicit. One residual concern: the proof body of `hquad` inside the bridge
lemma still relies on an ambiguous multi-match `rw` and is likely to fail
at the `Matrix.transpose_transpose` step. Fix is small (one explicit
argument). Details below.

## 1. Round-1 fixes — verification

### 1.1 Circular import (was blocker)

The plan now moves `gram_transpose` from `Chapter3Projections.lean` into
`LinearAlgebraUtils.lean` (Step 1, Decision Log entry, and Concrete-Steps
Step 1(a)+(b)). Spot checks:

- The new `LinearAlgebraUtils.lean` body for `gram_transpose` matches
  `Chapter3Projections.lean:16-19`'s current proof (`rw [Matrix.transpose_mul,
  Matrix.transpose_transpose]`). ✓
- Downstream callers (`Chapter3Projections.lean:36`,
  `Chapter4LeastSquaresRegression.lean:80,120,529`) all open `namespace
  HansenEconometrics` and import `LinearAlgebraUtils` (transitively or
  directly), so the relocation does not break them. ✓
- The `import HansenEconometrics.Chapter2LinearProjection` line is added
  to `Chapter3LeastSquaresAlgebra.lean`, and Chapter 2's projection file
  imports only `Mathlib`, `Basic`, `LinearAlgebraUtils`, and
  `ProbabilityUtils` — none of which loop back to Chapter 3. ✓

Plan now compiles on this axis.

### 1.2 `Matrix.mulVec_mulVec` direction (was blocker)

`gram_quadratic_nonneg` now uses `← Matrix.mulVec_mulVec` (Step 2). Trace:

```
Goal: 0 ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v)
← Matrix.mulVec_mulVec     →   0 ≤ v ⬝ᵥ (Xᵀ *ᵥ (X *ᵥ v))
Matrix.dotProduct_mulVec   →   0 ≤ vecMul v Xᵀ ⬝ᵥ (X *ᵥ v)
vecMul_eq_mulVec_transpose →   0 ≤ (Xᵀ)ᵀ *ᵥ v ⬝ᵥ (X *ᵥ v)
Matrix.transpose_transpose →   0 ≤ X *ᵥ v ⬝ᵥ (X *ᵥ v)
exact dotProduct_star_self_nonneg (X *ᵥ v)
```

Each step has a unique match, so the chain is robust. The auxiliary prose
in Step 2 explaining "forward collapses, reverse expands" is consistent
with the repo conventions confirmed by the cross-file grep. ✓

### 1.3 Streamlining via `linearProjectionBeta_minimizes_MSE` (round-1 §2)

`sumSquaredErrors_olsBeta_le` now reduces to two bridge `rw`s, a definitional
`rfl`-rewrite, and an `exact`. Trace:

```
Goal: SSE X y (olsBeta X y) ≤ SSE X y b
rw [bridge X y b, bridge X y (olsBeta X y), olsBeta = LPB by rfl]
  → Goal: LPM ... (LPB ...) ≤ LPM ... b
exact linearProjectionBeta_minimizes_MSE _ _ _ (gram_transpose X)
                                              (gram_quadratic_nonneg X) b
```

This is exactly the engine I suggested. `linearProjectionBeta_minimizes_MSE`
at `Chapter2LinearProjection.lean:97` matches the call signature.
The `show olsBeta X y = linearProjectionBeta (Xᵀ * X) (Xᵀ *ᵥ y) from rfl`
trick is the right way to insert a definitional rewrite into the `rw [...]`
chain. ✓

The Decision Log entry on this is appropriately self-critical ("violated
principle 2" — same kind of duplication AGENTS.md prohibits). ✓

### 1.4 Brittle bridge proof (round-1 §3)

The bridge lemma is now structured as

```
have hcross : y ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ (Xᵀ *ᵥ y) := ...
have hquad  : (X *ᵥ b) ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ ((Xᵀ * X) *ᵥ b) := ...
unfold sumSquaredErrors linearProjectionMSE
rw [sub_dotProduct, dotProduct_sub, dotProduct_sub,
    dotProduct_comm (X *ᵥ b) y, hcross, hquad]
ring
```

`hcross` is fine — I traced it (LHS-first match of
`Matrix.dotProduct_mulVec` instantiates `?v = y, ?A = X, ?w = b`, the
follow-up `vecMul_eq_mulVec_transpose` substitutes, and the trailing
`dotProduct_comm` flips to match the RHS). ✓

The body of the bridge after the two `have`s also traces cleanly. After
the rewrites, the goal reduces to `(A - B) - (B - C) = A - 2B + C`, which
is a polynomial identity in `A := y ⬝ᵥ y`, `B := b ⬝ᵥ (Xᵀ *ᵥ y)`,
`C := b ⬝ᵥ ((Xᵀ * X) *ᵥ b)` and `ring` closes it. ✓

`hquad` is the residual concern. See §2 below.

### 1.5–1.7 Variable binders, scope, hygiene

- §4: signatures of `sumSquaredErrors_eq_linearProjectionMSE`,
  `sumSquaredErrors_olsBeta_le`, `olsBeta_isMinOn` no longer redeclare
  `{n k : Type*}` or `[Fintype n] [Fintype k] [DecidableEq k]`. They
  inherit from the file-level `variable` block. `gram_quadratic_nonneg`
  and `gram_transpose` in `LinearAlgebraUtils.lean` correctly do declare
  the binders explicitly because that file has no file-level `variable`. ✓

- §7 (scope): plan title, opening paragraph, theorem docstring, inventory
  cell, and Progress checklist all carry the "(existence half)" annotation.
  The Decision Log explicitly defers uniqueness to a follow-up and explains
  why (strict positive-definiteness needs a separate ~10-line proof).
  The deferred follow-up will need `sumSquaredErrors_eq_olsBeta_add_gram_form`,
  which is also explicitly deferred. ✓

- §5 (counts and ambiguity): the "five declarations" miscount is fixed —
  acceptance criterion 5 now lists three theorems in
  `Chapter3LeastSquaresAlgebra.lean`, matching what is actually added. The
  ambiguous `olsBeta_eq_linearProjectionBeta` Progress bullet is gone;
  the `rfl`-resolution is documented in the "Why `olsBeta = linearProjectionBeta`
  reduces to `rfl`" Artifacts note. ✓

- §6 (Gram-form-nonneg location and ℝ-specialization): unchanged from
  prior plan; Decision Log adds the ℝ→star-ring generalization flag. ✓

- Crosswalk subsection note: Step 7 explicitly states "this is a *new*
  section". ✓

## 2. Remaining concern: `hquad`'s `rw` chain still has a multi-match collision

The plan's `hquad`:

```lean
have hquad : (X *ᵥ b) ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ ((Xᵀ * X) *ᵥ b) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      vecMul_eq_mulVec_transpose, Matrix.transpose_transpose,
      dotProduct_comm]
```

Trace, assuming Lean 4's `rw` finds the first match in pre-order traversal
(LHS of `=` before RHS — confirmed by `Lean.Meta.kabstract`'s left-to-right
expression walk and consistent with every other `rw` in this repo):

1. `← Matrix.mulVec_mulVec` rewrites `(Xᵀ * X) *ᵥ b → Xᵀ *ᵥ (X *ᵥ b)` on
   the RHS (only place `(?N * ?M) *ᵥ ?v` matches). New goal:
   ```
   (X *ᵥ b) ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ (Xᵀ *ᵥ (X *ᵥ b))
   ```

2. `Matrix.dotProduct_mulVec` has LHS pattern `?v ⬝ᵥ (?A *ᵥ ?w)`. Two
   matches in the goal:
   - LHS of `=`: `(X *ᵥ b) ⬝ᵥ (X *ᵥ b)` with `?v = X *ᵥ b, ?A = X, ?w = b`
   - RHS of `=`: `b ⬝ᵥ (Xᵀ *ᵥ (X *ᵥ b))` with `?v = b, ?A = Xᵀ, ?w = X *ᵥ b`

   `rw` instantiates with the first match (LHS of `=`) and rewrites only
   syntactic occurrences of *that* instantiation:
   ```
   vecMul (X *ᵥ b) X ⬝ᵥ b = b ⬝ᵥ (Xᵀ *ᵥ (X *ᵥ b))
   ```

3. `vecMul_eq_mulVec_transpose` rewrites `vecMul (X *ᵥ b) X → Xᵀ *ᵥ (X *ᵥ b)`:
   ```
   Xᵀ *ᵥ (X *ᵥ b) ⬝ᵥ b = b ⬝ᵥ (Xᵀ *ᵥ (X *ᵥ b))
   ```

4. `Matrix.transpose_transpose` has LHS pattern `(?A)ᵀᵀ`. **No double
   transpose appears anywhere in the goal.** `rw` fails with "no
   progress" or "motive is not type correct".

So the proof breaks at step 4. The plan's prose around `hquad` doesn't
notice this because it's structurally analogous to `gram_quadratic_nonneg`
(which is unambiguous because it's an inequality `0 ≤ ...` with no `=`
goal to confuse the matching).

### Fix: provide explicit arguments to direct `Matrix.dotProduct_mulVec` to the RHS

```lean
have hquad : (X *ᵥ b) ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ ((Xᵀ * X) *ᵥ b) := by
  rw [← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec b Xᵀ (X *ᵥ b),
      vecMul_eq_mulVec_transpose,
      Matrix.transpose_transpose]
```

Re-trace:

1. `← Matrix.mulVec_mulVec`: as before.
   Goal: `(X *ᵥ b) ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ (Xᵀ *ᵥ (X *ᵥ b))`.

2. `Matrix.dotProduct_mulVec b Xᵀ (X *ᵥ b)` instantiates the lemma at
   `b ⬝ᵥ (Xᵀ *ᵥ (X *ᵥ b)) = vecMul b Xᵀ ⬝ᵥ (X *ᵥ b)`, forcing the rewrite
   to land on the RHS:
   ```
   (X *ᵥ b) ⬝ᵥ (X *ᵥ b) = vecMul b Xᵀ ⬝ᵥ (X *ᵥ b)
   ```

3. `vecMul_eq_mulVec_transpose`: `vecMul b Xᵀ → (Xᵀ)ᵀ *ᵥ b`:
   ```
   (X *ᵥ b) ⬝ᵥ (X *ᵥ b) = (Xᵀ)ᵀ *ᵥ b ⬝ᵥ (X *ᵥ b)
   ```

4. `Matrix.transpose_transpose` now has a real `(Xᵀ)ᵀ` to collapse:
   ```
   (X *ᵥ b) ⬝ᵥ (X *ᵥ b) = X *ᵥ b ⬝ᵥ (X *ᵥ b)
   ```
   Goal closes by `rfl` (implicit in `rw`).

Note that the trailing `dotProduct_comm` is dropped — the goal closes
without it, and leaving it in would error with "no progress" since
`(X *ᵥ b) ⬝ᵥ (X *ᵥ b)` is symmetric.

### Alternative fix: rebuild `hquad` from `Matrix.dotProduct_mulVec` as a `have`

The `LinearAlgebraUtils.lean:52` proof of
`quadratic_form_eq_dotProduct_of_symm_idempotent` already uses this
safer pattern:

```lean
have hquad : (X *ᵥ b) ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ ((Xᵀ * X) *ᵥ b) := by
  have h := Matrix.dotProduct_mulVec b Xᵀ (X *ᵥ b)
  rw [vecMul_eq_mulVec_transpose, Matrix.transpose_transpose] at h
  rw [← Matrix.mulVec_mulVec, ← h]
  -- Goal: (X *ᵥ b) ⬝ᵥ (X *ᵥ b) = (X *ᵥ b) ⬝ᵥ (X *ᵥ b)   -- closed by rfl
```

Either fix is fine; the explicit-argument version is two characters longer
than the current proof. The plan should adopt one of them.

## 3. Other small observations

- **Step 1(a) wording.** The plan says "Delete lines 15–19 (the
  `gram_transpose` declaration)." Line numbers are fine for a guide, but
  worth noting that Lean's docstring convention also includes the
  preceding doc comment as part of the declaration; the implementer should
  remove the doc-comment block above line 15 too, otherwise the comment
  is left dangling. Cosmetic only.

- **Acceptance criterion 4** says "lines 15–19 of the original file". The
  exact line range depends on whether the doc comment is counted; in the
  current `Chapter3Projections.lean`, the `gram_transpose` block is
  lines 15–19 with its docstring. After deletion, the file should compile
  cleanly. Worth a quick verification step: after Step 1(a), open
  `Chapter3Projections.lean` and confirm that `inv_gram_transpose` (which
  references `gram_transpose`) still resolves — it will, because the
  relocated `gram_transpose` lives in the same `HansenEconometrics`
  namespace and `LinearAlgebraUtils` is already imported transitively.

- **Step 3 import duplication risk.** The plan adds
  `import HansenEconometrics.Chapter2LinearProjection` to
  `Chapter3LeastSquaresAlgebra.lean`. This is correct, but the plan should
  also verify (or note) that `Chapter2LinearProjection` does not already
  get pulled in via `Chapter2CondExp`. Looking at the current imports of
  `Chapter2CondExp.lean` quickly would settle whether the new import is
  redundant — not a bug, just a tidiness note.

- **Inventory line-numbers.** The new crosswalk row points links to
  `Chapter3LeastSquaresAlgebra.lean` without a `#L<n>` anchor, while the
  existing rows in the same table do include line anchors (e.g.
  `#L16`, `#L20`, `#L32`, `#L84`). For consistency, the new entries should
  include line anchors too. These can be filled in after the file is
  saved and the line numbers are known; the plan should call this out as
  a final-pass step.

- **`olsBeta_isMinOn`'s `[Invertible (Xᵀ * X)]` hypothesis.** The plan
  correctly carries this through. Worth double-checking that Lean's
  `IsMinOn` predicate doesn't interfere with the typeclass argument when
  it's last in the binder list — in practice it shouldn't, but if there
  is friction it can be moved before the `:` to ensure it is in scope.

None of these are blockers.

## 4. Summary of remaining edits before this plan is implementable

1. **Fix `hquad` in `sumSquaredErrors_eq_linearProjectionMSE`** (Step 4):
   add explicit arguments to `Matrix.dotProduct_mulVec` and drop the
   trailing `dotProduct_comm`. See §2 above for the exact replacement.

2. (Optional, cosmetic) Adopt one of the small observations in §3 above —
   most importantly, add line-anchor URLs to the crosswalk entries when
   line numbers are known.

After (1), `lake build` should succeed. The plan is otherwise sound and
consistent with AGENTS.md principles 1–4.
