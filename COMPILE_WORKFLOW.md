# Compile-and-Iterate Workflow for Lean + Claude Code

This document describes the day-to-day workflow for writing Lean proofs in this repo using
VS Code's Lean extension as your live feedback loop and Claude Code as your drafting and
debugging partner. It is aimed at someone new to Lean.

## One-time prerequisites

You need three pieces of software installed:

1. **Lean 4 toolchain via `elan`.** This is Lean's version manager. Install:

       curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

   The repo's `lean-toolchain` file pins the exact version (currently
   `leanprover/lean4:v4.29.0`), and `elan` will install it automatically the first time
   you build.

2. **VS Code** plus the **lean4** extension by `leanprover`. Install VS Code from
   <https://code.visualstudio.com/>, then in VS Code go to Extensions (Ctrl+Shift+X /
   Cmd+Shift+X), search for `lean4`, and install the one published by `leanprover`.

3. **Claude Code.** You already have this. It will live in a terminal window alongside
   VS Code.

## First-time project setup

From the repository root:

    lake exe cache get
    lake build

The first command downloads a precompiled Mathlib cache (saves ~30 minutes of compilation).
The second compiles the project. The first build after a fresh clone takes 5–15 minutes
even with the cache; subsequent builds are incremental and fast.

Open the project: `code .` from the repo root, or File → Open Folder in VS Code.

Open any `.lean` file. A blue spinner appears in the bottom status bar — that is Lean
loading Mathlib for the file. The first file takes 2–4 minutes; subsequent files in the
same VS Code session are seconds.

## The basic iteration loop

This is the entire daily workflow:

1. **Open the file you're editing** in VS Code. Open the **Lean infoview** with
   Ctrl+Shift+P (Cmd+Shift+P on Mac) → "Lean 4: Infoview: Toggle Infoview". Pin it to a
   side panel.

2. **Place your cursor inside a proof.** The infoview shows the current proof state —
   what hypotheses you have and what you need to prove. As you move the cursor between
   tactic lines, the infoview updates to show the goal at that point.

3. **Make a change.** Type a tactic, paste a draft from Claude Code, edit a definition.

4. **Wait 1–3 seconds.** Lean re-checks the file in the background. Red underlines
   appear on broken lines. The infoview updates with new goals or errors.

5. **Read the error.** Either fix it yourself, or copy the error text and paste it into
   Claude Code along with the surrounding code.

6. **Repeat until everything is green.** When the file has zero red underlines and the
   infoview shows "No goals" inside your proof, the proof is machine-verified.

7. **Run `lake build` from the terminal** to confirm the whole project still compiles
   (sometimes a change in one file breaks a downstream file the editor isn't watching).

The crucial mental shift from typical programming: **you are not writing code, you are
having a conversation with the type checker**. Every keystroke is a hypothesis; the
infoview tells you whether it lands. Don't try to write a proof end-to-end and check at
the end. Write one tactic, look at the infoview, write the next.

## Working with Claude Code on Lean

Claude Code is most useful for three things in Lean: drafting initial proofs, decoding
error messages, and suggesting tactics when you're stuck.

### Drafting

When asking Claude Code for a proof, give it concrete grounding:

- **The exact theorem statement** you want to prove.
- **The file context** — paste the surrounding 10–30 lines, including imports and any
  definitions used.
- **What's already available** — name the lemmas in scope that should be useful.

Vague: "Write a proof that OLS minimizes SSE."

Concrete: "Here is `Chapter3LeastSquaresAlgebra.lean` lines 1–115 [paste]. I want to add
a theorem `sumSquaredErrors_olsBeta_le` that proves `SSE(olsBeta X y) ≤ SSE X y b` for any
`b`, given `[Invertible (Xᵀ * X)]`. The Chapter 2 file has
`linearProjectionBeta_minimizes_MSE` which I can specialize. Draft the theorem and proof."

The concrete version produces something usable on the first try. The vague version
produces a generic proof sketch that doesn't match the repo's conventions.

### Debugging errors

When a tactic fails, paste the failing line **and** the error message **and** the goal
state shown in the infoview. The goal state is the key — Lean's error messages alone
often look cryptic, but the goal state shows you what shape the proof actually needs.

Example exchange that works:

> Got this error on the `rw [Matrix.transpose_transpose]` line:
> `tactic 'rewrite' failed, did not find instance of the pattern`
>
> The infoview shows the current goal as:
>
>     Xᵀ *ᵥ (X *ᵥ b) ⬝ᵥ b = b ⬝ᵥ (Xᵀ *ᵥ (X *ᵥ b))
>
> What's wrong?

Claude Code can see that there is no `(_)ᵀᵀ` in the goal and suggest the fix.

### When Claude Code is wrong

Claude Code will sometimes hallucinate Mathlib lemma names, get rewrite directions
backwards, or write proofs that look right but don't typecheck. Treat its output as a
hypothesis to test, not as ground truth. The Lean type checker is the authority. If
Claude Code says "this proof works" and the editor underlines it red, the editor is right.

When this happens, paste the actual error back. Don't accept "it should work" — drive it
to a green file.

## Reading the Lean infoview

The infoview shows two main things during proof editing:

- **Tactic state** — what you have to prove at the cursor position. Reads like:

      X : Matrix n k ℝ
      y : n → ℝ
      b : k → ℝ
      ⊢ sumSquaredErrors X y (olsBeta X y) ≤ sumSquaredErrors X y b

  Above the `⊢` are the hypotheses (variables and assumptions in scope). Below `⊢` is
  the goal — what you must prove. Each tactic transforms this.

- **Errors / warnings** — when a tactic fails, the infoview shows the failure reason and
  the goal state at that point.

After every tactic line, place your cursor on that line and look at the infoview. If you
see "No goals" in green, that subgoal is closed. If you see another goal, you have more
work to do.

`#check`, `#print`, and `#eval` are useful diagnostic commands. Type
`#check linearProjectionBeta_minimizes_MSE` on its own line; the infoview shows the
theorem's full type signature, which often reveals what arguments and instances are
needed.

## Common error messages and what they mean

- **"unknown identifier `foo`"** — `foo` is not in scope. Either you misspelled it, or its
  defining file is not imported. Add the import or fix the name.

- **"type mismatch, expected X, got Y"** — you supplied a term of type `Y` where `X` was
  expected. Often this is because Lean unfolded a definition you didn't expect, or a
  coercion is missing. Read both types carefully — they often differ in one small detail.

- **"failed to synthesize instance"** — Lean wants a typeclass argument and can't find one.
  Common cause: missing `[Fintype k]`, `[DecidableEq k]`, or `[Invertible (Xᵀ * X)]`.
  Either add the binder or check that the file-level `variable` block already provides it.

- **"tactic 'rewrite' failed, did not find instance of the pattern"** — the lemma you tried
  to apply with `rw` doesn't pattern-match anywhere in the goal. Either the direction is
  wrong (try `← lemma`), or the goal is in a different form than you expected. Look at
  the infoview's actual goal state, not what you think it should be.

- **"motive is not type correct"** — usually means a `rw` is trying to rewrite a term whose
  type depends on what's being rewritten. Often resolved by adding explicit arguments to
  the lemma to constrain which occurrence to rewrite (see the `hquad` case study below).

- **"no progress"** — the lemma matched but applying it produced an identical goal. This
  can happen when the LHS and RHS of the lemma are alpha-equivalent on your goal. Usually
  the lemma was the wrong choice; pick a different one.

- **"unsolved goals"** — your tactic block ended but the goal isn't closed. Either you
  forgot to handle a subgoal (`·` introduces a focus on the next goal) or your last
  tactic doesn't actually close the goal — check the infoview at the end of your block.

## A worked failure mode: multi-match `rw`

This is the single most common subtle bug in Lean 4 tactic proofs and is worth knowing
about up front.

When you write `rw [some_lemma]` and the lemma's pattern matches in **multiple places** in
your goal, Lean picks the leftmost match. This is sometimes what you want and sometimes
catastrophic.

For example, given the goal

    (X *ᵥ b) ⬝ᵥ (X *ᵥ b) = b ⬝ᵥ (Xᵀ *ᵥ (X *ᵥ b))

the lemma `Matrix.dotProduct_mulVec : ?v ⬝ᵥ (?A *ᵥ ?w) = vecMul ?v ?A ⬝ᵥ ?w` matches both
sides of `=`. Default `rw` rewrites the LHS occurrence — but if your downstream tactics
were written assuming the RHS got rewritten, the next tactic fails.

Two fixes:

- **Pass explicit arguments.** `rw [Matrix.dotProduct_mulVec b Xᵀ (X *ᵥ b)]` instantiates
  the lemma at specific values, forcing the rewrite onto the RHS occurrence (the one
  whose `?v = b, ?A = Xᵀ, ?w = X *ᵥ b`).

- **Refactor with named `have` lemmas.** Pull each tricky identity into a separate
  `have h : ... := by ...` block before the main rewrite. Each `have` has a unique
  small goal where multi-match is impossible.

Both styles are used in this repo. When in doubt, prefer the named-`have` style — it's
more verbose but more robust to refactoring and easier to debug.

## When you're stuck

If a proof has resisted three or four attempts:

1. **Drop a `sorry`.** Replace the proof body with `sorry`. The file compiles (with a
   warning). Now the lemma's *statement* is verified to typecheck, even if the proof is
   missing. Move on; come back to the proof later. Never commit a `sorry`, but it's a
   valid intermediate state during development.

2. **Read what's actually in scope.** Use `example` blocks to test ideas in isolation:

       example (X : Matrix n k ℝ) (v : k → ℝ) [Invertible (Xᵀ * X)] :
           True := by
         have h : 0 ≤ v ⬝ᵥ ((Xᵀ * X) *ᵥ v) := gram_quadratic_nonneg X v
         trivial

   This lets you confirm a lemma typechecks the way you expect, without contaminating
   the real file.

3. **Use `exact?` and `apply?`.** Place your cursor on the goal and run "Lean 4: Try
   This: exact?" from the command palette. Lean searches Mathlib for a matching theorem
   and suggests it. Often this finds the lemma you forgot the name of. `apply?` is the
   same but more permissive about partial matches.

4. **Search Mathlib.** Open a browser to <https://leanprover-community.github.io/mathlib4_docs/>
   and search for keywords. The doc site is well-indexed and has examples for most
   theorems.

5. **Ask Claude Code with the goal state pasted.** Restate the problem fresh, including
   the current goal state from the infoview. Often Claude Code can suggest a tactic
   you didn't think of.

6. **Search this repo.** Run `grep -rn "some_concept" HansenEconometrics/` to see how
   similar proofs are done in already-landed code. The repo's own conventions are
   the most reliable guide for what works in this Lean version with this Mathlib pin.

## Verification before commit

Before staging anything for commit, run from the repository root:

    lake build

Expected: a stream of compiled-file lines ending with no errors and exit code 0. If this
fails, the file you edited has a problem the in-editor checker may have missed (e.g.,
something in a downstream file that imports yours).

Also run:

    grep -rn "sorry" HansenEconometrics/ --include="*.lean"

Expected: no output. A `sorry` in committed code is a deal-breaker; the whole point of
the project is machine-verified proofs.

If both checks pass, you're safe to commit. See `DEV_INSTRUCTIONS.md` for the Git
workflow.

## A note on speed

Lean's elaborator is slow. A single line edit can take 1–3 seconds to re-check; a deep
file with many definitions can take 10+ seconds. This is normal. The trade-off is that
once it's green, the proof is *actually correct* — not "tests pass" correct, but
"machine-verified up to the foundations of mathematics" correct.

Embrace the slow loop. It rewards careful, incremental thinking. The wrong move is to
write a 30-line proof and run it once at the end; you'll spend an hour decoding the
error. The right move is to write one tactic, look at the infoview, write the next.
