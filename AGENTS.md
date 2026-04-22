# Agent Style Guide

This document describes the working principles for contributors and coding agents in this repo.
It is intentionally practical: the goal is to keep the formalization coherent, reusable, and easy to
review.

## Core principles

### 1. Reuse Mathlib first

- Before proving a theorem from scratch, check whether Mathlib already provides the main engine.
- Prefer wrapping or specializing an existing Mathlib theorem over rebuilding the same infrastructure
  locally.
- When Mathlib's statement is more general or more abstract than Hansen's statement, keep the
  Mathlib-facing theorem and add a thin Hansen-facing wrapper if the chapter benefits from it.

Examples:
- [HansenEconometrics/ProbabilityUtils.lean](./HansenEconometrics/ProbabilityUtils.lean)
  reuses Mathlib's conditional-expectation machinery and exposes reusable conditioning helpers on
  random variables.
- Chapter 2.10 reuses the earlier normal-equations theorem instead of reproving the algebra from
  scratch.

### 2. Reuse repo theorems before adding new ones

- Search the existing chapter files first.
- Prefer composing results already proved in this repo over duplicating algebra in a later chapter.
- If a later theorem is really just a corollary or a notation bridge, write it as such.

Preferred pattern:
1. prove the strongest reusable theorem once
2. add the textbook-shaped or chapter-facing corollary afterwards

Examples:
- backend sigma-algebra conditional-expectation results in
  [HansenEconometrics/Chapter2CondExp.lean](./HansenEconometrics/Chapter2CondExp.lean) support the
  chapter-facing variable wrappers proved in
  [HansenEconometrics/Chapter2CondExp.lean](./HansenEconometrics/Chapter2CondExp.lean) and
  [HansenEconometrics/Chapter2Variance.lean](./HansenEconometrics/Chapter2Variance.lean), while
  [HansenEconometrics/ProbabilityUtils.lean](./HansenEconometrics/ProbabilityUtils.lean)
  supplies the shared helper layer
- abstract `QXX` / `QXY` theorems first, moment or covariance wrappers second

### 3. Keep the core theorem general at the intended layer

- "General" means reusable at the layer that downstream proofs and readers should actually use.
- Public chapter-facing probability APIs should usually be variable-based.
- Sigma-algebra theorems are backend infrastructure and should only be surfaced when mathematically
  necessary.
- For algebraic and matrix infrastructure, abstract matrix or moment statements can still be the
  right public core.
- Do not optimize for maximal abstraction if that makes the chapter-facing API harder to use.

Examples:
- `condExpOn`, `cefErrorOn`, `condVarOn`, and `residualVarOn` live in the reusable helper layer
  [HansenEconometrics/ProbabilityUtils.lean](./HansenEconometrics/ProbabilityUtils.lean).
- textbook-facing Chapter 2 wrappers such as `tower_property_rv`, `best_predictor_rv`, and
  `law_total_variance_rv` belong in the chapter files
  [HansenEconometrics/Chapter2CondExp.lean](./HansenEconometrics/Chapter2CondExp.lean) and
  [HansenEconometrics/Chapter2Variance.lean](./HansenEconometrics/Chapter2Variance.lean).
- [HansenEconometrics/Chapter2CondExp.lean](./HansenEconometrics/Chapter2CondExp.lean) and
  [HansenEconometrics/Chapter2Variance.lean](./HansenEconometrics/Chapter2Variance.lean) remain the
  backend sigma-algebra support layer.
- [HansenEconometrics/Chapter2LinearProjection.lean](./HansenEconometrics/Chapter2LinearProjection.lean)
  keeps the abstract matrix/moment layer as the reusable core.

### 4. Use bridge lemmas instead of duplicating proof ideas

- When Hansen states a theorem in a notation that does not match Mathlib or the repo's internal API,
  add a thin bridge layer.
- Bridge lemmas should translate notation, not introduce a parallel theorem stack unless that stack
  is genuinely reusable.

Examples:
- `covVec`, `covMat`, and related Chapter 2.10 lemmas bridge scalar covariance facts to matrix
  notation.
- `condExp_apply`, `condExp_apply_apply`, `integral_apply`, and `integral_apply_apply` bridge
  generic conditional-expectation / integral machinery to coordinatewise arguments used in Chapter 4.

## Probability layer policy

- Default public probability statements to variable-based forms such as `condExpOn μ Y X`.
- Treat sigma-algebra statements as proof infrastructure unless the theorem is genuinely about
  information sets, filtrations, or sigma-algebra inclusion itself.
- If a theorem is expected to be cited in chapter prose or chapter-local development, prefer the
  variable-facing wrapper.
- If the main work is done by a sigma-algebra theorem, keep that theorem in the backend and expose
  the chapter-facing statement as a wrapper.
- When choosing between a sigma-algebra theorem and a variable wrapper, optimize for the theorem that
  later chapters will naturally want to reuse, not for the most abstract possible statement.

## Module boundary policy

- Extend [HansenEconometrics/ProbabilityUtils.lean](./HansenEconometrics/ProbabilityUtils.lean)
  when the result is a reusable variable-conditioned helper fact likely to be used across multiple
  Chapter 2+ proofs.
- Extend an existing chapter file when the theorem is chapter-local, tightly tied to nearby results,
  or not expected to be reused outside that chapter.
- Create a new module only when at least one of these is true:
  - the concept forms a coherent reusable family with its own small API
  - the imports or assumptions would otherwise bloat a widely used module
  - the material is likely to be reused across multiple later chapters
  - the new layer has a clearly different audience or abstraction level from the existing module
- Do not create a new module just to hold one helper theorem or one-off notation bridge.
- Prefer adding a few bridge lemmas before splitting into a new file.

Examples:
- [HansenEconometrics/ProbabilityUtils.lean](./HansenEconometrics/ProbabilityUtils.lean)
  merits its own module because it is a reusable helper layer with a distinct audience from the
  chapter-facing theorems and the backend sigma-algebra files.
- The Chapter 2 sigma-algebra files stay separate because they are backend support for multiple
  wrappers and later proofs.
- Chapter-facing probability theorems still belong in the chapter files when they are part of the
  chapter exposition rather than generic helper infrastructure.
- Chapter 2.10 matrix/covariance bridges belong next to the linear-projection development rather than
  in a new one-off file.

## Crosswalk policy

Each chapter now has a local `notes/chXX/latex_links.md`.

Purpose:
- map textbook statements to Lean theorems or definitions
- keep the LaTeX version and the Lean version close together
- show missing results explicitly by leaving the Lean target blank

Rules:
- keep links relative
- prefer one row per textbook theorem, equation, or named result
- if the theorem is not formalized yet, leave the Lean cell blank instead of inventing a placeholder
  theorem name
- if the Lean theorem is more general than Hansen's statement, say so in a short note
- if the main reusable theorem is a bridge theorem rather than a textbook theorem, include it in a
  short "Lean-only bridge results" section

Recommended structure:
1. short conventions section
2. links to inventory, excerpt, and relevant Lean files
3. a crosswalk table with textbook statement, LaTeX, and Lean theorem
4. brief notes about generalization, wrappers, or pending gaps

## Documentation policy

- `notes/chXX/inventory.md` is for planning, status, and dependency notes.
- `notes/chXX/latex_links.md` is for theorem-by-theorem statement mapping.
- Do not overload the inventory with full side-by-side theorem presentations.
- When a new theorem lands, update both:
  - the relevant Lean file docstring if needed
  - the chapter crosswalk

## Theorem-writing policy

- State assumptions explicitly and only as strongly as needed.
- Prefer names that describe the mathematical content instead of the proof technique.
- When a theorem is a textbook theorem, note that in the docstring.
- When a theorem is only a reusable helper, say so plainly.

Good pattern:
- backend theorem: reusable, Mathlib-friendly, or algebraically canonical
- public wrapper theorem: chapter-facing variable or textbook notation

## Proof strategy policy

- Use Mathlib's abstraction level when it shortens the proof and improves reuse.
- Use direct chapter-native proofs when they mirror Hansen closely and reuse existing chapter
  infrastructure cleanly.
- Avoid redoing Hilbert-space or matrix-algebra arguments manually when the relevant theorem is
  already available.
- Add small helper lemmas when they remove notation friction across several later proofs.

## Review checklist

Before opening or updating a PR, check:

- Does this theorem already exist in Mathlib?
- Does a stronger repo-local theorem already imply this?
- Is the theorem stated at the right layer of generality?
- If there is a textbook wrapper, is it thin?
- For probability results, is the public theorem variable-facing unless there is a good reason not to
  be?
- Does the result belong in an existing module rather than a new file?
- Did the corresponding `latex_links.md` file get updated?
- Are all new markdown links relative?

## Current examples

- [HansenEconometrics/ProbabilityUtils.lean](./HansenEconometrics/ProbabilityUtils.lean)
  is the current model for a reusable helper layer over random-variable conditioning.
- [HansenEconometrics/Chapter2CondExp.lean](./HansenEconometrics/Chapter2CondExp.lean) and
  [HansenEconometrics/Chapter2Variance.lean](./HansenEconometrics/Chapter2Variance.lean) are the
  main Chapter 2 probability files, containing both backend sigma-algebra results and chapter-facing
  variable wrappers.
- [HansenEconometrics/Chapter2LinearProjection.lean](./HansenEconometrics/Chapter2LinearProjection.lean)
  is the main example of reusable lower-level abstract matrix / moment infrastructure.
- Chapter 3 through Chapter 5 show the intended pattern: reusable helpers first, chapter-facing
  corollaries afterwards.
