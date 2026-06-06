# Adversarial Lean Review Harness — Design

**Date:** 2026-06-06
**Status:** Approved (design); pending implementation plan
**Author:** brainstormed with Claude Code

## Problem

The repo is a ~131k-line Lean 4 formalization of Hansen's *Econometrics* (≈50
files, 0 sorries, 2 axioms). Chapter 10 (Bootstrap) alone is ~80k lines and
holds most of the recent work. `AGENTS.md` already codifies strong
anti-redundancy and API-hygiene rules (reuse Mathlib → reuse repo theorems →
one canonical public API → thin wrappers only). What's missing is a *systematic,
adversarial* way to check the written Lean against that rubric and against the
source text.

We want a reusable review **harness** — not a one-off pass — that fans out
adversarial reviewers, verifies each finding to suppress false positives, and
turns confirmed mechanical fixes into reviewable draft PRs.

## Goals

- Catch **redundancy/duplication**, **API-hygiene** violations, **faithfulness
  to Hansen** gaps, and **proof-quality** issues (golfability + triviality).
- Be **adversarial**: every finding is independently verified by a skeptic
  before it can reach a report or a PR.
- Be **reusable** and **pilotable**: run on 1–2 files to tune, then scale to
  whole chapters.
- Be **cross-harness portable**: the review intelligence lives in
  harness-agnostic assets; only the orchestration glue is Claude-Code-specific.
- Produce a **structured report** and **draft PRs** (grouped, rebuilt green).

## Non-goals

- Not a correctness re-verification of Lean proofs themselves (the build already
  guarantees they typecheck). We check *whether the right thing was stated and
  whether it was stated/proved well*, not whether the kernel accepts them.
- Not automatic merging. Draft PRs are for human approval.
- Not a rewrite of `AGENTS.md`; the rubric *operationalizes* it.

## Architecture — two layers

### Layer 1 — Portable assets (`review/`)

Harness-agnostic. Any tool (Claude Code, Codex, Gemini CLI, or a human) can read
these and dispatch its own subagents.

```
review/
  rubric.md            # 4 dimensions → specific AGENTS.md rules → finding criteria + severity scale
  prompts/
    reviewer.md        # per (file × dimension) reviewer template
    verifier.md        # adversarial skeptic template — job is to REFUTE the finding
    fixer.md           # fix-agent template (mechanical, high-confidence fixes only)
  finding-schema.json  # structured finding shape (see below)
  worklist.md          # how to enumerate/chunk .lean files + locate each file's Hansen excerpt
  README.md            # how to run on Claude Code vs Codex vs manually
  reports/             # generated reports land here (YYYY-MM-DD-<scope>.md)
```

### Layer 2 — Claude Code orchestrator (`scripts/review.workflow.js`)

A **thin** JavaScript `Workflow` script that reads the Layer-1 assets and wires
up the deterministic pipeline. Saved to disk so it is re-runnable via
`{scriptPath}` and editable across sessions. Other harnesses replace *only* this
file with their own ~30-line orchestrator over the same Layer-1 assets.

## The four review dimensions

Each maps to concrete `AGENTS.md` rules so findings cite a rule, not a vibe.

1. **Redundancy / duplication**
   - Re-proved Mathlib lemmas (should reuse Mathlib first).
   - Duplicated proof ideas / parallel theorem stacks across files.
   - Near-identical lemmas that should collapse to one canonical result.
   - Copy-pasted algebra that should be a shared helper.

2. **API hygiene**
   - Helpers that should be `private` (removal would only break their own file).
   - Non-canonical public surface where a canonical one exists.
   - Number-named assumptions (number belongs in the docstring).
   - Missing module/declaration docstrings; missing `@[simp]` on recurring
     canonical rewrites; needlessly long identifiers.

3. **Faithfulness to Hansen**
   - The Lean statement's hypotheses/conclusion match the textbook excerpt.
   - Not vacuously true, not silently weakened, not a different theorem.

4. **Proof quality / triviality**
   - Unnecessarily long proofs (golfable).
   - Trivial/"cheating" statements that dodge the real mathematical content.

**Severity scale:** `blocker` > `major` > `minor` > `nit`.

## Finding schema

```json
{
  "id": "string",
  "file": "path/to/File.lean",
  "line": 123,
  "decl": "theoremOrDefName",
  "dimension": "redundancy | hygiene | faithfulness | proof-quality",
  "severity": "blocker | major | minor | nit",
  "rule": "AGENTS.md rule reference",
  "claim": "what is wrong",
  "evidence": "concrete proof: the duplicated decl name, the usage grep, the Hansen quote, etc.",
  "suggested_fix": "what to do",
  "mechanical": true,
  "confidence": "high | medium | low"
}
```

## Pipeline (Layer 2)

1. **Worklist** — enumerate target `.lean` files (pilot: 1–2 passed via `args`).
   For each, attach its Hansen source excerpt located from `textbook/<chXX>/`
   and the relevant `inventory/chXX-inventory.md` entry.

2. **Review** (pipeline, fan-out per file × dimension) — reviewer agent armed
   with `leansearch` / `loogle` / `lean_goal` MCP tools plus the excerpt emits
   structured findings against the rubric.

3. **Verify** (per finding, adversarial — the false-positive killer) — an
   independent skeptic tries to *refute* the finding; **default to refuted if
   uncertain**. Discipline per dimension:
   - *Redundancy*: must name the exact duplicated Mathlib/repo declaration
     (via loogle/leansearch/grep) or it's refuted.
   - *Hygiene*: must grep for real out-of-file usages (e.g. a "should-be-private"
     helper must have zero external references) or it's refuted.
   - *Faithfulness*: must quote the Hansen excerpt and compare hypotheses; a
     faithful or strictly stronger rendering is refuted.
   - *Proof-quality*: must confirm the statement is genuinely trivial/golfable
     (e.g. inspect hypotheses for vacuity) or it's refuted.

4. **Dedup** (barrier) — merge confirmed findings across dimensions by
   `file:line`/decl before any downstream work.

5. **Report** — write `review/reports/YYYY-MM-DD-<scope>.md`, grouped by file and
   dimension, severity-sorted, with evidence and suggested fixes. Date stamped by
   the caller (workflow scripts can't read the clock).

6. **Draft PRs** — group confirmed **mechanical** fixes (make private, dedup a
   lemma, add docstring, add `@[simp]`) into per-file/per-dimension commits inside
   a git **worktree**; run `lake build` **once per group** to confirm green.
   Non-mechanical items remain report-only. PRs are for human approval; nothing
   auto-merges.

## Key constraints

- **Build cost.** ~131k lines makes `lake build` expensive. Fixes are batched and
  built once per group; the pilot runs on small files to keep the loop fast.
- **False positives.** The adversarial verify stage is mandatory and
  refute-biased; nothing reaches a report's "confirmed" section or a PR unverified.
- **Cross-harness.** Codex/Gemini reuse all of Layer 1 and write their own thin
  orchestrator over the same prompts/schema. Only the glue is rewritten.

## Pilot plan

First run on 1–2 small Chapter 10 files (e.g. `HigherOrder.lean` ~895 LOC,
`Quantiles.lean` ~2113 LOC). Inspect real reviewer/verifier output, tune the
prompts and rubric thresholds, then scale to whole chapters.

## Success criteria

- Running the workflow on the pilot files produces a structured report whose
  confirmed findings are all genuinely actionable (low false-positive rate when
  spot-checked by a human).
- At least one confirmed mechanical fix flows end-to-end into a green draft commit.
- Re-running on the same files with no code changes reproduces the same confirmed
  findings (determinism of the rubric).
- A second harness (Codex) can, in principle, run the review using only the
  Layer-1 assets plus a small orchestrator — verified by the `review/README.md`
  instructions being complete and self-contained.
