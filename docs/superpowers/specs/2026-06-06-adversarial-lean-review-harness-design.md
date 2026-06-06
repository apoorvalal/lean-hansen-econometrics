# Adversarial Lean Review Harness — Design

**Date:** 2026-06-06
**Status:** Approved (design); pending implementation plan
**Author:** brainstormed with Claude Code

## Problem

The repo is a ~131k-line Lean 4 formalization of Hansen's *Econometrics* (≈50
files, 0 sorries, 2 axioms). Chapter 10 (Bootstrap) alone is ~80k lines and
holds most of the recent work. (The "2 axioms" figure is from `#print axioms`
— kernel axioms like `propext`/`Classical.choice` — not project-declared
`axiom`s; the source has none.) `AGENTS.md` already codifies strong
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

It targets the Claude Code `Workflow` primitives: `agent(prompt, {schema})` for
structured subagent calls, `pipeline(items, ...stages)` for the
review→verify-per-item flow (no barrier), `parallel(thunks)` for the dedup
barrier, `phase()`/`log()` for progress, and `isolation: 'worktree'` for the
draft-PR fix agents. Findings pass between stages as plain JS objects validated
against `finding-schema.json` via the `schema` option.

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

## Prerequisites / tool dependencies

- **Required:** `ripgrep` (`rg`) and `git` (worktrees). These are the guaranteed
  baseline — every dimension's reviewer and verifier must be able to do its job
  with grep alone.
- **Preferred (optional):** the Lean LSP MCP tools `leansearch`, `loogle`,
  `lean_goal`. They make redundancy and faithfulness checks far stronger. The
  repo currently has no MCP config; provisioning them is a setup step, not an
  assumption. If they are unavailable, the workflow degrades gracefully to
  `rg`-based search and the report notes which checks ran in degraded mode.
- **Lean toolchain:** `lake build` for the draft-PR green check (expensive — see
  constraints).

## Source-text lookup (excerpt mapping)

Chapter excerpts are **monolithic** (e.g. `textbook/ch10/ch10_excerpt.txt` is
~4600 lines covering the whole chapter), and `inventory/chN-inventory.md` maps
Hansen equations to *declaration* links that may span several files. There is no
file-to-excerpt-section mapping, so the harness does not try to pre-slice the
excerpt. Instead, for a target file the faithfulness reviewer is given:

1. the full chapter excerpt (`textbook/ch{NN}/*_excerpt.*`), and
2. the inventory rows whose decl-links resolve into the target file
   (`inventory/ch{N}-inventory.md`),

and is responsible for locating the relevant passage and quoting it. Note the
two path namespaces differ: excerpt dirs are zero-padded two-digit
(`textbook/ch01/` … `textbook/ch29/`); inventory files are **not** padded
(`inventory/ch1-inventory.md` … `inventory/ch10-inventory.md`). A literal glob
must handle both.

## Finding schema

```json
{
  "id": "stable: sha1(file:line:decl:dimension) — used for dedup + run-to-run comparison",
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

2. **Review** (pipeline, fan-out per file × dimension — **dimension-level, not
   per-decl**, to bound agent count to `files × 4`) — reviewer agent armed with
   the preferred MCP tools (or `rg` fallback) plus the excerpt/inventory rows
   emits structured findings against the rubric.

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

4. **Dedup** (barrier) — merge confirmed findings by `id` (i.e.
   `file:line:decl:dimension`). When two findings collapse, keep the higher
   severity and union their evidence; findings in *different* dimensions at the
   same `file:line` are kept separate (the dimension is part of identity).

5. **Report** — write `review/reports/YYYY-MM-DD-<scope>.md`, grouped by file and
   dimension, severity-sorted, with evidence and suggested fixes. Date stamped by
   the caller (workflow scripts can't read the clock).

6. **Draft PRs** — group confirmed **mechanical** fixes into per-file/per-dimension
   commits inside a git **worktree**; run `lake build` **once per group** to
   confirm green. The mechanical whitelist is deliberately narrow — only edits
   that are local to one declaration and cannot cascade: **make `private`, add a
   docstring, add `@[simp]`, rename within file**. **Lemma dedup is explicitly
   report-only** (it deletes a decl and repoints call sites, which can cascade
   across files and break the build) *unless* the duplicate has zero external
   usages, in which case its removal is treated as mechanical. Non-mechanical
   items remain report-only. PRs are for human approval; nothing auto-merges.

## Key constraints

- **Build cost.** ~131k lines makes `lake build` expensive. Fixes are batched and
  built once per group; the pilot runs on small files to keep the loop fast.
- **Fan-out bounds.** Reviewers are dimension-level (`files × 4`); each finding
  spawns one verifier. The workflow takes an explicit stop budget; on reviewer/
  verifier error the affected item drops to `null` and is logged, not retried
  indefinitely. The report logs any files/dimensions skipped due to budget.
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
- Re-running on the same files with no code changes yields a **stable**
  high-confidence finding set: the LLM reviewers/verifiers are nondeterministic,
  so the bar is high overlap of `blocker`/`major` findings across two runs
  (compared by `id`), not byte-identical output. A large run-to-run swing in the
  confirmed set signals an under-specified rubric to tighten.
- A second harness (Codex) can run the review using only the Layer-1 assets plus
  a small orchestrator. `review/README.md` includes a concrete self-containment
  checklist (rubric path, prompt paths, schema path, worklist procedure, tool
  prerequisites + fallback, output location) that a Codex runner can follow
  without reading the CC workflow script.
