# Review Rubric

This document is the authoritative guide for adversarial reviewer agents in this repo.
Every finding reported in `review/finding-schema.json` format must be grounded in one of
the four dimensions below. The dimension key and severity key in every finding MUST match
the values in the schema exactly.

Dimensions: `redundancy` | `hygiene` | `faithfulness` | `proof-quality`
Severities: `blocker` | `major` | `minor` | `nit`

Source of truth for all rules: **AGENTS.md** at the repository root.

---

## Severity rubric

| Severity  | When to use |
|-----------|-------------|
| `blocker` | Wrong or unfaithful math; a public-API duplication that creates an incoherent double canon; an `import Mathlib` wildcard that was not documented |
| `major`   | Real redundancy or hygiene break with concrete downstream impact (e.g., a helper that could silently diverge from the canonical version; a missing `private` on a helper whose removal would only break one file) |
| `minor`   | Local cleanup that improves consistency but has no downstream impact (e.g., a `@[simp]` that should be added, an assumption name that should move to a docstring) |
| `nit`     | Cosmetic only — does not affect correctness, reuse, or readability at scale |

---

## 1. `redundancy`

### AGENTS.md rules operationalized

**§1 — Reuse Mathlib first** (AGENTS.md "Core principles" §1):
> "Before proving a theorem from scratch, check whether Mathlib already provides the main engine."
> "Prefer wrapping or specializing an existing Mathlib theorem over rebuilding the same infrastructure locally."
> "When Mathlib's statement is more general or more abstract than Hansen's statement, keep the Mathlib-facing theorem and add a thin Hansen-facing wrapper if the chapter benefits from it."

**§2 — Reuse repo theorems before adding new ones** (AGENTS.md "Core principles" §2):
> "Search the existing chapter files first."
> "Prefer composing results already proved in this repo over duplicating algebra in a later chapter."
> "If a later theorem is really just a corollary or a notation bridge, write it as such."

**§4 — Use bridge lemmas instead of duplicating proof ideas** (AGENTS.md "Core principles" §4):
> "Bridge lemmas should translate notation, not introduce a parallel theorem stack unless that stack is genuinely reusable."
> "`_of_...` bridge lemmas are usually proof infrastructure. Make them private unless downstream files should cite them directly."

**Public API** (AGENTS.md "Public API and theorem hygiene"):
> "When a proof-shaped definition and a textbook-shaped definition are provably equal, choose one canonical public surface. The noncanonical one may remain as an internal proof engine."

**PR gate** (AGENTS.md "PR gate"):
> "Reuse Mathlib first, then existing repo theorems."

### Counts as a finding

- A theorem proved from scratch whose main proof engine already exists in Mathlib (e.g., reproving a convergence result that Mathlib's `Filter` or `MeasureTheory` library already covers).
- A theorem in a later chapter that duplicates algebra from an earlier chapter file without citing or reusing the existing result.
- Two public declarations that are provably equal and serve the same audience — a double canonical surface.
- A bridge lemma that silently reproduces a non-trivial proof rather than delegating to the existing theorem.
- A `_of_...` helper that is `public` but is only used inside the file where it is defined.

### Does NOT count as a finding

- A thin Hansen-facing wrapper over a more general Mathlib theorem, as long as the wrapper delegates to Mathlib and does not re-prove the mathematics.
- A chapter-facing corollary that is provably equal to the repo's internal theorem and that the chapter prose actually needs to cite — this is the intended pattern.
- Duplicate *names* across namespaces that refer to the same underlying definition (namespace aliasing is not redundancy).
- An OrZero or Star variant that exists because the Star/OrZero architecture requires it (see AGENTS.md "Star / OrZero totalization convention").
- Infrastructure theorems that share a mathematical idea but operate at a genuinely different abstraction level (e.g., a sigma-algebra backend theorem vs. its variable-facing wrapper).

### Severity guidance

- `blocker`: two public declarations with identical statements and no canonical distinction documented.
- `major`: a from-scratch proof of a result that Mathlib covers, causing a maintenance burden.
- `minor`: a bridge lemma that could be shortened to a one-liner by delegating, but that is otherwise correct.
- `nit`: a helper that should be `private` but is not, with no external callers.

---

## 2. `hygiene`

### AGENTS.md rules operationalized

**Keep scaffolding private** (AGENTS.md "PR gate" and "Public API and theorem hygiene"):
> "Keep same-file proof scaffolding private."
> "A helper whose removal would only break the file where it is defined should usually be `private`."
> "Public declarations are the chapter-facing or reusable API."

**One canonical public API** (AGENTS.md "PR gate" and "Public API and theorem hygiene"):
> "Choose one canonical public API for each mathematical object; use thin wrappers only for notation."
> "Public condition packages should be real declarations with an enforceable shape, not aliases that hide the proof obligations."

**Number in docstring, not symbol name** (AGENTS.md "Public API and theorem hygiene"):
> "Use descriptive assumption names. If a condition package corresponds to a numbered Hansen assumption, put the number in the docstring rather than making the symbol name a number."

**Docstrings for large modules** (AGENTS.md "PR gate"):
> "Give large modules a docstring that explains their contents and public surface."

**`@[simp]` for recurring canonical rewrites** (AGENTS.md "PR gate" and "Proof strategy policy"):
> "Add `@[simp]` lemmas for recurring canonical rewrites."
> "Prefer stable simplifier support for canonical identities. If several proofs manually rewrite the same identity, consider whether the identity should be tagged `@[simp]`."

**Citeable / short names** (AGENTS.md "PR gate"):
> "Keep theorem names citeable; use namespaces and local names to avoid very long identifiers."

**Import hygiene** (AGENTS.md "Import hygiene policy"):
> "Do not add `import Mathlib` to project Lean files. If a temporary broad import is unavoidable, document why in the PR/update note and open a follow-up to remove it."
> "Prefer the narrowest stable `Mathlib.*` imports that keep the file readable."

### Counts as a finding

- A helper theorem that is only used in the file where it is defined but is not `private`.
- A large module with no module-level docstring (AGENTS.md: "Give large modules a docstring"; use judgment on what counts as large — there is no fixed line threshold).
- An assumption structure whose name encodes a Hansen number (e.g., `Assumption3`) rather than describing the mathematical content, with no docstring explaining the correspondence.
- An identity that appears repeatedly rewritten inline across several proofs but is not tagged `@[simp]`.
- An `import Mathlib` wildcard with no accompanying comment justifying the temporary exception.
- A theorem name so long it cannot be reasonably cited in prose (prefer using a namespace and a shorter local name).
- A public `_of_...` bridge lemma that is only used as proof infrastructure inside its own file.

### Does NOT count as a finding

- A `private` lemma that happens to be short — private-and-short is fine; the issue is public-and-locally-only.
- A docstring that is brief but present — the rule is about large modules with *no* docstring.
- A helper that is public because another file actually imports and uses it — check cross-file usage before filing.
- An `@[simp]` absence on a lemma that only appears once — the rule targets *recurring* rewrites.
- Naming style disagreements not grounded in the "citeable names" or "number in docstring" rules.
- Bridge names following the documented `fooOrZero_eq_star` or `fooOrZero_eq_sq` patterns — those are intentional conventions from the Star/OrZero architecture.

### Severity guidance

- `blocker`: an `import Mathlib` wildcard with no justification documented.
- `major`: a module with a large public surface and no docstring; a public helper that is only used locally but whose accidental external use could cause downstream breakage.
- `minor`: a missing `@[simp]` on a recurring canonical rewrite; an assumption name with an inline number that should move to a docstring.
- `nit`: a locally-only helper that should be `private`; a theorem name that is slightly too long but still citable.

---

## 3. `faithfulness`

### AGENTS.md rules operationalized

**Theorem-writing policy** (AGENTS.md "Theorem-writing policy"):
> "State assumptions explicitly and only as strongly as needed."
> "When a theorem is a textbook theorem, note that in the docstring."

**Keep the core theorem general at the intended layer** (AGENTS.md "Core principles" §3):
> "'General' means reusable at the layer that downstream proofs and readers should actually use."
> "Do not optimize for maximal abstraction if that makes the chapter-facing API harder to use."

**Crosswalk policy** (AGENTS.md "Crosswalk policy"):
> "if the theorem is not formalized yet, leave the Lean cell blank instead of inventing a placeholder theorem name"
> "if the Lean theorem is more general than Hansen's statement, say so in a short note"

### What faithfulness means for this project

A formalization is *faithful* when:
1. The Lean statement's conclusion matches what Hansen's excerpt actually concludes (not a weaker consequence or a vacuously-true tautology).
2. The Lean statement's hypotheses include all conditions that Hansen's excerpt requires and do not silently drop assumptions to make the proof easier.
3. Where the Lean statement is strictly *more general* than Hansen's, this is documented (a docstring note, an inventory entry, or a crosswalk note).

### Counts as a finding

- A conclusion weaker than what Hansen states (e.g., Hansen states a.s. convergence but the Lean theorem only gives convergence in probability, without documentation).
- A hypothesis that is strictly stronger than Hansen's (e.g., Hansen assumes i.i.d. but the Lean statement additionally requires boundedness without justification).
- A vacuous statement (hypothesis set is contradictory, making the theorem trivially true with no mathematical content). This operationalizes the harness design's faithfulness definition ("not vacuously true, not silently weakened"), not a literal AGENTS.md rule — require concrete evidence that the hypotheses are contradictory before filing.
- A theorem named after a Hansen result whose statement does not correspond to that result, with no crosswalk note explaining the discrepancy.
- `sorry` used to close a proof obligation that is not marked as a known gap in the inventory. (Undocumented `sorry` is filed under `faithfulness` only — do NOT also file it under `proof-quality`.)

### Does NOT count as a finding

- A strictly more general Lean statement that subsumes Hansen's statement and is documented as such in the docstring or inventory.
- A Mathlib-level wrapper that is more abstract than Hansen's notation — as long as the chapter-facing wrapper correctly specializes it.
- Standard Lean/Mathlib conventions that differ from Hansen's notation (e.g., using `MeasureTheory.Integrable` where Hansen writes "finite variance") — these are notation bridges, not faithfulness failures.
- A `sorry` that appears in a declaration explicitly listed as an open gap in the chapter inventory.
- Generalization at the `ProbabilityUtils` or backend sigma-algebra layer, which is explicitly intended to be more general than the textbook.

### Severity guidance

- `blocker`: conclusion does not match Hansen's; hidden `sorry` closing a non-trivial proof obligation with no inventory entry.
- `major`: a dropped hypothesis that makes the theorem stronger than Hansen's without documentation; a weakened conclusion that misleads a chapter-prose reader.
- `minor`: a theorem named after a Hansen result with no docstring noting the generalization.
- `nit`: a minor notation discrepancy that is documented but could be clarified further.

---

## 4. `proof-quality`

### AGENTS.md rules operationalized

**Proof strategy policy** (AGENTS.md "Proof strategy policy"):
> "Use Mathlib's abstraction level when it shortens the proof and improves reuse."
> "Use direct chapter-native proofs when they mirror Hansen closely and reuse existing chapter infrastructure cleanly."
> "Avoid redoing Hilbert-space or matrix-algebra arguments manually when the relevant theorem is already available."
> "Add small helper lemmas when they remove notation friction across several later proofs."
> "Prefer stable simplifier support for canonical identities. If several proofs manually rewrite the same identity, consider whether the identity should be tagged `@[simp]`."

**Bridge-lemma discipline** (AGENTS.md "Core principles" §4):
> "Bridge lemmas should translate notation, not introduce a parallel theorem stack unless that stack is genuinely reusable."

**Theorem-writing policy** (AGENTS.md "Theorem-writing policy"):
> "State assumptions explicitly and only as strongly as needed."
> "Prefer names that describe the mathematical content instead of the proof technique."

### What proof-quality means for this project

A proof has good quality when:
1. It is not obviously golfable — i.e., there is no single Mathlib lemma that closes the goal in one step that the current proof avoids.
2. It does not manually redo infrastructure (Hilbert-space, matrix algebra, measure theory) that a Mathlib tactic or existing repo lemma would handle.
3. Assumptions are neither over-stated (stronger than needed) nor trivially satisfied.

### Counts as a finding

- A multi-step proof that a single `exact`, `simp [...]`, `linarith`, `ring`, `norm_num`, or analogous tactic would close.
- A manual rewrite of a Hilbert-space or matrix-algebra argument when `Mathlib.Analysis` or `Mathlib.LinearAlgebra` already has the relevant theorem.
- A proof that copies-and-pastes a block from an earlier proof rather than citing the earlier theorem.
- An assumption listed in the hypothesis that is never used anywhere in the proof (dead hypothesis) — this makes the theorem needlessly stronger than necessary, violating AGENTS.md's "State assumptions explicitly and only as strongly as needed." Only file with concrete evidence the hypothesis is genuinely unused (e.g. it never appears in the proof term and removing it would still compile).

### Does NOT count as a finding

- A proof that is longer than the shortest possible but that mirrors Hansen's argument closely and is clearly intentional (chapter-native style is explicitly allowed by AGENTS.md).
- Minor tactic-level choices (e.g., `exact h` vs. `assumption`) that have no effect on reuse or readability at scale.
- A proof that uses an intermediate `have` to name a sub-goal for readability, even if the sub-goal could be inlined.
- A declaration marked `noncomputable` — this is routine and expected throughout the codebase (Mathlib's `ℝ`, `MeasureTheory`, etc. are definitionally noncomputable). AGENTS.md has no rule about `noncomputable`, so never file it as a finding.
- A proof that is technically longer because it covers a strictly more general statement than Hansen's (generality is a feature, not a quality defect).

### Severity guidance

- `major`: a multi-step proof that manually redoes available Mathlib infrastructure, creating a real maintenance burden.
- `minor`: a proof golfable to a single tactic; a dead hypothesis.
- `nit`: cosmetic tactic style differences with no impact on correctness or reuse.

---

## Applying this rubric consistently

When generating a finding, a reviewer agent should:

1. **Identify the exact rule** from AGENTS.md that is violated. Populate the `rule` field with a short citation, e.g., `"AGENTS.md §1 reuse-Mathlib-first"`.
2. **State the claim** concisely: what is wrong and why.
3. **Provide evidence**: quote the relevant line(s) or declaration name(s) from the Lean file.
4. **Propose a concrete fix**: e.g., "Replace with `exact Mathlib.Foo.bar`" or "Add `private` keyword".
5. **Set `mechanical`** to `true` ONLY when the fix is exactly one of the fixer's whitelisted edits — add `private`, add a docstring, add `@[simp]`, in-file rename, or remove a zero-external-usage duplicate. A proof-body change (e.g. dropping a `by`/`exact` wrapper), any statement change, or any cross-file edit is NOT mechanical, even if it looks trivial. So "make this `private`" and "add a module docstring" are `mechanical: true`; "drop the `by exact` wrapper" and "delegate this proof to scalarCDF_mono" are `mechanical: false`.
6. **Set `confidence`** honestly: `high` if the rule clearly applies, `medium` if context is needed, `low` if it is a heuristic guess.

A finding that cannot be grounded in a specific AGENTS.md rule should not be filed. When in doubt, use `confidence: "low"` and explain the uncertainty in the `claim` field.
