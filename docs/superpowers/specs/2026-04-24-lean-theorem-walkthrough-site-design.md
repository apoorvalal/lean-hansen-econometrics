# Lean Theorem Walkthrough Site — Design

**Date:** 2026-04-24
**Status:** Approved (pending spec review)

## Problem

The Lean formalization in this repo proves theorems from Hansen's *Econometrics*, but the Lean theorem statements and proofs are hard to read for humans wanting to compare them to canonical textbook proofs. A single hand-written walkthrough exists (`hansen_theorem_5_7_walkthrough.md`) and demonstrates the value of a readable companion. We want a polished, browsable site that:

1. Makes each theorem's **assumptions** explicit.
2. Lays out the **proof steps** in textbook math alongside pointers into the Lean proof.
3. Provides full coverage of the Lean library, with hand-written walkthroughs for headline theorems and auto-generated stubs for everything else.

## Goals

- Hybrid coverage: auto-generated stub pages for every public Lean declaration, hand-written walkthrough pages for headline theorems.
- Authoritative theorem signatures sourced from the Lean environment itself (not regex).
- Academic/textbook aesthetic with first-class math rendering.
- Local-only workflow. No CI, no public deployment in v1.
- Minimal new infrastructure: one Lean meta script, one Python script, a Quarto project, a Makefile.

## Non-Goals (YAGNI)

- Search beyond Quarto's built-in.
- Auto-extracted dependency graphs (downstream-uses sections are hand-curated for v1).
- Versioning / multiple editions.
- PDF export.
- Comments / discussions.
- CI builds or public deployment (explicitly deferred — to be enabled later by user decision).
- Lint that validates walkthrough `lean_name:` frontmatter against the actual Lean environment.

## Architecture

A new top-level `site/` directory holds a Quarto project. The Lean source under `HansenEconometrics/` is untouched. A Lean meta-program emits authoritative declaration metadata as JSON; a Python script consumes it and writes per-theorem stub pages. Hand-written walkthroughs live alongside stubs and are linked from them when present.

### Repo layout

```
site/
  _quarto.yml                # nav, theme, KaTeX, sidebar by chapter
  index.qmd                  # landing page
  README.md                  # local workflow docs
  walkthroughs/
    _template.qmd            # template for new walkthroughs
    chapter5/
      theorem-5-7.qmd        # ported from hansen_theorem_5_7_walkthrough.md
  auto/
    chapter5/
      <theorem-name>.qmd     # auto-generated stubs
      index.qmd              # per-chapter table of theorems
  _generated/                # gitignored
    declarations.json
  _site/                     # gitignored, Quarto render output
scripts/
  ExportDecls.lean           # Lean meta-program
  build_stubs.py             # JSON → .qmd stubs (uv run, Jinja2)
Makefile                     # site-export, site-stubs, site-preview, site-render
```

`.gitignore` adds `site/_generated/` and `site/_site/`.

## Components

### 1. Lean export script — `scripts/ExportDecls.lean`

A `lake exe` target that walks `Environment.constants`, filters to declarations whose source file lives under `HansenEconometrics/`, and emits one JSON record per declaration:

```json
{
  "name": "scaledOlsResidualVarianceStatistic_hasLaw_chiSquared",
  "namespace": "HansenEconometrics.Chapter5",
  "kind": "theorem",
  "signature": "<pretty-printed type>",
  "docstring": "...",
  "file": "HansenEconometrics/Chapter5NormalRegression.lean",
  "line": 270,
  "chapter": 5,
  "isPrivate": false
}
```

Behavior:

- **Kind filter:** include `theorem`, `lemma`, `def`. Skip `instance`, `abbrev`, and auto-generated declarations (`_proof_*`, `_eqn_*`, `_aux_*`, etc.).
- **Chapter inference:** filename regex `Chapter(\d+)` → integer chapter. Files like `ChiSquared.lean`, `ProbabilityUtils.lean`, `LinearAlgebraUtils.lean`, `AsymptoticUtils.lean`, `Basic.lean` → chapter `null` (rendered under a "Utilities" group).
- **Signature pretty-printing:** use `PrettyPrinter.ppExpr` so the rendered type matches editor display (Unicode, default implicit-handling).
- **Stable output:** records sorted by `(file, line)` so re-runs yield minimal diffs.
- Invoked as: `lake exe export_decls > site/_generated/declarations.json`.

### 2. Stub builder — `scripts/build_stubs.py`

Python 3, run via `uv run`. Dependency: Jinja2 (declared inline via PEP 723).

Steps:

1. Read `site/_generated/declarations.json`.
2. Index `site/walkthroughs/**/*.qmd` by their `lean_name:` YAML frontmatter field.
3. For each declaration, compute slug = `name.lower().replace('.', '-')`, target path `site/auto/chapter{N}/{slug}.qmd` (or `site/auto/utilities/{slug}.qmd`).
4. Render via Jinja template:
   - If a hand-written walkthrough exists for that fully-qualified Lean name, the stub is a redirect-style page linking to the walkthrough.
   - Otherwise, the stub shows a "no walkthrough yet" callout, the signature in a Lean code block, the docstring (if any), and a GitHub source-link to `file.lean#Lline`.
5. Write `site/auto/chapter{N}/index.qmd` per chapter — a table listing every theorem in that chapter with columns: name, file:line, walkthrough? (✓ or —).
6. **Idempotent:** wipes and rewrites `site/auto/` wholesale on each run, so theorem deletions in Lean are reflected.

### 3. Walkthrough template — `site/walkthroughs/_template.qmd`

Sections (per Q4 of brainstorming):

1. **Textbook statement** — Hansen's wording and equation.
2. **Assumptions** — explicit bulleted list (model, distribution, regularity).
3. **Lean statement** — formal theorem with file:line links to each named object.
4. **Translation notes** — where Lean phrasing differs from Hansen and why it's equivalent.
5. **Proof sketch** — human-readable LaTeX.
6. **Lean proof structure** — chain of supporting lemmas, each linked.
7. **Downstream uses** — hand-curated; optional.

YAML frontmatter required: `title`, `lean_name` (fully-qualified Lean name, used by stub builder for matching), `chapter`.

The existing `hansen_theorem_5_7_walkthrough.md` is ported to `site/walkthroughs/chapter5/theorem-5-7.qmd` as the reference example.

### 4. Quarto project — `site/_quarto.yml`

- Project type: `book` (academic feel, native theorem/proof environments via `::: {.theorem}` / `::: {.proof}` divs).
- Math: KaTeX.
- Sidebar grouped by chapter, then "Utilities".
- Theme: a clean default (e.g., `cosmo` or Quarto book default).

### 5. Local workflow — `Makefile`

Targets:

- `site-export` — run `lake exe export_decls > site/_generated/declarations.json`.
- `site-stubs` — `uv run scripts/build_stubs.py`.
- `site-preview` — runs export + stubs, then `quarto preview site/` (live reload).
- `site-render` — runs export + stubs, then `quarto render site/` (one-shot to `site/_site/`).
- `site` — alias for `site-render`.

`site/README.md` documents prerequisites (Quarto installed, Lean toolchain present) and the targets above.

## Data flow

```
HansenEconometrics/*.lean
        │
        ▼ (lake exe export_decls)
site/_generated/declarations.json
        │
        ▼ (uv run build_stubs.py, reads walkthroughs/ index)
site/auto/**/*.qmd  +  site/auto/chapter*/index.qmd
        │
        ▼ (quarto render/preview, also reads site/walkthroughs/)
site/_site/  (HTML)
```

## Testing & verification

- Manual: `make site-render`, open `site/_site/index.html`, spot-check a stub page and the ported Theorem 5.7 walkthrough.
- The `build_stubs.py` script should be a pure function of its JSON input — re-running it twice produces no diff.
- The Lean export's stable sort makes `declarations.json` diff-friendly during development (even though the file is gitignored, this aids debugging).

## Open questions

None blocking. Future considerations (out of scope for v1):

- When/whether to enable a public deployment.
- Auto-extraction of "Downstream uses" from the Lean environment.
- A linter that checks every walkthrough's `lean_name:` actually exists in the environment.
