# Lean Theorem Walkthrough Site Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a local-only Quarto site that renders auto-generated stubs for every Lean declaration in `HansenEconometrics/` plus hand-written walkthroughs for headline theorems.

**Architecture:** A Lean meta-program (`scripts/ExportDecls.lean`) walks the environment and emits authoritative declaration metadata as JSON. A Python script (`scripts/build_stubs.py`) consumes that JSON and writes per-theorem `.qmd` stubs into `site/auto/`. Hand-written walkthroughs live in `site/walkthroughs/` and are linked from stubs via `lean_name:` frontmatter matching. Quarto renders everything to `site/_site/`. A `Makefile` wires it all together; nothing runs in CI.

**Tech Stack:** Lean 4 (existing), Quarto, Python 3 + Jinja2 (via `uv run` with PEP 723 inline deps), GNU Make.

**Spec:** `docs/superpowers/specs/2026-04-24-lean-theorem-walkthrough-site-design.md`

---

## Decisions resolved from spec review

- **GitHub source-link base URL:** hardcoded in `_quarto.yml` as a project metadata variable `github_repo: https://github.com/paulgp/lean-hansen-econometrics`. The Python builder reads this from `_quarto.yml`. (Single source of truth, easy to change.)
- **Slug case-collision risk:** slugs preserve case (`name.replace('.', '-')` — no lowercasing). Lean is case-sensitive; macOS HFS+ default is case-insensitive but not case-destructive, so distinct-by-case names produce distinct files. If two declarations differ only in case, the builder appends a short hash suffix.
- **`def` vs `theorem` in chapter index:** the per-chapter `index.qmd` table includes a `Kind` column so `def`/`theorem`/`lemma` are visible at a glance.
- **`quarto preview` flicker on `site/auto/` wipe:** acceptable for v1; documented in `site/README.md`. Mitigation deferred.

---

## File Structure

**New files:**
- `site/_quarto.yml` — Quarto book config
- `site/index.qmd` — landing page
- `site/README.md` — local workflow docs
- `site/walkthroughs/_template.qmd` — walkthrough template
- `site/walkthroughs/chapter5/theorem-5-7.qmd` — ported from existing walkthrough
- `scripts/ExportDecls.lean` — Lean meta-program
- `scripts/build_stubs.py` — stub generator (PEP 723 inline deps)
- `scripts/test_build_stubs.py` — pytest tests for the stub generator
- `Makefile` — local build targets

**Modified files:**
- `lakefile.toml` — register `export_decls` as a `lean_exe` target
- `.gitignore` — add `site/_generated/`, `site/_site/`

**Untouched:** everything under `HansenEconometrics/`.

---

## Task 1: Project skeleton + Makefile + gitignore

**Files:**
- Create: `site/_quarto.yml`, `site/index.qmd`, `site/README.md`, `Makefile`
- Modify: `.gitignore`

- [ ] **Step 1: Add gitignore entries**

Append to `.gitignore`:
```
# Walkthrough site build artifacts
site/_generated/
site/_site/
```

- [ ] **Step 2: Create `site/_quarto.yml`**

```yaml
project:
  type: book
  output-dir: _site

book:
  title: "Hansen Econometrics in Lean"
  author: "paulgp"
  search: true
  repo-url: https://github.com/paulgp/lean-hansen-econometrics
  repo-actions: [source]
  chapters:
    - index.qmd
    - part: "Walkthroughs"
      chapters:
        - walkthroughs/chapter5/theorem-5-7.qmd
    - part: "Auto-generated reference"
      chapters:
        - auto/index.qmd

format:
  html:
    theme: cosmo
    toc: true
    html-math-method: katex
    code-overflow: wrap

# Custom metadata consumed by build_stubs.py
github_repo: https://github.com/paulgp/lean-hansen-econometrics
```

- [ ] **Step 3: Create `site/index.qmd`**

```markdown
---
title: "Hansen Econometrics in Lean"
---

A companion site for the Lean formalization of Hansen's *Econometrics*.

- **Walkthroughs** — hand-written explanations of headline theorems with assumptions, proof sketches, and Lean-vs-textbook contrasts.
- **Auto-generated reference** — every public declaration in the Lean library, grouped by chapter.

See the [Theorem 5.7 walkthrough](walkthroughs/chapter5/theorem-5-7.qmd) for the canonical example of the walkthrough format.
```

- [ ] **Step 4: Create `site/README.md`**

```markdown
# Walkthrough site

Local-only Quarto site. Not deployed.

## Prerequisites

- [Quarto](https://quarto.org/docs/get-started/) installed
- Lean toolchain (already required for the main project)
- `uv` (already required globally)

## Build targets

From the repo root:

- `make site-export` — regenerate `site/_generated/declarations.json` from Lean
- `make site-stubs` — regenerate `site/auto/**` from the JSON
- `make site-preview` — export + stubs + `quarto preview` (live reload)
- `make site-render` — export + stubs + `quarto render` to `site/_site/`
- `make site` — alias for `site-render`

## Caveats

- `site/auto/` is wiped and regenerated on every stub build, so files there are never authored by hand.
- `quarto preview` may flicker briefly when stubs are regenerated.
```

- [ ] **Step 5: Create `Makefile`**

```makefile
.PHONY: site site-export site-stubs site-preview site-render

DECLS_JSON := site/_generated/declarations.json

$(DECLS_JSON): | site/_generated
	lake exe export_decls > $@

site/_generated:
	mkdir -p $@

site-export: $(DECLS_JSON)

site-stubs: site-export
	uv run scripts/build_stubs.py

site-preview: site-stubs
	cd site && quarto preview

site-render: site-stubs
	cd site && quarto render

site: site-render
```

- [ ] **Step 6: Verify skeleton**

Run: `cat site/_quarto.yml site/index.qmd site/README.md Makefile`
Expected: all files present and well-formed.

- [ ] **Step 7: Commit**

```bash
git add .gitignore site/_quarto.yml site/index.qmd site/README.md Makefile
git commit -m "Add Quarto site skeleton and Makefile"
```

---

## Task 2: Lean export script — `ExportDecls.lean`

**Files:**
- Create: `scripts/ExportDecls.lean`
- Modify: `lakefile.toml`

**Context for the engineer:**

> ⚠️ Lean toolchain APIs drift between releases. The current toolchain is in `lean-toolchain` at the repo root — check it before starting. Where the snippet below uses an API that has moved, look up the equivalent in Mathlib (`rg "findDeclarationRanges?" .lake/packages/mathlib/`) and adapt.
>
> Use `Lean.Json` (from `import Lean.Data.Json`) for JSON construction rather than building strings by hand — `Json.mkObj` + `Json.compress` (or `Json.pretty`) handles escaping correctly. The `escapeJson` helper shown below is illustrative; replace it with `Json` if straightforward.
>
> `Name.anyS` does not exist; iterate name components via `n.components.any (fun c => ...)` or pattern-match on `Name.str`/`Name.num` directly.

The Lean environment exposes `Environment.constants` (a `SMap Name ConstantInfo`). For each `ConstantInfo` we need: name, kind (theorem/def/etc.), source position, docstring, and a pretty-printed type. Source positions are in `Environment.const2ModIdx` + `ModuleInfo`. Docstrings via `Lean.findDocString?`. Pretty-printing via `Lean.PrettyPrinter.ppExpr`.

We filter to declarations whose source module starts with `HansenEconometrics`. We skip auto-generated decls (those whose names contain `_proof_`, `_eqn_`, `_aux_`, `_cstage`, or any `Name` component starting with `_`).

- [ ] **Step 1: Add `lean_exe` target to `lakefile.toml`**

Append to `lakefile.toml`:
```toml
[[lean_exe]]
name = "export_decls"
root = "scripts.ExportDecls"
```

- [ ] **Step 2: Write `scripts/ExportDecls.lean`**

```lean
import Lean
import HansenEconometrics

open Lean Elab

namespace ExportDecls

structure DeclRecord where
  name : String
  «namespace» : String
  kind : String
  signature : String
  docstring : Option String
  file : String
  line : Nat
  chapter : Option Nat
  isPrivate : Bool
  deriving Inhabited

def escapeJson (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | c =>
      if c.toNat < 0x20 then
        acc ++ s!"\\u{(toString c.toNat).leftpad 4 '0'}"
      else
        acc.push c

def jsonString (s : String) : String := "\"" ++ escapeJson s ++ "\""

def jsonOptString : Option String → String
  | none => "null"
  | some s => jsonString s

def jsonOptNat : Option Nat → String
  | none => "null"
  | some n => toString n

def DeclRecord.toJson (r : DeclRecord) : String :=
  "{" ++
    "\"name\":" ++ jsonString r.name ++ "," ++
    "\"namespace\":" ++ jsonString r.namespace ++ "," ++
    "\"kind\":" ++ jsonString r.kind ++ "," ++
    "\"signature\":" ++ jsonString r.signature ++ "," ++
    "\"docstring\":" ++ jsonOptString r.docstring ++ "," ++
    "\"file\":" ++ jsonString r.file ++ "," ++
    "\"line\":" ++ toString r.line ++ "," ++
    "\"chapter\":" ++ jsonOptNat r.chapter ++ "," ++
    "\"isPrivate\":" ++ (if r.isPrivate then "true" else "false") ++
  "}"

def kindOf : ConstantInfo → Option String
  | .thmInfo _ => some "theorem"
  | .defnInfo _ => some "def"
  | .axiomInfo _ => some "axiom"
  | _ => none

def isHidden (n : Name) : Bool :=
  n.anyS fun s =>
    s.startsWith "_" ||
    s == "match" || s == "rec" ||
    s.startsWith "match_" || s.startsWith "rec_" ||
    s.endsWith "._proof_" || s.endsWith "._eqn_" || s.endsWith "._cstage1" || s.endsWith "._cstage2"

def chapterOfModule (mod : Name) : Option Nat := Id.run do
  let s := mod.toString
  -- look for "Chapter<N>" prefix on the last component
  let parts := s.splitOn "."
  let last := parts.getLastD ""
  if last.startsWith "Chapter" then
    let rest := last.drop "Chapter".length
    let digits := rest.takeWhile Char.isDigit
    if digits.isEmpty then none else digits.toNat?
  else
    none

def relativeFilePath (mod : Name) : String :=
  -- HansenEconometrics.Chapter5NormalRegression -> HansenEconometrics/Chapter5NormalRegression.lean
  (mod.toString.replace "." "/") ++ ".lean"

def collect : MetaM (Array DeclRecord) := do
  let env ← getEnv
  let mut out : Array DeclRecord := #[]
  for (name, ci) in env.constants.toList do
    let some kind := kindOf ci | continue
    if isHidden name then continue
    let some modIdx := env.const2ModIdx.find? name | continue
    let mod := env.allImportedModuleNames.get? modIdx |>.getD .anonymous
    let modStr := mod.toString
    unless modStr.startsWith "HansenEconometrics" do continue
    let isPrivate := Lean.isPrivateName name
    let docstring ← Lean.findDocString? env name
    let pos := (← Lean.findDeclarationRanges? name).map (·.range.pos)
    let line := pos.map (·.line) |>.getD 0
    let sig ← Meta.ppExpr ci.type
    let nsName := name.getPrefix
    out := out.push {
      name := name.toString
      «namespace» := nsName.toString
      kind
      signature := toString sig
      docstring
      file := relativeFilePath mod
      line
      chapter := chapterOfModule mod
      isPrivate
    }
  let sorted := out.qsort (fun a b =>
    if a.file == b.file then a.line < b.line else a.file < b.file)
  return sorted

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `HansenEconometrics }] {} 0
  let ctx : Core.Context := { fileName := "<export>", fileMap := default }
  let coreState : Core.State := { env }
  let (records, _) ← (Meta.MetaM.run' collect).run ctx coreState
  IO.println "["
  let n := records.size
  for h : i in [:n] do
    let r := records[i]
    let comma := if i + 1 == n then "" else ","
    IO.println s!"  {r.toJson}{comma}"
  IO.println "]"

end ExportDecls

def main : IO Unit := ExportDecls.main
```

- [ ] **Step 3: Build the executable**

Run: `lake build export_decls`
Expected: build succeeds. If type errors arise (Lean API surface drifts version-to-version), fix them by consulting the Mathlib source for the equivalent calls — common adjustments: `Meta.ppExpr` signature, `findDeclarationRanges?` location, `allImportedModuleNames` shape.

- [ ] **Step 4: Run and inspect output**

Run: `lake exe export_decls > /tmp/decls.json && head -50 /tmp/decls.json && echo "---" && wc -l /tmp/decls.json`
Expected: valid JSON array, first record is from `HansenEconometrics/...`, total length is hundreds of lines (one record per declaration).

- [ ] **Step 5: Spot-check known theorem**

Run: `grep -A1 scaledOlsResidualVarianceStatistic_hasLaw_chiSquared /tmp/decls.json | head -5`
Expected: a record with `"chapter": 5` and `"line": 270`.

- [ ] **Step 6: Commit**

```bash
git add lakefile.toml scripts/ExportDecls.lean
git commit -m "Add Lean export_decls executable for site generation"
```

---

## Task 3: Python stub builder — tests first

**Files:**
- Create: `scripts/build_stubs.py`, `scripts/test_build_stubs.py`

**Context:** the builder is pure: `(declarations.json, walkthroughs index, github_repo) → set of .qmd files`. We test it by giving it a small synthetic JSON and asserting the produced file tree matches expectations.

- [ ] **Step 1: Write the failing test file**

Create `scripts/test_build_stubs.py`:
```python
# /// script
# requires-python = ">=3.11"
# dependencies = ["jinja2", "pytest", "pyyaml"]
# ///
"""Tests for build_stubs.py.

Run via: uv run pytest scripts/test_build_stubs.py -v
"""
from pathlib import Path
import json
import textwrap
import sys

sys.path.insert(0, str(Path(__file__).parent))
from build_stubs import build  # noqa: E402


def write_json(path: Path, records):
    path.write_text(json.dumps(records))


def test_stub_for_unwalked_theorem(tmp_path):
    decls = tmp_path / "decls.json"
    write_json(decls, [{
        "name": "HansenEconometrics.Chapter5.foo",
        "namespace": "HansenEconometrics.Chapter5",
        "kind": "theorem",
        "signature": "∀ x, P x",
        "docstring": "A simple theorem.",
        "file": "HansenEconometrics/Chapter5NormalRegression.lean",
        "line": 42,
        "chapter": 5,
        "isPrivate": False,
    }])
    out = tmp_path / "auto"
    build(decls_path=decls, walkthroughs_dir=tmp_path / "walkthroughs",
          out_dir=out, github_repo="https://github.com/x/y")
    stub = out / "chapter5" / "HansenEconometrics-Chapter5-foo.qmd"
    assert stub.exists()
    text = stub.read_text()
    assert "No walkthrough yet" in text
    assert "github.com/x/y" in text
    assert "L42" in text
    assert "∀ x, P x" in text
    assert "A simple theorem." in text


def test_walkthrough_match_overrides_stub(tmp_path):
    walkthroughs = tmp_path / "walkthroughs" / "chapter5"
    walkthroughs.mkdir(parents=True)
    (walkthroughs / "theorem-foo.qmd").write_text(textwrap.dedent("""\
        ---
        title: "Theorem foo"
        lean_name: "HansenEconometrics.Chapter5.foo"
        chapter: 5
        ---
        Body.
        """))
    decls = tmp_path / "decls.json"
    write_json(decls, [{
        "name": "HansenEconometrics.Chapter5.foo",
        "namespace": "HansenEconometrics.Chapter5",
        "kind": "theorem",
        "signature": "∀ x, P x",
        "docstring": None,
        "file": "HansenEconometrics/Chapter5NormalRegression.lean",
        "line": 42,
        "chapter": 5,
        "isPrivate": False,
    }])
    out = tmp_path / "auto"
    build(decls_path=decls, walkthroughs_dir=tmp_path / "walkthroughs",
          out_dir=out, github_repo="https://github.com/x/y")
    stub = out / "chapter5" / "HansenEconometrics-Chapter5-foo.qmd"
    text = stub.read_text()
    assert "See full walkthrough" in text
    assert "../walkthroughs/chapter5/theorem-foo.qmd" in text or "theorem-foo" in text


def test_chapter_index_lists_all_decls(tmp_path):
    decls = tmp_path / "decls.json"
    write_json(decls, [
        {"name": "A.bar", "namespace": "A", "kind": "theorem",
         "signature": "T", "docstring": None,
         "file": "HansenEconometrics/Chapter3FWL.lean", "line": 1,
         "chapter": 3, "isPrivate": False},
        {"name": "A.baz", "namespace": "A", "kind": "def",
         "signature": "D", "docstring": None,
         "file": "HansenEconometrics/Chapter3FWL.lean", "line": 5,
         "chapter": 3, "isPrivate": False},
    ])
    out = tmp_path / "auto"
    build(decls_path=decls, walkthroughs_dir=tmp_path / "walkthroughs",
          out_dir=out, github_repo="https://github.com/x/y")
    idx = (out / "chapter3" / "index.qmd").read_text()
    assert "A.bar" in idx and "A.baz" in idx
    assert "theorem" in idx and "def" in idx


def test_utilities_bucket_for_no_chapter(tmp_path):
    decls = tmp_path / "decls.json"
    write_json(decls, [{
        "name": "ChiSquared.foo", "namespace": "ChiSquared", "kind": "theorem",
        "signature": "T", "docstring": None,
        "file": "HansenEconometrics/ChiSquared.lean", "line": 1,
        "chapter": None, "isPrivate": False,
    }])
    out = tmp_path / "auto"
    build(decls_path=decls, walkthroughs_dir=tmp_path / "walkthroughs",
          out_dir=out, github_repo="https://github.com/x/y")
    assert (out / "utilities" / "ChiSquared-foo.qmd").exists()
    assert (out / "utilities" / "index.qmd").exists()


def test_wholesale_wipe(tmp_path):
    out = tmp_path / "auto"
    out.mkdir()
    (out / "stale.qmd").write_text("old")
    decls = tmp_path / "decls.json"
    write_json(decls, [])
    build(decls_path=decls, walkthroughs_dir=tmp_path / "walkthroughs",
          out_dir=out, github_repo="https://github.com/x/y")
    assert not (out / "stale.qmd").exists()


def test_top_level_index(tmp_path):
    decls = tmp_path / "decls.json"
    write_json(decls, [
        {"name": "A.bar", "namespace": "A", "kind": "theorem",
         "signature": "T", "docstring": None,
         "file": "HansenEconometrics/Chapter3FWL.lean", "line": 1,
         "chapter": 3, "isPrivate": False},
        {"name": "B.qux", "namespace": "B", "kind": "theorem",
         "signature": "T", "docstring": None,
         "file": "HansenEconometrics/Chapter5NormalRegression.lean", "line": 1,
         "chapter": 5, "isPrivate": False},
    ])
    out = tmp_path / "auto"
    build(decls_path=decls, walkthroughs_dir=tmp_path / "walkthroughs",
          out_dir=out, github_repo="https://github.com/x/y")
    top = (out / "index.qmd").read_text()
    assert "Chapter 3" in top and "Chapter 5" in top
```

- [ ] **Step 2: Run tests, expect all to fail (no module yet)**

Run: `uv run pytest scripts/test_build_stubs.py -v`
Expected: ImportError or ModuleNotFoundError on `build_stubs`.

- [ ] **Step 3: Write `scripts/build_stubs.py`**

```python
# /// script
# requires-python = ">=3.11"
# dependencies = ["jinja2", "pyyaml"]
# ///
"""Generate per-declaration Quarto stubs from the Lean export JSON.

Idempotent: wipes and rewrites the output directory on every run.
"""
from __future__ import annotations

import json
import shutil
from pathlib import Path
from typing import Iterable

import yaml
from jinja2 import Environment, BaseLoader


REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_DECLS = REPO_ROOT / "site" / "_generated" / "declarations.json"
DEFAULT_OUT = REPO_ROOT / "site" / "auto"
DEFAULT_WALKTHROUGHS = REPO_ROOT / "site" / "walkthroughs"
DEFAULT_QUARTO_YML = REPO_ROOT / "site" / "_quarto.yml"


STUB_TEMPLATE = """\
---
title: "`{{ name }}`"
lean_name: "{{ name }}"
---

{% if walkthrough_path %}
::: {.callout-tip}
**See full walkthrough:** [{{ walkthrough_title }}]({{ walkthrough_path }})
:::
{% else %}
::: {.callout-note}
No walkthrough yet. [Source]({{ source_url }})
:::
{% endif %}

## Signature

```lean
{{ signature }}
```

{% if docstring %}
## Docstring

{{ docstring }}
{% endif %}

**Kind:** `{{ kind }}` &middot; **Source:** [{{ file }}:{{ line }}]({{ source_url }})
"""

CHAPTER_INDEX_TEMPLATE = """\
---
title: "{{ heading }}"
---

| Name | Kind | Walkthrough | Source |
|------|------|-------------|--------|
{% for r in rows -%}
| [`{{ r.name }}`]({{ r.stub }}) | `{{ r.kind }}` | {{ "✓" if r.has_walkthrough else "—" }} | [{{ r.file }}:{{ r.line }}]({{ r.source_url }}) |
{% endfor %}
"""

TOP_INDEX_TEMPLATE = """\
---
title: "Auto-generated reference"
---

Every public declaration in `HansenEconometrics/`, grouped by chapter.

{% for group in groups %}
- [{{ group.heading }}]({{ group.path }}) ({{ group.count }} declarations)
{% endfor %}
"""


def load_walkthroughs(walkthroughs_dir: Path) -> dict[str, tuple[Path, str]]:
    """Map fully-qualified Lean name -> (path, title)."""
    index: dict[str, tuple[Path, str]] = {}
    if not walkthroughs_dir.exists():
        return index
    for qmd in walkthroughs_dir.rglob("*.qmd"):
        if qmd.name.startswith("_"):
            continue
        text = qmd.read_text()
        if not text.startswith("---"):
            continue
        end = text.find("\n---", 3)
        if end < 0:
            continue
        meta = yaml.safe_load(text[3:end]) or {}
        lean_name = meta.get("lean_name")
        if lean_name:
            index[lean_name] = (qmd, meta.get("title", lean_name))
    return index


def slug_for(name: str) -> str:
    return name.replace(".", "-")


def chapter_dir(chapter: int | None) -> str:
    return f"chapter{chapter}" if chapter is not None else "utilities"


def chapter_heading(chapter: int | None) -> str:
    return f"Chapter {chapter}" if chapter is not None else "Utilities"


def github_repo_from_quarto(quarto_yml: Path) -> str:
    if not quarto_yml.exists():
        return ""
    data = yaml.safe_load(quarto_yml.read_text()) or {}
    return data.get("github_repo", "")


def build(
    decls_path: Path,
    walkthroughs_dir: Path,
    out_dir: Path,
    github_repo: str,
) -> None:
    records = json.loads(Path(decls_path).read_text())
    walkthroughs = load_walkthroughs(walkthroughs_dir)

    # Wipe out_dir wholesale.
    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True)

    env = Environment(loader=BaseLoader(), keep_trailing_newline=True)
    stub_t = env.from_string(STUB_TEMPLATE)
    chapter_t = env.from_string(CHAPTER_INDEX_TEMPLATE)
    top_t = env.from_string(TOP_INDEX_TEMPLATE)

    grouped: dict[int | None, list[dict]] = {}

    # Detect case-only collisions.
    seen_slugs: dict[tuple[int | None, str], str] = {}

    for r in records:
        chap = r.get("chapter")
        cdir_name = chapter_dir(chap)
        cdir = out_dir / cdir_name
        cdir.mkdir(exist_ok=True)
        slug = slug_for(r["name"])
        key = (chap, slug.lower())
        if key in seen_slugs and seen_slugs[key] != slug:
            slug = f"{slug}-{abs(hash(r['name'])) % 0x10000:04x}"
        seen_slugs[key] = slug

        source_url = (
            f"{github_repo}/blob/main/{r['file']}#L{r['line']}"
            if github_repo else f"{r['file']}#L{r['line']}"
        )

        wt = walkthroughs.get(r["name"])
        if wt:
            wt_path, wt_title = wt
            rel = "../" + wt_path.relative_to(walkthroughs_dir.parent).as_posix()
            walkthrough_path = rel
            walkthrough_title = wt_title
        else:
            walkthrough_path = None
            walkthrough_title = None

        stub_text = stub_t.render(
            name=r["name"],
            signature=r["signature"],
            docstring=r.get("docstring"),
            kind=r["kind"],
            file=r["file"],
            line=r["line"],
            source_url=source_url,
            walkthrough_path=walkthrough_path,
            walkthrough_title=walkthrough_title,
        )
        (cdir / f"{slug}.qmd").write_text(stub_text)

        grouped.setdefault(chap, []).append({
            "name": r["name"],
            "kind": r["kind"],
            "stub": f"{slug}.qmd",
            "file": r["file"],
            "line": r["line"],
            "source_url": source_url,
            "has_walkthrough": wt is not None,
        })

    # Per-chapter index pages.
    sorted_chaps = sorted(grouped.keys(), key=lambda c: (c is None, c or 0))
    groups_meta = []
    for chap in sorted_chaps:
        rows = sorted(grouped[chap], key=lambda r: r["name"])
        cdir = out_dir / chapter_dir(chap)
        idx_text = chapter_t.render(heading=chapter_heading(chap), rows=rows)
        (cdir / "index.qmd").write_text(idx_text)
        groups_meta.append({
            "heading": chapter_heading(chap),
            "path": f"{chapter_dir(chap)}/index.qmd",
            "count": len(rows),
        })

    # Top-level index.
    (out_dir / "index.qmd").write_text(top_t.render(groups=groups_meta))


def main() -> None:
    github_repo = github_repo_from_quarto(DEFAULT_QUARTO_YML)
    build(
        decls_path=DEFAULT_DECLS,
        walkthroughs_dir=DEFAULT_WALKTHROUGHS,
        out_dir=DEFAULT_OUT,
        github_repo=github_repo,
    )
    print(f"Wrote stubs to {DEFAULT_OUT}")


if __name__ == "__main__":
    main()
```

- [ ] **Step 4: Run tests, expect all to pass**

Run: `uv run pytest scripts/test_build_stubs.py -v`
Expected: 6 passed.

- [ ] **Step 5: Commit**

```bash
git add scripts/build_stubs.py scripts/test_build_stubs.py
git commit -m "Add stub generator with tests"
```

---

## Task 4: Walkthrough template + port Theorem 5.7

**Files:**
- Create: `site/walkthroughs/_template.qmd`, `site/walkthroughs/chapter5/theorem-5-7.qmd`

- [ ] **Step 1: Create `site/walkthroughs/_template.qmd`**

```markdown
---
title: "Theorem X.Y — <short name>"
lean_name: "<HansenEconometrics.fully.qualified.Name>"
chapter: N
---

## Textbook statement

> Hansen's wording (paraphrased), with the equation:
>
> $$\text{...}$$

## Assumptions

- ...
- ...

## Lean statement

The corresponding Lean theorem:

- [`<name>`](<github source link>) at `HansenEconometrics/...lean:<line>`

```lean
theorem ... := ...
```

## Translation notes

Where the Lean phrasing differs from Hansen and why the difference is harmless.

## Proof sketch

Human-readable LaTeX walkthrough.

## Lean proof structure

Chain of supporting lemmas, each linked:

- [`lemma_a`](<link>)
- [`lemma_b`](<link>)

## Downstream uses

- (optional) where this theorem is consumed elsewhere in the formalization.
```

- [ ] **Step 2: Port `hansen_theorem_5_7_walkthrough.md` into the template**

Read the existing `hansen_theorem_5_7_walkthrough.md` and produce `site/walkthroughs/chapter5/theorem-5-7.qmd` following the template. Required:

- Frontmatter `lean_name: "HansenEconometrics.Chapter5.scaledOlsResidualVarianceStatistic_hasLaw_chiSquared"` (or whatever the actual fully-qualified name is — verify by grepping the Lean source).
- The "Assumptions" section must be explicit: homoskedastic linear model, $e \sim N(0, \sigma^2 I)$, $X$ full column rank.
- All `Chapter5NormalRegression.lean:NNN` references become full GitHub permalinks: `https://github.com/paulgp/lean-hansen-econometrics/blob/main/HansenEconometrics/Chapter5NormalRegression.lean#LNNN`.
- Math blocks use Quarto's standard `$$...$$` syntax (already compatible).

- [ ] **Step 3: Verify lean_name matches the Lean source**

Run: `rg "scaledOlsResidualVarianceStatistic_hasLaw_chiSquared" HansenEconometrics/Chapter5NormalRegression.lean`
Expected: shows the theorem declaration. The `lean_name` frontmatter must equal the fully-qualified name (namespace + theorem name) exactly as it appears in the Lean environment.

- [ ] **Step 4: Commit**

```bash
git add site/walkthroughs/_template.qmd site/walkthroughs/chapter5/theorem-5-7.qmd
git commit -m "Add walkthrough template and port Theorem 5.7"
```

---

## Task 5: End-to-end smoke test

**Files:** none new — exercising the full pipeline.

- [ ] **Step 1: Run the full export + stubs pipeline**

Run: `make site-stubs`
Expected: succeeds, populates `site/_generated/declarations.json` and `site/auto/**`.

- [ ] **Step 2: Verify Theorem 5.7 stub redirects to walkthrough**

Run: `cat site/auto/chapter5/HansenEconometrics-Chapter5-scaledOlsResidualVarianceStatistic_hasLaw_chiSquared.qmd 2>/dev/null || ls site/auto/chapter5/ | grep -i scaled`
Expected: the file exists; its body contains `See full walkthrough` rather than `No walkthrough yet`. (If the slug differs, identify the actual filename and check it.)

- [ ] **Step 3: Render the site**

Run: `make site-render`
Expected: succeeds; `site/_site/index.html` exists.

- [ ] **Step 4: Visual spot-check**

Run: `open site/_site/index.html` (or note the path for the user to inspect).
Expected (for the user to confirm): landing page renders, Theorem 5.7 walkthrough renders with math, chapter index pages list theorems, an arbitrary auto-stub renders the signature in a Lean code block.

- [ ] **Step 5: Confirm idempotency**

Run: `make site-stubs && git status site/auto/ 2>/dev/null; echo "(site/auto/ is gitignored — checking by hash)"; find site/auto -type f | sort | xargs shasum > /tmp/h1 && make site-stubs && find site/auto -type f | sort | xargs shasum > /tmp/h2 && diff /tmp/h1 /tmp/h2 && echo "IDEMPOTENT"`
Expected: prints `IDEMPOTENT`.

- [ ] **Step 6: Final commit (if any tweaks needed)**

If steps 1–5 surfaced bugs, fix them in the appropriate task's files, re-run, then commit with a `Fix:` message describing the bug. Otherwise nothing to commit — Task 5 is verification only.

---

## Done when

- `make site-render` succeeds from a clean checkout (after `lake build`).
- `site/_site/index.html` opens locally and shows the landing page, Theorem 5.7 walkthrough, and chapter indexes.
- `pytest scripts/test_build_stubs.py` is green.
- The Theorem 5.7 stub in `site/auto/` links to the hand-written walkthrough rather than showing the "no walkthrough yet" callout.
- No CI workflow exists; nothing is deployed.
