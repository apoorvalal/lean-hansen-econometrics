# Adversarial Lean Review Harness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a reusable, cross-harness adversarial review harness for the Lean code that flags redundancy, API-hygiene, faithfulness-to-Hansen, and proof-quality issues, verifies each finding, emits a report, and drafts mechanical fixes as green commits.

**Architecture:** Two layers. Layer 1 = harness-agnostic assets under `review/` (rubric, prompt templates, finding schema, a testable worklist resolver, README). Layer 2 = a thin Claude Code `Workflow` orchestrator at `scripts/review.workflow.js` that reads Layer 1 and runs review → adversarial-verify → dedup → report → draft-PR. Other harnesses (Codex) reuse Layer 1 and swap only Layer 2.

**Tech Stack:** Lean 4 + Lake (target codebase), Python 3 via `uv` (worklist resolver + schema validation, PEP 723 inline deps, stdlib-only), JavaScript (Claude Code `Workflow` script), Markdown/JSON (assets). `rg`/`git` required; Lean LSP MCP tools (`leansearch`/`loogle`/`lean_goal`) optional with `rg` fallback.

**Spec:** `docs/superpowers/specs/2026-06-06-adversarial-lean-review-harness-design.md`

**Conventions for the implementer:**
- Use `uv run` for all Python (never bare `python`/`pip`). Tests use stdlib `unittest` so no deps are needed.
- Use `rg` (ripgrep), not `grep -r`/`find`, for any searching.
- Commit after every task. Keep commits scoped to the task's files.
- Path-namespace rule (critical, easy to get wrong): excerpt dirs are **zero-padded** (`textbook/ch07/`, `textbook/ch10/`); inventory files are **unpadded** (`inventory/ch7-inventory.md`, `inventory/ch10-inventory.md`). The excerpt filename is `ch{NN}_excerpt.txt`.
- Test discovery relies on Python ≥3.3 implicit namespace packages: create `tests/review/__init__.py` but do **not** add a `tests/__init__.py` (there is no `pyproject.toml`, so `uv run` puts cwd on `sys.path` and `uv run python -m unittest tests.review.test_worklist -v` works as-is). Don't "fix" the missing parent `__init__.py`.

---

## File Structure

**Create:**
- `review/finding-schema.json` — JSON Schema for a single finding.
- `review/worklist.py` — testable resolver: file → {chapter, excerpt_path, inventory_path, decls}. Also a `--validate-schema` mode that validates finding JSON against the schema (replaces the missing `jq`).
- `tests/review/test_worklist.py` — unit tests for the resolver.
- `tests/review/__init__.py`, `tests/review/fixtures/` — test scaffolding/fixtures.
- `review/rubric.md` — 4 dimensions → AGENTS.md rules → finding criteria + severity.
- `review/prompts/reviewer.md` — per (file × dimension) reviewer template.
- `review/prompts/verifier.md` — adversarial skeptic (refute-biased) template.
- `review/prompts/fixer.md` — mechanical fix-agent template.
- `review/worklist.md` — human-readable procedure (documents what `worklist.py` automates).
- `review/README.md` — how to run on Claude Code vs Codex vs manually, with a self-containment checklist.
- `review/reports/.gitkeep` — output dir for generated reports.
- `scripts/review.workflow.js` — Layer-2 Claude Code orchestrator.

**Modify:** none (the harness is purely additive).

**Responsibilities:** `worklist.py` is the single source of truth for "what inputs does the review of file X get." The workflow and any Codex runner both shell out to it, so the fragile path/decl logic is written and tested once.

---

## Task 1: Finding schema + a schema validator (no jq)

**Files:**
- Create: `review/finding-schema.json`
- Create: `review/worklist.py` (start with the `--validate-schema` subcommand only)
- Create: `tests/review/__init__.py`
- Create: `tests/review/test_worklist.py`

- [ ] **Step 1: Write the failing test**

`tests/review/test_worklist.py`:
```python
import json, subprocess, sys, unittest
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
WORKLIST = REPO / "review" / "worklist.py"

def run(*args, stdin=None):
    return subprocess.run(
        ["uv", "run", str(WORKLIST), *args],
        input=stdin, capture_output=True, text=True, cwd=REPO,
    )

VALID_FINDING = {
    "id": "abc123", "file": "HansenEconometrics/X.lean", "line": 10,
    "decl": "foo", "dimension": "redundancy", "severity": "major",
    "rule": "AGENTS.md reuse-Mathlib-first", "claim": "duplicates Mathlib",
    "evidence": "Real.foo exists", "suggested_fix": "reuse Real.foo",
    "mechanical": False, "confidence": "high",
}

class TestSchemaValidation(unittest.TestCase):
    def test_valid_finding_passes(self):
        r = run("--validate-schema", stdin=json.dumps([VALID_FINDING]))
        self.assertEqual(r.returncode, 0, r.stderr)

    def test_missing_required_field_fails(self):
        bad = {k: v for k, v in VALID_FINDING.items() if k != "dimension"}
        r = run("--validate-schema", stdin=json.dumps([bad]))
        self.assertEqual(r.returncode, 1)
        self.assertIn("dimension", r.stderr)

    def test_bad_enum_value_fails(self):
        bad = {**VALID_FINDING, "severity": "catastrophic"}
        r = run("--validate-schema", stdin=json.dumps([bad]))
        self.assertEqual(r.returncode, 1)

if __name__ == "__main__":
    unittest.main()
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `uv run python -m unittest tests.review.test_worklist -v`
Expected: FAIL (worklist.py missing / no `--validate-schema`).

- [ ] **Step 3: Write `review/finding-schema.json`**

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "Lean review finding",
  "type": "object",
  "additionalProperties": false,
  "required": ["id", "file", "line", "decl", "dimension", "severity",
               "rule", "claim", "evidence", "suggested_fix", "mechanical", "confidence"],
  "properties": {
    "id":        {"type": "string", "description": "sha1(file:line:decl:dimension)"},
    "file":      {"type": "string"},
    "line":      {"type": "integer", "minimum": 1},
    "decl":      {"type": "string"},
    "dimension": {"enum": ["redundancy", "hygiene", "faithfulness", "proof-quality"]},
    "severity":  {"enum": ["blocker", "major", "minor", "nit"]},
    "rule":      {"type": "string"},
    "claim":     {"type": "string"},
    "evidence":  {"type": "string"},
    "suggested_fix": {"type": "string"},
    "mechanical": {"type": "boolean"},
    "confidence": {"enum": ["high", "medium", "low"]}
  }
}
```

- [ ] **Step 4: Write `review/worklist.py` with the `--validate-schema` subcommand**

Implement a minimal, dependency-free JSON-Schema check (the schema only uses
`required`, `enum`, `type`, `minimum`, `additionalProperties`). PEP 723 header,
stdlib only. Reads a JSON array of findings from stdin; prints the first failing
field name to stderr and exits 1 on any violation, else exits 0.

```python
# /// script
# requires-python = ">=3.10"
# ///
"""Worklist resolver + finding-schema validator for the Lean review harness."""
import json, sys, argparse   # hashlib, re added in Tasks 2-3
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
SCHEMA = json.loads((REPO / "review" / "finding-schema.json").read_text())

def _check(obj, schema, path=""):
    """Tiny validator for the subset of JSON Schema we use. Returns error str or None."""
    t = schema.get("type")
    if t == "object" or "properties" in schema:
        if not isinstance(obj, dict):
            return f"{path or 'root'}: expected object"
        for req in schema.get("required", []):
            if req not in obj:
                return f"{path}{req}: required field missing"
        if schema.get("additionalProperties") is False:
            for k in obj:
                if k not in schema.get("properties", {}):
                    return f"{path}{k}: unexpected field"
        for k, sub in schema.get("properties", {}).items():
            if k in obj:
                err = _check(obj[k], sub, f"{path}{k}.")
                if err:
                    return err
        return None
    if "enum" in schema:
        return None if obj in schema["enum"] else f"{path[:-1]}: {obj!r} not in {schema['enum']}"
    if t == "string":
        return None if isinstance(obj, str) else f"{path[:-1]}: expected string"
    if t == "integer":
        if not isinstance(obj, int) or isinstance(obj, bool):
            return f"{path[:-1]}: expected integer"
        if "minimum" in schema and obj < schema["minimum"]:
            return f"{path[:-1]}: below minimum"
        return None
    if t == "boolean":
        return None if isinstance(obj, bool) else f"{path[:-1]}: expected boolean"
    return None

def validate_schema(stream) -> int:
    try:
        findings = json.load(stream)
    except json.JSONDecodeError as e:
        print(f"invalid JSON on stdin: {e}", file=sys.stderr)
        return 2
    if not isinstance(findings, list):
        findings = [findings]
    for i, f in enumerate(findings):
        err = _check(f, SCHEMA, "")
        if err:
            print(f"finding[{i}]: {err}", file=sys.stderr)
            return 1
    return 0

def main(argv=None):
    p = argparse.ArgumentParser()
    p.add_argument("--validate-schema", action="store_true")
    # (resolve subcommand added in Task 2/3)
    p.add_argument("files", nargs="*")
    args = p.parse_args(argv)
    if args.validate_schema:
        return validate_schema(sys.stdin)
    p.error("no command given")

if __name__ == "__main__":
    sys.exit(main())
```

- [ ] **Step 5: Run the test to verify it passes**

Run: `uv run python -m unittest tests.review.test_worklist -v`
Expected: 3 tests PASS.

- [ ] **Step 6: Commit**

```bash
git add review/finding-schema.json review/worklist.py tests/review/__init__.py tests/review/test_worklist.py
git commit -m "Add review finding schema and stdlib schema validator"
```

---

## Task 2: Worklist resolver — chapter & path resolution

**Files:**
- Modify: `review/worklist.py` (add `resolve`)
- Modify: `tests/review/test_worklist.py`

- [ ] **Step 1: Write the failing test** (append a class)

```python
class TestResolvePaths(unittest.TestCase):
    def resolve(self, path):
        r = run("resolve", path)
        self.assertEqual(r.returncode, 0, r.stderr)
        return json.loads(r.stdout)[0]

    def test_padded_excerpt_unpadded_inventory_ch10(self):
        out = self.resolve("HansenEconometrics/Chapter10Bootstrap/HigherOrder.lean")
        self.assertEqual(out["chapter"], 10)
        self.assertEqual(out["excerpt_path"], "textbook/ch10/ch10_excerpt.txt")
        self.assertEqual(out["inventory_path"], "inventory/ch10-inventory.md")

    def test_single_digit_chapter_padding_split(self):
        out = self.resolve("HansenEconometrics/Chapter7Asymptotics.lean")
        self.assertEqual(out["chapter"], 7)
        self.assertEqual(out["excerpt_path"], "textbook/ch07/ch07_excerpt.txt")  # padded
        self.assertEqual(out["inventory_path"], "inventory/ch7-inventory.md")    # unpadded

    def test_nested_module_file(self):
        out = self.resolve("HansenEconometrics/Chapter7Asymptotics/Normality.lean")
        self.assertEqual(out["chapter"], 7)

    def test_non_chapter_file_has_null_chapter(self):
        out = self.resolve("HansenEconometrics/ProbabilityUtils.lean")
        self.assertIsNone(out["chapter"])
        self.assertIsNone(out["excerpt_path"])
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `uv run python -m unittest tests.review.test_worklist.TestResolvePaths -v`
Expected: FAIL (no `resolve` subcommand).

- [ ] **Step 3: Implement chapter/path resolution in `worklist.py`**

Add a `resolve` subcommand that takes one or more file paths and prints a JSON
array. For each file, extract the chapter with `re.search(r"Chapter(\d+)", path)`.
If found: `chapter=int(n)`, `excerpt_path=f"textbook/ch{n:02d}/ch{n:02d}_excerpt.txt"`,
`inventory_path=f"inventory/ch{n}-inventory.md"`. If not found, all three are
`None`. (Do **not** require the files to exist on disk — keep the resolver pure so
tests need no fixtures; existence is checked separately in the workflow.) Emit
`{"file", "chapter", "excerpt_path", "inventory_path", "decls": []}` (decls filled
in Task 3).

Wire `resolve` into `main()` via a subparser; keep `--validate-schema` working.

- [ ] **Step 4: Run the test to verify it passes**

Run: `uv run python -m unittest tests.review.test_worklist -v`
Expected: all tests PASS (Task 1 + Task 2).

- [ ] **Step 5: Commit**

```bash
git add review/worklist.py tests/review/test_worklist.py
git commit -m "Add worklist chapter/excerpt/inventory path resolution"
```

---

## Task 3: Worklist resolver — declaration extraction

**Files:**
- Modify: `review/worklist.py` (fill `decls`)
- Create: `tests/review/fixtures/Sample.lean`
- Modify: `tests/review/test_worklist.py`

- [ ] **Step 1: Create the fixture** `tests/review/fixtures/Sample.lean`

Cover the real-world cases observed in the codebase: decl name on the same line,
decl keyword with the name on the **next** line, `private`, `noncomputable def`,
and a `@[simp]` attribute line that must NOT be treated as a decl.

```lean
theorem foo_same_line (x : Nat) : x = x := rfl

@[simp]
theorem bar_after_attr : True := trivial

private theorem baz_private : True := trivial

noncomputable def myDef : Nat := 0

theorem
    name_on_next_line : True := trivial

@[simp]
theorem
    combo_name : True := trivial

lemma qux_lemma : True := trivial

-- definition_like_word should not be parsed as a decl
```

- [ ] **Step 2: Write the failing test** (append a class)

```python
class TestDeclExtraction(unittest.TestCase):
    def test_extracts_decls_with_lines_and_visibility(self):
        fixture = "tests/review/fixtures/Sample.lean"
        out = json.loads(run("resolve", fixture).stdout)[0]
        names = {d["name"]: d for d in out["decls"]}
        self.assertIn("foo_same_line", names)
        self.assertIn("bar_after_attr", names)
        self.assertIn("name_on_next_line", names)      # name on the next line
        self.assertIn("combo_name", names)             # attr + bare kw + next-line name
        self.assertIn("myDef", names)                  # name follows `noncomputable def`
        self.assertIn("qux_lemma", names)
        self.assertTrue(names["baz_private"]["private"])
        self.assertFalse(names["foo_same_line"]["private"])
        self.assertFalse(names["combo_name"]["private"])
        # negative: a comment mentioning "definition_like_word" is not a decl
        self.assertNotIn("definition_like_word", names)
        # line numbers are 1-based and point at the decl KEYWORD line (not the name line)
        self.assertEqual(names["foo_same_line"]["line"], 1)
        self.assertEqual(names["name_on_next_line"]["line"], 10)  # `theorem` keyword line
```

- [ ] **Step 3: Run the test to verify it fails**

Run: `uv run python -m unittest tests.review.test_worklist.TestDeclExtraction -v`
Expected: FAIL (`decls` is empty).

- [ ] **Step 4: Implement decl extraction**

In `resolve`, when the file exists on disk, scan lines for declarations using an
**anchored** keyword regex so substrings like `definition_like_word` never match:

```python
KW = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?"
                r"(?:(?P<vis>private|protected)\s+)?"
                r"(?:noncomputable\s+|scoped\s+|unsafe\s+)*"
                r"(?:theorem|lemma|def|abbrev|instance)\b"
                r"\s*(?P<name>[^\s:({\[]+)?")
IDENT = re.compile(r"^\s*(?P<name>[A-Za-z_][^\s:({\[]*)")
```

For each line, if `KW` matches: the name is the `name` group if present; otherwise
the keyword is alone on its line, so read forward to the next non-blank line and
take its leading identifier via `IDENT`. Record `{"name", "line", "private":
bool}` where `line` is the 1-based line of the **keyword** (not the name line) and
`private` is true iff the `vis` group is `private`. Skip pure attribute lines
(`@[...]` with no keyword) — they won't match `KW`. If the file does not exist,
leave `decls` empty (keeps Task 2's pure-path tests valid).

- [ ] **Step 5: Run the test to verify it passes**

Run: `uv run python -m unittest tests.review.test_worklist -v`
Expected: all PASS.

- [ ] **Step 6: Sanity-check on a real file**

Run: `uv run review/worklist.py resolve HansenEconometrics/Chapter10Bootstrap/HigherOrder.lean | uv run python -c "import json,sys; d=json.load(sys.stdin)[0]; print(len(d['decls']),'decls'); print(d['decls'][0])"`
Expected: a plausible decl count (≳ 15) and a first decl named `secondOrder_scaled_probability_transfer` at line 24.

- [ ] **Step 7: Commit**

```bash
git add review/worklist.py tests/review/fixtures/Sample.lean tests/review/test_worklist.py
git commit -m "Add Lean declaration extraction to worklist resolver"
```

---

## Task 4: Rubric asset

**Files:**
- Create: `review/rubric.md`
- Modify: `tests/review/test_worklist.py` (add a lightweight asset-presence test)

- [ ] **Step 1: Write the failing test** (append a class)

```python
class TestRubricAsset(unittest.TestCase):
    def test_rubric_covers_all_dimensions_and_severities(self):
        text = (REPO / "review" / "rubric.md").read_text()
        for dim in ["redundancy", "hygiene", "faithfulness", "proof-quality"]:
            self.assertIn(dim, text)
        for sev in ["blocker", "major", "minor", "nit"]:
            self.assertIn(sev, text)
        self.assertIn("AGENTS.md", text)
```

- [ ] **Step 2: Run to verify it fails**

Run: `uv run python -m unittest tests.review.test_worklist.TestRubricAsset -v`
Expected: FAIL (file missing).

- [ ] **Step 3: Write `review/rubric.md`**

One section per dimension. Each section: the AGENTS.md rule(s) it operationalizes
(quote the rule), what concretely counts as a finding, what does NOT (to suppress
false positives), and how to assign severity. Use the exact dimension keys
(`redundancy`, `hygiene`, `faithfulness`, `proof-quality`) and severity keys
(`blocker`, `major`, `minor`, `nit`) so they match the schema. Map:
- redundancy → AGENTS.md §1 reuse-Mathlib-first, §2 reuse-repo-theorems, "one canonical public API", "no parallel theorem stacks".
- hygiene → "keep same-file scaffolding private", "one canonical public API", number-in-docstring, docstrings, `@[simp]`, citeable/short names.
- faithfulness → statement matches the Hansen excerpt's hypotheses/conclusion; not vacuous/weakened.
- proof-quality → golfable length; trivial/cheating statements.

Include a short "severity rubric" table (blocker = wrong/unfaithful math or a public-API duplication; major = real redundancy/hygiene break with downstream impact; minor = local cleanup; nit = cosmetic).

- [ ] **Step 4: Run to verify it passes**

Run: `uv run python -m unittest tests.review.test_worklist.TestRubricAsset -v`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add review/rubric.md tests/review/test_worklist.py
git commit -m "Add review rubric mapping dimensions to AGENTS.md rules"
```

---

## Task 5: Prompt templates (reviewer, verifier, fixer)

**Files:**
- Create: `review/prompts/reviewer.md`, `review/prompts/verifier.md`, `review/prompts/fixer.md`
- Modify: `tests/review/test_worklist.py`

- [ ] **Step 1: Write the failing test** (append a class)

```python
class TestPromptAssets(unittest.TestCase):
    P = REPO / "review" / "prompts"
    def test_reviewer_prompt(self):
        t = (self.P / "reviewer.md").read_text()
        self.assertIn("finding-schema.json", t)   # must emit schema-valid findings
        self.assertIn("rg", t)                     # fallback tool named
    def test_verifier_is_refute_biased(self):
        t = (self.P / "verifier.md").read_text().lower()
        self.assertIn("refute", t)
        self.assertIn("uncertain", t)              # default-to-refuted-if-uncertain
    def test_fixer_is_mechanical_only(self):
        t = (self.P / "fixer.md").read_text().lower()
        self.assertIn("mechanical", t)
        self.assertIn("lake build", t)             # must rebuild green
```

- [ ] **Step 2: Run to verify it fails**

Run: `uv run python -m unittest tests.review.test_worklist.TestPromptAssets -v`
Expected: FAIL.

- [ ] **Step 3: Write `review/prompts/reviewer.md`**

A template with placeholders (`{{file}}`, `{{dimension}}`, `{{rubric_section}}`,
`{{excerpt_path}}`, `{{inventory_path}}`, `{{decls_json}}`). Instructs: read the
target file and the rubric section for this dimension; use `leansearch`/`loogle`/
`lean_goal` if available, else `rg`; for faithfulness, open the chapter excerpt
and inventory rows and quote the matching passage; output a JSON array of findings
conforming to `finding-schema.json` (compute `id = sha1(file:line:decl:dimension)`);
report nothing speculative — every finding needs concrete evidence.

- [ ] **Step 4: Write `review/prompts/verifier.md`**

Refute-biased skeptic template (placeholder `{{finding_json}}`). Job: try to
**refute** the finding; **default to refuted if uncertain**. Per-dimension proof
burden from the spec: redundancy must name the exact duplicated decl (loogle/
leansearch/`rg`); hygiene must show zero out-of-file usages via `rg`; faithfulness
must quote the excerpt and compare hypotheses (faithful-or-stronger ⇒ refuted);
proof-quality must confirm genuine triviality/golfability. Output: `{verdict:
"confirmed"|"refuted", reason, evidence}`.

- [ ] **Step 5: Write `review/prompts/fixer.md`**

Mechanical-fix-only template. Allowed edits ONLY: make `private`, add docstring,
add `@[simp]`, in-file rename; and removal of a zero-external-usage duplicate.
Forbidden: anything that can cascade. Must run `lake build` and only keep the
change if green; otherwise revert and downgrade the finding to report-only. Works
inside a git worktree.

- [ ] **Step 6: Run to verify it passes**

Run: `uv run python -m unittest tests.review.test_worklist.TestPromptAssets -v`
Expected: PASS.

- [ ] **Step 7: Commit**

```bash
git add review/prompts/ tests/review/test_worklist.py
git commit -m "Add reviewer, verifier, and fixer prompt templates"
```

---

## Task 6: Worklist + README docs and self-containment checklist

**Files:**
- Create: `review/worklist.md`, `review/README.md`, `review/reports/.gitkeep`
- Modify: `tests/review/test_worklist.py`

- [ ] **Step 1: Write the failing test** (append a class)

```python
class TestDocsAssets(unittest.TestCase):
    def test_readme_self_containment_checklist(self):
        t = (REPO / "review" / "README.md").read_text()
        for token in ["rubric.md", "finding-schema.json", "worklist.py",
                      "prompts/reviewer.md", "review/reports", "Codex"]:
            self.assertIn(token, t)
    def test_reports_dir_exists(self):
        self.assertTrue((REPO / "review" / "reports").is_dir())
```

- [ ] **Step 2: Run to verify it fails**

Run: `uv run python -m unittest tests.review.test_worklist.TestDocsAssets -v`
Expected: FAIL.

- [ ] **Step 3: Write the docs**

`review/worklist.md`: the human-readable procedure that `worklist.py` automates
(how a file maps to chapter/excerpt/inventory, the padded-vs-unpadded rule, how
decls are listed), plus a note that `worklist.py resolve <files...>` is the
executable form.

`review/README.md`: how to run the harness on (a) Claude Code — invoke
`scripts/review.workflow.js` via the Workflow tool with a file list as `args`;
(b) Codex/other — call `uv run review/worklist.py resolve ...`, feed each
file/dimension the matching prompt template + rubric section, run your own
verify pass, validate output with `worklist.py --validate-schema`, write to
`review/reports/`; (c) manually. End with a **self-containment checklist**
naming: `rubric.md`, `finding-schema.json`, `worklist.py`, `prompts/reviewer.md`,
`prompts/verifier.md`, `prompts/fixer.md`, `review/reports`, tool prerequisites +
`rg` fallback. Explicitly mention Codex.

Create `review/reports/.gitkeep`.

- [ ] **Step 4: Run to verify it passes**

Run: `uv run python -m unittest tests.review.test_worklist -v`
Expected: all PASS.

- [ ] **Step 5: Commit**

```bash
git add review/worklist.md review/README.md review/reports/.gitkeep tests/review/test_worklist.py
git commit -m "Add worklist/README docs and reports output dir"
```

---

## Task 7: Layer-2 Claude Code Workflow orchestrator

**Files:**
- Create: `scripts/review.workflow.js`
- Modify: `tests/review/test_worklist.py`

> Note: the workflow runs inside the Claude Code `Workflow` tool, not under
> `node`, so it has no standalone unit test. We validate its *structure* (it
> references the right assets and primitives) with a text test, and validate its
> *behavior* via the Task 8 pilot run.

- [ ] **Step 1: Write the failing structure test** (append a class)

```python
class TestWorkflowScript(unittest.TestCase):
    def test_workflow_wires_assets_and_pipeline(self):
        t = (REPO / "scripts" / "review.workflow.js").read_text()
        self.assertIn("export const meta", t)
        for asset in ["review/worklist.py", "review/rubric.md",
                      "review/prompts/reviewer.md", "review/prompts/verifier.md",
                      "finding-schema.json"]:
            self.assertIn(asset, t)
        for prim in ["pipeline(", "parallel(", "agent("]:
            self.assertIn(prim, t)
        self.assertIn("worktree", t)   # draft-PR fixers run isolated
```

- [ ] **Step 2: Run to verify it fails**

Run: `uv run python -m unittest tests.review.test_worklist.TestWorkflowScript -v`
Expected: FAIL.

- [ ] **Step 3: Write `scripts/review.workflow.js`**

A thin orchestrator implementing the spec pipeline. Required shape:
- `export const meta = {name, description, phases:[{title:'Worklist'},{title:'Review'},{title:'Verify'},{title:'Dedup'},{title:'Report'},{title:'Draft fixes'}]}` (pure literal).
- Read target files from `args` (array of paths; the pilot passes 2). Bash out via an `agent()` or document that resolution is done by `uv run review/worklist.py resolve <files>` — since the workflow can't call uv directly, resolution is performed by the first-phase `agent()` which runs `uv run review/worklist.py resolve ...` and returns the parsed worklist (schema'd).
- Load asset texts (rubric, prompt templates, schema) by instructing the phase-1 agent to read them and pass their contents forward, OR have each reviewer agent read them itself by path. Prefer: each reviewer agent is told the asset paths and reads them — keeps the script thin.
- **Review** (`pipeline`, dimension-level, `files × 4`): each stage-1 agent gets `reviewer.md` filled for (file, dimension) and returns `{findings: [...]}` validated against `finding-schema.json` (use the `schema` option mirroring the JSON schema).
- **Verify** (pipeline stage-2): for each finding, one `agent()` using `verifier.md`; keep only `verdict === "confirmed"`.
- **Dedup** (`parallel` barrier + plain JS): merge by `id`; on collision keep higher severity, union evidence.
- **Report**: build a markdown report grouped by file then dimension, severity-sorted; return it as the workflow result (the caller writes it to `review/reports/<date>-<scope>.md` since the script can't read the clock).
- **Draft fixes**: filter confirmed findings to `mechanical === true`; group per file×dimension; for each group spawn a `fixer.md` agent with `isolation: 'worktree'`; it applies edits, runs `lake build`, keeps only if green.
- Use `log()`/`phase()` for progress; respect a stop budget; drop failed items to `null` and log them.

- [ ] **Step 4: Run to verify the structure test passes**

Run: `uv run python -m unittest tests.review.test_worklist.TestWorkflowScript -v`
Expected: PASS.

- [ ] **Step 5: Full test sweep**

Run: `uv run python -m unittest discover -s tests/review -v`
Expected: all PASS.

- [ ] **Step 6: Commit**

```bash
git add scripts/review.workflow.js tests/review/test_worklist.py
git commit -m "Add Claude Code Workflow orchestrator for review harness"
```

---

## Task 8: Pilot run + tuning (integration / acceptance)

**Files:**
- Produces: `review/reports/2026-06-06-pilot-ch10.md` (or current date)
- Possibly modifies: `review/rubric.md`, `review/prompts/*.md` (tuning)

> This task is run by the human operator (or the orchestrating session), not a
> headless TDD subagent — it requires judgment about finding quality and uses the
> Workflow tool interactively.

- [ ] **Step 1: Dry-resolve the pilot files, then smoke-test the validator separately**

Resolve (inspect the output visually):
`uv run review/worklist.py resolve HansenEconometrics/Chapter10Bootstrap/HigherOrder.lean HansenEconometrics/Chapter10Bootstrap/Quantiles.lean`
Expected: two worklist entries with `chapter: 10`, `excerpt_path: textbook/ch10/ch10_excerpt.txt`, `inventory_path: inventory/ch10-inventory.md`, and non-empty `decls`.

Then a separate validator smoke test on a known-good finding (do NOT pipe the
worklist into it — worklist entries are not findings):
`echo '[]' | uv run review/worklist.py --validate-schema && echo "validator OK"`
Expected: prints `validator OK` (empty finding list is trivially valid).

- [ ] **Step 2: Run the workflow on the two pilot files**

Invoke the `Workflow` tool with `{scriptPath: "scripts/review.workflow.js", args: ["HansenEconometrics/Chapter10Bootstrap/HigherOrder.lean", "HansenEconometrics/Chapter10Bootstrap/Quantiles.lean"]}`.
Expected: a returned markdown report with confirmed findings grouped by file/dimension.

- [ ] **Step 3: Write the report to disk**

Save the returned report to `review/reports/2026-06-06-pilot-ch10.md` (use the actual run date).

- [ ] **Step 4: Spot-check finding quality (acceptance gate)**

Human reads 5–10 confirmed findings and checks: each cites a real rule, has
concrete evidence, and is genuinely actionable (low false-positive rate). Note
any false positives — these indicate prompt/rubric gaps.

- [ ] **Step 5: Tune if needed**

If false positives appear, tighten `review/rubric.md` (the "what does NOT count"
sections) or the `verifier.md` proof burden, then re-run Step 2. Repeat until the
spot-check is clean (max ~3 iterations, then surface to human).

- [ ] **Step 6: Verify one mechanical fix end-to-end**

Confirm at least one `mechanical` confirmed finding produced a green draft commit
in a worktree (or, if none were mechanical in the pilot, document that and
manually apply one to confirm the fixer path builds green). Note: `lake build` on
this repo is slow — budget several minutes for the green check and don't treat a
long build as a failure.

- [ ] **Step 7: Stability check (spec success gate)**

Run the workflow a second time on the same two files with no code changes. Compare
the confirmed `blocker`/`major` finding `id`s across the two runs and record the
overlap in the report (e.g. "run-to-run blocker/major overlap: 9/10"). A large
swing signals an under-specified rubric — tighten and note it. (LLM agents are
nondeterministic, so exact equality is not expected; high overlap is the bar.)

- [ ] **Step 8: Commit the pilot report and any tuning**

```bash
git add review/reports/2026-06-06-pilot-ch10.md review/rubric.md review/prompts/
git commit -m "Add Chapter 10 pilot review report and prompt tuning"
```

---

## Definition of Done

- `uv run python -m unittest discover -s tests/review -v` is green (Tasks 1–7).
- `review/` contains rubric, three prompt templates, schema, testable `worklist.py`, worklist/README docs, and a reports dir.
- `scripts/review.workflow.js` runs end-to-end on the two pilot files and returns a grouped, severity-sorted report.
- The pilot report's confirmed findings pass a human spot-check for low false-positive rate.
- At least one mechanical fix has been shown to flow into a green draft commit.
- `review/README.md`'s self-containment checklist lets a Codex runner reproduce the review using only Layer-1 assets.
