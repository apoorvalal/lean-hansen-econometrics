# Lean Review Harness

Adversarial code-review harness for the Hansen Econometrics Lean 4 formalization.
The harness inspects Lean files across four review dimensions (`redundancy`, `hygiene`,
`faithfulness`, `proof-quality`), produces schema-validated JSON findings, and writes
reports to `review/reports/`.

---

## Quick-start: Which entry point to use?

| Runner | Entry point |
|---|---|
| Claude Code | `scripts/review.workflow.js` (via the Workflow tool) |
| Codex / other agent | `review/worklist.py` + prompt templates (see below) |
| Human / manual | Follow the manual procedure in this file |

---

## (a) Running with Claude Code

The Claude Code orchestrator is `scripts/review.workflow.js`. Invoke it via the Workflow
tool, passing the list of Lean files to review as `args`:

```
Workflow: scripts/review.workflow.js
args: ["HansenEconometrics/Chapter10Bootstrap/HigherOrder.lean"]
```

The workflow calls `worklist.py resolve` internally, fans out reviewer/verifier/fixer passes
per file per dimension, validates output against the schema, and writes reports to
`review/reports/`.

> **Known limitation (draft-fix stage):** the fixer agents run under Workflow `isolation:
> 'worktree'`, which provisions each worktree from the repository's **default branch (`main`)**.
> If you review files that exist only on an unmerged feature branch, the fixer worktree will not
> contain them and every mechanical fix downgrades to report-only. The review/verify/report stages
> are unaffected (they run in the main checkout). To exercise auto-fixes, run on files present on
> `main`, or merge the branch first.

---

## (b) Running with Codex or another agent

Codex and other code-generation agents that have no built-in workflow runner can execute the
harness layer by layer using the CLI tools and prompt templates directly. A Codex runner reuses
**all** of Layer 1 (this directory) and only re-implements the orchestration glue — there is no need
to port `scripts/review.workflow.js`.

**Orchestration shape** (what `scripts/review.workflow.js` does, for you to mirror):

```
resolve worklist (1 call)
  └─ for each file × each of the 4 dimensions:        # the review fan-out
       reviewer agent  -> {findings: [...]}
         └─ for each finding: verifier agent -> keep only verdict=="confirmed"
  dedup confirmed findings by id (keep higher severity, union evidence)
  write report grouped by file -> dimension, severity-sorted, to review/reports/
  (optional) for mechanical==true findings: fixer agent in an isolated checkout + lake build
```

Run reviewers per `(file, dimension)` rather than per declaration — that keeps the agent count at
`files × 4`. Each finding gets its own independent verifier (the false-positive killer).

### Step 1 — Resolve worklist metadata

```bash
uv run --no-project review/worklist.py resolve \
    HansenEconometrics/Chapter10Bootstrap/HigherOrder.lean \
    HansenEconometrics/Chapter7Asymptotics.lean \
    > /tmp/worklist.json
```

Each entry in the output array contains `file`, `chapter`, `excerpt_path`,
`inventory_path`, and `decls`. See `review/worklist.md` for the full schema.

### Step 2 — Run reviewer pass (one file × one dimension)

For each `(file, dimension)` pair, fill in the placeholders in
`review/prompts/reviewer.md` and run the agent:

- `{{file}}` — repo-relative Lean path
- `{{dimension}}` — one of `redundancy | hygiene | faithfulness | proof-quality`
- `{{rubric_section}}` — the matching section from `review/rubric.md`
- `{{excerpt_path}}` / `{{inventory_path}}` — from Step 1 output (empty string if null)
- `{{decls_json}}` — the `decls` array from Step 1 output as a JSON string

The reviewer outputs a JSON object `{"findings": [...]}` whose array elements each conform to
`review/finding-schema.json`. Each finding's `id` is `sha1("<file>:<line>:<decl>:<dimension>")`
(hex digest of the UTF-8 string) — this id is what the dedup step keys on, so compute it
consistently. Validate the array with
`echo '<findings-array>' | uv run --no-project review/worklist.py --validate-schema`.

### Step 3 — Run verifier pass

For each finding array from Step 2, fill in `review/prompts/verifier.md` and run the
agent to adversarially refute each finding. The verifier defaults to refuting when
uncertain. Retain only findings the verifier confirms.

### Step 4 — Run fixer pass (mechanical findings only)

For findings with `"mechanical": true`, fill in `review/prompts/fixer.md` and run the
agent to apply the edit and confirm `lake build` passes green.

### Step 5 — Validate output

Pipe the final findings array to `worklist.py --validate-schema` to confirm every finding
conforms to the schema:

```bash
cat findings.json | uv run --no-project review/worklist.py --validate-schema
```

Exit code 0 = all valid. Exit code 1 = schema violation (see stderr). Exit code 2 =
malformed JSON.

### Step 6 — Write reports

Write the validated findings array to `review/reports/<chapter>-<dimension>.json` (or
any name that keeps reports organized under `review/reports/`).

---

## (c) Running manually

1. For each Lean file you want to review, run `worklist.py resolve` to get chapter,
   excerpt, inventory, and declaration list (see `review/worklist.md`).
2. Open the Lean file and `review/rubric.md`. Work through the rubric section for the
   dimension you are reviewing.
3. For each candidate finding: gather evidence with `rg` (cross-file usage checks,
   duplicate algebra searches), open the excerpt and inventory for faithfulness checks.
4. Apply the "Does NOT count as a finding" filter from the rubric section.
5. Write findings as JSON objects matching `review/finding-schema.json`.
6. Validate with `worklist.py --validate-schema` before saving to `review/reports/`.

---

## Self-containment checklist

All assets required to run the harness without external dependencies:

| Asset | Purpose |
|---|---|
| `review/rubric.md` | Authoritative rules for all four review dimensions; every finding must be grounded here |
| `review/finding-schema.json` | JSON Schema for findings; used by `--validate-schema` and reviewer prompt |
| `review/worklist.py` | CLI: `resolve` subcommand for chapter metadata + decl extraction; `--validate-schema` flag for output validation |
| `review/prompts/reviewer.md` | Reviewer agent prompt template (fill in 6 placeholders) |
| `review/prompts/verifier.md` | Verifier agent prompt — refute-biased, defaults to refuted when uncertain |
| `review/prompts/fixer.md` | Fixer agent prompt — mechanical fixes only, must rebuild green with `lake build` |
| `review/reports` | Output directory for validated finding JSON files |

### Tool prerequisites

| Tool | Required for | Fallback |
|---|---|---|
| `uv` | Running `worklist.py` without a venv | None — `uv` is the required Python runner |
| `lake` | Fixer pass (`lake build` must pass) | None |
| Lean LSP (`leansearch`, `loogle`, `lean_goal`) | Reviewer evidence gathering (preferred) | `rg` (ripgrep) — explicitly listed in `prompts/reviewer.md` as the fallback |
| `rg` (ripgrep) | Cross-file usage checks, duplicate algebra search | Reviewer prompt specifies `rg`; do not substitute `grep -r` |

The harness does **not** require `jq`; `worklist.py --validate-schema` handles JSON
Schema validation in pure Python.

### Codex compatibility

The harness is designed to run in Codex and similar non-interactive agents. Codex should
follow the step-by-step procedure in section (b) above, using `uv run --no-project review/worklist.py`
for metadata resolution and schema validation, and the prompt templates in `review/prompts/`
for each agent pass.
