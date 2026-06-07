---
name: review-harness
description: Run the repo's portable adversarial Lean review harness from Codex or another non-Workflow agent. Trigger when asked to use the review harness, review Lean files across redundancy/hygiene/faithfulness/proof-quality dimensions, follow review/README.md section (b), validate findings with review/worklist.py, or write schema-valid reports under review/reports/.
---

# Review Harness

Use this skill for the repo's schema-validated adversarial Lean review harness. This is not the
ordinary `code-review` output format: the harness produces JSON findings that conform to
`review/finding-schema.json`, then writes them under `review/reports/`.

Keep the rules in Layer 1. Do not re-implement review policy in this skill or in a local runner:
read `AGENTS.md`, `review/README.md`, `review/rubric.md`, and the prompt templates for the current
run.

## Preconditions

- Work on a branch that contains both the target Lean files and the `review/` harness.
- If the user names a branch, switch to it before reviewing.
- If the repo lacks `review/worklist.py`, `review/rubric.md`, or the prompt templates, stop and say
  the portable Layer 1 assets are missing.
- Do not run the fixer step unless the user explicitly asks for fixes. The default review pass is
  read-only except for writing report JSON.

Run this deterministic smoke test once per environment or branch before spending review effort:

```bash
uv run review/worklist.py resolve <file>
echo '[]' | uv run review/worklist.py --validate-schema && echo "validator OK"
```

If `uv` fails because the sandbox cannot read its cache, rerun the same `uv run ...` command with
escalation.

## Scope

- Required input: at least one Lean file.
- Dimension values: `redundancy`, `hygiene`, `faithfulness`, `proof-quality`.
- If the user gives no dimension, run all four dimensions.
- If the user gives no report path, write a descriptive file under `review/reports/`.

For multiple files or dimensions, run the same one-file x one-dimension loop and deduplicate
confirmed findings by `id`. Keep the higher severity if duplicate ids appear, and merge useful
evidence.

## One File x One Dimension

1. Resolve metadata:

   ```bash
   uv run review/worklist.py resolve <file>
   ```

   Use the returned `file`, `chapter`, `excerpt_path`, `inventory_path`, and `decls` values.

2. Read the harness instructions and assets:

   - `AGENTS.md` section "Reviewing code with the review harness"
   - `review/README.md` section `(b)`
   - the matching dimension section from `review/rubric.md`
   - `review/prompts/reviewer.md`
   - `review/prompts/verifier.md`
   - the target Lean file in full
   - excerpt and inventory files when the dimension or finding needs them

3. Run the reviewer pass in Codex by filling `review/prompts/reviewer.md`:

   - `{{file}}`: repo-relative Lean file
   - `{{dimension}}`: current dimension
   - `{{rubric_section}}`: matching section from `review/rubric.md`
   - `{{excerpt_path}}` and `{{inventory_path}}`: resolver values, or empty strings
   - `{{decls_json}}`: resolver declaration array as JSON

4. Gather evidence exactly as the prompt requires.

   Prefer Lean LSP/search tools if available. In Codex, they are often unavailable; use `rg` as the
   fallback. If this local `rg` does not support `--include='*.lean'`, use `-g '*.lean'`.

   Dimension-specific evidence burdens:

   - `redundancy`: name the exact Mathlib or repo declaration that duplicates the candidate.
   - `hygiene`: for "should be private", prove zero out-of-file callers with `rg`.
   - `faithfulness`: compare the Lean statement with the excerpt and inventory.
   - `proof-quality`: name the exact tactic or lemma that would close the proof, or refute.

5. Produce a reviewer object:

   ```json
   {"findings": []}
   ```

   Each finding id is:

   ```text
   sha1("<file>:<line>:<decl>:<dimension>")
   ```

   Compute ids with Python/hashlib or an equivalent deterministic method.

6. Run the verifier pass for each reviewer finding by following `review/prompts/verifier.md`.

   The verifier is refute-biased. Keep only findings with:

   ```json
   "verdict": "confirmed"
   ```

   For redundancy findings, also record the required caller check with `rg -l '<decl>' -g '*.lean'`
   or equivalent evidence.

7. Validate only the final findings array, not the wrapper object:

   ```bash
   echo '<confirmed-findings-array>' | uv run review/worklist.py --validate-schema
   ```

   Exit code 0 means valid. If shell quoting is unsafe, write the array to the report file first and
   validate it with:

   ```bash
   uv run review/worklist.py --validate-schema < review/reports/<name>.json
   ```

8. Write the validated findings array to `review/reports/<name>.json`.

   Reports are arrays of finding objects, not `{"findings": [...]}` wrappers.

## Finding Rules

- Every finding must cite a real AGENTS.md rule.
- Do not report speculative findings.
- Apply the rubric's "Does NOT count" filters before verification.
- `mechanical` is `true` only for the fixer whitelist: add `private`, add a docstring, add
  `@[simp]`, in-file rename, or remove a zero-external-usage duplicate.
- Statement changes, proof-body edits, and cross-file edits are not mechanical.
- Thin Hansen-facing wrappers that delegate to an existing theorem are not redundancy findings.
- Public helpers with out-of-file callers are not "should be private" hygiene findings.
- Documented generalizations are not faithfulness findings.
- Undocumented `sorry` belongs under `faithfulness`, not `proof-quality`.

## Final Response

Report:

- branch and smoke-test status
- file and dimension scope
- number of confirmed findings
- report path
- validator status
- whether the fixer step was skipped or run

Do not paste the full report unless the user asks for it.
