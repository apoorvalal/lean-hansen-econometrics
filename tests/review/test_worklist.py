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
        self.assertIn("severity", r.stderr)

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
        # asymmetric: dir is zero-padded (ch07) but the filename is NOT (ch7_excerpt.txt)
        self.assertEqual(out["excerpt_path"], "textbook/ch07/ch7_excerpt.txt")
        self.assertEqual(out["inventory_path"], "inventory/ch7-inventory.md")    # unpadded

    def test_nested_module_file(self):
        out = self.resolve("HansenEconometrics/Chapter7Asymptotics/Normality.lean")
        self.assertEqual(out["chapter"], 7)

    def test_non_chapter_file_has_null_chapter(self):
        out = self.resolve("HansenEconometrics/ProbabilityUtils.lean")
        self.assertIsNone(out["chapter"])
        self.assertIsNone(out["excerpt_path"])
        self.assertIsNone(out["inventory_path"])

    def test_multiple_files_preserve_order(self):
        r = run("resolve",
                "HansenEconometrics/Chapter10Bootstrap/HigherOrder.lean",
                "HansenEconometrics/ProbabilityUtils.lean")
        self.assertEqual(r.returncode, 0, r.stderr)
        out = json.loads(r.stdout)
        self.assertEqual(len(out), 2)
        self.assertEqual(out[0]["chapter"], 10)
        self.assertIsNone(out[1]["chapter"])


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
        self.assertIn("MyStruct", names)               # structure decls are extracted
        self.assertIn("μ_same_line", names)            # Unicode-initial name (same line)
        # line numbers are 1-based and point at the decl KEYWORD line (not the name line)
        self.assertEqual(names["foo_same_line"]["line"], 1)
        self.assertEqual(names["name_on_next_line"]["line"], 10)  # `theorem` keyword line


class TestRubricAsset(unittest.TestCase):
    def test_rubric_covers_all_dimensions_and_severities(self):
        text = (REPO / "review" / "rubric.md").read_text()
        for dim in ["redundancy", "hygiene", "faithfulness", "proof-quality"]:
            self.assertIn(dim, text)
        for sev in ["blocker", "major", "minor", "nit"]:
            self.assertIn(sev, text)
        self.assertIn("AGENTS.md", text)


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


class TestDocsAssets(unittest.TestCase):
    def test_readme_self_containment_checklist(self):
        t = (REPO / "review" / "README.md").read_text()
        for token in ["rubric.md", "finding-schema.json", "worklist.py",
                      "prompts/reviewer.md", "review/reports", "Codex"]:
            self.assertIn(token, t)
    def test_reports_dir_exists(self):
        self.assertTrue((REPO / "review" / "reports").is_dir())


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


if __name__ == "__main__":
    unittest.main()
