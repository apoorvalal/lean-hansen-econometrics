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


if __name__ == "__main__":
    unittest.main()
