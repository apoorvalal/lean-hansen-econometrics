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

if __name__ == "__main__":
    unittest.main()
