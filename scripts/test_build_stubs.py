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
