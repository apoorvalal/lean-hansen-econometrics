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

## Metadata

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

    if out_dir.exists():
        shutil.rmtree(out_dir)
    out_dir.mkdir(parents=True)

    env = Environment(loader=BaseLoader(), keep_trailing_newline=True)
    stub_t = env.from_string(STUB_TEMPLATE)
    chapter_t = env.from_string(CHAPTER_INDEX_TEMPLATE)
    top_t = env.from_string(TOP_INDEX_TEMPLATE)

    grouped: dict[int | None, list[dict]] = {}
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
