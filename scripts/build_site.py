# /// script
# requires-python = ">=3.11"
# dependencies = ["markdown"]
# ///
"""Build the generated Quarto result pages and dependency-graph data.

The Lean environment is the source of declaration metadata. The chapter
inventories are the source of the curated textbook-to-Lean crosswalk.
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import re
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from urllib.parse import unquote

import markdown


REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_DECLS = REPO_ROOT / "site" / "_generated" / "declarations.json"
DEFAULT_INVENTORY = REPO_ROOT / "inventory"
DEFAULT_RESULTS = REPO_ROOT / "site" / "results"
DEFAULT_GRAPH_PAGE = REPO_ROOT / "site" / "dependencies.qmd"

GITHUB_REPO = "https://github.com/apoorvalal/lean-hansen-econometrics"

CHAPTER_TITLES = {
    2: "Conditional Expectation and Projection",
    3: "The Algebra of Least Squares",
    4: "Least Squares Regression",
    5: "Normal Regression",
    6: "A Review of Large Sample Asymptotics",
    7: "Asymptotic Theory for Least Squares",
    8: "Restricted Estimation",
    9: "Hypothesis Testing",
    10: "Resampling Methods",
    11: "Multivariate Regression",
    12: "Instrumental Variables",
    13: "Generalized Method of Moments",
}

LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")
CODE_RE = re.compile(r"`([A-Za-z_][A-Za-z0-9_'.]*)`")
LINE_RE = re.compile(r"#L(\d+)")
CH2_HEADING_RE = re.compile(r"^###\s+(T2\.\d+(?:\.\d+)*)\s*(.*)$")
MATH_RE = re.compile(r"(?s)(?<!\\)(\${1,2})(.+?)(?<!\\)\1")


@dataclass
class ResultGroup:
    label: str
    statement: str
    declarations: list[dict] = field(default_factory=list)
    linked_count: int = 0


def slug(text: str) -> str:
    base = re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")
    if base:
        return base
    return hashlib.sha1(text.encode()).hexdigest()[:10]


def declaration_id(name: str) -> str:
    return "decl-" + slug(name)


def split_table_row(line: str) -> list[str]:
    """Split a Markdown table row while preserving escaped pipes."""
    cells: list[str] = []
    current: list[str] = []
    escaped = False
    for char in line.strip():
        if escaped:
            current.append(char)
            escaped = False
        elif char == "\\":
            current.append(char)
            escaped = True
        elif char == "|":
            cells.append("".join(current).strip())
            current = []
        else:
            current.append(char)
    cells.append("".join(current).strip())
    if cells and not cells[0]:
        cells = cells[1:]
    if cells and not cells[-1]:
        cells = cells[:-1]
    return cells


class DeclarationIndex:
    def __init__(self, records: list[dict]) -> None:
        self.records = records
        self.by_name = {record["name"]: record for record in records}
        self.by_file_leaf: dict[tuple[str, str], list[dict]] = defaultdict(list)
        self.by_leaf: dict[str, list[dict]] = defaultdict(list)
        self.by_file: dict[str, list[dict]] = defaultdict(list)
        for record in records:
            leaf = record["name"].split(".")[-1]
            self.by_file_leaf[(record["file"], leaf)].append(record)
            self.by_leaf[leaf].append(record)
            self.by_file[record["file"]].append(record)

    def resolve_name(self, name: str, file: str | None = None) -> dict | None:
        clean = name.strip().strip("`")
        if clean in self.by_name:
            return self.by_name[clean]
        leaf = clean.split(".")[-1]
        if file:
            matches = self.by_file_leaf.get((file, leaf), [])
            if len(matches) == 1:
                return matches[0]
        matches = self.by_leaf.get(leaf, [])
        if len(matches) == 1:
            return matches[0]
        return None

    def resolve_link(self, label: str, target: str) -> dict | None:
        path = unquote(target.split("#", 1)[0])
        while path.startswith("../"):
            path = path[3:]
        if not path.startswith("HansenEconometrics/") or not path.endswith(".lean"):
            return None
        label_name = label.strip().strip("`")
        exact = self.resolve_name(label_name, path)
        if exact:
            return exact
        line_match = LINE_RE.search(target)
        if not line_match:
            return None
        line = int(line_match.group(1))
        candidates = self.by_file.get(path, [])
        if not candidates:
            return None
        exact_line = [record for record in candidates if record["line"] == line]
        if exact_line:
            return sorted(exact_line, key=lambda record: record["kind"] != "theorem")[0]
        nearest = min(candidates, key=lambda record: abs(record["line"] - line))
        if abs(nearest["line"] - line) <= 3:
            return nearest
        return None


def declarations_from_cell(cell: str, index: DeclarationIndex) -> list[dict]:
    found: list[dict] = []
    seen: set[str] = set()
    linked_spans: list[tuple[int, int]] = []
    for match in LINK_RE.finditer(cell):
        linked_spans.append(match.span())
        record = index.resolve_link(match.group(1), match.group(2))
        if record and record["name"] not in seen:
            found.append(record)
            seen.add(record["name"])
    for match in CODE_RE.finditer(cell):
        if any(start <= match.start() < end for start, end in linked_spans):
            continue
        record = index.resolve_name(match.group(1))
        if record and record["name"] not in seen:
            found.append(record)
            seen.add(record["name"])
    return found


def endpoint_score(record: dict, label: str) -> tuple[int, int, int]:
    """Rank crosswalk links for the compact result view.

    The inventory keeps the complete supporting surface. The site selects the
    declarations whose names or docstrings most directly identify the labeled
    textbook result.
    """
    doc = (record.get("docstring") or "").lower()
    name = record["name"].lower()
    normalized_label = re.sub(r"\s+", " ", label.lower()).strip()
    score = 0
    if normalized_label and normalized_label in doc:
        score += 120
    number = re.search(r"(theorem|proposition|lemma|corollary|equation)\s+(\d+)\.(\d+)", normalized_label)
    if number:
        kind, chapter, result = number.groups()
        compact = f"{kind}{chapter}_{result}"
        if compact in re.sub(r"[^a-z0-9_]+", "", name):
            score += 100
        if f"{kind} {chapter}.{result}" in doc:
            score += 80
        if f"({chapter}.{result})" in doc:
            score += 30
    if doc.startswith("**hansen") or doc.startswith("hansen"):
        score += 25
    if "canonical" in doc or "textbook-facing" in doc:
        score += 18
    if record["kind"] == "theorem":
        score += 10
    if "orzero" in name:
        score += 5
    if "generic" in doc or "support" in doc or "bridge" in doc:
        score -= 8
    if "star" in name:
        score -= 2
    return score, -len(record["name"]), -record["line"]


def compact_group(group: ResultGroup, limit: int = 6) -> ResultGroup:
    group.linked_count = len(group.declarations)
    if len(group.declarations) > limit:
        group.declarations = sorted(
            group.declarations,
            key=lambda record: endpoint_score(record, group.label),
            reverse=True,
        )[:limit]
    return group


def parse_crosswalk_table(text: str, index: DeclarationIndex) -> list[ResultGroup]:
    lines = text.splitlines()
    start = None
    width = 0
    for position, line in enumerate(lines):
        if line.startswith("|") and "Textbook result" in line and "Lean" in line:
            start = position + 2
            width = len(split_table_row(line))
    if start is None:
        return []
    groups: list[ResultGroup] = []
    for line in lines[start:]:
        if not line.startswith("|"):
            if groups:
                break
            continue
        cells = split_table_row(line)
        if len(cells) < 2 or len(cells) != width:
            continue
        label = cells[0].strip()
        if not label or set(label) <= {"-", ":", " "}:
            continue
        statement = cells[1].strip() if len(cells) > 2 else ""
        lean_cell = cells[-1]
        groups.append(
            compact_group(ResultGroup(
                label=label,
                statement=statement,
                declarations=declarations_from_cell(lean_cell, index),
            ))
        )
    return groups


def parse_chapter_two(text: str, index: DeclarationIndex) -> list[ResultGroup]:
    lines = text.splitlines()
    groups: list[ResultGroup] = []
    current: tuple[str, str, list[str]] | None = None
    for line in lines:
        match = CH2_HEADING_RE.match(line)
        if match:
            if current:
                groups.append(chapter_two_group(*current, index=index))
            label = match.group(1)
            title = match.group(2).strip()
            current = (f"{label} {title}".strip(), "", [])
            continue
        if current and line.startswith("### "):
            groups.append(chapter_two_group(*current, index=index))
            current = None
            continue
        if current:
            label, statement, body = current
            body.append(line)
            if line.startswith("|"):
                cells = split_table_row(line)
                if cells and cells[0] and "LaTeX" not in cells[0] and not cells[0].startswith("---"):
                    statement = cells[0]
            current = (label, statement, body)
    if current:
        groups.append(chapter_two_group(*current, index=index))
    return groups


def chapter_two_group(
    label: str,
    statement: str,
    body: list[str],
    index: DeclarationIndex,
) -> ResultGroup:
    declarations: list[dict] = []
    seen: set[str] = set()
    body_text = "\n".join(body)
    for match in LINK_RE.finditer(body_text):
        record = index.resolve_link(match.group(1), match.group(2))
        if record and record["name"] not in seen:
            declarations.append(record)
            seen.add(record["name"])
    return compact_group(
        ResultGroup(label=label, statement=statement, declarations=declarations)
    )


def parse_inventory(chapter: int, path: Path, index: DeclarationIndex) -> list[ResultGroup]:
    text = path.read_text()
    if chapter == 2:
        return parse_chapter_two(text, index)
    return parse_crosswalk_table(text, index)


def inline_markdown(text: str) -> str:
    if not text:
        return ""
    text = MATH_RE.sub(
        lambda match: (
            match.group(1)
            + match.group(2).replace("<", r"\lt ").replace(">", r"\gt ")
            + match.group(1)
        ),
        text,
    )
    rendered = markdown.markdown(text, extensions=["sane_lists"])
    return rendered


def source_url(record: dict) -> str:
    return f"{GITHUB_REPO}/blob/main/{record['file']}#L{record['line']}"


def render_declaration(record: dict) -> str:
    doc = inline_markdown(record.get("docstring") or "No plain-language docstring is available.")
    dependencies = record.get("refs") or []
    dependency_html = ""
    if dependencies:
        items = "".join(f"<li><code>{html.escape(name)}</code></li>" for name in dependencies)
        dependency_html = (
            '<details class="dependency-list"><summary>Direct statement dependencies '
            f"({len(dependencies)})</summary><ul>{items}</ul></details>"
        )
    return f"""
<details class="lean-declaration" id="{declaration_id(record['name'])}">
<summary><span class="declaration-kind">{html.escape(record['kind'])}</span> <code>{html.escape(record['name'])}</code></summary>
<div class="declaration-body">
<div class="declaration-doc">{doc}</div>
<details class="formal-statement"><summary>Formal statement</summary>
<pre><code class="language-lean">{html.escape(record['signature'])}</code></pre>
</details>
{dependency_html}
<p class="declaration-meta"><a href="{source_url(record)}">{html.escape(record['file'])}:{record['line']}</a></p>
</div>
</details>""".strip()


def render_result_group(group: ResultGroup, open_by_default: bool = False) -> str:
    statement = inline_markdown(group.statement) if group.statement else ""
    statement_block = f'<div class="textbook-statement">{statement}</div>' if statement else ""
    if group.declarations:
        declarations = "\n".join(render_declaration(record) for record in group.declarations)
    else:
        declarations = (
            '<p class="result-gap">The canonical crosswalk does not name a compiled Lean endpoint. '
            "See the chapter inventory for the current qualification.</p>"
        )
    endpoint_label = "endpoint" if len(group.declarations) == 1 else "endpoints"
    if group.linked_count > len(group.declarations):
        count_text = f"{len(group.declarations)} of {group.linked_count} linked {endpoint_label}"
    else:
        count_text = f"{len(group.declarations)} {endpoint_label}"
    open_attr = " open" if open_by_default else ""
    return f"""
<details class="result-group" id="{slug(group.label)}"{open_attr}>
<summary><span>{html.escape(group.label)}</span><span class="result-count">{count_text}</span></summary>
<div class="result-body">
{statement_block}
{declarations}
</div>
</details>""".strip()


def render_chapter_page(chapter: int, groups: list[ResultGroup], inventory_path: Path) -> str:
    title = CHAPTER_TITLES[chapter]
    endpoint_count = sum(len(group.declarations) for group in groups)
    inventory_url = f"{GITHUB_REPO}/blob/main/{inventory_path.as_posix()}"
    body = "\n\n".join(
        render_result_group(group, open_by_default=position == 0)
        for position, group in enumerate(groups)
    )
    return f"""---
title: "Chapter {chapter}: {title}"
description: "Foldable textbook-to-Lean result crosswalk for Chapter {chapter}."
---

This page is generated from the [canonical Chapter {chapter} inventory]({inventory_url}) and the compiled Lean environment. It contains {len(groups)} textbook result groups and {endpoint_count} selected Lean endpoints. When an inventory row links a large proof surface, this page shows at most six theorem-facing endpoints. The inventory remains the source of truth for all supporting links, qualifications, and open gaps.

<div class="results-toolbar" role="group" aria-label="Result display controls">
<button type="button" data-results-action="expand">Expand all results</button>
<button type="button" data-results-action="collapse">Collapse all results</button>
</div>

<div class="result-groups">
{body}
</div>
"""


def render_results_index(chapter_groups: dict[int, list[ResultGroup]]) -> str:
    rows = []
    total_groups = 0
    total_endpoints = 0
    for chapter, groups in chapter_groups.items():
        endpoints = sum(len(group.declarations) for group in groups)
        gaps = sum(not group.declarations for group in groups)
        total_groups += len(groups)
        total_endpoints += endpoints
        rows.append(
            f"| [Chapter {chapter}: {CHAPTER_TITLES[chapter]}](chapter{chapter}.qmd) "
            f"| {len(groups)} | {endpoints} | {gaps} |"
        )
    table = "\n".join(rows)
    return f"""---
title: "Important results"
---

The chapter inventories define the important textbook results. These generated pages place the inventory summary first and keep each Lean endpoint, formal statement, and direct statement-dependency list foldable.

The current generated view contains {total_groups} textbook result groups and {total_endpoints} selected Lean endpoints.

| Chapter | Result groups | Selected endpoints | Groups without a canonical link |
| --- | ---: | ---: | ---: |
{table}

Use the [dependency graph](../dependencies.qmd) to see how the linked results depend on one another and on supporting project declarations.
"""


def graph_payload(
    records: list[dict],
    chapter_groups: dict[int, list[ResultGroup]],
) -> dict:
    by_name = {record["name"]: record for record in records}
    important_owner: dict[str, int] = {}
    for chapter, groups in chapter_groups.items():
        for group in groups:
            for record in group.declarations:
                important_owner.setdefault(record["name"], chapter)

    included = set(important_owner)
    for name in list(included):
        record = by_name[name]
        included.update(ref for ref in record.get("refs", []) if ref in by_name)

    selected = sorted((by_name[name] for name in included), key=lambda item: item["name"])
    node_index = {record["name"]: position for position, record in enumerate(selected)}
    nodes = []
    for record in selected:
        owner = important_owner.get(record["name"])
        chapter = owner if owner is not None else record.get("chapter")
        if owner is not None:
            page = f"results/chapter{owner}.html#{declaration_id(record['name'])}"
        else:
            page = source_url(record)
        nodes.append(
            {
                "name": record["name"],
                "short": record["name"].split(".")[-1],
                "kind": record["kind"],
                "chapter": chapter,
                "module": record["module"],
                "important": owner is not None,
                "page": page,
                "doc": (record.get("docstring") or "").replace("\n", " ")[:240],
            }
        )
    edges: list[list[int]] = []
    for dependent in selected:
        dependent_index = node_index[dependent["name"]]
        for dependency in dependent.get("refs", []):
            dependency_index = node_index.get(dependency)
            if dependency_index is not None:
                edges.append([dependency_index, dependent_index])
    return {
        "nodes": nodes,
        "edges": edges,
        "chapters": sorted(CHAPTER_TITLES),
    }


def render_graph_page(payload: dict) -> str:
    data = json.dumps(payload, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    return f"""---
title: "Dependency graph"
description: "Interactive statement-dependency graph for the important Hansen results."
include-after-body:
  - text: |
      <script src="assets/vendor/d3.v7.min.js"></script>
      <script src="assets/dependency-graph.js"></script>
---

Arrows point from a prerequisite declaration to the result that uses it in its formal statement. This follows the CausalForge and LeanBlueprint convention. The overview aggregates links by textbook chapter. Select a chapter to inspect its important endpoints and their direct project dependencies.

<div id="dependency-graph" class="dependency-graph">
<div class="graph-toolbar">
<button type="button" id="graph-overview">Chapter overview</button>
<label for="graph-chapter">Chapter</label>
<select id="graph-chapter"><option value="">Overview</option></select>
<button type="button" id="graph-reset">Reset view</button>
<span id="graph-status" role="status"></span>
</div>
<div class="graph-legend" aria-label="Graph legend">
<span class="legend-important">Important result</span>
<span class="legend-supporting">Direct dependency</span>
<span class="legend-arrow">Arrow: prerequisite to result</span>
<span>Zoom in or point at a node to show more labels.</span>
</div>
<svg id="graph-canvas" width="100%" height="680" role="img" aria-label="Lean declaration dependency graph"></svg>
</div>

<script id="dependency-data" type="application/json">{data}</script>
"""


def build(
    decls_path: Path,
    inventory_dir: Path,
    results_dir: Path,
    graph_page: Path,
) -> dict[int, list[ResultGroup]]:
    records = json.loads(decls_path.read_text())
    index = DeclarationIndex(records)
    results_dir.mkdir(parents=True, exist_ok=True)
    chapter_groups: dict[int, list[ResultGroup]] = {}
    for chapter in CHAPTER_TITLES:
        inventory_path = inventory_dir / f"ch{chapter}-inventory.md"
        groups = parse_inventory(chapter, inventory_path, index)
        chapter_groups[chapter] = groups
        page = render_chapter_page(
            chapter,
            groups,
            inventory_path.relative_to(REPO_ROOT),
        )
        (results_dir / f"chapter{chapter}.qmd").write_text(page)
    (results_dir / "index.qmd").write_text(render_results_index(chapter_groups))
    graph_page.write_text(render_graph_page(graph_payload(records, chapter_groups)))
    return chapter_groups


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--decls", type=Path, default=DEFAULT_DECLS)
    parser.add_argument("--inventory", type=Path, default=DEFAULT_INVENTORY)
    parser.add_argument("--results", type=Path, default=DEFAULT_RESULTS)
    parser.add_argument("--graph-page", type=Path, default=DEFAULT_GRAPH_PAGE)
    args = parser.parse_args()
    groups = build(args.decls, args.inventory, args.results, args.graph_page)
    result_count = sum(len(chapter) for chapter in groups.values())
    endpoint_count = sum(
        len(group.declarations)
        for chapter in groups.values()
        for group in chapter
    )
    print(
        f"Generated {result_count} result groups with {endpoint_count} linked endpoints"
    )


if __name__ == "__main__":
    main()
