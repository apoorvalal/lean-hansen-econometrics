from __future__ import annotations

import sys
import unittest
from pathlib import Path


sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

from build_site import (  # noqa: E402
    DeclarationIndex,
    ResultGroup,
    compact_group,
    graph_payload,
    parse_crosswalk_table,
    render_result_group,
)


def record(
    name: str,
    *,
    file: str = "HansenEconometrics/Chapter13GMM.lean",
    line: int = 10,
    chapter: int | None = 13,
    refs: list[str] | None = None,
    docstring: str = "",
) -> dict:
    return {
        "name": name,
        "namespace": name.rsplit(".", 1)[0],
        "kind": "theorem",
        "signature": "True",
        "docstring": docstring,
        "module": file.removesuffix(".lean").replace("/", "."),
        "file": file,
        "line": line,
        "chapter": chapter,
        "refs": refs or [],
        "isPrivate": False,
    }


class DeclarationIndexTests(unittest.TestCase):
    def test_resolves_descriptive_link_by_source_line(self) -> None:
        target = record("HansenEconometrics.gmmResult", line=42)
        index = DeclarationIndex([target])
        resolved = index.resolve_link(
            "Textbook-facing endpoint",
            "../HansenEconometrics/Chapter13GMM.lean#L42",
        )
        self.assertEqual(resolved, target)

    def test_parses_crosswalk_and_caps_large_support_surface(self) -> None:
        records = [
            record(
                f"HansenEconometrics.result{i}",
                line=i + 1,
                docstring=(
                    "Hansen Theorem 13.1 canonical endpoint."
                    if i == 7
                    else "Supporting theorem."
                ),
            )
            for i in range(8)
        ]
        links = ", ".join(
            f"[`result{i}`](../HansenEconometrics/Chapter13GMM.lean#L{i + 1})"
            for i in range(8)
        )
        text = (
            "| Textbook result | Textbook statement | Lean theorem |\n"
            "| --- | --- | --- |\n"
            f"| Theorem 13.1 | Statement | {links} |\n"
        )
        groups = parse_crosswalk_table(text, DeclarationIndex(records))
        self.assertEqual(len(groups), 1)
        self.assertEqual(groups[0].linked_count, 8)
        self.assertEqual(len(groups[0].declarations), 6)
        self.assertIn("HansenEconometrics.result7", {item["name"] for item in groups[0].declarations})


class RenderingTests(unittest.TestCase):
    def test_result_and_formal_statement_are_foldable(self) -> None:
        group = compact_group(
            ResultGroup(
                label="Theorem 13.1",
                statement="A result.",
                declarations=[record("HansenEconometrics.gmmResult")],
            )
        )
        rendered = render_result_group(group)
        self.assertIn('class="result-group"', rendered)
        self.assertIn('class="lean-declaration"', rendered)
        self.assertIn('class="formal-statement"', rendered)

    def test_graph_edges_point_from_dependency_to_dependent(self) -> None:
        dependency = record("HansenEconometrics.base", line=1)
        dependent = record(
            "HansenEconometrics.result",
            line=2,
            refs=[dependency["name"]],
        )
        groups = {
            13: [
                compact_group(
                    ResultGroup(
                        label="Theorem 13.1",
                        statement="",
                        declarations=[dependent],
                    )
                )
            ]
        }
        payload = graph_payload([dependency, dependent], groups)
        names = [node["name"] for node in payload["nodes"]]
        self.assertIn([names.index(dependency["name"]), names.index(dependent["name"])], payload["edges"])


if __name__ == "__main__":
    unittest.main()
