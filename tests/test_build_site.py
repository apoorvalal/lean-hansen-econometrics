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
    inline_markdown,
    apply_reader_statements,
    parse_crosswalk_table,
    parse_reader_statement_table,
    render_result_group,
    split_table_row,
    validate_statement_coverage,
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
    def test_table_splitter_preserves_pipes_in_literal_content(self) -> None:
        cells = split_table_row(
            r"| Theorem | $\Pr(|T| > c)$ and `|xi|` | "
            r"<code>{x | x > 0}</code> and $$\{z | z > 0\}$$ |"
        )
        self.assertEqual(len(cells), 3)
        self.assertEqual(cells[0], "Theorem")

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

    def test_reader_statement_prefix_preserves_endpoint_crosswalk(self) -> None:
        target = record("HansenEconometrics.result")
        groups = [
            compact_group(
                ResultGroup(
                    label="Theorem 10.9 indexed support",
                    statement="Implementation-specific detail.",
                    declarations=[target],
                )
            )
        ]
        table = (
            "| Result prefix | Reader-facing TeX statement |\n"
            "| --- | --- |\n"
            r"| Theorem 10.9 | $V_n^* \xrightarrow{p^*} V$. |" "\n"
        )
        statements = parse_reader_statement_table(table)
        merged = apply_reader_statements(groups, statements)
        self.assertTrue(merged[0].statement.startswith(r"$V_n^* \xrightarrow{p^*} V$"))
        self.assertEqual(merged[0].declarations, [target])

    def test_later_chapter_statement_coverage_requires_tex(self) -> None:
        with self.assertRaisesRegex(ValueError, "without TeX"):
            validate_statement_coverage(
                {12: [ResultGroup(label="Theorem 12.1", statement="Consistency.")]}
            )


class RenderingTests(unittest.TestCase):
    def test_math_relations_are_not_encoded_as_html_entities(self) -> None:
        rendered = inline_markdown(r"$\mathbb{E}[Y^2] < \infty$ and `x < y`")
        self.assertIn(r"$\mathbb{E}[Y^2] \lt  \infty$", rendered)
        self.assertNotIn(r"$\mathbb{E}[Y^2] &lt; \infty$", rendered)
        self.assertIn("<code>x &lt; y</code>", rendered)

    def test_markdown_does_not_parse_tex_subscripts_as_emphasis(self) -> None:
        rendered = inline_markdown(
            r"$\hat{e}_{\text{full}} = M_{M_1 X_2} M_1 Y$"
        )
        self.assertIn(
            r"$\hat{e}_{\text{full}} = M_{M_1 X_2} M_1 Y$",
            rendered,
        )
        self.assertNotIn("<em>", rendered)

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
