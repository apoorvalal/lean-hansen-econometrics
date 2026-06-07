# Worklist Procedure

This document describes the human-readable procedure that `review/worklist.py` automates.
Run `uv run review/worklist.py resolve <files...>` to execute this procedure programmatically.

---

## How a Lean file maps to chapter metadata

Given a repo-relative Lean file path, the harness derives three pieces of metadata:

### 1. Chapter number

The chapter number is extracted from the first occurrence of `Chapter(\d+)` anywhere in the
file path. Examples:

| Path | Chapter |
|---|---|
| `HansenEconometrics/Chapter10Bootstrap/HigherOrder.lean` | 10 |
| `HansenEconometrics/Chapter7Asymptotics.lean` | 7 |
| `HansenEconometrics/ProbabilityUtils.lean` | *(none — null)* |

If no `Chapter<N>` token appears in the path, all three metadata fields are `null`.

### 2. Excerpt path (padded directory, unpadded filename)

The textbook excerpt for chapter `N` lives at:

```
textbook/ch<NN>/ch<N>_excerpt.txt
```

where `<NN>` is **zero-padded to two digits** (e.g. `ch07`, `ch10`) but `<N>` in the
**filename** is **unpadded** (e.g. `ch7_excerpt.txt`, `ch10_excerpt.txt`).

Examples:

| Chapter | Excerpt path |
|---|---|
| 7 | `textbook/ch07/ch7_excerpt.txt` |
| 10 | `textbook/ch10/ch10_excerpt.txt` |

### 3. Inventory path (always unpadded)

The chapter inventory is at:

```
inventory/ch<N>-inventory.md
```

where `<N>` is always **unpadded**:

| Chapter | Inventory path |
|---|---|
| 7 | `inventory/ch7-inventory.md` |
| 10 | `inventory/ch10-inventory.md` |

---

## Declaration listing

For each file the resolver also extracts all top-level declarations. Each declaration entry
contains:

| Field | Description |
|---|---|
| `name` | Declaration name (Unicode-transparent; captures names like `μ_eq_zero`) |
| `line` | 1-based line number of the **keyword** line (e.g. `theorem`, `def`, `lemma`) |
| `private` | `true` if the declaration is prefixed with `private`, else `false` |

Extracted declaration kinds: `theorem`, `lemma`, `def`, `abbrev`, `instance`, `structure`,
`class`, `inductive`.

The extractor handles:
- Attribute annotations before the keyword (e.g. `@[simp]`)
- Modifiers before the keyword (`noncomputable`, `scoped`, `unsafe`)
- Visibility modifiers (`private`, `protected`)
- Names on the same line as the keyword, or on the next non-blank line

---

## Programmatic form

```bash
uv run review/worklist.py resolve \
    HansenEconometrics/Chapter10Bootstrap/HigherOrder.lean \
    HansenEconometrics/ProbabilityUtils.lean
```

Output is a **JSON array**, one object per input file:

```json
[
  {
    "file": "HansenEconometrics/Chapter10Bootstrap/HigherOrder.lean",
    "chapter": 10,
    "excerpt_path": "textbook/ch10/ch10_excerpt.txt",
    "inventory_path": "inventory/ch10-inventory.md",
    "decls": [
      {"name": "higherOrder_theorem", "line": 15, "private": false},
      {"name": "helper_lemma", "line": 42, "private": true}
    ]
  },
  {
    "file": "HansenEconometrics/ProbabilityUtils.lean",
    "chapter": null,
    "excerpt_path": null,
    "inventory_path": null,
    "decls": [...]
  }
]
```

---

## Schema validation

After generating findings, validate them against `review/finding-schema.json` by piping the
JSON array to `worklist.py --validate-schema`:

```bash
cat review/reports/findings.json | uv run review/worklist.py --validate-schema
```

Returns exit code 0 on success, 1 on schema violation (with a descriptive error on stderr),
or 2 on malformed JSON. This replaces `jq`, which is not required.
