# Chapter 21 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch21_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 21.1 | Theorem 21.1 Assume that treatment is assigned as D = 1{X ≥ c}. Suppose that m0(x) and m1(x) are continuous at x = c. Then θ = m (c+) − m (c−). |  |
| Theorem 21.2 | Theorem 21.2 Suppose that m0(x) and m1(x) are continuous at x = c, p(x) is discontinuous at x = c, and D is independent of θ for X near c. Then θ = m (c+) − m (c−) p (c+) − p (c−) . (21.6) |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
