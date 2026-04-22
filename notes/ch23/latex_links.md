# Chapter 23 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch23_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 23.1 | Theorem 23.1 Consistency of NLLS Estimator If Assumption 23.1 holds then ˆθ − →p θ0 as n → ∞. The first three assumptions are standard. Assumption 23.1.4 is not essential but simplifies the proof. |  |
| Theorem 23.2 | Theorem 23.2 Asymptotic Normality of NLLS Estimator If Assumptions 23.1 and 23.2 hold thenpn (ˆθ − θ0 ) − → d N(0,V ) as n → ∞, where V = Q −1ΩQ −1. |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
