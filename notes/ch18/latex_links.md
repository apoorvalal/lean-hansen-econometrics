# Chapter 18 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch18_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 18.1 | Theorem 18.1 Suppose the following conditions hold: 1. Yi t = θDi t + X ′ i tβ + ui + vt + εi t. 2. E [ ¨Zi t ¨Z ′ i t ] > 0. 3. E[Xi tεi s] = 0 for all t and s. 4. Conditional on Xi 1, Xi 2,..., Xi T the random variables Di t and εi s are statistically independent for all t and s. Then the coefficientθ in (18.5) equals the average causal effect forD on Y conditional on X . Condition 1 states that the outcome equals the specified linear regression model which is additively separable in the observables, individual effect, and time effect. Condition 2 states that the two-way within transformed regressors have a non-singular design matrix. |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
