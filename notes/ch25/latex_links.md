# Chapter 25 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch25_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 25.1 | Theorem 25.1 Consistency of Logit Estimation. If (1) (Y i , Xi ) are i.i.d.; (2) E ∥X ∥ < ∞; (3) Qlogit > 0; and (4) B is bounded; then ˆβlogit − →p βlogit as n → ∞. |  |
| Theorem 25.2 | Theorem 25.2 Consistency of Probit Estimation. If (1) (Y i , Xi ) are i.i.d.; (2) E ∥X ∥2 < ∞; (3) Qprobit > 0; and (4) B is bounded; then ˆβprobit − →p βprobit as n → ∞. |  |
| Theorem 25.3 | Theorem 25.3 If the conditions of Theorem 25.1 hold plus E ∥X ∥4 < ∞ and βlogit is in the interior of B; then as n → ∞ p n ( ˆβlogit − βlogit ) − → d N ( 0,V logit ) where V logit = Q −1 logitΩlogitQ −1 logit. |  |
| Theorem 25.4 | Theorem 25.4 If the conditions of Theorem 25.2 hold plus E ∥X ∥4 < ∞ and βprobit is in the interior of B; then as n → ∞ p n ( ˆβprobit − βprobit ) − → d N ( 0,V probit ) where V probit = Q −1 probitΩprobitQ −1 probit. |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
