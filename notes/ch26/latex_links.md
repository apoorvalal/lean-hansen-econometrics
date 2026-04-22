# Chapter 26 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch26_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 26.1 | Theorem 26.1 Assume the utility of alternative j is U ∗ j = X ′βj + εj and the error vector (ε1, ...,εJ ) has GEV distribution (26.3). Then the response probabilities equal P j (X ) = exp ( X ′βj /τ ) J∑ ℓ=1 exp ( X ′βℓ/τ ) . |  |
| Theorem 26.2 | Theorem 26.2 Assume the utility of alternative j k is U ∗ j k = µj k + εj k and the error vector has distribution function (26.13). Then the response probabilities equal P j k = Pk&#124;j P j where Pk&#124;j = exp ( µj k/τj ) K j∑ m=1 exp ( µj m/τj ) and P j = ( K j∑ m=1 exp ( µj m/τj ) )τj J∑ ℓ=1 ( K j∑ m=1 exp ( µℓm/τℓ ) )τℓ . |  |
| Theorem 26.3 | Theorem 26.3 In the simple multinomial probit and simple conditional multinomial probit models the response probabilities equal P j (W, X ) = ∫ ∞ −∞ ∏ ℓ̸=j Φ ( W ′ ( βj − βℓ ) + ( X j − Xℓ )′ γ + v ) φ(v)d v (26.18) where Φ(v) and φ(v) are the normal distribution and density functions. 9If the random coefficientη is scalar a computationally more efficient method is integration by quadrature. |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
