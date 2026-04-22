# Chapter 17 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch17_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 17.1 | Theorem 17.1 The fixed effects estimator ofβ algebraically equals the dummy variable estimator of β. The two estimators have the same residuals. |  |
| Theorem 17.2 | Theorem 17.2 Under Assumption 17.2, as N → ∞, p N (ˆβfe − β ) − → d N ( 0,V β ) where V β = Q −1 T ΩT Q −1 T and ΩT = E [ ˙X ′ i εi ε′ i ˙X i ] .This asymptotic distribution is derived as the number of individuals N diverges to infinity while the time number of time periods T is held fixed. Therefore the normalization is p N rather than pn (though either could be used sinceT is fixed). This approximation is appropriate for the context of a large number of individuals. We could alternatively derive an approximation for the case where both N and T diverge to infinity but this would not be a stronger result. One way of thinking about this is that Theorem 17.2 does not require T to be large. |  |
| Theorem 17.3 | Theorem 17.3 Under Assumption 17.3, as N → ∞, p N (ˆβfe − β ) − → d N ( 0,V β ) where V β = Q −1 T ΩT Q −1 T and ΩT = E [ ˙X ′ i εi ε′ i ˙X i ] .We now prove Theorem 17.3. The assumptions imply that the variables ( ˙X i , εi ) are i.i.d. across i and have finite fourth moments. By the WLLN 1 N N∑ i =1 ˙X ′ i ˙X i − →p E [ ˙X ′ i ˙X i ] = QT . |  |
| Theorem 17.4 | Theorem 17.4 Under Assumption 17.4, as N → ∞, p N (ˆβ2sls − β ) − → d N ( 0,V β ) where V β = ( Q ′ Z X Ω−1 Z ZQ Z X )−1 ( Q ′ Z X Ω−1 Z Z ΩZ εΩ−1 Z ZQ Z X ) ( Q ′ Z X Ω−1 Z ZQ Z X )−1 ΩZ ε = E [ ˙Z ′ i εi ε′ i ˙Z i ] . |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
