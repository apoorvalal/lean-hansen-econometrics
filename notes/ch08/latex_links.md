# Chapter 8 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch8_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 8.1 | Theorem 8.1 The CLS estimator satisfies 1. R ′ ˆβ − c = R ′ ( X ′X )−1 X ′e 2. ˜βcls − β = (( X ′X )−1 X ′ − AX ′ ) e 3. ˜e = ( I − P + X AX ′) e 4. I n − P + X AX ′ is symmetric and idempotent 5. tr ( I n − P + X AX ′) = n − k + q where P = X ( X ′X )−1 X ′ and A = ( X ′X )−1 R ( R ′ ( X ′X )−1 R )−1 R ′ ( X ′X )−1. |  |
| Theorem 8.2 | Theorem 8.2 In the linear regression model (8.14)-(8.15) under (8.1), E [˜βcls &#124;X ] = β. |  |
| Theorem 8.3 | Theorem 8.3 In the homoskedastic linear regression model (8.14)-(8.15) with E [ e2 &#124;X ] = σ2, under (8.1), V 0 ˜β = var [˜βcls &#124;X ] = (( X ′X )−1 − ( X ′X )−1 R ( R ′ ( X ′X )−1 R )−1 R ′ ( X ′X )−1 ) σ2. |  |
| Theorem 8.4 | Theorem 8.4 In the homoskedastic linear regression model (8.14)-(8.15) with E [ e2 &#124;X ] = σ2, under (8.1), E [ s2 cls &#124;X ] = σ2 and E [ ˆV 0 ˜β &#124;X ] = V 0 ˜β. Now consider the distributional properties in the normal regression model Y = X ′β + e with e ∼ N(0, σ2). By the linearity of Theorem 8.1.2, conditional on X , ˜βcls − β is normal. Given Theorems 8.2 and. |  |
| Theorem 8.5 | Theorem 8.5 In the normal linear regression model (8.14)-(8.15) with constraint (8.1), ˜βcls ∼ N ( β,V 0 ˜β ) ( n − k + q ) s2 cls σ2 ∼ χ2 n−k+q T ∼ tn−k+q . An interesting relationship is that in the homoskedastic regression model cov (ˆβols − ˜βcls, ˜βcls &#124;X ) = E [(ˆβols − ˜βcls ) (˜βcls − β )′ &#124;X ] = E [ AX ′ee ′ ( X ( X ′X )−1 − X A ) &#124;X ] = AX ′ ( X ( X ′X )−1 − X A ) σ2 = 0. |  |
| Theorem 8.6 | Theorem 8.6 Consistency Under Assumptions 7.1, 8.1, and 8.2, ˜βmd − →p β as n → ∞. |  |
| Theorem 8.7 | Theorem 8.7 Asymptotic Normality Under Assumptions 7.2, 8.1, and 8.2, p n (˜βmd − β ) − → d N ( 0,V β(W ) ) as n → ∞, where V β(W ) = V β − W −1R ( R ′W −1R )−1 R ′V β −V βR ( R ′W −1R )−1 R ′W −1 +W −1R ( R ′W −1R )−1 R ′V βR ( R ′W −1R )−1 R ′W −1 (8.24) and V β = Q −1 X X ΩQ −1 X X . |  |
| Theorem 8.8 | Theorem 8.8 Asymptotic Distribution of CLS Estimator Under Assumptions 7.2 and 8.1, as n → ∞ p n (˜βcls − β ) − → d N(0,V cls) where V cls = V β −Q −1 X X R ( R ′Q −1 X X R )−1 R ′V β − V βR ( R ′Q −1 X X R )−1 R ′Q −1 X X +Q −1 X X R ( R ′Q −1 X X R )−1 R ′V βR ( R ′Q −1 X X R )−1 R ′Q −1 X X . |  |
| Theorem 8.9 | Theorem 8.9 Efficient Minimum Distance Estimator Under Assumptions 7.2 and 8.1, p n (˜βemd − β ) − → d N ( 0,V β,emd ) as n → ∞, where V β,emd = V β − V βR ( R ′V βR )−1 R ′V β. (8.26) Since V β,emd ≤ V β (8.27) the estimator (8.25) has lower asymptotic variance than the unrestricted estimator. Furthermore, for any W , V β,emd ≤ V β(W ) (8.28) so (8.25) is asymptotically efficient in the class of minimum distance estimators. |  |
| Theorem 8.10 | Theorem 8.10 Under Assumptions 7.2, 8.2, and 8.3, for ˜β = ˜βmd and ˜β = ˜βcls defined in (8.45) and (8.46), p n (˜β − β ) − → d N ( 0,V β(W ) ) as n → ∞ where V β(W ) is defined in (8.24). For ˜βcls, W = Q X X and V β(W ) = V cls as defined in Theorem 8.8. V β(W ) is minimized with W = V −1 β in which case the asymptotic variance is V ∗ β = V β − V βR ( R ′V βR )−1 R ′V β. The asymptotic covariance matrix for the efficient minimum distance estimator can be estimated by ˆV ∗ β = ˆV β − ˆV β ˆR ( ˆR ′ ˆV β ˆR )−1 ˆR ′ ˆV β where ˆR = ∂ ∂β r ( ˜βmd)′. (8.48) Standard errors for the elements of ˜βmd are the square roots of the diagonal elements of ˆV ∗ ˜β = n−1 ˆV ∗ β. |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
