# Chapter 9 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch9_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 9.1 | Theorem 9.1 Under Assumptions 7.2, 7.3, and H0 : θ = θ0 ∈ R, T (θ0) − → d Z ∼ N(0,1). For c satisfying α = 2(1 − Φ(c)), P[&#124;T (θ0)&#124;> c &#124;H0] → α, and the test “Reject H0 if &#124;T (θ0)&#124;> c” has asymptotic size α. |  |
| Theorem 9.2 | Theorem 9.2 Under Assumptions 7.2, 7.3, 7.4, andH0 : θ = θ0 ∈ Rq , then W − → d χ2 q . For c satisfying α = 1 − Gq (c), P(W > c &#124;H0) − →α so the test “Reject H0 if W > c” has asymptotic size α. Notice that the asymptotic distribution in Theorem 9.2 depends solely on q, the number of restrictions being tested. It does not depend on k, the number of parameters estimated. The asymptotic p-value for W is p = 1 −Gq (W ), and this is particularly useful when testing multiple restrictions. For example, if you write that a Wald test on eight restrictions ( q = 8) has the value W =. |  |
| Theorem 9.3 | Theorem 9.3 Under Assumptions 7.2 and 7.3, E [ e2 &#124;X ] = σ2 > 0, and H0 : θ = θ0 ∈ Rq , then W 0 − → d χ2 q . For c satisfying α = 1 −Gq (c), P [ W 0 > c &#124;H0 ] − →α so the test “Reject H0 if W 0 > c” has asymptotic size α. |  |
| Theorem 9.4 | Theorem 9.4 Under Assumptions 7.2, 7.3, 7.4, and H0 : θ = θ0 ∈ Rq , J ∗ − → d χ2 q . Testing using the minimum distance statistic J ∗ is similar to testing using the Wald statisticW . Critical values and p-values are computed using theχ2 q distribution. H0 is rejected in favor ofH1 if J ∗ exceeds the level α critical value, which can be calculated in MATLAB as chi2inv(1- α,q). The asymptotic pvalue is p = 1 −Gq (J ∗). In MATLAB, use the command 1-chi2cdf(J,q) . |  |
| Theorem 9.5 | Theorem 9.5 Under Assumptions 7.2 and 7.3, E [ e2 &#124;X ] = σ2 > 0, and H0 : θ = θ0 ∈ Rq , then J 0 − → d χ2 q . |  |
| Theorem 9.6 | Theorem 9.6 For tests of linear hypotheses H0 : R ′β = θ0 ∈ Rq , the F statistic equals F = W 0/q where W 0 is the homoskedastic Wald statistic. Thus under. |  |
| Theorem 9.7 | Theorem 9.7 For general hypotheses the Hausman test statistic is H = n (ˆβols − ˜βemd )′ ˆR ( ˆR ′ ˆV β ˆR )−1 ˆR ′ (ˆβols − ˜βemd ) . Under Assumptions 7.2, 7.3, 7.4, and H0 : r (β) = θ0 ∈ Rq , H − → d χ2 q . |  |
| Theorem 9.8 | Theorem 9.8 Under Assumptions 7.2, 7.3, and 7.4, for θ = r (β) ̸= θ0 and q = 1, then &#124;T &#124;− →p ∞. For any c < ∞ the test “Reject H0 if &#124;T &#124;> c” is consistent against fixed alternatives. The Wald statistic for H0 : θ = r (β) = θ0 against H1 : θ ̸= θ0 is W = n (ˆθ − θ0 )′ ˆV −1 θ (ˆθ − θ0 ) . Under H1, ˆθ − →p θ ̸= θ0. Thus (ˆθ − θ0 )′ ˆV −1 θ (ˆθ − θ0 ) − →p (θ − θ0)′ V −1 θ (θ − θ0) > 0. Hence under H1, W − →p ∞. Again, this implies that Wald tests are consistent. |  |
| Theorem 9.9 | Theorem 9.9 Under Assumptions 7.2, 7.3, and 7.4, for θ = r (β) ̸= θ0, then W − →p ∞. For any c < ∞ the test “Reject H0 if W > c” is consistent against fixed alternatives. |  |
| Theorem 9.10 | Theorem 9.10 Under Assumptions 7.2, 7.3, 7.4, and θn = r (βn) = r0 + n−1/2h, then T (θ0) = ˆθ − θ0 s(ˆθ) − → d Z + δ where Z ∼ N(0,1) and δ = h/ √ Vθ. For c such that Φ(c) = 1 − α, P[T (θ0) > c] − →Φ(δ − c). Furthermore, for c such that Φ(c) = 1 − α/2, P[&#124;T (θ0)&#124;> c] − →Φ(δ − c) + Φ(−δ − c). |  |
| Theorem 9.11 | Theorem 9.11 Under Assumptions 7.2, 7.3, 7.4, and θn = r (βn) = θ0 + n−1/2h, then W − → d χ2 q (λ) where λ = h′V −1 θ h. Furthermore, for c such that P [ χ2 q > c ] = α, P[W > c] − →P [ χ2 q (λ) > c ] . |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
