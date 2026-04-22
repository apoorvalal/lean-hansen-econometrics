# Chapter 15 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch15_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 15.1 | Theorem 15.1 If Yt is covariance stationary it has the projection equation Yt = P t −1 [Yt ] + et . The innovations et satisfy E[et ] = 0, E [ et −ℓe′ t ] = 0 for ℓ ≥ 1, and Σ = E [ ee ′] < ∞. If Yt is strictly stationary then et is strictly stationary. The uncorrelatedness of the projection errors is a property of a multivariate white noise process. Definition 15.1 The vector process et is multivariate white noise if E[et ] = 0, E [ et e′ t ] = Σ < ∞, and E [ et e′ t −ℓ ] = 0 for ℓ ̸= 0. |  |
| Theorem 15.2 | Theorem 15.2 If Yt is covariance stationary and non-deterministic then it has the linear representation Yt = µ + ∞∑ ℓ=0 Θℓet −ℓ (15.3) where et are the white noise projection errors and Θ0 = I m. The coefficient matrices Θℓ are m × m. |  |
| Theorem 15.3 | Theorem 15.3 If Yt is covariance stationary, non-deterministic, with Wold representation Yt = Θ(L)et , such that λmin (Θ∗(z)Θ(z)) ≥ δ > 0 for all complex &#124;z&#124;≤ 1, and for some integer s ≥ 0 the Wold coefficients satisfy∑∞ j =0 ∑∞ k=0 k sΘj +k 2 < ∞, then Yt has an infinite-order autoregressive representation A (L)Yt = a0 + et (15.4) where A (z) = I m − ∞∑ ℓ=1 Aℓzℓ and the coefficients satisfy∑∞ k=1 k s ∥Ak ∥ < ∞. The series in (15.4) is convergent. |  |
| Theorem 15.4 | Theorem 15.4 If et ∈ Rm is strictly stationary, ergodic, E ∥et ∥ < ∞, and∑∞ ℓ=0 ∥Θℓ∥ < ∞, then Yt = ∑∞ ℓ=0 Θℓet −ℓ is strictly stationary and ergodic. |  |
| Theorem 15.5 | Theorem 15.5 For j ≥ 1, Θj = ∑j ℓ=1 AℓΘj −ℓ. |  |
| Theorem 15.6 | Theorem 15.6 If et is strictly stationary, ergodic, E ∥et ∥ < ∞, and &#124;λi (A1)&#124;< 1 for i = 1, ...,m, then the VAR(1) process Yt is strictly stationary and ergodic. | #124;λi (A1)|#124;< 1 | |
| Theorem 15.7 | Theorem 15.7 If all roots r of det (A (z)) satisfy &#124;r &#124;> 1 then the VAR(p) process Yt is strictly stationary and ergodic. | #124;r |#124;> 1 then the VAR(p) process | |
| Theorem 15.8 | Theorem 15.8 If Yt is strictly stationary and 0 < Σ < ∞ for Σ defined in (15.6), then Q = E [ Xt X ′ t ] > 0 and the coefficient vector (14.45) is identified. |  |
| Theorem 15.9 | Theorem 15.9 If Yt is strictly stationary, ergodic, and 0 < Σ < ∞ then ˆA − →p A and ˆΣ − →p Σ as n → ∞. VAR models can be estimated in Stata using the var command. |  |
| Theorem 15.10 | Theorem 15.10 Suppose that Yt follows the VAR(p) model, all roots r of det(A (z)) satisfy &#124;r &#124;> 1, E[et &#124;Ft −1] = 0, E ∥et ∥4 < ∞, and Σ > 0, then as n → ∞,pn ( ˆa − a) − → d N(0,V ) where V = Q −1 ΩQ −1 Q = I m ⊗Q Q = E [ Xt X ′ t ] Ω = E [ et e′ t ⊗ Xt X ′ t ] . |  |
| Theorem 15.11 | Theorem 15.11 Assume that Yt is strictly stationary, ergodic, and for somer > 4, E ∥Yt ∥r < ∞ and the mixing coefficients satisfy ∑∞ ℓ=1 α(ℓ)1−4/r < ∞. Let a be the projection coefficient vector and et the projection error. Then as n → ∞,pn ( ˆa − a) − → d N(0,V ) where V = ( I m ⊗Q −1) Ω ( I m ⊗Q −1) Q = E [ Xt X ′ t ] Ω = ∞∑ ℓ=−∞ E [ et −ℓe′ t ⊗ Xt −ℓX ′ t ] . |  |
| Theorem 15.12 | Theorem 15.12 If Yt is a VAR(p) process then its h-step predictive regression is a predictive VAR(p) with ut a MA(h-1) process and B 1 = Θh = IRF(h). |  |
| Theorem 15.13 | Theorem 15.13 If Yt is strictly stationary, ergodic, Σ > 0, and for some r > 4, E ∥Yt ∥r < ∞ and the mixing coefficients satisfy∑∞ ℓ=1 α(ℓ)1−4/r < ∞, then as n → ∞, pn (ˆb − b ) − → d N(0,V ) where V = ( I m ⊗Q −1) Ω ( I m ⊗Q −1) Q = E [ Xt X ′ t ] Ω = ∞∑ ℓ=−∞ E [ ( ˆut −ℓ ⊗ Xt −ℓ) ( ˆu′ t ⊗ X ′ t )] . |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
