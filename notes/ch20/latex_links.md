# Chapter 20 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch20_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 20.1 | Theorem 20.1 If for someα ≥ 0, m(α)(x) is uniformly continuous on a compact set S and XK (x) is either a polynomial basis or a spline basis (with uniform knot spacing) of order s ≥ α, then as K → ∞ δ∗ K ≤ o ( K −α) . (20.11) Furthermore, if m(2)(x) is uniformly continuous on S and XK (x) is a linear spline basis, then δ∗ K ≤ O ( K −2) . |  |
| Theorem 20.2 | Theorem 20.2 If X has compact support S, for some α ≥ 0 m(α)(x) is uniformly continuous on S, and XK (x) is either a polynomial basis or a spline basis of order s ≥ α, then as K → ∞ δK ≤ δ∗ K ≤ o ( K −α) . Furthermore, if m(2)(x) is uniformly continuous on S and XK (x) is a linear spline basis, then δK ≤ O ( K −2) . |  |
| Theorem 20.3 | Theorem 20.3 If X has compact support S with a strictly positive density f (x) on S then 1. ζK ≤ O (K ) for polynomials 2. ζK ≤ O ( K 1/2) for splines. |  |
| Theorem 20.4 | TODO: fill from source. The local excerpt only clearly preserves the start of the statement: under Assumption 20.1, $\\lVert \\tilde Q_K - I_K \\rVert \\to_p 0$. |  |
| Theorem 20.5 | Theorem 20.5 If Assumption 20.1 holds then  ˜Q −1 K − I K  p − →0 (20.20) and λmax ( ˜Q −1 K ) = 1/λmin (˜QK ) p − →1. (20.21) |  |
| Theorem 20.6 | Theorem 20.6 Under Assumption 20.1 and δK = o(1), then as n,K → ∞, ISE(K ) = op (1). (20.23) |  |
| Theorem 20.7 | Theorem 20.7 Under Assumption 20.1 and σ2 (x) ≤ σ2 < ∞, then as n,K → ∞, ISE(K ) ≤ Op ( δ2 K + K n ) (20.24) where δ2 K is the expected squared prediction error (20.13). Furthermore, if m′′(x) is uniformly continuous then for polynomial or spline basis functions ISE(K ) ≤ Op ( K −4 + K n ) . (20.25) |  |
| Theorem 20.8 | Theorem 20.8 Under Assumption 20.2, as n → ∞, pn (ˆθK − θ + a (rK ) ) V 1/2 K − → d N(0, 1). (20.26) |  |
| Theorem 20.9 | Theorem 20.9. Under Assumption 20.2, as n → ∞, $\\sqrt{n}(\\hat m_K(x)-m(x)+r_K(x)) V_K(x)^{-1/2} \\to_d N(0,1)$ where $V_K(x)=X_K(x)'Q_K^{-1}\\Omega_K Q_K^{-1}X_K(x)$. |  |
| Theorem 20.10 | Theorem 20.10 Under Assumption 20.2, if in addition nδ∗2 K → 0 then pn ( ˆmK (x) − m(x)) V 1/2 K (x) − → d N(0, 1). (20.28) |  |
| Proposition 20.1 | TODO: fill from source. The local excerpt only partially preserves the completeness criterion for identification of $m(x)$. |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
