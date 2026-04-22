# Chapter 7 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch7_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 7.1 | Theorem 7.1 Consistency of Least Squares. Under Assumption 7.1, ˆQ X X − →p Q X X , ˆQ X Y − →p Q X Y , ˆQ −1 X X − →p Q −1 X X , ˆQ X e − →p 0, and ˆβ − →p β as n → ∞. |  |
| Theorem 7.2 | Theorem 7.2 Assumption 7.2 implies that Ω < ∞ (7.6) and 1pn n∑ i =1 Xi ei − → d N(0, Ω) (7.7) as n → ∞. |  |
| Theorem 7.3 | Theorem 7.3 Asymptotic Normality of Least Squares Estimator. Under Assumption 7.2, as n → ∞, $\\sqrt{n}(\\hat{\\beta}-\\beta) \\to_d N(0,V_\\beta)$ where $Q_{XX}=E[XX']$, $\\Omega=E[XX'e^2]$, and $V_\\beta = Q_{XX}^{-1}\\Omega Q_{XX}^{-1}$. |  |
| Theorem 7.4 | Theorem 7.4 Under Assumption 7.1, ˆσ2 − →p σ2 and s2 − →p σ2 as n → ∞. |  |
| Theorem 7.5 | Theorem 7.5 Under Assumption 7.1, ˆV 0 β − →p V 0 β as n → ∞. |  |
| Theorem 7.6 | Theorem 7.6 Under Assumption 7.2, as n → ∞, ˆΩ − →p Ω and ˆV HC0 β − →p V β. |  |
| Theorem 7.7 | Theorem 7.7. Under Assumption 7.2, as n → ∞, $\\tilde{\\Omega} \\to_p \\Omega$, $\\hat{\\Omega} \\to_p \\Omega$, and $\\hat V^{HC1}_\\beta$, $\\hat V^{HC2}_\\beta$, and $\\hat V^{HC3}_\\beta$ each converge in probability to $V_\\beta$. |  |
| Theorem 7.8 | Theorem 7.8 Under Assumption 7.1, if r (β) is continuous at the true value of β then as n → ∞, ˆθ − →p θ. |  |
| Theorem 7.9 | Theorem 7.9 Asymptotic Distribution of Functions of Parameters. Under Assumptions 7.2 and 7.3, as n → ∞, $\\sqrt{n}(\\hat{\\theta}-\\theta) \\to_d N(0,V_\\theta)$ where $V_\\theta = R'V_\\beta R$. |  |
| Theorem 7.10 | Theorem 7.10 Under Assumptions 7.2 and 7.3, as n → ∞, ˆV θ − →p V θ. |  |
| Theorem 7.11 | Theorem 7.11. Under Assumptions 7.2, 7.3, and 7.4, $T(\\theta) \\to_d Z \\sim N(0,1)$ and $|T(\\theta)| \\to_d |Z|$. |  |
| Theorem 7.12 | Theorem 7.12 Under Assumptions 7.2, 7.3 and 7.4, for ˆC defined in (7.35) with c = Φ−1(1 − α/2), P [ θ ∈ ˆC ] → 1 − α. For c = 1.96, P [ θ ∈ ˆC ] → 0.95. |  |
| Theorem 7.13 | Theorem 7.13 Under Assumptions 7.2, 7.3 and 7.4, as n → ∞, W (θ) − → d χ2 q . |  |
| Theorem 7.14 | Theorem 7.14 Under Assumptions 7.2, 7.3, and E [ e2 &#124;X ] = σ2 > 0, as n → ∞, W 0(θ) − → d χ2 q . |  |
| Theorem 7.15 | Theorem 7.15 Under Assumptions 7.2, 7.3, Ω > 0, E ∥e∥16 < ∞, E ∥X ∥16 < ∞, g ( β ) has five continuous derivatives in a neighborhood of β, and E [ exp ( t ( ∥e∥4 + ∥X ∥4))] ≤ B < 1, as n → ∞ P[T (θ) ≤ x] = Φ(x) + n−1/2p1(x)φ(x) + n−1p2(x)φ(x) + o ( n−1) uniformly in x, where p1(x) is an even polynomial of order 2 and p2(x) is an odd polynomial of degree 5 with coefficients depending on the moments of e and X up to order 16. |  |
| Theorem 7.16 | Theorem 7.16 Under Assumption 7.2 and E ∥X ∥r < ∞, then max 1≤i ≤n &#124;ˆei − ei &#124;= op ( n−1/2+1/r ) . (7.41) |  |
| Theorem 7.17 | Theorem 7.17 If Xi is i.i.d., Q X X > 0, and E ∥X ∥r < ∞ for some r ≥ 2, then max 1≤i ≤n hi i = op ( n2/r −1) . For any r ≥ 2 then hi i = op (1) (uniformly in i ≤ n). Larger r implies a stronger rate of convergence. For example r = 4 implies hi i = op ( n−1/2) . |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
