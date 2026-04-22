# Chapter 24 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch24_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 24.1 | Theorem 24.1 Assume Y is continuously distributed. Then the median m satisfies E [ sgn(Y − m) ] = 0. (24.2) If in addition E &#124;Y &#124;< ∞ it satisfies m = argmin θ E &#124;Y − θ&#124;. (24.3) If the conditional distribution F (y &#124;x) of Y given X = x is continuous in y the conditional median error e = Y − m(X ) satisfies E [ sgn(e) &#124;X ] = 0. (24.4) If in addition E &#124;Y &#124;< ∞ the conditional median satisfies m(x) = argmin θ E[&#124;Y − θ&#124;&#124;X = x]. (24.5) If (Y , X ) satisfy the linear median regression model (24.1) and E &#124;Y &#124;< ∞ then the coefficientβ satisfies β = argmin b E ⏐⏐Y − X ′b ⏐ ⏐. (24.6)The proof is in Section 24.16. |  |
| Theorem 24.2 | Theorem 24.2 Assume Y is continuously distributed. Then the quantile qτ satisfies E [ ψτ ( Y − qτ )] = 0. (24.11) If in addition E &#124;Y &#124;< ∞ it satisfies qτ = argmin θ E [ ρτ (Y − θ) ] . (24.12) If the conditional distribution F (y &#124;x) of Y given X = x is continuous in y the conditional quantile error e = Y − qτ(X ) satisfies E [ ψτ (e) &#124;X ] = 0. (24.13) If in addition E &#124;Y &#124;< ∞ the conditional quantile function satisfies qτ(x) = argmin θ E [ ρτ (Y − θ) &#124;X = x ] . (24.14) If (Y , X ) satisfy the linear quantile regression model (24.9) and E &#124;Y &#124;< ∞ then the coefficientβ satisfies β = argmin b E [ ρτ ( Y − X ′b )] . (24.15) |  |
| Theorem 24.3 | Theorem 24.3 Consistency of Quantile Regression Estimator Assume that (Yi , Xi ) are i.i.d., E &#124;Y &#124;< ∞ , E ∥X ∥ < ∞ , fτ (e &#124;x) exists and satisfies fτ (e &#124;x) ≤ D < ∞, and the parameter space for β is bounded. For any τ ∈ (0, 1) such that Q τ def = E [ X X ′ fτ (0 &#124;X ) ] > 0 (24.18) then ˆβτ − →p βτ as n → ∞. |  |
| Theorem 24.4 | Theorem 24.4 Asymptotic Distribution of Quantile Regression Estimator In addition to the assumptions of Theorem 24.3, assume that E ∥X ∥3 < ∞ , fτ (e &#124;x) is continuous in e, and βτ is in the interior of the parameter space. Then as n → ∞ p n (ˆβτ − βτ ) − → d N(0,V τ) where V τ = Q −1 τ ΩτQ −1 τ and Ωτ = E [ X X ′ψ2 τ ] for ψτ = τ − 1 { Y < X ′βτ } . |  |
| Theorem 24.5 | Theorem 24.5 Quantile Causal Effect If Assumption 24.1 holds then Dτ(x) = Qτ(x), the quantile regression derivative equals the quantile treatment effect. |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
