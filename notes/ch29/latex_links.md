# Chapter 29 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch29_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 29.1 | Theorem 29.1 The leave-one-out ridge regression prediction errors are ˜ei (λ) = ( 1 − X ′ i ( X ′X + Λ )−1 Xi )−1 ˆei (λ) (29.6) where ˆei (λ) = Yi − X ′ i ˆβridge(λ) are the ridge regression residuals. |  |
| Theorem 29.2 | Theorem 29.2 In the linear regression model, if 0 < λ < 2σ2/β′β, mse [ˆβridge &#124;X ] < mse [ˆβols &#124;X ] . |  |
| Theorem 29.3 | Theorem 29.3 Suppose model (29.11) holds, ω = max1≤j ≤p E [ X 2 j e2 ] < ∞, and. |  |
| Theorem 29.4 | Theorem 29.4 Suppose model (29.11) holds, Assumption 29.2 holds, and ω = max1≤j ≤p E [ X 2 j e2 ] < ∞. Take any α > 0, set λ as (29.14), and K = A ( n/log p )1/2s for A sufficiently large. Suppose that for this sequence min b∈BK b′Qnb b′b ≥ c2 > 0. Then there is D < ∞ such that with probability exceeding 1 − α, (ˆβLasso − βK )′ Qn (ˆβLasso − βK ) ≤ D (log p n )1− 1 2s ,  ˆβLasso − βK   1 ≤ D (log p n ) 1 2 − 1 2s , and  ˆβLasso − βK   2 ≤ D (log p n ) 1 2 − 1 4s . |  |
| Theorem 29.5 | Theorem 29.5 Under the Assumptions listed in Theorem 3 of Belloni, Chen, Chernozhukov, and Hansen (2012), including ∥Γ∥0 log ppn → 0, (29.19) then ( Q −1ΩQ −1)p n (ˆβLasso−IV − β ) − → d N(0, I k) (29.20) where Q = E [ W W ′] , Ω = E [ W W ′e2] , and W = Γ′Z . Furthermore, the standard covariance matrix estimators are consistent for the asymptotic covariance matrix. The same distribution result holds for ˆβLasso−SSIV under the assumptions listed in their Theorem 7. In particular, (29.19) is replaced by ∥Γ∥0 log p n → 0. (29.21) For a sketch of the proof see Section 29.23. Equation (29.19) requires that the reduced form coefficient Γ is sparse in the sense that the number of non-zero reduced form coefficients∥Γ∥0 grows more slowly than p n. This allows for p to grow exponentially with n but at a somewhat slower rate than allowed by Theorem 29.3. Condition (29.19) is one of the key assumptions needed for the distribution result (29.20). For Lasso SSIV , equation (29.21) replaces (29.19). This rate condition is weaker, allowingp to grow at the same rate as for regression estimation. The difference is due to the split-sample estimation, which breaks the dependence between the reduced form coefficient estimates and the second-stage structural estimates. There are two interpretable implications of the difference between (29.19) and (29.21). First, a direct implication is that Lasso SSIV allows for larger number of variablesp. Second, an indirect implication is that for any set of variables, Lasso SSIV will have reduced bias relative to Lasso IV . Both interpretations suggest that Lasso SSIV is the preferred estimator. |  |
| Theorem 29.6 | Theorem 29.6 Suppose model (29.22)-(29.23) holds, max 1≤j ≤p E [ X 4 j ] < ∞, E [ e4] < ∞, E [ V 4] < ∞, Assumption 29.1 holds for both β and γ, the Lasso parameter satisfiesλ = C √ n log p for C sufficiently large, and (β   0 +  γ   0 ) log p pn = o(1). (29.26) Then p n (ˆθPR − θ ) − → d N ( 0, E [ V 2e2] ( E [ V 2])2 ) . Furthermore, the standard variance estimator for ˆθPR is consistent for the asymptotic variance. |  |
| Theorem 29.7 | Theorem 29.7 Under the assumptions of Theorem 29.6, p n (ˆθDML − θ ) − → d N ( 0, E [ V 2e2] ( E [ V 2])2 ) . Furthermore, the standard variance estimator for ˆθDML is consistent for the asymptotic variance. |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
