# Chapter 28 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch28_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 28.1 | Theorem 28.1 Schwarz . If the model f (y, θ) satisfies standard regularity conditions and the prior π(θ) is diffuse then −2 logp(Y ) = −2ℓn(ˆθ) + K log(n) +O(1) where the O(1) term is bounded as n → ∞. A heuristic proof for normal linear regression is given in Section 28.32. A “diffuse” prior is one which distributes weight uniformly over the parameter space. Schwarz’ s theorem shows that the marginal likelihood approximately equals the maximized likelihood multiplied by an adjustment depending on the number of estimated parameters and the sample size. The approximation (28.6) is commonly called the Bayesian Information Criterion or BIC. The BIC is a penalized log likelihood. The term K log(n) can be interpreted as an over-parameterization penalty. The multiplication of the log likelihood by −2 is traditional as it puts the criterion into the same units as a log-likelihood statistic. |  |
| Theorem 28.2 | Theorem 28.2 Suppose ˆf (y) is an estimated normal linear regression model with K regressors and a known variance σ2. Suppose that the true density g (y) is a conditionally homoskedastic regression with variance σ2. Then T = n log ( 2πσ2) + n + K = T0 + K (28.12) E [ −2ℓn(ˆθ) ] = n log ( 2πσ2) + n − K = T0 − K . (28.13) |  |
| Theorem 28.3 | Theorem 28.3 Under the assumptions of Theorem 28.2, E[AIC] = T . AIC is thus an unbiased estimator of T . One of the interesting features of these results are that they are exact – there is no approximation error – and they do not require that the true error is normally distributed. The critical assumption is conditional homoskedasticity. If homoskedasticity fails then the AIC loses its validity. In more general contexts these results do not hold exactly but instead hold as approximations (as discussed in the next section). The AIC may be obtained in Stata by using the command estimates stats after an estimated model. |  |
| Theorem 28.4 | Theorem 28.4 Under standard regularity conditions for maximum likelihood estimation, plus the assumption that certain statistics (identified in the proof) are uniformly integrable, E[AIC] = T + O ( n1/2) . AIC is thus an approximately unbiased estimator of T . A sketch of the proof is given in Section 28.32. |  |
| Theorem 28.5 | Theorem 28.5 If ˆm = AY is a linear estimator, the regression error is conditionally mean zero and homoskedastic, and ˜σ2 is unbiased for σ2, then E [ C ∗ p ] = R so the adjusted Mallows criterion C ∗ p is an unbiased estimator of R. |  |
| Theorem 28.6 | Theorem 28.6 Under standard regularity conditions for maximum likelihood estimation, selection based on IC is model selection consistent ifc(n,K ) = o(n) as n → ∞. |  |
| Theorem 28.7 | Theorem 28.7 Under standard regularity conditions for maximum likelihood estimation, selection based on IC asymptotically over-selects if c(n,K ) = O(1) as n → ∞. |  |
| Theorem 28.8 | Theorem 28.8 Under standard regularity conditions for maximum likelihood estimation, selection based on IC is consistent for parsimonious models if for all K2 > K1 c(n,K2) − c(n,K1) → ∞ (28.16) as n → ∞, yet c(n,K ) = o(n) as n → ∞. |  |
| Theorem 28.9 | Theorem 28.9 Assumption 28.1 implies (28.18). Thus Mallows selection is asymptotically equivalent to using the infeasible optimal model. |  |
| Theorem 28.10 | Theorem 28.10 If ˆθ ∼ N(θ, I K ) then mse [ˆθpms ] = K + (2λ − K )FK +2 (c, λ) − λFK +4 (c, λ) where Fr (x, λ) is the non-central chi-square distribution function with r degrees of freedom and non-centrality parameter λ = θ′θ. |  |
| Theorem 28.11 | Theorem 28.11 If ˆθ ∼ (θ,V ) and ˜θ = (1 − w) ˆθ then 1. wmse [˜θ ] < wmse [ˆθ ] if 0 < w < 2K /(K + λ). 2. wmse [˜θ ] is minimized by the shrinkage weight w0 = K /(K + λ). 3. The minimized WMSE is wmse [˜θ ] = K λ/(K + λ). |  |
| Theorem 28.12 | Theorem 28.12 Assume that ˆθ ∼ N(θ,V ), ˜θ is defined in (28.25), andK > 2. 1. If 0 < c < 2(K − 2) then wmse [˜θ ] < wmse [ˆθ ] . 2. The WMSE is minimized by setting c = K − 2 and equals wmse [˜θ ] = K − (K − 2)2 E [ Q −1 K ] where QK ∼ χ2 K (λ). See Theorem 15.3 of Introduction to Econometrics. |  |
| Theorem 28.13 | Theorem 28.13 Under the assumptions of Theorem 28.12 wmse [˜θ+] < wmse [˜θ ] . (28.26) |  |
| Theorem 28.14 | Theorem 28.14 Under the assumptions of Theorem 28.12, if q > 2 then wmse [˜θ+] < wmse [˜θ ] . The shrinkage estimator achieves uniformly smaller MSE if the number of restrictions is three or greater. The number of restrictions q plays the same role as the number of parameters K in the classical James-Stein estimator. Shrinkage achieves greater gains when there are more restrictionsq, and achieves greater gains when the restrictions are close to being satisfied in the population. If the imposed restrictions are far from satisfied then the shrinkage estimator will have similar performance as the original estimator. It is therefore important to select the restrictions carefully. In practice the covariance matrix V is unknown so it is replaced by an estimator ˆV . Thus the feasible version of the estimators equal ˆθR = ˆθ − ˆV R ( R ′ ˆV R )−1 ( R ′ ˆθ − r ) |  |
| Theorem 28.15 | Theorem 28.15 Under the assumptions of Theorem 28.12, if WMSE is defined with respect to W = diag(V −1 1 ,..., V −1 G ) and Kg > 2 for all g = 1, ...,G then wmse [˜θ ] < wmse [ˆθ ] .The proof is a simple extension of the classical James-Stein theory. The block diagonal structure of W means that the WMSE is the sum of the WMSE of each group. The classical James-Stein theory can be applied to each group finding that the WMSE is reduced by shrinkage group-by-group. Thus the total WMSE is reduced by shrinkage. |  |
| Theorem 28.16 | Theorem 28.16 The non-central chi-square density function (28.37) obeys the recursive relationship fK (x, λ) = K x fK +2(x, λ) + λ x fK +4(x, λ). |  |
| Theorem 28.17 | Theorem 28.17 If X ∼ N(θ, I K ) then for any function h (u) E [ X h ( X ′X )] = θE[h (QK +2)] (28.38) E [ X ′X h ( X ′X )] = K E[h (QK +2)] + λE[h (QK +4)] (28.39) where λ = θ′θ and Qr ∼ χ2 r (λ), a non-central chi-square random variable with r degrees of freedom and non-centrality parameter λ. |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
