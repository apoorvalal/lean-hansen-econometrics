# Chapter 10 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch10_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 10.1 | Theorem 10.1 If Zn − →p Z as n → ∞ then Zn − → p ∗ Z . Given Definition 10.1, we can establish a law of large numbers for the bootstrap sample mean. |  |
| Theorem 10.2 | Theorem 10.2 Bootstrap WLLN. If Yi are independent and uniformly integrable then Y ∗ − Y − → p ∗ 0 and Y ∗ − → p ∗ µ = E[Y ] as n → ∞. The proof (presented in Section 10.31) is somewhat different from the classical case as it is based on the Marcinkiewicz WLLN (Theorem 10.20, presented in Section 10.31). Notice that the conditions for the bootstrap WLLN are the same for the conventional WLLN. Notice as well that we state two related but slightly different results. The first is that the difference between the bootstrap sample mean Y ∗ and the sample mean Y diminishes as the sample size diverges. The second result is that the bootstrap sample mean converges to the population meanµ. The latter is not surprising (since the sample mean Y converges in probability to µ) but it is constructive to be precise since we are dealing with a new convergence concept. |  |
| Theorem 10.3 | Theorem 10.3 Bootstrap Continuous Mapping Theorem . If Z ∗ n − → p ∗ c as n → ∞ and g (·) is continuous at c, then g (Z ∗ n ) − → p ∗ g (c) as n → ∞. |  |
| Theorem 10.4 | Theorem 10.4 Bootstrap CLT. If Yi are i.i.d., E ∥Y ∥2 < ∞, and Σ = var[Y ] > 0, then as n → ∞, pn ( Y ∗ − Y ) − → d ∗ N(0, Σ). |  |
| Theorem 10.5 | Theorem 10.5 Bootstrap Continuous Mapping Theorem If Z ∗ n − → d ∗ Z as n → ∞ and g : Rm → Rk has the set of discontinuity points Dg such that P∗ [ Z ∗ ∈ Dg ] = 0, then g (Z ∗ n ) − → d ∗ g (Z ) as n → ∞. |  |
| Theorem 10.6 | Theorem 10.6 Bootstrap Delta Method: If ˆµ − →p µ, p n ( ˆµ∗ − ˆµ ) − → d ∗ ξ, and g (u) is continuously differentiable in a neighborhood of µ, then as n → ∞ p n ( g ( ˆµ∗) − g (ˆµ) ) − → d ∗ G ′ξ where G(x) = ∂ ∂x g (x)′ and G = G(µ). In particular, if ξ ∼ N(0,V ) then as n → ∞ p n ( g ( ˆµ∗) − g (ˆµ) ) − → d ∗ N ( 0,G ′V G ) . |  |
| Theorem 10.7 | Theorem 10.7 Under the assumptions of Theorem 6.10, that is, if Yi is i.i.d., µ = E[h (Y )], θ = g ( µ ) , E ∥h (Y )∥2 < ∞, and G (x) = ∂ ∂x g (x)′ is continuous in a neighborhood of µ, for ˆθ = g ( ˆµ ) with ˆµ = 1 n ∑n i =1 h (Yi ) and ˆθ∗ = g ( ˆµ∗) with ˆµ∗ = 1 n ∑n i =1 h ( Y ∗ i ) , as n → ∞ p n (ˆθ∗ − ˆθ ) − → d ∗ N(0,V θ) where V θ = G ′V G , V = E [( h (Y ) − µ ) ( h (Y ) − µ )′] and G = G ( µ ) . |  |
| Theorem 10.8 | Theorem 10.8 Under the assumptions of Theorem 10.7, ˆV ∗ θ − → p ∗ V θ as n → ∞.For a proof, see Exercise 10.9. |  |
| Theorem 10.9 | Theorem 10.9 If (10.15) and (10.16) hold for some sequence an and Z ∗ n  2 is uniformly integrable, then as B → ∞ ˆV boot,B θ − → p ∗ ˆV boot θ = var [ Z ∗ n ] , and as n → ∞ ˆV boot θ − → p ∗ V θ = var[ξ].This raises the question: Is the normalized sequence Zn uniformly integrable? We spend the remainder of this section exploring this question and turn in the next section to trimmed variance estimators which do not require uniform integrability. |  |
| Theorem 10.10 | Theorem 10.10 In the smooth function model of Theorem 10.7, if for some p ≥ 1 the p t h-order derivatives of g (x) are bounded, then Z ∗ n = pn (ˆθ∗ − ˆθ ) is uniformly square integrable and the bootstrap estimator of variance is consistent as in Theorem 10.9. |  |
| Theorem 10.11 | Theorem 10.11 As B → ∞, ˆV boot,B,τ θ − → p ∗ ˆV boot,τ θ = var [ Z ∗∗ n ] . We next examine the behavior of the bootstrap estimator ˆV boot,τ θ as n grows to infinity. We focus on the smooth function model of Theorem 10.7, which showed that Z ∗ n = p n (ˆθ∗ − ˆθ ) − → d ∗ Z ∼ N(0,V θ). Since the trimming is asymptotically negligible, it follows that Z ∗∗ n − → d ∗ Z . If we can show that Z ∗∗ n is uniformly square integrable, Theorem 10.9 will show that var [ Z ∗∗ n ] → var[Z ] = V θ as n → ∞. This is shown in the following result, whose proof is presented in Section 10.31. |  |
| Theorem 10.12 | Theorem 10.12 Under the assumptions of Theorem 10.7, ˆV boot,τ θ − → p ∗ V θ.Theorems 10.11 and 10.12 show that the trimmed bootstrap estimator of variance is consistent for the asymptotic variance in the smooth function model, which includes most econometric estimators. |  |
| Theorem 10.13 | Theorem 10.13 Assume that for some sequence an an (ˆθ − θ ) − → d ξ (10.18) and an (ˆθ∗ − ˆθ ) − → d ∗ ξ (10.19) where ξ is continuously distributed and symmetric about zero. Then P [ θ ∈ C pc] → 1 − α as n → ∞. The assumptions (10.18)-(10.19) hold for the smooth function model of Theorem 10.7, so this result incorporates many applications. The beauty of Theorem 10.13 is that the simple confidence interval C pc – which does not require technical calculation of asymptotic standard errors – has asymptotically valid coverage for any estimator which falls in the smooth function class, as well as any other estimator satisfying the convergence results (10.18)-(10.19) with ξ symmetrically distributed. The conditions are weaker than those required for consistent bootstrap variance estimation (and normal-approximation. |  |
| Theorem 10.14 | Theorem 10.14 If (10.30) and (10.31) hold whereξ is continuously distributed, then P [ θ ∈ C pt] → 1 − α as n → ∞. The bootstrap percentile-t intervals for the four estimators are reported in Table 13.2. They are similar but somewhat different from the percentile-type intervals, and generally wider. The largest difference arises with the interval for σ2 which is noticably wider than the other intervals. |  |
| Theorem 10.15 | Theorem 10.15 Under the assumptions of Theorem 9.11 of Introduction to Econometrics, P [ θ ∈ C pt] = 1 − α +O(n−1). |  |
| Theorem 10.16 | Theorem 10.16 If (10.30) and (10.31) hold whereξ is continuously distributed, then the bootstrap critical value satisfiesq ∗ 1−α − →p q1−α where q1−α is the 1−αt h quantile of &#124;ξ&#124;. The bootstrap test “Reject H0 in favor of H1 if &#124;T &#124;> q ∗ 1−α” has asymptotic size α: P [ &#124;T &#124;> q ∗ 1−α &#124;H0 ] − →α as n → ∞. In the smooth function model the t-test (with correct standard errors) has the following performance. |  |
| Theorem 10.17 | Theorem 10.17 Under the assumptions of Theorem 9.11 of Introduction to Econometrics, q ∗ 1−α = z1−α + op ( n−1) where zα = Φ−1 ((1 + α)/2) is the αt h quantile of &#124;Z &#124;. The asymptotic test “Reject H0 in favor of H1 if &#124;T &#124;> z1−α” has accuracy P [ &#124;T &#124;> z1−α &#124;H0 ] = 1 − α +O ( n−1) and the bootstrap test “Reject H0 in favor of H1 if &#124;T &#124;> q ∗ 1−α” has accuracy P [ &#124;T &#124;> q ∗ 1−α &#124;H0 ] = 1 − α + o ( n−1) . |  |
| Theorem 10.18 | Theorem 10.18 Under Assumption 7.2, as n → ∞ p n (ˆθ∗ − ˆθ ) − → d ∗ N ( 0,V β ) . If Assumption 7.3 also holds then p n (ˆθ∗ − ˆθ ) − → d ∗ N(0,V θ). If Assumption 7.4 also holds then T ∗ − → d ∗ N(0, 1). |  |
| Theorem 10.19 | Theorem 10.19 Under Assumption 7.2 and 7.3, as n → ∞, ˆV boot,τ θ − → p ∗ V θ. Programs such as Stata use the untrimmed estimatorˆV boot θ rather than the trimmed estimatorˆV boot,τ θ . |  |
| Theorem 10.20 | Theorem 10.20 Marcinkiewicz WLLN If ui are independent and uniformly integrable, then for any r > 1, as n → ∞, n−r ∑n i =1 &#124;ui &#124;r − →p 0. |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
