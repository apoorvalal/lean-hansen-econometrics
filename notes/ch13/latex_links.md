# Chapter 13 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch13_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 13.1 | Theorem 13.1 For the overidentified IV model ˆβgmm = ( X ′Z W Z ′X )−1 ( X ′Z W Z ′Y ) . (13.6) |  |
| Theorem 13.2 | Theorem 13.2 If W = ( Z ′Z )−1 then ˆβgmm = ˆβ2sls. Furthermore, if k = ℓ then ˆβgmm = ˆβiv. |  |
| Theorem 13.3 | Theorem 13.3 Asymptotic Distribution of GMM Estimator. Under Assumption 12.2, as n → ∞, pn (ˆβgmm − β ) − → d N ( 0,V β ) where V β = ( Q ′W Q )−1 ( Q ′W ΩW Q ) ( Q ′W Q )−1 . (13.7) The GMM estimator is asymptotically normal with a “sandwich form” asymptotic variance. Our derivation treated the weight matrix W as if it is non-random but Theorem 13.3 applies to the random weight matrix case so long as ˆW converges in probability to a positive definite limit W . This may require scaling the weight matrix, for example replacing ˆW = ( Z ′Z )−1 with ˆW = ( n−1Z ′Z )−1. Since rescaling the weight matrix does not affect the estimator this is ignored in implementation. |  |
| Theorem 13.4 | Theorem 13.4 Asymptotic Distribution of GMM with Efficient Weight Matrix. Under Assumption 12.2 and W = Ω−1, as n → ∞, pn (ˆβgmm − β ) − → d N ( 0,V β ) where V β = ( Q ′Ω−1Q )−1. |  |
| Theorem 13.5 | Theorem 13.5 Efficient GMM. Under Assumption 12.2, for any W > 0, ( Q ′W Q )−1 ( Q ′W ΩW Q ) ( Q ′W Q )−1 − ( Q ′Ω−1Q )−1 ≥ 0. The inequality “ ≥” can be replaced with “>” if W ̸= Ω−1. Thus if ˆβgmm is the efficient GMM estimator and ˜βgmm is another GMM estimator, then avar [ˆβgmm ] ≤ avar [˜βgmm ] . |  |
| Theorem 13.6 | Theorem 13.6 Under Assumption 12.2 and E [ e2 &#124;Z ] = σ2, ˆβ2sls is efficient GMM. |  |
| Theorem 13.7 | Theorem 13.7 Under Assumption 12.2 and Ω > 0, if ˆW = ˆΩ−1 or ˆW = ˆΩ∗−1 where the latter are defined in (13.8) and (13.9) then as n → ∞ ,pn (ˆβgmm − β ) − → d N ( 0,V β ) where V β = ( Q ′Ω−1Q )−1. |  |
| Theorem 13.8 | Theorem 13.8 Under Assumption 12.2, Assumption 7.3, and H0, as n → ∞ , W − → d χ2 q . For c satisfying α = 1 −Gq (c), P[W > c &#124;H0] − →α so the test “Reject H0 if W > c” has asymptotic size α. |  |
| Theorem 13.9 | Theorem 13.9 Under Assumptions 12.2 and 8.3, for the constrained GMM estimator (13.16), pn (ˆβcgmm − β ) − → d N ( 0,V cgmm ) as n → ∞, where V cgmm = V β − ( Q ′W Q )−1 R ( R ′ ( Q ′W Q )−1 R )−1 R ′V β (13.18) − V βR ( R ′ ( Q ′W Q )−1 R )−1 R ′ ( Q ′W Q )−1 + ( Q ′W Q )−1 R ( R ′ ( Q ′W Q )−1 R )−1 R ′V βR ( R ′ ( Q ′W Q )−1 R )−1 R ′ ( Q ′W Q )−1 . |  |
| Theorem 13.10 | Theorem 13.10 Under Assumptions 12.2 and 8.3, for the efficient constrained GMM estimator (13.19), pn (ˆβcgmm − β ) − → d N ( 0,V cgmm ) as n → ∞, where V cgmm = V β − V βR ( R ′V βR )−1 R ′V β. (13.20) |  |
| Theorem 13.11 | Theorem 13.11 Under Assumptions 12.2 and 8.3, for the constrained GMM estimator (13.23), pn (ˆβcgmm − β ) − → d N ( 0,V cgmm ) as n → ∞ , where V cgmm equals (13.18). If W = ˆΩ−1, then V cgmm equals (13.20). The asymptotic covariance matrix in the efficient case is estimated by (13.21) with R replaced with ˆR = ∂ ∂β r (ˆβcgmm )′ . The asymptotic covariance matrix (13.18) in the general case is estimated similarly. To implement an iterated restricted GMM estimator the weight matrix may be set asW = ˜Ω−1 where ˜Ω is defined in (13.22), and then iterated until convergence. |  |
| Theorem 13.12 | Theorem 13.12 Under Assumption 12.2, Assumption 7.3, and H0, then as n → ∞, D − → d χ2 q . For c satisfying α = 1 −Gq (c), P[D > c &#124;H0] − →α. The test “Reject H0 if D > c” has asymptotic size α. |  |
| Theorem 13.13 | Theorem 13.13 If ˜Ω = ˆΩ then D ≥ 0. Furthermore, if r is linear in β then D equals the Wald statistic. The statement that ˜Ω = ˆΩ implies D ≥ 0 follows from the fact that in this case the criterion functions ˆJ(β) = ˜J(β) are identical so the constrained minimum cannot be smaller than the unconstrained. The statement that linear hypotheses and ˜Ω = ˆΩ implies D = W follows from applying the expression for the constrained GMM estimator (13.19) and using the covariance matrix formula (13.11). The fact that D ≥ 0 when ˜Ω = ˆΩ motivated Newey and West (1987a) to recommend this choice. However, this is necessary. Setting ˜Ω to be the constrained efficient weight matrix is natural for efficient estimation of ˆβcgmm. In the event that D < 0 the test simply fails to reject H0 at any significance level. As discussed in Section 9.17 for tests of nonlinear hypotheses the Wald statistic can work quite poorly. In particular, the Wald statistic is affected by how the hypothesis r ( β ) is formulated. In contrast, the distance statistic D is not affected by the algebraic formulation of the hypothesis. |  |
| Theorem 13.14 | Theorem 13.14 Under Assumption 12.2 then asn → ∞, J = J (ˆβgmm ) − → d χ2 ℓ−k. For c satisfying α = 1−Gℓ−k(c), P[J > c &#124;H0] − →α so the test “Reject H0 if J > c” has asymptotic size α. |  |
| Theorem 13.15 | Theorem 13.15 Under Assumption 12.2 and E [ Za X ′] has full rank k, then as n → ∞, C − → d χ2 ℓb . For c satisfying α = 1 − Gℓb (c), P[C > c &#124;H0] − →α. The test “Reject H0 if C > c” has asymptotic size α. |  |
| Theorem 13.16 | Theorem 13.16 Under Assumption 12.2 and E [ Z2Y ′ 2 ] has full rank k2, then as n → ∞, C − → d χ2 k2 . For c satisfying α = 1 − Gk2(c), P[C > c &#124;H0] → α. The test “Reject H0 if C > c” has asymptotic size α. In Stata the command estat endogenous afer ivregress gmm can be used to implement the test for endogeneity. The statistic C and its asymptotic p-value using the χ2 k2 distribution are reported. |  |
| Theorem 13.17 | Theorem 13.17 Under Assumption 12.2 andE [ Z2 ( Y ′ 2,Y ′ 3 )] has full rankk2+k3, then as n → ∞, C − → d χ2 k2 . For c satisfying α = 1 − Gk2(c), P[C > c &#124;H0] − →α. The test “Reject H0 if C > c” has asymptotic size α. In Stata, the command estat endogenous x2 afer ivregress gmm can be used to implement the test for endogeneity where x2 is the name(s) of the variable(s) tested for endogeneity. The statisticC and its asymptotic p-value using the χ2 k2 distribution are reported. 2If the homoskedastic weight matrix is used this GMM estimator equals least squares, but when the weight matrix allows for heteroskedasticity the efficient GMM estimator does not equal least squares as the model is overidentified. |  |
| Proposition 13.1 | Proposition 13.1 Distribution of Nonlinear GMM Estimator Under general regularity conditions, p n (ˆβgmm − β ) − → d N ( 0,V β ) where V β = ( Q ′W Q )−1 ( Q ′W ΩW Q ) ( Q ′W Q )−1 with Ω = E [ gi g ′ i ] and Q = E [ ∂ ∂β′ gi (β) ] . If the efficient weight matrix is used thenV β = ( Q ′Ω−1Q )−1. |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
