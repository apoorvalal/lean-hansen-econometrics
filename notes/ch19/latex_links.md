# Chapter 19 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch19_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 19.1 | Theorem 19.1 Suppose Assumption 19.1 holds and m′′(x) and f ′(x) are continuous in N . Then 1. E[ ˆmnw(x) &#124;X ] = m(x) + h2Bnw(x) + op ( h2) +Op (√ h n ) where Bnw(x) = 1 2 m′′(x) + f (x)−1 f ′(x)m′(x). 2. E[ ˆmLL(x) &#124;X ] = m(x) + h2BLL(x) + op ( h2) +Op (√ h n ) where BLL(x) = 1 2 m′′(x). The proof for the Nadaraya-Watson estimator is presented in Section 19.26. |  |
| Theorem 19.2 | Theorem 19.2 Under Assumption 19.1, 1. var [ ˆmnw(x) &#124;X ] = RK σ2(x) f (x)nh + op ( 1 nh ) . 2. var [ ˆmLL(x) &#124;X ] = RK σ2(x) f (x)nh + op ( 1 nh ) . In these expressions RK = ∫ ∞ −∞ K (u)2du is the roughness of the kernel K (u). The proof for the Nadaraya-Watson estimator is presented in Section 19.26. For the local linear estimator see Fan and Gijbels (1996). |  |
| Theorem 19.3 | Theorem 19.3 The bandwidth which minimizes the AIMSE (19.5) is h0 = ( RK σ2 4B )1/5 n−1/5. (19.6) With h ∼ n−1/5 then AIMSE[ ˆm(x)] = O ( n−4/5) . |  |
| Theorem 19.4 | Theorem 19.4 The AIMSE (19.5) of the Nadaraya-Watson and Local Linear regression estimators is minimized by the Epanechnikov kernel. The efficiency loss by using the other standard kernels, however, is small. The relative efficiency2 of estimation using the another kernel is ( RK /RK ( Epanechnikov ))2/5. Using the values of RK from Table. |  |
| Theorem 19.5 | Theorem 19.5 Suppose Assumption 19.1 holds. Set µK = 2 ∫ ∞ 0 K (u)du . Let the support of X be S = [x,x]. If m′′(x+), σ2(x+) and f ′(x+) exist, and f (x+) > 0 then E [ ˆmnw(x) &#124;X ] = m(x) + hm ′(x)µK + op (h) +Op   √ h n  . If m′′( x−), σ2(x−) and f ′(x−) exist, and f (x−) > 0 then E [ ˆmnw(x) &#124;X ] = m(x) − hm ′(x)µK + op (h) +Op   √ h n  . |  |
| Theorem 19.6 | Theorem 19.6 shows that the asymptotic bias of the LL estimator at a boundary is O(h2), the same as at interior points and is invariant to the slope of m(x). The theorem also shows that the asymptotic variance has the same rate as at interior points. Taking Theorems 19.1, 19.2, 19.5, and 19.6 together we conclude that the local linear estimator has superior asymptotic properties relative to the NW estimator. At interior points the two estimators have the same asymptotic variance. The bias of the LL estimator is invariant to the slope of m(x) and its asymptotic bias only depends on the second derivative while the bias of the NW estimator depends on both the first and second derivatives. At boundary points the asymptotic bias of the NW estimator is O(h) which is of higher order than the O(h2) bias of the LL estimator. For these reasons we recommend the local linear estimator over the Nadaraya-Watson estimator. The asymptotic bias and variance of the LL estimator at the boundary is slightly different than in the interior. The difference is that the bias and variance depend on the moments of the kernel-like function K ∗(u) rather than the original kernel K (u). An interesting question is to find the optimal kernel function for boundary estimation. By the same calculations as for Theorem 19.4 we find that the optimal kernel K ∗(u) minimizes the roughness R ∗ K given the second moment σ2 K ∗ and as argued for Theorem 19.4 this is achieved when K ∗(u) equals a quadratic function in u. Since K ∗(u) is the product of K (u) and a linear function this means that K (u) must be linear in &#124;u&#124;, implying that the optimal kernel K (u) is the Triangular kernel. See Cheng, Fan, and Marron (1997). Calculations similar to those following Theorem 19.4 show that efficiency loss 5 of estimation using the Epanechnikov, Gaussian, and Rectangular kernels are 1%, 1%, and 3%, respectively. 5Measured by root AIMSE. |  |
| Theorem 19.7 | Theorem 19.7 E[CV(h)] = σ2 + IMSEn−1(h) (19.12) where σ2 = E [ e2w(X ) ] . |  |
| Theorem 19.8 | Theorem 19.8 Under Assumption 19.1, ˆmnw(x) − →p m(x) and ˆmLL(x) − →p m(x). A proof for the Nadaraya-Watson estimator is presented in Section 19.26. For the local linear estimator see Fan and Gijbels (1996). |  |
| Theorem 19.9 | Theorem 19.9 Suppose Assumption 19.1 holds. Assume in addition that m′′(x) and f ′(x) are continuous in N , that for some r > 2 and x ∈ N , E [ &#124;e&#124;r &#124;X = x ] ≤ σ < ∞, (19.14) and nh 5 = O(1). (19.15) Then p nh ( ˆmnw(x) − m(x) − h2Bnw(x) ) − → d N ( 0, RK σ2(x) f (x) ) . (19.16) Similarly, p nh ( ˆmLL(x) − m(x) − h2BLL(x) ) − → d N ( 0, RK σ2(x) f (x) ) . A proof for the Nadaraya-Watson estimator appears in Section 19.26. For the local linear estimator see Fan and Gijbels (1996). |  |
| Theorem 19.10 | Theorem 19.10 Under the conditions of Theorem 19.9, and nh 5 = o (1), p nh ( ˆmnw(x) − m(x)) − → d N ( 0, RK σ2(x) f (x) ) p nh ( ˆmLL(x) − m(x)) − → d N ( 0, RK σ2(x) f (x) ) . |  |
| Proposition 19.1 | Proposition 19.1 Let ˆm(x) denote either the Nadarya-Watson or Local Linear estimator of m(x). As n → ∞ and h j → 0 such that n &#124;h&#124;→ ∞, √ n &#124;h&#124; ( ˆm(x) − m(x) − d∑ j =1 h2 j B j (x) ) − → d N ( 0, Rd K σ2(x) f (x) ) . For the Nadaraya-Watson estimator B j (x) = 1 2 ∂2 ∂x2 j m(x) + f (x)−1 ∂ ∂x j f (x) ∂ ∂x j m(x) and for the Local Linear estimator B j (x) = 1 2 ∂2 ∂x2 j m(x). We do not provide regularity conditions or a formal proof but instead refer interested readers to Fan and Gijbels (1996). |  |
| Theorem 19.11 | Theorem 19.11 For vector-valued X the bandwidth which minimizes the AIMSE is of order h ∼ n−1/(4+d). With h ∼ n−1/(4+d) then AIMSE = O ( n−4/(4+d)) . |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
