# Chapter 11 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- The textbook statement column is cleaned from the local excerpt where possible.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch11_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 11.1 | Theorem 11.1 Under Assumption 7.2, pn (ˆβ − β ) − → d N ( 0,V β ) where V β = Q −1ΩQ −1 and Q = E [ X ′ X ] =   E [ X1X ′ 1 ] 0 · · · 0 ... ... ... 0 0 · · · E [ Xm X ′ m ]  . |  |
| Theorem 11.2 | Theorem 11.2 Under Assumptions 7.2 and 7.3, pn (ˆθ − θ ) − → d N(0,V θ) where V θ = R ′V βR and R = ∂ ∂β r ( β )′. |  |
| Theorem 11.3 | Theorem 11.3 Under Assumption 7.2, n ˆV ˆβ − →p V β and n ˆV 0 ˆβ − →p V 0 β. |  |
| Theorem 11.4 | Theorem 11.4 Under Assumption 7.2 and (11.8) p n (ˆβsur − β ) − → d N ( 0,V ∗ β ) where V ∗ β = ( E [ X ′ Σ−1X ])−1 . |  |
| Theorem 11.5 | Theorem 11.5 Under Assumption 7.2 and (11.8) V ∗ β = ( E [ X ′ Σ−1X ])−1 ≤ ( E [ X ′ X ])−1 E [ X ′ ΣX ] ( E [ X ′ X ])−1 = V β and thus ˆβsur is asymptotically more efficient than ˆβols. |  |
| Theorem 11.6 | Theorem 11.6 Under Assumption 7.2 and (11.8) n ˆV ˆβ − →p V β. |  |
| Theorem 11.7 | Theorem 11.7 The MLE for the reduced rank model (11.19) under e ∼ N(0, Σ) is given as follows. Let ˜Y and ˜X be the residual matrices from multivariate regression of Y and X on Z , respectively. Then ˆGmle = {v1, ...,vr }, the generalized eigenvectors of ˜X ′ ˜Y ( ˜Y ′ ˜Y )−1 Y ′ ˜X with respect to ˜X ′ ˜X corresponding to the r largest eigenvalues ˆλj . ˆAmle, ˆC mle and ˆΣmle are obtained by the least squares regression Yi = ˆAmle ˆG ′ mleXi + ˆC ′ mleZi + ˆei ˆΣmle = 1 n n∑ i =1 ˆei ˆe′ i . Let ˜E be the residual matrix from a multivariate regression of Y on X and Z . Then ˆA⊥ equals the generalized eigenvectors of ˜E ′ ˜E with respect to ˜Y ′ ˜Y corresponding to the m − r smallest eigenvalues. The maximized likelihood equals ℓn = m 2 ( n log(2π) − 1 ) − n 2 log ( det ( ˜Y ′ ˜Y )) − n 2 r∑ j =1 log ( 1 − ˆλj ) . An R package for reduced rank regression is “RRR” . I am unaware of a Stata command. |  |
| Theorem 11.8 | Theorem 11.8 The principal components of X are U j = h′ j X , where h j is the eigenvector of Σ associated with the j t h ordered eigenvalue λj of Σ. Another way to see the PCA construction is as follows. Since Σ is symmetric the spectral decomposition (Theorem A.3) states that Σ = H D H′ where H = [h1,..., hk] and D = diag(d1,..., dk) are the eigenvectors and eigenvalues of Σ. Since Σ is positive semi-definite the eigenvalues are real, non-negative, and ordered d1 ≥ d2 ≥ · · · ≥dk. Let U = (U1,..., Uk) be the principal components of X . By Theorem 11.8, U = H ′X . The covariance matrix of U is var[U ] = var [ H ′X ] = H ′ΣH = D which is diagonal. This shows that var [ U j ] = d j and the principal components are mutually uncorrelated. The relative variance contribution of the j t h principal component is d j /tr (Σ). Principal components are sensitive to the scaling ofX . Consequently, it is recommended to first scale each element of X to have mean zero and unit variance. In this case Σ is a correlation matrix. The sample principal components are obtained by replacing the unknowns by sample estimators. Let ˆΣ be the sample covariance or correlation matrix and ˆh1, ˆh2,..., ˆhk its ordered eigenvectors. The sample principal components are ˆh′ j Xi . |  |
| Theorem 11.9 | Theorem 11.9 The least squares estimator of the factor model (11.23) under the normalization n−1 ∑n i =1 ˆFi ˆF ′ i = I r has the following solution: 1. Let ˆD = diag [ ˆd1,..., ˆdr ] and ˆH = [ˆh1, ...,ˆhr ] be the firstr eigenvalues and eigenvectors of the sample covariance matrix ˆΣ. 2. ˆΛ = ˆH ˆD 1/2 . 3. ˆFi = ˆD −1/2 ˆH ′ Xi . |  |
| Theorem 11.10 | Theorem 11.10 If Yi ∼ N ( µ, Σ ) are independent then ˆΣ ∼ Wm ( n − 1, 1 n−1 Σ ) . The following manipulation is useful. |  |
| Theorem 11.11 | Theorem 11.11 If W ∼ Wm (n, Σ) then for m × 1 α, ( α′W −1α )−1 ∼ χ2 n−m+1. α′Σ−1α To prove this, note that without loss of generality we can take Σ = I m and α′α = 1. Let H be m × m orthonormal with first row equal to α. so that H α = ( 1 0 ) . Since the distribution of Y and Y H are identical we can without loss of generality set α = ( 1 0 ) . Partition Y = [Y 1, Y 2] where Y 1 is n × 1, Y 2 is n × (m − 1), and they are independent. Then ( α′W −1α )−1 = ( ( 1 0 )( Y ′ 1Y 1 Y ′ 1Y 2 Y ′ 2Y 1 Y ′ 2Y 2 )−1 ( 1 0 ))−1 = Y ′ 1Y 1 − Y ′ 1Y 2 ( Y ′ 2Y 2 )−1 Y ′ 2Y 1 = Y ′ 1M 2Y 1 ∼ χ2 n−(m−1) where M 2 = I m−1 − Y 2 ( Y ′ 2Y 2 )−1 Y ′ 2. The final distributional equality holds conditional on Y 2 by the same argument in the proof of Theorem 5.7. Since this does not depend on Y 2 it is the unconditional distribution as well. This establishes the stated result. To test hypotheses about µ a classical statistic is known as Hotelling’sT 2: T 2 = n ( Y − µ )′ ˆΣ−1 ( Y − µ ) . |  |
| Theorem 11.12 | Theorem 11.12 If Y ∼ N ( µ, Σ ) then T 2 ∼ m (n − m)(n − 1) F (m,n − m) a scaled F distribution. To prove this recall thatY is independent of ˆΣ. Apply Theorem 11.11 with α = Y − µ. Conditional on Y and using the fact that ˆΣ ∼ Wm ( n − 1, 1 n−1 Σ ) , n T 2 = (( Y − Σ )′ ˆΣ−1 ( Y − Σ ))−1 ∼ χ2 n−1−m+1( Y − µ )′ ( 1 n−1 Σ )−1 ( Y − µ ) ∼ n(n − 1) χ2 n−m χ2 m . Since the two chi-square variables are independent, this is the stated result. A very interesting property of this result is that the T 2 statistic is a multivariate quadratric form in normal random variables, yet it has the exact F distribution. _____________________________________________________________________________________________. |  |

## Notes

- Rows marked `TODO: fill from source` need better source text than the current local excerpt provides.
- The Lean column is intentionally left blank until there is actual formalization to link.
