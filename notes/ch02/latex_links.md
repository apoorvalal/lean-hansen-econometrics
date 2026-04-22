# Chapter 2 LaTeX / Lean Crosswalk

This file is a Chapter 2-only crosswalk between textbook-style mathematical statements and the Lean
theorems currently formalized in this repo.

Conventions:
- All links in this file are relative.
- The left column gives a compact LaTeX rendering of the formalized statement.
- The right column gives the corresponding Lean conclusion, not the full proof script.
- Reusable helper definitions and bridge lemmas live in
  [ProbabilityUtils.lean](../../HansenEconometrics/ProbabilityUtils.lean).
- Public Chapter 2 probability theorems point to
  [Chapter2CondExp.lean](../../HansenEconometrics/Chapter2CondExp.lean) and
  [Chapter2Variance.lean](../../HansenEconometrics/Chapter2Variance.lean).
- Backend sigma-algebra results remain linked in notes when they are the main proof substrate.
- This file avoids raw HTML `<pre>` blocks, since many Markdown math renderers do not parse LaTeX
  inside HTML or code/pre blocks.

## Textbook-numbered results

### T2.1 Simple Law of Iterated Expectations

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L491)
- [Backend sigma-algebra theorem](../../HansenEconometrics/Chapter2CondExp.lean#L18)

| LaTeX | Lean conclusion |
| --- | --- |
| $\int \mathbb{E}[Y \mid \mathcal{G}] \, d\mu = \int Y \, d\mu$ | <code>∫ ω, (μ[Y &#124; m]) ω ∂μ = ∫ ω, Y ω ∂μ</code> |

Notes:
- This remains a backend sigma-algebra theorem.

### T2.2 Tower Property

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L543)
- [Variable-facing theorem](../../HansenEconometrics/Chapter2CondExp.lean)
- [Backend sigma-algebra theorem](../../HansenEconometrics/Chapter2CondExp.lean#L26)
- [Older `X₁, X₂` wrapper](../../HansenEconometrics/Chapter2CondExp.lean#L37)

| LaTeX | Lean conclusion |
| --- | --- |
| $\mathbb{E}[\mathbb{E}[Y \mid \mathcal{G}_2] \mid \mathcal{G}_1] = \mathbb{E}[Y \mid \mathcal{G}_1]$ | <code>condExpOn μ (condExpOn μ Y X₂) X₁ =ᵐ[μ] condExpOn μ Y X₁</code> |

Notes:
- The public theorem is variable-facing and assumes `conditioningSpace X₁ ≤ conditioningSpace X₂`.
- The backend sigma-algebra theorem remains the proof substrate.

### T2.3 Conditioning Theorem

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L587)
- [Variable-facing a.e. form](../../HansenEconometrics/Chapter2CondExp.lean)
- [Variable-facing integrated form](../../HansenEconometrics/Chapter2CondExp.lean)
- [Backend sigma-algebra form](../../HansenEconometrics/Chapter2CondExp.lean#L54)

| LaTeX | Lean conclusion |
| --- | --- |
| $\mathbb{E}[gY \mid X] = g \, \mathbb{E}[Y \mid X]$ | <code>condExpOn μ (fun ω => g ω * Y ω) X =ᵐ[μ] fun ω => g ω * condExpOn μ Y X ω</code> |
| $\int gY \, d\mu = \int g \, \mathbb{E}[Y \mid X] \, d\mu$ | <code>∫ ω, g ω * Y ω ∂μ = ∫ ω, g ω * condExpOn μ Y X ω ∂μ</code> |

Notes:
- The backend theorem is still sigma-algebra based.

### T2.4 Properties of the CEF Error

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L632)
- [T2.4.1 variable-facing theorem](../../HansenEconometrics/Chapter2CondExp.lean)
- [T2.4.2 variable-facing theorem](../../HansenEconometrics/Chapter2CondExp.lean)
- [T2.4.4 variable-facing theorem](../../HansenEconometrics/Chapter2CondExp.lean)
- [Backend sigma-algebra proofs](../../HansenEconometrics/Chapter2CondExp.lean#L78)

| LaTeX | Lean conclusion |
| --- | --- |
| $\mathbb{E}[e \mid X] = 0$ | <code>condExpOn μ (cefErrorOn μ Y X) X =ᵐ[μ] 0</code> |
| $\int e \, d\mu = 0$ | <code>∫ ω, cefErrorOn μ Y X ω ∂μ = 0</code> |
| $\int g(X) e \, d\mu = 0$ | <code>∫ ω, g ω * cefErrorOn μ Y X ω ∂μ = 0</code> |

### T2.5 Finite Regression-error Variance

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L691)
- [Backend theorem](../../HansenEconometrics/Chapter2Variance.lean#L28)
- [Public CEF error wrapper](../../HansenEconometrics/ProbabilityUtils.lean)

| LaTeX | Lean conclusion |
| --- | --- |
| $\mathbb{E}[Y^2] < \infty \Longrightarrow \mathbb{E}[e^2] < \infty$ | <code>MemLp (cefError μ Y m) 2 μ</code> |

Notes:
- The theorem currently lives in the backend sigma-algebra layer.
- The public variable-facing error object is `cefErrorOn μ Y X`.

### T2.6 More Information Weakly Reduces Residual Variance

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L711)
- [Variable-facing theorem](../../HansenEconometrics/Chapter2Variance.lean)
- [Backend sigma-algebra theorem](../../HansenEconometrics/Chapter2Variance.lean#L76)

| LaTeX | Lean conclusion |
| --- | --- |
| $\operatorname{Var}(Y - \mathbb{E}[Y \mid \mathcal{G}_2]) \le \operatorname{Var}(Y - \mathbb{E}[Y \mid \mathcal{G}_1])$ | <code>residualVarOn μ Y X₂ ≤ residualVarOn μ Y X₁</code> |

Notes:
- The public theorem is variable-facing and assumes `conditioningSpace X₁ ≤ conditioningSpace X₂`.
- The backend theorem remains stated directly in sigma-algebra language.

### T2.7 Conditional Expectation as Best Predictor

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L778)
- [Variable-facing theorem](../../HansenEconometrics/Chapter2CondExp.lean)
- [Backend sigma-algebra theorem](../../HansenEconometrics/Chapter2CondExp.lean#L175)

| LaTeX | Lean conclusion |
| --- | --- |
| $\mathbb{E}[(Y - g(X))^2] \ge \mathbb{E}[(Y - \mathbb{E}[Y \mid X])^2]$ | <code>∫ ω, (Y ω - condExpOn μ Y X ω)^2 ∂μ ≤ ∫ ω, (Y ω - g ω)^2 ∂μ</code> |

Notes:
- The backend sigma-algebra theorem is still available when a later proof genuinely needs it.

### T2.8 Law of Total Variance

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L847)
- [Variable-facing law of total variance](../../HansenEconometrics/Chapter2Variance.lean)
- [Explained-variance bound](../../HansenEconometrics/Chapter2Variance.lean)
- [Backend sigma-algebra theorem](../../HansenEconometrics/Chapter2Variance.lean#L35)

| LaTeX | Lean conclusion |
| --- | --- |
| $\operatorname{Var}(Y) = \mathbb{E}[\operatorname{Var}(Y \mid X)] + \operatorname{Var}(\mathbb{E}[Y \mid X])$ | <code>μ[condVarOn μ Y X] + Var[condExpOn μ Y X; μ] = Var[Y; μ]</code> |

Notes:
- The explained-variance corollary is also available as
  `variance_condExpOn_le_variance`, while the main RV-facing variance-decomposition theorem is
  `law_total_variance_rv`.

### T2.9 Linear Projection Model

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L1448)
- [Normal equations](../../HansenEconometrics/Chapter2LinearProjection.lean#L25)
- [Orthogonality](../../HansenEconometrics/Chapter2LinearProjection.lean#L34)
- [Criterion at `β`](../../HansenEconometrics/Chapter2LinearProjection.lean#L52)
- [Quadratic completion](../../HansenEconometrics/Chapter2LinearProjection.lean#L62)
- [Minimization](../../HansenEconometrics/Chapter2LinearProjection.lean#L96)
- [Moment wrapper](../../HansenEconometrics/Chapter2LinearProjection.lean#L108)

| LaTeX | Lean conclusion |
| --- | --- |
| $Q_{XX} \beta = Q_{XY}$ | <code>QXX *ᵥ linearProjectionBeta QXX QXY = QXY</code> |
| $Q_{XY} - Q_{XX} \beta = 0$ | <code>QXY - QXX *ᵥ linearProjectionBeta QXX QXY = 0</code> |
| $S(\beta) = Q_{YY} - \beta' Q_{XY}$ | <code>linearProjectionMSE QXX QXY QYY (linearProjectionBeta QXX QXY) = QYY - linearProjectionBeta QXX QXY ⬝ᵥ QXY</code> |
| $S(b) = S(\beta) + (b - \beta)' Q_{XX} (b - \beta)$ | <code>linearProjectionMSE QXX QXY QYY b =</code><br><code>linearProjectionMSE QXX QXY QYY (linearProjectionBeta QXX QXY)</code><br><code>+ (b - linearProjectionBeta QXX QXY) ⬝ᵥ (QXX *ᵥ (b - linearProjectionBeta QXX QXY))</code> |
| $S(\beta) \le S(b)$ | <code>linearProjectionMSE QXX QXY QYY (linearProjectionBeta QXX QXY) ≤ linearProjectionMSE QXX QXY QYY b</code> |
| If $EXX = E[XX']$, $EXY = E[XY]$, and $EY2 = E[Y^2]$, then $S(\beta) \le S(b)$ | <code>linearProjectionMSE EXX EXY EY2 (linearProjectionBeta EXX EXY) ≤ linearProjectionMSE EXX EXY EY2 b</code> |

Notes:
- The last row is the textbook moment wrapper for the minimization statement.
- Lean also includes the uniqueness result [`linearProjectionBeta_eq_of_MSE_eq`](../../HansenEconometrics/Chapter2LinearProjection.lean#L119).

### T2.10 Regression Coefficients

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L1765)
- [Intercept formula](../../HansenEconometrics/Chapter2LinearProjection.lean#L229)
- [Slope formula](../../HansenEconometrics/Chapter2LinearProjection.lean#L258)

| LaTeX | Lean conclusion |
| --- | --- |
| $\alpha = \mu_Y - \mu_X' \beta$ | <code>α = ∫ ω, Y ω ∂μ - meanVec μ X ⬝ᵥ β</code> |
| $\beta = \operatorname{var}[X]^{-1} \operatorname{cov}(X, Y)$ | <code>β = linearProjectionBeta (covMat μ X) (covVec μ X Y)</code> |

Notes:
- The slope formula is a covariance-form corollary of the earlier normal-equations theorem.

## Lean-only bridge results

These theorems are not direct textbook labels, but they are the key translation lemmas between
Hansen's notation and the Lean formalization.

- [`condExp_apply`](../../HansenEconometrics/ProbabilityUtils.lean):
  coordinate projection commutes with conditional expectation.
- [`condExp_apply_apply`](../../HansenEconometrics/ProbabilityUtils.lean):
  entrywise conditional expectation for finite-dimensional arrays.
- [`integral_apply`](../../HansenEconometrics/ProbabilityUtils.lean):
  coordinate projection commutes with integration.
- [`integral_apply_apply`](../../HansenEconometrics/ProbabilityUtils.lean):
  entrywise integration for finite-dimensional arrays.
- [`condExpL2_minimal`](../../HansenEconometrics/Chapter2CondExp.lean#L137):
  $\lVert Y - \mathbb{E}[Y \mid m] \rVert_2 \le \lVert Y - g \rVert_2$ in the $L^2$ projection language
  used by Mathlib.
- [`integral_condVar_eq_integral_cefError_sq`](../../HansenEconometrics/Chapter2Variance.lean#L16):
  $\int \operatorname{Var}(Y \mid \mathcal{G}) \, d\mu = \int e^2 \, d\mu$.
- [`linearProjectionBeta_eq_of_normal_equations`](../../HansenEconometrics/Chapter2LinearProjection.lean#L41):
  solves $Q_{XX} b = Q_{XY}$ as $b = Q_{XX}^{-1} Q_{XY}$.
- [`integral_dotProduct_eq_meanVec_dotProduct`](../../HansenEconometrics/ProbabilityUtils.lean):
  $\int X' b \, d\mu = (\int X \, d\mu)' b$.
- [`covVec_dotProduct_eq_covMat_mulVec`](../../HansenEconometrics/ProbabilityUtils.lean):
  $\operatorname{cov}(X, X' b) = \operatorname{covMat}(X) b$.
- [`covVec_linearProjectionModel`](../../HansenEconometrics/Chapter2LinearProjection.lean#L191):
  $\operatorname{cov}(X, \alpha + X' \beta + e) = \operatorname{covMat}(X)\beta +
  \operatorname{cov}(X, e)$.
