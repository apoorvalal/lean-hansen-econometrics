# Chapter 3 theorem inventory

## Target chapter
- `chapters/03-the-algebra-of-least-squares.pdf`

## First-pass formalization order

### Layer 1: finite-sample OLS algebra
1. define the sum of squared errors objective
2. define OLS coefficient in closed form under invertibility of `Xᵀ X`
3. define fitted values and residual vector
4. prove the normal equations
5. prove residual orthogonality: `Xᵀ ê = 0`
6. if a constant is in the column span of `X`, derive mean-zero residuals

### Layer 2: projection matrices
7. define hat matrix `P = X (Xᵀ X)⁻¹ Xᵀ`
8. define annihilator matrix `M = I - P`
9. prove `P` symmetric and idempotent
10. prove `M` symmetric and idempotent
11. prove `Ŷ = P Y` and `ê = M Y`
12. prove `P X = X` and `M X = 0`

### Layer 3: orthogonal decomposition / variance algebra
13. prove `Y = Ŷ + ê`
14. prove `⟪Ŷ, ê⟫ = 0`
15. derive finite-sample Pythagorean / sum-of-squares decomposition

### Layer 4: partitioned regression / FWL
16. partition regressors as `[X₁ X₂]`
17. define residual-maker `M₁`
18. prove FWL formula for `β̂₂`
19. prove FWL residual equivalence

## Immediate target
Start with Layer 1 in Lean. Those theorems are the most reusable and should not require importing too much specialized matrix infrastructure beyond basic finite-dimensional linear algebra.

## Strategy note

A desirable route for the FWL theorem is through projection geometry / Gram-Schmidt style decomposition:

- interpret the column spaces of `X₁` and `[X₁ X₂]` as nested subspaces,
- use annihilator/projection operators to partial out the `X₁` component,
- then show the coefficient on `X₂` equals the OLS coefficient from the residualized regression.
