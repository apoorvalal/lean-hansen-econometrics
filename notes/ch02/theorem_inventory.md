# Hansen Chapter 2 formalization plan

## Working scope

Target chapter:
- `chapters/02-conditional-expectation-and-projection.pdf`

Formalization focus so far:
- the conditional-expectation backbone before projection geometry:
  1. simple law of iterated expectations
  2. tower property / nested conditional expectations
  3. conditioning theorem / pull-out property
  4. CEF error mean-zero facts and orthogonality
  5. conditional-variance / total-variance identities
  6. population-moment algebra for the best linear projection coefficient

These are the cleanest early results to formalize because Mathlib already has strong conditional-expectation infrastructure.

Crosswalk:
- The Chapter 2 LaTeX/Lean side-by-side notes live in [latex_links.md](./latex_links.md).

## Dependency graph

### Level 0: imported Mathlib primitives
- `MeasureTheory.integral_condExp`
- `MeasureTheory.condExp_condExp_of_le`
- `MeasureTheory.condExp_mul_of_aestronglyMeasurable_left`
- `MeasureTheory.condExp_of_stronglyMeasurable`
- `MeasureTheory.condExp_sub`

### Level 1: direct specializations
- **T2.1 (simple LIE)**: `E[E[Y | m]] = E[Y]`
- **T2.2 (tower property)**: `E[E[Y | m₂] | m₁] = E[Y | m₁]` for `m₁ ≤ m₂`
- **T2.3a (conditioning theorem, a.e. version)**:
  `E[g(X)Y | X] = g(X) E[Y|X]`
- **T2.3b (integrated version)**:
  `E[g(X)Y] = E[g(X)E[Y|X]]`

### Level 2: CEF error package
Define
- `e = Y - E[Y | m]`

Then prove:
- **T2.4.1**: `E[e | m] = 0`
- **T2.4.2**: `E[e] = 0`
- **T2.4.4**: for `g` measurable wrt `m`, `E[g e] = 0`

### Level 3: variance package
- **Definitions 2.1-2.2**:
  expected conditional variance as expected squared CEF error
- **T2.8**:
  law of total variance, plus the rearranged decomposition
- reusable consequence:
  `Var[E[Y | m]] ≤ Var[Y]`

### Level 4: linear projection package
- **Definition 2.5 / T2.9 core**:
  `β = QXX⁻¹ QXY`
- population normal equations:
  `QXX β = QXY`
- population orthogonality:
  `QXY - QXX β = 0`
- uniqueness from the normal equations
- quadratic criterion simplification at `β`
- quadratic completion:
  `S(b) = S(β) + (b - β)' QXX (b - β)`
- best-linear-predictor minimization statement
- textbook moment wrapper:
  `β = (E[XX'])⁻¹ E[XY]` minimizes the population criterion
- **T2.10**:
  separating the constant gives
  `α = μY - μX' β`
  and
  `β = var[X]⁻¹ cov(X, Y)`

## Later chapter targets (not yet formalized)
- **T2.5** finite regression-error variance from `E[Y²] < ∞` (PGP has done this in `Chapter2Variance`)
- **T2.6** monotonic decrease of residual variance under larger conditioning sets (PGP has done this in `Chapter2Variance` -- `variance_cefError_antitone`)
- finite-second-moment consequences

## Files
- `HansenEconometrics/Chapter2CondExp.lean` — first formalized theorem chain
- `HansenEconometrics/Chapter2Variance.lean` — conditional-variance / total-variance layer
- `HansenEconometrics/Chapter2LinearProjection.lean` — population linear-projection algebra
