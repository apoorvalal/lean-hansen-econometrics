# Hansen Chapter 2 formalization plan

## Working scope (first pass)

Target chapter:
- `chapters/02-conditional-expectation-and-projection.pdf`

Initial formalization focus:
- the first conditional-expectation backbone before projection geometry:
  1. simple law of iterated expectations
  2. tower property / nested conditional expectations
  3. conditioning theorem / pull-out property
  4. CEF error mean-zero facts and orthogonality

These are the cleanest early results to formalize because Mathlib already has strong conditional-expectation infrastructure.

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

## Later chapter targets (not yet formalized)
- variance decomposition
- conditional expectation as best predictor
- linear projection coefficient existence / orthogonality
- finite-second-moment consequences

## Files
- `HansenEconometrics/Chapter2CondExp.lean` — first formalized theorem chain
- later likely additions:
  - `HansenEconometrics/Chapter2Variance.lean`
  - `HansenEconometrics/Chapter2Projection.lean`
