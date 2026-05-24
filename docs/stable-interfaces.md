# Stable Interfaces for Econometrics Formalization

This note explains a design pattern for keeping the Hansen formalization usable as
the project moves from finite-sample algebra into probability, asymptotics, and
inference.

The short version:

> A stable interface is a named Lean structure that records the mathematical
> capability a later theorem needs, while hiding the particular proof route used
> to establish that capability.

For example, a theorem about Wald tests usually should not care whether a score
CLT came from iid sampling, a triangular array, martingale differences, or a
high-level assumption. It should care that the relevant score statistic has the
right limiting distribution.

## Why This Matters

In textbook econometrics, authors routinely say things like:

- assume a law of large numbers applies,
- assume a central limit theorem applies,
- assume the covariance estimator is consistent,
- assume the estimator admits an asymptotic linear expansion.

Those are not shortcuts in the bad sense. They are the correct abstraction level
for many theorems. Lean, however, forces every hidden side condition to become
explicit somewhere: measurability, integrability, finite-dimensional topology,
almost-everywhere equality, nonsingularity, totalization, and so on.

Stable interfaces are how we prevent those details from leaking into every
chapter-facing theorem.

## The Layering Pattern

Use three layers.

### 1. Public Theorem Layer

This layer contains the results a reader would cite as Hansen theorem wrappers:
OLS consistency, asymptotic normality, t-statistic limits, Wald limits,
restricted least squares, minimum distance, and so on.

These theorems should consume named mathematical interfaces.

Example shape:

```lean
theorem ols_wald_limit
    (hlin : AsymptoticallyLinearEstimator mu bhat beta root score A)
    (hclt : ScoreCLT mu score Omega)
    (hcov : CovarianceEstimatorConsistent mu Vhat V)
    (hpos : IsUnit V.det) :
    ...
```

The theorem statement is then about econometrics, not about the mechanics of one
chosen proof of a WLLN or CLT.

### 2. Interface Layer

This layer defines reusable structures such as:

- `GramConsistency`
- `ScoreCLT`
- `AsymptoticallyLinearEstimator`
- `CovarianceEstimatorConsistent`
- `FeasibleStandardErrorConsistent`
- `SandwichCovarianceLimit`

These structures should be stable across chapters and proof strategies.

Example:

```lean
structure ScoreCLT
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (score : Nat -> Omega -> k -> Real)
    (Omegamat : Matrix k k Real) where
  aemeasurable : forall n, AEMeasurable (score n) mu
  limit :
    TendstoInDistribution
      score atTop
      gaussianScoreLimit Omegamat
      (fun _ => mu)
      (multivariateGaussian 0 Omegamat)
```

The exact target type will depend on the surrounding definitions, but the point
is the same: the structure states the reusable capability.

### 3. Constructor Layer

This layer proves that concrete assumptions imply the stable interfaces.

Example shape:

```lean
theorem scoreCLT_of_iid_moments
    (h : IidScoreMomentConditions mu X e) :
    ScoreCLT mu (score X e) Omega := by
  ...

theorem scoreCLT_of_projection_clts
    (h : ProjectionScoreCLTConditions mu X e Omega) :
    ScoreCLT mu (score X e) Omega := by
  ...
```

The constructor layer is where raw assumptions belong:

- independence,
- identical distribution,
- finite moments,
- coordinate measurability,
- projection CLTs,
- Lindeberg conditions,
- uniform integrability,
- bounded-in-probability side conditions.

The public theorem layer should not need to know which constructor was used.

## What Makes an Interface Stable?

A stable interface should satisfy most of these checks.

### It Names a Reusable Econometric Concept

Good candidates:

- "the sample Gram matrix converges to `Q`"
- "the score statistic has a Gaussian limit"
- "the estimator is asymptotically linear"
- "the covariance estimator converges to `V`"
- "the standard error is consistent and positive in the limit"

Less stable candidates:

- "this fourth-moment scalar summand is integrable"
- "this particular residual-substitution cross-weight is bounded in probability"
- "this finite list of measurability facts discharges one theorem"

The less stable facts may be necessary, but they usually belong in constructor
or proof-facing structures.

### It Can Have More Than One Constructor

This is the most useful test.

If the same interface could be proved from iid assumptions, triangular-array
assumptions, cluster assumptions, or simply assumed as a high-level limit fact,
then it is probably stable.

For example:

```lean
ScoreCLT
  <- iid finite-moment constructor
  <- triangular-array Lindeberg constructor
  <- martingale-difference constructor
  <- high-level projection-CLT constructor
```

The downstream OLS theorem should consume `ScoreCLT`, not the iid constructor.

### Its Fields Are Inputs, Not Conclusions

Do not make a structure that assumes exactly the theorem you are trying to
prove.

Bad:

```lean
structure OLSAsymptoticNormalityAssumptions where
  conclusion :
    TendstoInDistribution
      (fun n omega => scaledError root bhat beta n omega)
      atTop Z (fun _ => mu) nu
```

Better:

```lean
structure AsymptoticallyLinearEstimator
    (mu : Measure Omega)
    (bhat : Nat -> Omega -> k -> Real)
    (beta : k -> Real)
    (root : Nat -> Real)
    (score : Nat -> Omega -> k -> Real)
    (A : Matrix k k Real) where
  expansion :
    TendstoInMeasure mu
      (fun n omega => scaledError root bhat beta n omega - A *v score n omega)
      atTop
      (fun _ => 0)
```

This does not assume asymptotic normality. It states the reusable linear
representation from which asymptotic normality follows once a score CLT is
available.

### It Is Not Tied to One Theorem Number

Textbook-numbered aliases are useful for compatibility and citation, but the
core interface should have a mathematical name.

Good pattern already used in this repo:

```lean
structure LeastSquaresConsistencyConditions ...

abbrev SampleMomentAssumption71 := LeastSquaresConsistencyConditions
```

The reusable name is `LeastSquaresConsistencyConditions`; the numbered name is a
textbook crosswalk.

### It Hides Proof Plumbing

Fields such as `AEMeasurable`, `Integrable`, and `Pairwise IndepFun` are often
necessary somewhere. But if every public theorem takes them directly, the public
API becomes brittle.

Prefer:

```lean
theorem wald_limit
    (hlin : AsymptoticallyLinearEstimator ...)
    (hcov : CovarianceEstimatorConsistent ...)
    (hclt : ScoreCLT ...) :
    ...
```

over:

```lean
theorem wald_limit
    (hX_meas : forall i, AEStronglyMeasurable (X i) mu)
    (he_meas : forall i, AEStronglyMeasurable (e i) mu)
    (hindep1 : Pairwise ...)
    (hindep2 : Pairwise ...)
    (hmoment1 : Integrable ...)
    (hmoment2 : Integrable ...)
    ... :
    ...
```

The latter shape may appear in constructors, but it should not be the main
surface for theorem-facing econometrics.

## Suggested Interfaces for This Repository

The current repo already has useful condition packages:

- `LeastSquaresConsistencyConditions`
- `ErrorVarianceConsistencyConditions`
- `ScoreCLTConditions`
- `RobustCovarianceConsistencyConditions`
- `RobustFeasibleHCMomentConditions`
- `MultivariateLindebergCLTConditions`

The next useful step is not to replace these immediately. Instead, add a small
number of more stable interfaces above them.

### `GramConsistency`

Purpose: package convergence of the sample Gram matrix and nonsingularity of
the population target.

Likely fields:

```lean
structure GramConsistency
    (mu : Measure Omega)
    (Qhat : Nat -> Omega -> Matrix k k Real)
    (Q : Matrix k k Real) where
  Qhat_measurable : forall n, AEMeasurable (Qhat n) mu
  Qhat_tendsto :
    TendstoInMeasure mu Qhat atTop (fun _ => Q)
  Q_nonsing : IsUnit Q.det
```

Useful for:

- OLS consistency,
- feasible inverse arguments,
- sandwich covariance,
- restricted least squares,
- minimum distance.

### `ScoreCLT`

Purpose: package the limiting distribution of the normalized score.

Likely fields:

```lean
structure ScoreCLT
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (score : Nat -> Omega -> k -> Real)
    (Omegamat : Matrix k k Real) where
  score_measurable : forall n, AEMeasurable (score n) mu
  score_tendsto :
    TendstoInDistribution
      score atTop
      (gaussianLimit Omegamat)
      (fun _ => mu)
      (multivariateGaussian 0 Omegamat)
```

Useful constructors:

- from current `ScoreCLTConditions`,
- from `MultivariateLindebergCLTConditions`,
- later from martingale, mixing, cluster, or high-level assumptions.

### `AsymptoticallyLinearEstimator`

Purpose: express that an estimator is equal to a linear transform of a score,
up to an `o_p(1)` remainder after scaling.

Likely fields:

```lean
structure AsymptoticallyLinearEstimator
    (mu : Measure Omega)
    (bhat : Nat -> Omega -> k -> Real)
    (beta : k -> Real)
    (root : Nat -> Real)
    (score : Nat -> Omega -> k -> Real)
    (A : Matrix k k Real) where
  bhat_measurable : forall n, AEMeasurable (bhat n) mu
  expansion :
    TendstoInMeasure mu
      (fun n omega => scaledError root bhat beta n omega - A *v score n omega)
      atTop
      (fun _ => 0)
```

Useful for:

- OLS asymptotic normality,
- nonlinear delta method,
- restricted least squares,
- minimum distance,
- Wald/t/CI wrappers.

### `CovarianceEstimatorConsistent`

Purpose: package convergence of a covariance estimator to a target covariance.

Likely fields:

```lean
structure CovarianceEstimatorConsistent
    (mu : Measure Omega)
    (Vhat : Nat -> Omega -> Matrix k k Real)
    (V : Matrix k k Real) where
  Vhat_measurable : forall n, AEMeasurable (Vhat n) mu
  Vhat_tendsto :
    TendstoInMeasure mu Vhat atTop (fun _ => V)
```

Optional separate interfaces can record positivity or invertibility:

```lean
structure PositiveCovarianceLimit (V : Matrix k k Real) where
  symmetric : V.transpose = V
  nonsing : IsUnit V.det
```

Useful constructors:

- HC0 consistency,
- HC1 consistency,
- HC2 consistency,
- HC3 consistency,
- homoskedastic covariance consistency,
- cluster-robust covariance consistency later.

### `StudentizedStatisticReady`

Purpose: package the exact ingredients needed for a t-statistic or Wald statistic
limit without exposing the underlying estimator/covariance proof.

This may be useful after the lower-level interfaces settle.

Likely fields:

```lean
structure StudentizedStatisticReady
    (mu : Measure Omega)
    (T : Nat -> Omega -> Real) where
  measurable : forall n, AEMeasurable (T n) mu
  tendsto_standardNormal :
    TendstoInDistribution T atTop standardNormalRV (fun _ => mu) gaussianReal
```

Use sparingly. This is close to the final theorem shape, so it should only be
introduced when many CI and test wrappers share it.

## Existing Patterns to Preserve

### Variable-Facing Probability APIs

The repo already prefers variable-based APIs such as `condExpOn`, rather than
forcing all public statements to mention raw sigma-algebras. This is the right
pattern.

Sigma-algebra lemmas should remain available as backend tools, while chapter
theorems use variable-facing wrappers.

### Star and OrZero Totalization

The Chapter 7 `Star` / `OrZero` split is a good example of a stable interface
decision.

- `Star` definitions are proof engines: total, convenient, and compatible with
  asymptotic convergence.
- `OrZero` definitions are textbook-facing wrappers: they agree with ordinary
  OLS on nonsingular samples.
- Bridge lemmas connect them.

This pattern should continue for estimators that must be total random variables
in asymptotic statements.

### Numbered Assumption Aliases

Using aliases such as `SampleMomentAssumption71` is helpful for crosswalks.
Keep the reusable core name mathematical, and use numbered aliases for the
textbook inventory.

## How to Decide Where a New Fact Goes

Ask these questions.

### Is This Fact Used Across Chapters or Estimators?

If yes, consider a stable interface or a reusable helper module.

Examples:

- convergence of a sample covariance matrix,
- Slutsky transfer from an asymptotic-linear representation,
- covariance estimator consistency,
- Gaussian quadratic-form limit.

### Is This Fact Only Needed to Prove One Interface?

If yes, keep it as a constructor lemma or private helper.

Examples:

- a specific coordinatewise fourth-moment domination bound,
- a particular residual-substitution cross-weight expansion,
- a one-off measurability proof for a matrix-valued statistic.

### Would a Textbook Reader Recognize the Assumption?

If yes, it may belong in the public interface layer.

If the assumption reads like Lean bookkeeping, it probably belongs below the
interface layer.

### Could the Proof Strategy Change Without Changing Later Theorems?

If yes, put the stable result in an interface and make the proof strategy a
constructor.

For example, if a future Mathlib theorem gives a better CLT, downstream OLS
theorems should not need to change. Only the constructor proving `ScoreCLT`
should change.

## Recommended Workflow

When formalizing a new theorem cluster:

1. State the theorem first at the econometric interface level.
2. Identify the exact stable capabilities it needs.
3. Reuse existing interfaces if possible.
4. If a new interface is needed, give it a mathematical name.
5. Prove the theorem from the interface.
6. Add constructors from current textbook or proof-engine assumptions.
7. Add numbered aliases only as crosswalks.
8. Keep one-off proof plumbing private unless another file genuinely needs it.

## Warning Signs

A design probably needs another interface if:

- public theorem signatures are dominated by measurability and integrability
  arguments;
- the same bundle of assumptions is copied into several theorems;
- a theorem about inference directly mentions HC0/HC1/HC2/HC3 residual
  expansion details;
- changing from iid to triangular-array assumptions would require rewriting
  many downstream theorem statements;
- a structure name contains a theorem number but no mathematical concept;
- a structure field is essentially the theorem conclusion.

## Practical Goal

The goal is not to hide rigor. The goal is to put rigor at the right layer.

Econometric theorem wrappers should read like econometrics. Constructor lemmas
should do the work of deriving those assumptions from iid sampling, moments,
Lindeberg conditions, or whatever primitive assumptions are currently available.
Backend helpers should absorb Mathlib-specific measure-theoretic plumbing.

This gives the project a sustainable path:

```text
raw measure/probability facts
        |
        v constructors
stable econometric interfaces
        |
        v theorem wrappers
textbook-facing Hansen results
```

That is the formalization analogue of allowing a Euclidean-geometry theorem to
use the Euclidean toolkit without reproving the whole geometry inside every
single result.
