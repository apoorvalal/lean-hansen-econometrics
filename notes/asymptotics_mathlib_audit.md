# Mathlib audit: probability / asymptotics machinery for Hansen Ch 5–7

Audit performed against the Mathlib snapshot vendored in `.lake/packages/mathlib/`.
Goal: decide what to use directly, wrap, or build from scratch as we move from
Chapter 5 (finite-sample classical inference) into Chapter 7 (OLS asymptotics).

## What's already there (use directly)

| Item | File | Declaration |
|---|---|---|
| Convergence in distribution | `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean` | `MeasureTheory.TendstoInDistribution` |
| Convergence in probability / measure | `Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean` | `MeasureTheory.TendstoInMeasure` |
| Slutsky | `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean` | `TendstoInDistribution.prodMk_of_tendstoInMeasure_const`, `continuous_comp_prodMk_of_tendstoInMeasure_const` |
| Continuous Mapping Theorem (in distribution) | `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean` | `TendstoInDistribution.continuous_comp` |
| Strong Law of Large Numbers (real & Banach-valued, iid) | `Mathlib/Probability/StrongLaw.lean` | `strong_law_ae`, `strong_law_Lp` |
| Univariate Lindeberg-Lévy CLT | `Mathlib/Probability/CentralLimitTheorem.lean` | `tendstoInDistribution_inv_sqrt_mul_sum_sub` |
| Real Gaussian | `Mathlib/Probability/Distributions/Gaussian/Real.lean` | `gaussianReal m v` |
| Multivariate Gaussian | `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean` | `multivariateGaussian μ S`, `stdGaussian E` |
| `HasGaussianLaw` predicate | `Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Def.lean` | `HasGaussianLaw X P`, `IsGaussian` |
| Gaussian uncorrelated ⇒ independent | `Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Independence.lean` | `ProbabilityTheory.HasGaussianLaw.indepFun_of_covariance_eq_zero`, `iIndepFun_of_covariance_eq_zero` |
| Gamma distribution | `Mathlib/Probability/Distributions/Gamma.lean` | `gammaMeasure a r` |

Caveats worth noting:

- `TendstoInDistribution` requires the image space to be `OpensMeasurableSpace`.
- Slutsky requires `IsCountablyGenerated` on the filter and same underlying probability space.
- `multivariateGaussian` is parameterized over `EuclideanSpace ℝ ι` for finite `ι`; covariance must be PSD.
- The Gaussian independence lemma uses `covarianceBilinDual` (an abstract bilinear-form formulation); applying it to concrete linear maps `A`, `B` will require translating to a matrix-form statement.

## What's missing (must build or wrap)

1. **Weak Law of Large Numbers** — only the strong law is in Mathlib. Trivial wrap (a.s. convergence ⇒ convergence in measure).
2. **Named χ²(k) distribution** — only `gammaMeasure` is present. χ²(k) = Γ(k/2, 1/2). Define a wrapper plus the basic API (mean, variance, support).
3. **Multivariate Lindeberg-Lévy CLT** — only the univariate version is in Mathlib. Cleanest port: Cramér-Wold reduction (every linear projection converges in distribution ⇒ joint converges).
4. **Delta Method** — not present as a named theorem. Straightforward via CMT + Fréchet derivative; not blocking until late Ch 7.
5. **Quadratic form of standard normal under symmetric idempotent → χ²(rank)** — not present. **Load-bearing missing piece for Chapter 5.** Construction: spectral decomposition of `M` (eigenvalues 0 / 1, `M = U diag(1,…,1,0,…,0) Uᵀ`), giving `eᵀ M e = ∑_{i ≤ r} (Uᵀe)_iˆ²`, a sum of `r` iid standard normal squares = χ²(r). Needs χ²(k) defined first, plus the additivity / sum-of-squares lemmas (Gamma additivity is likely already in Mathlib — worth a quick confirm).

## Phase 2 spike findings (Ch 7 consistency)

Second pass, focused on the chain behind Theorem 7.1 (`β̂ₙ →ₚ β`).

**Present and usable as-is:**

| Item | File:line | Notes |
|---|---|---|
| `ProbabilityTheory.strong_law_ae` | `Mathlib/Probability/StrongLaw.lean:788` | Works in any Banach space `E` (real or vector); consumes `Pairwise ((· ⟂ᵢ[μ] ·) on X)` and `IdentDistrib`. |
| `MeasureTheory.tendstoInMeasure_of_tendsto_ae` | `Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:223` | Needs `[IsFiniteMeasure μ]` and `AEStronglyMeasurable`. Bridges SLLN → convergence-in-measure. |
| `exists_seq_tendstoInMeasure_atTop_iff` | `Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:339` | Characterizes `TendstoInMeasure ... atTop` by every-subsequence-has-a.s.-convergent-subsubsequence. This is the lever for a CMT wrapper. |
| `NormedRing.inverse_continuousAt` | `Mathlib/Analysis/Normed/Ring/Units.lean` (general Banach algebra) | For matrix inversion at an invertible matrix: specialize to `Matrix n n ℝ` with a Banach-algebra-compatible norm. |
| `Continuous.matrix_mulVec` | `Mathlib/Topology/Instances/Matrix.lean:169` | Direct continuity of `(A, v) ↦ A *ᵥ v`. Closes the matrix-vector step of the CMT chain. |
| Scoped matrix norms | `Mathlib/Analysis/Matrix/Normed.lean` | `Matrix.Norms.Frobenius`, `Matrix.Norms.L2Operator`, `Matrix.Norms.Elementwise` — pick one scope to unlock the Banach structure needed by `strong_law_ae`. |

**Not in Mathlib — must wrap:**

1. **CMT for `TendstoInMeasure`.** There is no `TendstoInMeasure.continuous_comp`. `TendstoInMeasure.comp` only composes with the *index* filter, not with a function on the codomain. The subsequence-characterization (`exists_seq_tendstoInMeasure_atTop_iff`) gives a clean route: every subsequence has an a.s.-convergent sub-subsequence, continuity lifts a.s. convergence, and the iff closes the loop.

2. **Pi-decomposition of `TendstoInMeasure`.** No `TendstoInMeasure μ f l g ↔ ∀ j, TendstoInMeasure μ (·.j) l g.j` for `Fintype`-indexed Pi types. Needs a short bespoke proof; the `←` direction composes through `Finset`-sum of ball measures, the `→` direction is component-projection continuity + CMT wrapper above.

3. **Arithmetic of `TendstoInMeasure`.** No named `TendstoInMeasure.add`, `.mul`, `.smul`. Once the generic CMT wrapper lands, `.add` etc. follow by continuity of `+`, `·`, `•`.

4. **No WLLN named lemma.** But `tendstoInMeasure_of_tendsto_ae ∘ strong_law_ae` is a direct one-liner.

**Architectural decision:** build the missing utilities as a standalone `HansenEconometrics/AsymptoticUtils.lean`, then use them in `Chapter7Asymptotics.lean`. The CMT wrapper + Pi-decomposition are reusable well beyond Hansen and are reasonable upstream-PR candidates for Mathlib later.

**Matrix norm scope choice:** the `Elementwise` norm (sup of entry norms) is the most natural match for entry-wise WLLN arguments. But since the SLLN chain works in any Banach space, Frobenius is equally fine. Pick one globally at the top of `Chapter7Asymptotics.lean` via `open scoped Matrix.Norms.Frobenius` (or Elementwise) — consistency matters more than the choice itself.

### Phase 2 utilities landed (`HansenEconometrics/AsymptoticUtils.lean`)

| Utility | Lean name | Role |
|---|---|---|
| CMT for convergence in measure along `atTop` | `HansenEconometrics.tendstoInMeasure_continuous_comp` | For continuous `h : E → F` and `f n →ₚ g`, yields `h ∘ f n →ₚ h ∘ g`. Proved via the subsequence characterization. |
| Pi-decomposition (joint ⇒ coordinate) | `HansenEconometrics.TendstoInMeasure.pi_apply` | `f n →ₚ g` on `∀ b, X b` implies each `(f n · b) →ₚ (g · b)`. Follows from `edist_le_pi_edist`. |
| Pi-decomposition (coordinate ⇒ joint) | `HansenEconometrics.tendstoInMeasure_pi` | Coordinatewise convergence in measure on a `Fintype`-indexed Pi type gives joint convergence. Uses `Finset.le_sup_iff` and finite-union measure bound. |
| WLLN for Banach-valued iid | `HansenEconometrics.tendstoInMeasure_wlln` | Direct composition of `strong_law_ae` and `tendstoInMeasure_of_tendsto_ae`. Works for scalar, vector-, and matrix-valued targets on any Banach space. |

### What's still missing for Theorem 7.1

The remaining chain to close `β̂ₙ →ₚ β`:

1. **iid-sample representation.** Decide the shape: per-observation regressor `X : ℕ → Ω → (k → ℝ)` plus error `e : ℕ → Ω → ℝ`, with the pair packaged as an iid sequence. Define empirical moments `Q̂ₙ(ω) = (1/n) ∑ Xᵢ Xᵢᵀ(ω)` and `g̑ₙ(ω) = (1/n) ∑ eᵢ Xᵢ(ω)` directly from the sum (no design-matrix stacking needed for the consistency argument).

2. **Matrix-valued WLLN for `Q̂ₙ →ₚ Q`.** Apply `tendstoInMeasure_wlln` to `Xᵢ Xᵢᵀ : Ω → Matrix k k ℝ` under an appropriate matrix Banach norm (Frobenius or Elementwise). Requires `Integrable (X 0 · X 0ᵀ)` — i.e., `E[Xᵢ Xᵢᵀ]` exists entry-wise, which follows from `Xᵢⱼ ∈ L²`.

3. **Vector-valued WLLN for `g̑ₙ →ₚ 0`.** Same pattern on `fun ω => eᵢ ω • Xᵢ ω : Ω → (k → ℝ)`, under `E[Xᵢ eᵢ] = 0`.

4. **CMT for matrix inversion.** Apply `tendstoInMeasure_continuous_comp` with `h = Ring.inverse` (or `Matrix.inv`) at `Q`. The continuity input comes from `NormedRing.inverse_continuousAt` specialized to matrices. Care: `Ring.inverse` agrees with `⅟` only on units, and at non-invertible matrices returns 0 — need to argue the sample is eventually in the invertible neighborhood, or restrict the result to "on the set where `Q̂ₙ` is invertible."

5. **CMT for matrix-vector multiplication.** Compose `Q̂ₙ⁻¹ *ᵥ g̑ₙ →ₚ Q⁻¹ *ᵥ 0 = 0` via `Continuous.matrix_mulVec` and `tendstoInMeasure_continuous_comp` on the joint pair `(Q̂ₙ⁻¹, g̑ₙ)`. This also needs a "jointly continuous map" variant or a two-step reduction.

6. **Deterministic ⇒ probabilistic bridge.** The `Chapter7Asymptotics.lean` identity `β̂ₙ - β = Q̂ₙ⁻¹ *ᵥ g̑ₙ` is expressed using the `Matrix (Fin n) k ℝ` design matrix. To use it with iid-indexed sample moments, either (a) prove that for every `ω` with invertible `Q̂ₙ(ω)`, `betaHatₙ(ω) = β + Q̂ₙ⁻¹(ω) *ᵥ g̑ₙ(ω)` directly from the sum-of-outer-products form, or (b) connect via a stacking equivalence `Matrix (Fin n) k ℝ(ω) = stack (X · ω)`. Option (a) avoids the stacking plumbing entirely.

Step 6 is the most delicate piece architecturally — choose (a) to keep the asymptotics argument independent of `Matrix (Fin n) k ℝ` entirely, at the cost of re-proving the algebraic identity for sample-moment-expressed `betaHatₙ`.

## Proposed order of attack

1. Define `chiSquared k` as a `gammaMeasure` wrapper + minimal API.
2. Prove (or import) sum-of-squares-of-standard-normals = χ²(k).
3. Prove the symmetric-idempotent quadratic-form theorem (uses our existing `rank_eq_natCast_trace_of_isHermitian_idempotent`).
4. Finish Chapter 5: chi-square law for `s²` (1–3 above), independence of `β̂` and `s²` (almost free given Mathlib's Gaussian-independence lemma — main work is setting up the joint-Gaussian structure for `(Pe, Me)`), exact t, CIs / tests.
5. Asymptotics wrappers in this order: WLLN (trivial), multivariate CLT (Cramér-Wold), delta method (later, only when Ch 7 functional-of-parameters needs it).
6. Begin Chapter 7 with the iid-sample bridge that lifts our matrix-formulation OLS to a sample-size-indexed sequence.
