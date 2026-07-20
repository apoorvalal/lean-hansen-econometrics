import HansenEconometrics.Chapter14CLT
import HansenEconometrics.ErgodicTheory.MeanErgodic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Chapter 14: discharging the MDS CLT characteristic-function core (bounded, constant
conditional variance)

This file is a research attempt at *proving* the analytic field `charFun_tendsto` of
`ProbabilityTheory.MDSCLTConditions` (Hansen Theorem 14.11) in the most tractable nontrivial
case: a strictly stationary martingale difference sequence that is **uniformly bounded**
(`|uₜ| ≤ C` a.s.) with **constant conditional variance** (`E[uₜ² | ℱₜ₋₁] = σ²` a.s.). The
constant conditional variance is exactly what removes the ergodic-theorem dependency of the
general case: the per-step comparison target `a = 1 - σ²θ²/2` is then a genuine constant, so the
telescoping collapses to a clean geometric `aⁿ` rather than a random product needing Birkhoff
normalization of `(1/n)∑ σₜ²(ω)`.

## Proof architecture (Billingsley 1961 / Hall–Heyde Thm 3.2, constant-variance specialization)

Fix `s` and `n`; write `θ = s/√n`, `Sₖ = u₁ + ⋯ + uₖ`, `ψₖ = E[exp(iθ Sₖ)]`, and
`a = 1 - σ²θ²/2`. Successive conditioning on `ℱₖ` gives the linear recursion
`ψₖ₊₁ = a·ψₖ + εₖ` with `|εₖ| ≤ |θ|³C³/6`, because
`εₖ = ∫ e^{iθ Sₖ}·(e^{iθ uₖ₊₁} − a)` and `e^{iθ u} − a = rem + iθ u − (θ²/2)(u² − σ²)` splits
into a pointwise Taylor remainder `rem` (bounded by `|θu|³/6`) plus two terms whose integrals
vanish by conditioning on `ℱₖ` (MDS mean-zero and constant conditional variance). The abstract
recursion then gives `‖ψₙ − aⁿ‖ ≤ n·|θ|³C³/6 = |s|³C³/(6√n) → 0`, while
`aⁿ = (1 − σ²s²/2n)ⁿ → exp(−σ²s²/2)`; a squeeze delivers `charFun → exp(−σ²s²/2)`.

## Main declarations

* `ProbabilityTheory.charFun_tendsto_of_bounded_constCondVar` — the analytic
  field proved from the honest hypotheses in the constant-conditional-variance case.
* `ProbabilityTheory.MDSCLTConditions.of_bounded_constCondVar` — the full bundle constructed from
  the honest hypotheses, upgrading Theorem 14.11 to discharged in the constant-variance case.
* `ProbabilityTheory.charFun_tendsto_of_bounded_ergodic` — **the analytic field for the bounded
  stationary–ergodic case (Hall–Heyde variance hypotheses)**, proved via the McLeish exact
  martingale `Mₙ = exp(iθSₙ)/Pₙ`. This is the main result of the general-case assembly.
* `ProbabilityTheory.MDSCLTConditions.of_bounded_ergodic` — **Hansen Theorem 14.11 discharged for a
  bounded stationary–ergodic MDS** with a stationary–ergodic conditional-variance process: the full
  bundle is constructed, so `MDSCLTConditions.central_limit` delivers convergence in distribution.
  The only remaining delta to Hansen's literal statement is unboundedness (a truncation layer,
  future work).

Self-contained, Mathlib-shaped pieces (upstreamable, no repository dependency):

* `ProbabilityTheory.norm_sub_pow_le_of_recursion` — the abstract scalar comparison: a sequence
  `ψ` with `ψ₀ = 1` and per-step defect `‖ψₖ₊₁ − a·ψₖ‖ ≤ B` (with `‖a‖ ≤ 1`) satisfies
  `‖ψₙ − aⁿ‖ ≤ n·B`.
* `ProbabilityTheory.tendsto_one_sub_pow_exp` — `(1 − v s²/2n)ⁿ → exp(−v s²/2)`.

## The general (random conditional variance) case — committed ingredients

The constant-variance telescoping above collapses to a geometric `aⁿ` only because `a = 1 − vθ²/2`
is a constant. With a genuinely random `σₜ²(ω) = E[uₜ² | ℱₜ₋₁](ω)` the scalar recursion no longer
closes (`∫ exp(iθSₖ)·σₖ₊₁² ≠ σₖ₊₁²·ψₖ` when `σₖ₊₁²` is random and `exp(iθSₖ)` oscillates), so the
argument must become multiplicative/random. The formalizable route is McLeish's exact martingale:
with `Pₙ = ∏ₖ E[exp(iθuₖ) | ℱₖ₋₁]` and `Mₙ = exp(iθSₙ)/Pₙ`, the process `Mₙ` is a genuine complex
martingale with `E[Mₙ] = 1` exactly, and `E[exp(iθSₙ)] = E[Mₙ·Pₙ] → exp(−σ̄²s²/2)` once `Pₙ → c`
in `L¹`. This file lands the self-contained analytic ingredients of that route (all
Mathlib-shaped, kernel-clean). What is **not** yet assembled is the definitional wiring: forming
`Pₙ = ∏ₖ φₖ` and `Mₙ = exp(iθSₙ)/Pₙ` as concrete random variables, the reverse-induction
`E[Mₙ] = 1`, the `Pₙ → c` `L¹`-convergence chain, and the final `E[exp(iθSₙ)] = E[MₙPₙ]` gluing.

Decorrelation and pull-out (the reduction skeleton):

* `ProbabilityTheory.tendsto_integral_mul_of_tendsto_integral_norm_sub` — the **decorrelation
  lemma**, the analytic heart of the reduction: `∫ Mₙ = 1`, `‖Mₙ‖ ≤ K`, and `Qₙ → c` in `L¹` give
  `∫ Mₙ·Qₙ → c`.
* `ProbabilityTheory.condExp_cmul_of_stronglyMeasurable_left` — the **complex
conditional-expectation pull-out** `E[f·g | ℱ] = f·E[g | ℱ]` for `ℱ`-measurable complex `f`, from
the bilinear `condExp_bilin_of_aestronglyMeasurable_left` (the a.e.-`ℱ`-measurable-left version of
which powers the `E[Mₙ] = 1` step). This shows the complex conditional expectation the martingale
step needs is available in the pinned Mathlib.
* `ProbabilityTheory.tendsto_eLpNorm_exp_neg_average_sub` — the **ergodic normalization**:
  `exp(−λ·(1/n)∑ₜ vₜ) → exp(−λ·E[v₀])` in `L¹` for a nonnegative ergodic process `v`, via the `L¹`
  mean ergodic theorem (Hansen 14.9) and the `1`-Lipschitz bound on `x ↦ exp(−x)`.

Per-piece analytic cores (bounded MDS with Hall–Heyde stationary-ergodic conditional variance):

* `ProbabilityTheory.condExp_cos_bounds` / `ProbabilityTheory.norm_condExp_cexp_bounds` — **Piece
D**: the per-step factor `φ = E[exp(iθw) | ℱ]` has real part `E[cos(θw)|ℱ] ≥ 1 − θ²C²/2` and modulus
in `[1 − θ²C²/2, 1]` a.e., so it is nonvanishing for `θ²C² < 2`.
* `ProbabilityTheory.exp_neg_two_mul_le_one_sub` / `ProbabilityTheory.norm_prod_ge_of_ae_norm_ge` —
  **Piece E** uniform bound: `exp(−2x) ≤ 1 − x` on `[0,1/2]` gives `‖Pₙ‖ = ∏‖φₖ‖ ≥ exp(−s²C²)`
  uniformly in `n` (with `x = s²C²/2n`), i.e. `‖Mₙ‖ ≤ exp(s²C²)`, the decorrelation lemma's `K`.
* `ProbabilityTheory.norm_condExp_cexp_sub_taylor_le` — **Piece C** analytic heart: the conditional
  second-order Taylor expansion `‖E[exp(iθw)|ℱ] − (1 − (θ²/2)E[w²|ℱ])‖ ≤ |θ|³C³/6` a.e. (MDS kills
  the linear term; `E[w²|ℱ]` supplies the conditional variance).
* `ProbabilityTheory.norm_prod_sub_prod_le_of_norm_le_one` — **Piece C** comparison engine:
  `‖∏ fₖ − ∏ gₖ‖ ≤ ∑ ‖fₖ − gₖ‖` for factors of modulus `≤ 1`, which (with
  `Complex.norm_exp_sub_one_sub_id_le`) reduces `‖Pₙ − exp(∑ aₖ)‖` to `∑ ‖aₖ‖² ≤ K²/n → 0`.

These ingredients are now **fully assembled** into `charFun_tendsto_of_bounded_ergodic` and
`MDSCLTConditions.of_bounded_ergodic` (the Hall–Heyde analogue of the constant-variance bundle): the
concrete random variables `φₖ = E[exp(iθu_{k+1})|ℱₖ]`, `Pₙ = ∏ₖ φₖ`, `Mₙ = exp(iθSₙ)/Pₙ` are
defined (`mcPhi`, `mcProd`, `mcM`), the reverse-induction `E[Mₙ] = 1` is proved
(`mcM_integral_eq_one`), the `L¹` chain `Pₙ → exp(−Var·s²/2)` is proved
(`mcProd_tendsto_integral_norm_sub`), and the decorrelation glue closes the characteristic-function
limit. See the final section for what remains (unboundedness only).
-/

open MeasureTheory Filter Complex
open scoped Topology

namespace ProbabilityTheory

/-! ### Abstract, Mathlib-shaped ingredients (no repository dependency) -/

/-- **Abstract scalar comparison lemma.** If a complex sequence `ψ` starts at `ψ₀ = 1`, the
scalar `a` has `‖a‖ ≤ 1`, and every one-step defect is bounded, `‖ψₖ₊₁ − a·ψₖ‖ ≤ B` with
`0 ≤ B`, then `ψ` stays within `n·B` of the geometric sequence `aⁿ`:
`‖ψₙ − aⁿ‖ ≤ n·B`. This is the deterministic core of the characteristic-function telescoping;
the probabilistic content is entirely in verifying the hypotheses. Proved by induction, peeling
`ψₙ₊₁ − aⁿ⁺¹ = (ψₙ₊₁ − a·ψₙ) + a·(ψₙ − aⁿ)`. -/
theorem norm_sub_pow_le_of_recursion {ψ : ℕ → ℂ} {a : ℂ} {B : ℝ}
    (ha : ‖a‖ ≤ 1) (h0 : ψ 0 = 1)
    (hrec : ∀ k, ‖ψ (k + 1) - a * ψ k‖ ≤ B) (n : ℕ) :
    ‖ψ n - a ^ n‖ ≤ n * B := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    have hstep : ψ (n + 1) - a ^ (n + 1)
        = (ψ (n + 1) - a * ψ n) + a * (ψ n - a ^ n) := by ring
    have h2 : ‖a‖ * ‖ψ n - a ^ n‖ ≤ 1 * ((n : ℝ) * B) :=
      mul_le_mul ha ih (norm_nonneg _) zero_le_one
    rw [hstep]
    calc ‖(ψ (n + 1) - a * ψ n) + a * (ψ n - a ^ n)‖
        ≤ ‖ψ (n + 1) - a * ψ n‖ + ‖a * (ψ n - a ^ n)‖ := norm_add_le _ _
      _ ≤ B + 1 * ((n : ℝ) * B) := add_le_add (hrec n) (by rw [norm_mul]; exact h2)
      _ = ((n : ℕ) + 1 : ℝ) * B := by ring
      _ = ((n + 1 : ℕ) : ℝ) * B := by push_cast; ring

/-- **The geometric limit.** For real `v, s`, `(1 − v s²/2n)ⁿ → exp(−v s²/2)`. Immediate from
`Real.tendsto_one_add_div_pow_exp` at `t = −v s²/2`. -/
theorem tendsto_one_sub_pow_exp (v s : ℝ) :
    Tendsto (fun n : ℕ => (1 - v * s ^ 2 / (2 * (n : ℝ))) ^ n) atTop
      (𝓝 (Real.exp (-(v * s ^ 2) / 2))) := by
  refine (Real.tendsto_one_add_div_pow_exp (-(v * s ^ 2) / 2)).congr (fun n => ?_)
  congr 1
  ring

/-- **Piece E helper (uniform lower-bound arithmetic).** On `[0, 1/2]`, `exp(−2x) ≤ 1 − x`.
Proof: `exp(2x) ≥ 1 + 2x` (`Real.add_one_le_exp`), so `exp(−2x) = 1/exp(2x) ≤ 1/(1+2x)`, and
`1/(1+2x) ≤ 1 − x` because `(1 − x)(1 + 2x) = 1 + x − 2x² ≥ 1` exactly when `x ≤ 1/2`. Used to
turn the per-factor modulus lower bound `1 − s²C²/2n` into the uniform product lower bound
`|Pₙ| ≥ exp(−s²C²)`. -/
theorem exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-(2 * x)) ≤ 1 - x := by
  have h12 : (0 : ℝ) < 1 + 2 * x := by linarith
  have he : 1 + 2 * x ≤ Real.exp (2 * x) := by
    have := Real.add_one_le_exp (2 * x); linarith
  calc Real.exp (-(2 * x)) = 1 / Real.exp (2 * x) := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / (1 + 2 * x) := one_div_le_one_div_of_le h12 he
    _ ≤ 1 - x := by
        rw [div_le_iff₀ h12]
        nlinarith [mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ 1 - 2 * x)]

/-- **Piece C telescoping bound.** For complex sequences whose factors are all bounded by `1` in
modulus, the difference of the finite products is controlled by the sum of the factor differences:
`‖∏_{k<n} f k − ∏_{k<n} g k‖ ≤ ∑_{k<n} ‖f k − g k‖`. Proof by induction, peeling the top factor
via `A·fₙ − B·gₙ = (A − B)·fₙ + B·(fₙ − gₙ)` and bounding `‖fₙ‖ ≤ 1`, `‖∏ g‖ ≤ 1`. This is the
product-vs-exponential comparison engine: with `f = Pₙ`'s factors and `g k = exp(a k)` (both of
modulus `≤ 1`), it reduces `‖Pₙ − exp(∑ aₖ)‖` to `∑ ‖1 + aₖ − exp aₖ‖ ≤ ∑ ‖aₖ‖²`. -/
theorem norm_prod_sub_prod_le_of_norm_le_one {f g : ℕ → ℂ}
    (hf : ∀ k, ‖f k‖ ≤ 1) (hg : ∀ k, ‖g k‖ ≤ 1) (n : ℕ) :
    ‖(∏ k ∈ Finset.range n, f k) - ∏ k ∈ Finset.range n, g k‖
      ≤ ∑ k ∈ Finset.range n, ‖f k - g k‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hgprod : ‖∏ k ∈ Finset.range n, g k‖ ≤ 1 := by
      rw [norm_prod]
      calc ∏ k ∈ Finset.range n, ‖g k‖ ≤ ∏ _k ∈ Finset.range n, (1 : ℝ) :=
            Finset.prod_le_prod (fun k _ => norm_nonneg _) (fun k _ => hg k)
        _ = 1 := by simp
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.sum_range_succ]
    calc ‖(∏ k ∈ Finset.range n, f k) * f n - (∏ k ∈ Finset.range n, g k) * g n‖
        = ‖((∏ k ∈ Finset.range n, f k) - ∏ k ∈ Finset.range n, g k) * f n
            + (∏ k ∈ Finset.range n, g k) * (f n - g n)‖ := by ring_nf
      _ ≤ ‖((∏ k ∈ Finset.range n, f k) - ∏ k ∈ Finset.range n, g k) * f n‖
            + ‖(∏ k ∈ Finset.range n, g k) * (f n - g n)‖ := norm_add_le _ _
      _ = ‖(∏ k ∈ Finset.range n, f k) - ∏ k ∈ Finset.range n, g k‖ * ‖f n‖
            + ‖∏ k ∈ Finset.range n, g k‖ * ‖f n - g n‖ := by rw [norm_mul, norm_mul]
      _ ≤ (∑ k ∈ Finset.range n, ‖f k - g k‖) * 1 + 1 * ‖f n - g n‖ :=
          add_le_add
            (mul_le_mul ih (hf n) (norm_nonneg _)
              (Finset.sum_nonneg fun k _ => norm_nonneg _))
            (mul_le_mul_of_nonneg_right hgprod (norm_nonneg _))
      _ = (∑ k ∈ Finset.range n, ‖f k - g k‖) + ‖f n - g n‖ := by ring

section Probabilistic

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℤ m} {u : ℤ → Ω → ℝ}

/-- **Decorrelation lemma (analytic heart of the McLeish reduction).** If `Mₙ` are complex random
variables with unit mean (`∫ Mₙ = 1`) that are uniformly bounded (`‖Mₙ‖ ≤ K` a.e.), and the complex
random variables `Qₙ` converge to a constant `c` in `L¹` (`∫ ‖Qₙ − c‖ → 0`), then the paired means
converge: `∫ Mₙ·Qₙ → c`. Proof: `∫ Mₙ Qₙ − c = ∫ Mₙ Qₙ − c·∫ Mₙ = ∫ Mₙ (Qₙ − c)`, and
`‖∫ Mₙ (Qₙ − c)‖ ≤ ∫ ‖Mₙ‖·‖Qₙ − c‖ ≤ K·∫ ‖Qₙ − c‖ → 0`.

This is the step that, in the general (random conditional variance) MDS CLT, converts the exact
martingale mean identity `∫ Mₙ = 1` (with `Mₙ = exp(iθSₙ)/Pₙ` and `Pₙ = ∏ E[exp(iθuₖ)|ℱₖ₋₁]`)
together with `Pₙ → exp(−σ̄²s²/2)` in `L¹` into the characteristic-function limit
`∫ exp(iθSₙ) = ∫ Mₙ Pₙ → exp(−σ̄²s²/2)`. It carries no repository dependency and is Mathlib-shaped.
-/
theorem tendsto_integral_mul_of_tendsto_integral_norm_sub
    {M Q : ℕ → Ω → ℂ} {c : ℂ} {K : ℝ}
    (hM_int : ∀ n, Integrable (M n) P) (hQ_int : ∀ n, Integrable (Q n) P)
    (hMQ_int : ∀ n, Integrable (fun ω => M n ω * Q n ω) P)
    (hM_mean : ∀ n, ∫ ω, M n ω ∂P = 1)
    (hM_bdd : ∀ n, ∀ᵐ ω ∂P, ‖M n ω‖ ≤ K)
    (hQ : Tendsto (fun n => ∫ ω, ‖Q n ω - c‖ ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, M n ω * Q n ω ∂P) atTop (𝓝 c) := by
  have hcore : ∀ n, ‖(∫ ω, M n ω * Q n ω ∂P) - c‖ ≤ K * ∫ ω, ‖Q n ω - c‖ ∂P := by
    intro n
    have hM_aesm : AEStronglyMeasurable (M n) P := (hM_int n).aestronglyMeasurable
    have hcM_int : Integrable (fun ω => c * M n ω) P := (hM_int n).const_mul c
    have hQc_int : Integrable (fun ω => Q n ω - c) P := (hQ_int n).sub (integrable_const c)
    have hMc_int : Integrable (fun ω => M n ω * (Q n ω - c)) P :=
      hQc_int.bdd_mul hM_aesm (hM_bdd n)
    have hcMint_eq : ∫ ω, c * M n ω ∂P = c * ∫ ω, M n ω ∂P := integral_const_mul c (M n)
    have hstep1 : (∫ ω, M n ω * Q n ω ∂P) - c = ∫ ω, M n ω * (Q n ω - c) ∂P := by
      have hc : (∫ ω, M n ω * Q n ω ∂P) - c
          = (∫ ω, M n ω * Q n ω ∂P) - ∫ ω, c * M n ω ∂P := by
        rw [hcMint_eq, hM_mean n, mul_one]
      rw [hc, ← integral_sub (hMQ_int n) hcM_int]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      ring
    rw [hstep1]
    calc ‖∫ ω, M n ω * (Q n ω - c) ∂P‖
        ≤ ∫ ω, ‖M n ω * (Q n ω - c)‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, K * ‖Q n ω - c‖ ∂P := by
          refine integral_mono_ae hMc_int.norm (hQc_int.norm.const_mul K) ?_
          filter_upwards [hM_bdd n] with ω hω
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right hω (norm_nonneg _)
      _ = K * ∫ ω, ‖Q n ω - c‖ ∂P := integral_const_mul K _
  have hbound : Tendsto (fun n => K * ∫ ω, ‖Q n ω - c‖ ∂P) atTop (𝓝 0) := by
    simpa using hQ.const_mul K
  have hnorm : Tendsto (fun n => ‖(∫ ω, M n ω * Q n ω ∂P) - c‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) hcore hbound
  have hsub : Tendsto (fun n => (∫ ω, M n ω * Q n ω ∂P) - c) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  simpa using hsub.add_const c

omit [IsProbabilityMeasure P] in
/-- **Complex conditional-expectation pull-out.** For a complex `f` that is `ℱ(j)`-strongly
measurable and a complex integrable `g` with `f·g` integrable, the `ℱ(j)`-measurable factor pulls
out: `E[f·g | ℱ(j)] = f·E[g | ℱ(j)]` a.e. This is the complex analogue of the real
`condExp_mul_of_stronglyMeasurable_left`, obtained from the general bilinear pull-out
`condExp_bilin_of_aestronglyMeasurable_left` with the ℝ-bilinear complex multiplication
`ContinuousLinearMap.mul ℝ ℂ`. It is the missing ingredient behind the exact-martingale identity of
the general MDS CLT — the conditional characteristic-function step
`E[exp(iθSₙ) | ℱₙ₋₁] = exp(iθSₙ₋₁)·E[exp(iθuₙ) | ℱₙ₋₁]` — showing that the complex conditional
expectation needed there is available in the pinned Mathlib. -/
theorem condExp_cmul_of_stronglyMeasurable_left {j : ℤ} {f g : Ω → ℂ}
    (hf : StronglyMeasurable[ℱ j] f) (hfg : Integrable (fun ω => f ω * g ω) P)
    (hg : Integrable g P) :
    P[fun ω => f ω * g ω | ℱ j] =ᵐ[P] fun ω => f ω * P[g | ℱ j] ω := by
  have hfg' : Integrable (fun ω => (ContinuousLinearMap.mul ℝ ℂ) (f ω) (g ω)) P := by
    simpa only [ContinuousLinearMap.mul_apply'] using hfg
  have hB := condExp_bilin_of_aestronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
    hf.aestronglyMeasurable hfg' hg
  simpa only [ContinuousLinearMap.mul_apply'] using hB

/-- **Piece D core (real conditional cosine bound).** For a real integrable `w` with `|w| ≤ C`
a.e., the conditional expectation of `cos(θ w)` is two-sidedly controlled a.e.:
`1 − θ²C²/2 ≤ E[cos(θ w) | ℱ j] ≤ 1`. The lower bound is the quadratic cosine estimate
`cos x ≥ 1 − x²/2` (`Real.one_sub_sq_div_two_le_cos`) with `(θw)² ≤ θ²C²`, pushed through
`condExp_mono` (the constant lower bound conditions to itself); the upper bound is `cos ≤ 1`
pushed the same way. This is the real part of the McLeish per-step factor `E[exp(iθw) | ℱ j]`,
and its lower bound `1 − θ²C²/2` is what keeps the factor's modulus uniformly away from `0`. -/
theorem condExp_cos_bounds {j : ℤ} {w : Ω → ℝ} {C θ : ℝ}
    (hw_int : Integrable w P) (hbdd : ∀ᵐ ω ∂P, |w ω| ≤ C) :
    (∀ᵐ ω ∂P, 1 - θ ^ 2 * C ^ 2 / 2 ≤ P[fun ω => Real.cos (θ * w ω) | ℱ j] ω)
      ∧ (∀ᵐ ω ∂P, P[fun ω => Real.cos (θ * w ω) | ℱ j] ω ≤ 1) := by
  have hcos_int : Integrable (fun ω => Real.cos (θ * w ω)) P := by
    refine Integrable.of_bound
      (Real.continuous_cos.comp_aestronglyMeasurable (hw_int.aestronglyMeasurable.const_mul θ))
      1 (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
  refine ⟨?_, ?_⟩
  · have hle : (fun _ : Ω => 1 - θ ^ 2 * C ^ 2 / 2) ≤ᵐ[P] fun ω => Real.cos (θ * w ω) := by
      filter_upwards [hbdd] with ω hω
      have h1 : 1 - (θ * w ω) ^ 2 / 2 ≤ Real.cos (θ * w ω) :=
        Real.one_sub_sq_div_two_le_cos (x := θ * w ω)
      have hwsq : w ω ^ 2 ≤ C ^ 2 := by
        rw [← sq_abs (w ω)]; exact pow_le_pow_left₀ (abs_nonneg _) hω 2
      have h2 : (θ * w ω) ^ 2 ≤ θ ^ 2 * C ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left hwsq (sq_nonneg θ)
      linarith
    have hmono := condExp_mono (m := ℱ j) (integrable_const (1 - θ ^ 2 * C ^ 2 / 2)) hcos_int hle
    have hconst : P[fun _ : Ω => 1 - θ ^ 2 * C ^ 2 / 2 | ℱ j] = fun _ => 1 - θ ^ 2 * C ^ 2 / 2 :=
      condExp_const (ℱ.le j) _
    filter_upwards [hmono] with ω hω; rwa [hconst] at hω
  · have hle : (fun ω => Real.cos (θ * w ω)) ≤ᵐ[P] fun _ : Ω => (1 : ℝ) :=
      Eventually.of_forall fun ω => Real.cos_le_one _
    have hmono := condExp_mono (m := ℱ j) hcos_int (integrable_const 1) hle
    have hconst : P[fun _ : Ω => (1 : ℝ) | ℱ j] = fun _ => 1 := condExp_const (ℱ.le j) _
    filter_upwards [hmono] with ω hω; rwa [hconst] at hω

/-- **The McLeish per-step factor's modulus bounds.** For a real integrable `w` with `|w| ≤ C`
a.e., the complex conditional characteristic value `φ = E[exp(iθ w) | ℱ j]` has modulus in
`[1 − θ²C²/2, 1]` a.e. The upper bound is conditional Jensen
(`‖E[f|ℱ]‖ ≤ E[‖f‖|ℱ] = E[1|ℱ] = 1`, using `‖exp(iθw)‖ = 1`); the lower bound is
`‖φ‖ ≥ Re φ = E[cos(θw)|ℱ] ≥ 1 − θ²C²/2` (`Complex.re_le_norm`,
`ContinuousLinearMap.comp_condExp_comm` for `reCLM`, and `condExp_cos_bounds`). This makes `φ`
nonvanishing when `θ²C² < 2` and, taking products, bounds `Pₙ = ∏ φ` between `(1 − θ²C²/2)ⁿ` and
`1`. -/
theorem norm_condExp_cexp_bounds {j : ℤ} {w : Ω → ℝ} {C θ : ℝ}
    (hw_int : Integrable w P) (hbdd : ∀ᵐ ω ∂P, |w ω| ≤ C) :
    (∀ᵐ ω ∂P, 1 - θ ^ 2 * C ^ 2 / 2
        ≤ ‖P[fun ω => Complex.exp (((θ * w ω : ℝ) : ℂ) * Complex.I) | ℱ j] ω‖)
      ∧ (∀ᵐ ω ∂P,
        ‖P[fun ω => Complex.exp (((θ * w ω : ℝ) : ℂ) * Complex.I) | ℱ j] ω‖ ≤ 1) := by
  set f : Ω → ℂ := fun ω => Complex.exp (((θ * w ω : ℝ) : ℂ) * Complex.I) with hfdef
  have hf_norm : ∀ ω, ‖f ω‖ = 1 := fun ω => Complex.norm_exp_ofReal_mul_I _
  have hf_aesm : AEStronglyMeasurable f P :=
    Complex.continuous_exp.comp_aestronglyMeasurable
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable
        (hw_int.aestronglyMeasurable.const_mul θ)).mul_const _)
  have hf_int : Integrable f P :=
    Integrable.of_bound hf_aesm 1 (Eventually.of_forall fun ω => (hf_norm ω).le)
  refine ⟨?_, ?_⟩
  · -- Lower bound via `Re φ = E[cos|ℱ]`.
    have hfeq : (Complex.reCLM ∘ f) = fun ω => Real.cos (θ * w ω) := by
      funext ω
      simp only [Function.comp_apply, Complex.reCLM_apply, hfdef]
      exact exp_ofReal_mul_I_re _
    have hcomm := Complex.reCLM.comp_condExp_comm (m := ℱ j) hf_int
    rw [hfeq] at hcomm
    obtain ⟨hcos_ge, _⟩ := condExp_cos_bounds (ℱ := ℱ) (j := j) hw_int hbdd
    filter_upwards [hcomm, hcos_ge] with ω hcomm_ω hcos_ω
    simp only [Function.comp_apply, Complex.reCLM_apply] at hcomm_ω
    calc 1 - θ ^ 2 * C ^ 2 / 2 ≤ P[fun ω => Real.cos (θ * w ω) | ℱ j] ω := hcos_ω
      _ = (P[f | ℱ j] ω).re := hcomm_ω.symm
      _ ≤ ‖P[f | ℱ j] ω‖ := Complex.re_le_norm _
  · -- Upper bound via conditional Jensen.
    have hjensen : (fun ω => ‖P[f | ℱ j] ω‖) ≤ᵐ[P] P[fun ω => ‖f ω‖ | ℱ j] := by
      exact AEStronglyMeasurable.norm_condExp_le hf_aesm
    have hnorm_eq : P[(fun ω => ‖f ω‖) | ℱ j] =ᵐ[P] fun _ => (1 : ℝ) := by
      have h1 : (fun ω => ‖f ω‖) =ᵐ[P] fun _ => (1 : ℝ) := Eventually.of_forall hf_norm
      calc P[(fun ω => ‖f ω‖) | ℱ j] =ᵐ[P] P[fun _ : Ω => (1 : ℝ) | ℱ j] := condExp_congr_ae h1
        _ = fun _ => (1 : ℝ) := condExp_const (ℱ.le j) (1 : ℝ)
    filter_upwards [hjensen, hnorm_eq] with ω h1 h2
    exact h1.trans (le_of_eq h2)

/-- **Conditional Taylor step (the analytic heart of Piece C).** For a bounded MDS increment
`w = u_{k+1}` (real, `|w| ≤ C` a.e., integrable with integrable square, and `E[w | ℱ j] = 0`), the
per-step factor is a conditional second-order Taylor polynomial with an a.e. cubic remainder:
`‖E[exp(iθ w) | ℱ j] − (1 − (θ²/2)·E[w² | ℱ j])‖ ≤ |θ|³C³/6` a.e. Pointwise
`exp(iθw) = (1 − θ²w²/2) + iθw + rem` with `‖rem‖ ≤ |θw|³/6 ≤ |θ|³C³/6`
(`norm_cexp_sub_taylor_three`); taking `E[·|ℱ j]`, the real part `1 − θ²w²/2` conditions (via the
`ofRealCLM` commute `ContinuousLinearMap.comp_condExp_comm` and real condExp linearity) to
`1 − (θ²/2)·E[w²|ℱ j]`, the imaginary linear term `iθw` vanishes by the MDS mean-zero
`E[w|ℱ j] = 0` (complex scalar pull-out `condExp_smul`), and the remainder is controlled by
conditional Jensen (`AEStronglyMeasurable.norm_condExp_le`). With `θ = s/√n` this is the conditional
expansion `a_k = φ_k − 1 = −(s²/2n)·σ_k² + O(n^{−3/2})` a.e. that Piece C's telescoping consumes. -/
theorem norm_condExp_cexp_sub_taylor_le {j : ℤ} {w : Ω → ℝ} {C θ : ℝ}
    (hw_int : Integrable w P) (hwsq_int : Integrable (fun ω => (w ω) ^ 2) P)
    (hbdd : ∀ᵐ ω ∂P, |w ω| ≤ C) (hmean : P[w | ℱ j] =ᵐ[P] 0) :
    ∀ᵐ ω ∂P, ‖P[fun ω => Complex.exp (((θ * w ω : ℝ) : ℂ) * Complex.I) | ℱ j] ω
        - ((1 - θ ^ 2 / 2 * P[fun ω => (w ω) ^ 2 | ℱ j] ω : ℝ) : ℂ)‖ ≤ |θ| ^ 3 * C ^ 3 / 6 := by
  set f : Ω → ℂ := fun ω => Complex.exp (((θ * w ω : ℝ) : ℂ) * Complex.I) with hfdef
  -- Real bracket `br = 1 − θ²w²/2` and its complex lift `Rc`, plus the imaginary term `Imc·I`.
  set br : Ω → ℝ := fun ω => 1 - θ ^ 2 / 2 * (w ω) ^ 2 with hbrdef
  set Rc : Ω → ℂ := fun ω => ((br ω : ℝ) : ℂ) with hRcdef
  set Imc : Ω → ℂ := fun ω => ((θ * w ω : ℝ) : ℂ) with hImcdef
  set poly : Ω → ℂ := fun ω => Rc ω + Imc ω * Complex.I with hpolydef
  set rem : Ω → ℂ := fun ω => f ω - poly ω with hremdef
  have hf_norm : ∀ ω, ‖f ω‖ = 1 := fun ω => Complex.norm_exp_ofReal_mul_I _
  have hf_aesm : AEStronglyMeasurable f P :=
    Complex.continuous_exp.comp_aestronglyMeasurable
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable
        (hw_int.aestronglyMeasurable.const_mul θ)).mul_const _)
  have hf_int : Integrable f P :=
    Integrable.of_bound hf_aesm 1 (Eventually.of_forall fun ω => (hf_norm ω).le)
  -- Integrability of the real bracket and the polynomial pieces.
  have hbr_int : Integrable br P := (integrable_const 1).sub (hwsq_int.const_mul (θ ^ 2 / 2))
  have hRc_int : Integrable Rc P := hbr_int.ofReal
  have hImc_int : Integrable Imc P := (hw_int.const_mul θ).ofReal
  have hImcI_int : Integrable (fun ω => Imc ω * Complex.I) P := hImc_int.mul_const _
  have hpoly_int : Integrable poly P := hRc_int.add hImcI_int
  have hrem_int : Integrable rem P := hf_int.sub hpoly_int
  -- Pointwise: `poly` is the second-order Taylor polynomial, so `rem` is its remainder.
  have hpoly_taylor : ∀ ω, poly ω
      = 1 + ((θ * w ω : ℝ) : ℂ) * Complex.I - ((θ * w ω : ℝ) : ℂ) ^ 2 / 2 := by
    intro ω; simp only [hpolydef, hRcdef, hbrdef, hImcdef]; push_cast; ring
  have hrem_bound : ∀ᵐ ω ∂P, ‖rem ω‖ ≤ |θ| ^ 3 * C ^ 3 / 6 := by
    filter_upwards [hbdd] with ω hω
    have hpt : rem ω = Complex.exp (((θ * w ω : ℝ) : ℂ) * Complex.I)
        - (1 + ((θ * w ω : ℝ) : ℂ) * Complex.I - ((θ * w ω : ℝ) : ℂ) ^ 2 / 2) := by
      simp only [hremdef, hfdef, hpoly_taylor ω]
    have hb : ‖rem ω‖ ≤ |θ * w ω| ^ 3 / 6 := by
      rw [hpt]
      exact (norm_cexp_sub_taylor_three (θ * w ω)).trans (min_le_left _ _)
    refine hb.trans ?_
    rw [abs_mul, mul_pow]
    exact (div_le_div_iff_of_pos_right (by norm_num)).mpr
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hω 3)
        (pow_nonneg (abs_nonneg θ) 3))
  -- Conditional expectation of the polynomial equals the real target.
  -- Real part: `E[Rc|ℱ] = (E[br|ℱ] : ℂ) = (1 − θ²/2·E[w²|ℱ] : ℂ)`.
  have hbr_condExp : P[br | ℱ j] =ᵐ[P] fun ω => 1 - θ ^ 2 / 2 * P[fun ω => (w ω) ^ 2 | ℱ j] ω := by
    have hbr_eq : br = (fun _ : Ω => (1 : ℝ)) - fun ω => θ ^ 2 / 2 * (w ω) ^ 2 := by
      funext ω; simp only [hbrdef, Pi.sub_apply]
    have hsub := condExp_sub (m := ℱ j) (integrable_const (1 : ℝ)) (hwsq_int.const_mul (θ ^ 2 / 2))
    have hconst : P[fun _ : Ω => (1 : ℝ) | ℱ j] = fun _ => 1 := condExp_const (ℱ.le j) 1
    have hsmul : P[fun ω => θ ^ 2 / 2 * (w ω) ^ 2 | ℱ j]
        =ᵐ[P] fun ω => θ ^ 2 / 2 * P[fun ω => (w ω) ^ 2 | ℱ j] ω := by
      have := condExp_smul (μ := P) (m := ℱ j) (θ ^ 2 / 2) (fun ω => (w ω) ^ 2)
      simpa only [smul_eq_mul, Pi.smul_apply] using this
    rw [hbr_eq]
    filter_upwards [hsub, hsmul] with ω h1 h2
    rw [h1]; simp only [Pi.sub_apply, hconst, h2]
  have hRc_condExp : P[Rc | ℱ j] =ᵐ[P] fun ω => ((1 - θ ^ 2 / 2 * P[fun ω => (w ω) ^ 2 | ℱ j] ω
      : ℝ) : ℂ) := by
    have hcomm := Complex.ofRealCLM.comp_condExp_comm (m := ℱ j) hbr_int
    -- hcomm : ofRealCLM ∘ E[br|ℱ] =ᵐ E[ofRealCLM ∘ br | ℱ] = E[Rc|ℱ]
    have hRceq : (Complex.ofRealCLM ∘ br) = Rc := by
      funext ω; simp only [Function.comp_apply, Complex.ofRealCLM_apply, hRcdef]
    rw [hRceq] at hcomm
    filter_upwards [hcomm.symm, hbr_condExp] with ω hc hb
    rw [hc]; simp only [Function.comp_apply, Complex.ofRealCLM_apply]; rw [hb]
  -- Imaginary part: `E[Imc·I|ℱ] = I·E[Imc|ℱ] = I·(θ·E[w|ℱ]:ℂ) = 0`.
  have hImc_condExp : P[Imc | ℱ j] =ᵐ[P] 0 := by
    have hcomm := Complex.ofRealCLM.comp_condExp_comm (m := ℱ j) (hw_int.const_mul θ)
    have hImceq : (Complex.ofRealCLM ∘ fun ω => (θ * w ω : ℝ)) = Imc := by
      funext ω; simp only [Function.comp_apply, Complex.ofRealCLM_apply, hImcdef]
    rw [hImceq] at hcomm
    have hw_condExp : P[fun ω => θ * w ω | ℱ j] =ᵐ[P] 0 := by
      have := condExp_smul (μ := P) (m := ℱ j) θ w
      have hz : P[fun ω => θ * w ω | ℱ j] =ᵐ[P] fun ω => θ * P[w | ℱ j] ω := by
        simpa only [smul_eq_mul, Pi.smul_apply] using this
      filter_upwards [hz, hmean] with ω h1 h2; rw [h1, h2]; simp
    filter_upwards [hcomm.symm, hw_condExp] with ω hc hw
    rw [hc]; simp only [Function.comp_apply, Complex.ofRealCLM_apply]; rw [hw]; simp
  have hImcI_condExp : P[fun ω => Imc ω * Complex.I | ℱ j] =ᵐ[P] 0 := by
    have hsm := condExp_smul (μ := P) (m := ℱ j) Complex.I Imc
    have hIeq : (Complex.I • Imc) = fun ω => Imc ω * Complex.I := by
      funext ω; simp [smul_eq_mul, mul_comm]
    rw [hIeq] at hsm
    filter_upwards [hsm, hImc_condExp] with ω h1 h2
    rw [h1]; simp [h2]
  have hpoly_condExp : P[poly | ℱ j] =ᵐ[P] fun ω => ((1 - θ ^ 2 / 2
      * P[fun ω => (w ω) ^ 2 | ℱ j] ω : ℝ) : ℂ) := by
    have hpoly_add : poly = Rc + fun ω => Imc ω * Complex.I := by
      funext ω; simp only [hpolydef, Pi.add_apply]
    have hadd := condExp_add (m := ℱ j) hRc_int hImcI_int
    rw [hpoly_add]
    filter_upwards [hadd, hRc_condExp, hImcI_condExp] with ω h1 h2 h3
    rw [h1]; simp only [Pi.add_apply, Pi.zero_apply, h2, h3, add_zero]
  -- Assemble: `E[f|ℱ] − target = E[rem|ℱ]`, then bound the remainder by conditional Jensen.
  have hf_split : P[f | ℱ j] =ᵐ[P] fun ω => P[poly | ℱ j] ω + P[rem | ℱ j] ω := by
    have hfeq : f = fun ω => poly ω + rem ω := by funext ω; rw [hremdef]; ring
    rw [hfeq]
    exact condExp_add (m := ℱ j) hpoly_int hrem_int
  -- Remainder bound via conditional Jensen.
  have hjensen : (fun ω => ‖P[rem | ℱ j] ω‖) ≤ᵐ[P] P[fun ω => ‖rem ω‖ | ℱ j] := by
    exact AEStronglyMeasurable.norm_condExp_le hrem_int.aestronglyMeasurable
  have hnorm_le : P[fun ω => ‖rem ω‖ | ℱ j] ≤ᵐ[P] fun _ => |θ| ^ 3 * C ^ 3 / 6 := by
    have hmono := condExp_mono (m := ℱ j) hrem_int.norm (integrable_const (|θ| ^ 3 * C ^ 3 / 6))
      hrem_bound
    have hconst : P[fun _ : Ω => |θ| ^ 3 * C ^ 3 / 6 | ℱ j] = fun _ => |θ| ^ 3 * C ^ 3 / 6 :=
      condExp_const (ℱ.le j) _
    filter_upwards [hmono] with ω hω; rwa [hconst] at hω
  filter_upwards [hf_split, hpoly_condExp, hjensen, hnorm_le] with ω hsplit hpc hj hn
  have hval : P[f | ℱ j] ω - ((1 - θ ^ 2 / 2 * P[fun ω => (w ω) ^ 2 | ℱ j] ω : ℝ) : ℂ)
      = P[rem | ℱ j] ω := by rw [hsplit, hpc]; ring
  rw [hval]
  exact hj.trans hn

omit [IsProbabilityMeasure P] in
/-- **Uniform product lower bound (Piece D/E bridge to the decorrelation `‖Mₙ‖ ≤ K`).** For a
factor sequence `φ` whose every factor has modulus `≥ 1 − x` a.e. with `0 ≤ x ≤ 1/2`, the finite
product is bounded below a.e. by `exp(−2nx)`: `‖∏_{k<n} φ k‖ = ∏ ‖φ k‖ ≥ (1 − x)ⁿ ≥ exp(−2x)ⁿ =
exp(−2nx)` (via `exp_neg_two_mul_le_one_sub`). In the McLeish application `φ k = E[exp(iθ u_{k+1})
| ℱ k]` with `θ = s/√n` and `x = s²C²/2n` (so `n ≥ s²C²` gives `x ≤ 1/2`), the exponent `2nx =
s²C²` is independent of `n`, delivering the uniform lower bound `‖Pₙ‖ ≥ exp(−s²C²)` — equivalently
`‖Mₙ‖ = ‖Pₙ‖⁻¹ ≤ exp(s²C²)`, the uniform bound the decorrelation lemma consumes. -/
theorem norm_prod_ge_of_ae_norm_ge {φ : ℕ → Ω → ℂ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hlb : ∀ k, ∀ᵐ ω ∂P, 1 - x ≤ ‖φ k ω‖) (n : ℕ) :
    ∀ᵐ ω ∂P, Real.exp (-(2 * ((n : ℝ) * x))) ≤ ‖∏ k ∈ Finset.range n, φ k ω‖ := by
  filter_upwards [ae_all_iff.mpr hlb] with ω hω
  have hb : Real.exp (-(2 * x)) ≤ 1 - x := exp_neg_two_mul_le_one_sub hx0 hx1
  have h1 : (1 - x) ^ n ≤ ‖∏ k ∈ Finset.range n, φ k ω‖ := by
    rw [norm_prod]
    calc (1 - x) ^ n = ∏ _k ∈ Finset.range n, (1 - x) := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ k ∈ Finset.range n, ‖φ k ω‖ :=
          Finset.prod_le_prod (fun k _ => by linarith) (fun k _ => hω k)
  have h2 : Real.exp (-(2 * ((n : ℝ) * x))) ≤ (1 - x) ^ n := by
    calc Real.exp (-(2 * ((n : ℝ) * x)))
        = Real.exp ((n : ℝ) * -(2 * x)) := by
          rw [show -(2 * ((n : ℝ) * x)) = (n : ℝ) * -(2 * x) from by ring]
      _ = Real.exp (-(2 * x)) ^ n := Real.exp_nat_mul _ n
      _ ≤ (1 - x) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le hb n
  exact h2.trans h1

/-- The map `x ↦ exp(−x)` is `1`-Lipschitz on the nonnegative half-line: for `0 ≤ x, y`,
`|exp(−x) − exp(−y)| ≤ |x − y|`. Used to transfer `L¹` convergence of the ergodic average of the
conditional variances to `L¹` convergence of the Gaussian factor `exp(−λ·average)`. -/
private lemma abs_exp_neg_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  have exp_le_one : ∀ z : ℝ, 0 ≤ z → Real.exp (-z) ≤ 1 := fun z hz =>
    (Real.exp_le_exp.mpr (by linarith)).trans_eq Real.exp_zero
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → Real.exp (-a) - Real.exp (-b) ≤ b - a := by
    intro a b ha hab
    have hba : (0 : ℝ) ≤ b - a := by linarith
    have h1 : 1 - (b - a) ≤ Real.exp (-(b - a)) := by
      have := Real.add_one_le_exp (-(b - a)); linarith
    have hsplit : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hnn : 0 ≤ 1 - Real.exp (-(b - a)) := by linarith [exp_le_one (b - a) hba]
    calc Real.exp (-a) - Real.exp (-b)
        = Real.exp (-a) * (1 - Real.exp (-(b - a))) := by rw [hsplit]; ring
      _ ≤ 1 * (1 - Real.exp (-(b - a))) := mul_le_mul_of_nonneg_right (exp_le_one a ha) hnn
      _ = 1 - Real.exp (-(b - a)) := one_mul _
      _ ≤ b - a := by linarith
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonneg (by linarith [Real.exp_le_exp.mpr (show -y ≤ -x by linarith)] :
        (0 : ℝ) ≤ Real.exp (-x) - Real.exp (-y)),
      abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith [key x y hx hxy]
  · rw [abs_of_nonpos (by linarith [Real.exp_le_exp.mpr (show -x ≤ -y by linarith)] :
        Real.exp (-x) - Real.exp (-y) ≤ 0),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y)]
    linarith [key y x hy hxy]

/-- **Ergodic normalization of the random conditional variances (the general-case new ingredient).**
Let `v : ℤ → Ω → ℝ` be the conditional-variance process `vₜ = E[uₜ₊₁² | ℱₜ]` (under the
Hall–Heyde design decision, `v` is taken strictly stationary and ergodic jointly with `u`, and is
nonnegative and integrable — all automatic when `u` is bounded). Then for every `λ ≥ 0` the Gaussian
factor `exp(−λ·(1/n)∑ₜ vₜ)` converges in `L¹` to the constant `exp(−λ·E[v₀])`. This is the exact
form consumed by `tendsto_integral_mul_of_tendsto_integral_norm_sub`: with `λ = s²/2` and
`E[v₀] = Var[u₁]`, the limit constant is the Gaussian target `exp(−Var[u₁]·s²/2)`.

The proof is the `L¹` mean ergodic theorem (`IsErgodicProcess.tendsto_average_eLpNorm_one`,
Hansen 14.9) for `v`, transferred through the pointwise `1`-Lipschitz bound `abs_exp_neg_sub_le`
(the averages and `E[v₀]` are nonnegative because `v ≥ 0`) and the scaling identity
`eLpNorm (λ • ·) 1 = ‖λ‖·eLpNorm ·`. This is the sole place the ergodic theorem enters the general
MDS CLT; the constant conditional variance case bypassed it entirely. -/
theorem tendsto_eLpNorm_exp_neg_average_sub {v : ℤ → Ω → ℝ}
    (hv_erg : IsErgodicProcess v P) (hv_meas : ∀ t, AEMeasurable (v t) P)
    (hv_int : Integrable (v 0) P) (hv_nonneg : ∀ t, 0 ≤ᵐ[P] v t) {lam : ℝ} (hlam : 0 ≤ lam) :
    Tendsto (fun n : ℕ => eLpNorm
        (fun ω => Real.exp (-(lam * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω)))
          - Real.exp (-(lam * ∫ ω, v 0 ω ∂P))) 1 P)
      atTop (𝓝 0) := by
  have hb0 : 0 ≤ ∫ ω, v 0 ω ∂P := integral_nonneg_of_ae (hv_nonneg 0)
  have hall := ae_all_iff.mpr hv_nonneg
  have hMET := hv_erg.tendsto_average_eLpNorm_one hv_meas hv_int
  set b : ℝ := ∫ ω, v 0 ω ∂P with hbdef
  -- The upper bounding sequence `‖λ‖·eLpNorm(averageₙ − b) → 0`.
  have hupper : Tendsto (fun n : ℕ => ‖lam‖ₑ *
      eLpNorm (fun ω => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω - b) 1 P) atTop (𝓝 0) := by
    have hlt : ‖lam‖ₑ ≠ ⊤ := enorm_ne_top
    have h := ENNReal.Tendsto.const_mul hMET (Or.inr hlt)
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun n => zero_le _) (Eventually.of_forall fun n => ?_)
  have hbound_pt : ∀ᵐ ω ∂P,
      ‖Real.exp (-(lam * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω)))
          - Real.exp (-(lam * b))‖
        ≤ ‖(lam • (fun ω => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω - b)) ω‖ := by
    filter_upwards [hall] with ω hω
    have havg_nn : 0 ≤ (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ => hω _)
    have hL := abs_exp_neg_sub_le (mul_nonneg hlam havg_nn) (mul_nonneg hlam hb0)
    simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs]
    refine hL.trans (le_of_eq ?_)
    rw [mul_sub]
  calc eLpNorm (fun ω => Real.exp (-(lam * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω)))
          - Real.exp (-(lam * b))) 1 P
      ≤ eLpNorm (lam • (fun ω => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω - b)) 1 P :=
        eLpNorm_mono_ae hbound_pt
    _ = ‖lam‖ₑ * eLpNorm (fun ω => (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω - b) 1 P :=
        eLpNorm_const_smul lam _ 1 P

omit [IsProbabilityMeasure P] in
/-- The partial sum `Sₖ = ∑_{t < k} u₍ₜ₊₁₎ = u₁ + ⋯ + uₖ` is `ℱ(k)`-strongly-measurable: each
summand `u₍ₜ₊₁₎` is `ℱ(t+1)`-measurable by adaptedness, and `t + 1 ≤ k` for `t < k`. -/
private theorem stronglyMeasurable_partialSum (h : IsMDS ℱ u P) (k : ℕ) :
    StronglyMeasurable[ℱ (k : ℤ)] (fun ω => ∑ t ∈ Finset.range k, u ((t : ℤ) + 1) ω) := by
  refine Finset.stronglyMeasurable_fun_sum _ (fun t ht => ?_)
  simp only [Finset.mem_range] at ht
  exact ((h.adapted ((t : ℤ) + 1)).stronglyMeasurable).mono (ℱ.mono (by omega))

/-- **The one conditioning step, real form.** For a real function `g` that is
`ℱ(j)`-strongly-measurable, and a real integrable `h` with `E[h | ℱ(j)] = 0` a.s., the mixed
moment vanishes: `∫ g·h = 0`. Proof: tower law `∫ g h = ∫ E[g h | ℱ(j)]`, pull the
`ℱ(j)`-measurable factor `g` out (`condExp_mul_of_stronglyMeasurable_left`), leaving
`∫ g·E[h | ℱ(j)] = ∫ g·0 = 0`. This is the only place conditional expectations enter, and both
multiplicands are real, so the real pull-out suffices. -/
private theorem integral_mul_eq_zero_of_condExp_eq_zero {j : ℤ} {g h : Ω → ℝ}
    (hg : StronglyMeasurable[ℱ j] g) (hgh : Integrable (fun ω => g ω * h ω) P)
    (hh : Integrable h P) (hcond : P[h | ℱ j] =ᵐ[P] 0) :
    ∫ ω, g ω * h ω ∂P = 0 := by
  have hmul : P[fun ω => g ω * h ω | ℱ j] =ᵐ[P] fun ω => g ω * (P[h | ℱ j]) ω :=
    condExp_mul_of_stronglyMeasurable_left hg hgh hh
  calc ∫ ω, g ω * h ω ∂P
      = ∫ ω, (P[fun ω => g ω * h ω | ℱ j]) ω ∂P := (integral_condExp (ℱ.le j)).symm
    _ = ∫ ω, g ω * (P[h | ℱ j]) ω ∂P := integral_congr_ae hmul
    _ = 0 := integral_eq_zero_of_ae (by filter_upwards [hcond] with ω hω; simp [hω])

/-- **The conditioning step, complex form.** For any `ℱ(j)`-strongly-measurable real `S` and any
real integrable `f` with `E[f | ℱ(j)] = 0` a.s., the mixed moment of `exp(iθ S)·f` vanishes:
`∫ exp(iθ S)·f = 0`. The complex exponential splits as `cos(θS) + i sin(θS)`, both factors
`ℱ(j)`-measurable and bounded, so the claim reduces to two applications of the real conditioning
step `integral_mul_eq_zero_of_condExp_eq_zero`. -/
private theorem integral_cexp_mul_ofReal_eq_zero {j : ℤ} {S : Ω → ℝ} (θ : ℝ)
    (hSsm : StronglyMeasurable[ℱ j] S) {f : Ω → ℝ}
    (hf_int : Integrable f P) (hcond : P[f | ℱ j] =ᵐ[P] 0) :
    ∫ ω, Complex.exp (((θ * S ω : ℝ) : ℂ) * Complex.I) * ((f ω : ℝ) : ℂ) ∂P = 0 := by
  have hcos_sm : StronglyMeasurable[ℱ j] (fun ω => Real.cos (θ * S ω)) :=
    Real.continuous_cos.comp_stronglyMeasurable (hSsm.const_mul θ)
  have hsin_sm : StronglyMeasurable[ℱ j] (fun ω => Real.sin (θ * S ω)) :=
    Real.continuous_sin.comp_stronglyMeasurable (hSsm.const_mul θ)
  have hcos_aesm : AEStronglyMeasurable (fun ω => Real.cos (θ * S ω)) P :=
    (hcos_sm.mono (ℱ.le _)).aestronglyMeasurable
  have hsin_aesm : AEStronglyMeasurable (fun ω => Real.sin (θ * S ω)) P :=
    (hsin_sm.mono (ℱ.le _)).aestronglyMeasurable
  have hcos_int : Integrable (fun ω => Real.cos (θ * S ω) * f ω) P :=
    hf_int.bdd_mul hcos_aesm (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hsin_int : Integrable (fun ω => Real.sin (θ * S ω) * f ω) P :=
    hf_int.bdd_mul hsin_aesm (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hcos0 : ∫ ω, Real.cos (θ * S ω) * f ω ∂P = 0 :=
    integral_mul_eq_zero_of_condExp_eq_zero hcos_sm hcos_int hf_int hcond
  have hsin0 : ∫ ω, Real.sin (θ * S ω) * f ω ∂P = 0 :=
    integral_mul_eq_zero_of_condExp_eq_zero hsin_sm hsin_int hf_int hcond
  have hpt : ∀ ω, Complex.exp (((θ * S ω : ℝ) : ℂ) * Complex.I) * ((f ω : ℝ) : ℂ)
      = ((Real.cos (θ * S ω) * f ω : ℝ) : ℂ)
        + ((Real.sin (θ * S ω) * f ω : ℝ) : ℂ) * Complex.I := by
    intro ω
    have hZ := Complex.re_add_im (Complex.exp (((θ * S ω : ℝ) : ℂ) * Complex.I))
    rw [exp_ofReal_mul_I_re, exp_ofReal_mul_I_im] at hZ
    rw [← hZ]; push_cast; ring
  have hIcos : ∫ ω, ((Real.cos (θ * S ω) * f ω : ℝ) : ℂ) ∂P = 0 := by
    rw [integral_complex_ofReal, hcos0, Complex.ofReal_zero]
  have hIsin : ∫ ω, ((Real.sin (θ * S ω) * f ω : ℝ) : ℂ) * Complex.I ∂P = 0 := by
    have h1 : ∫ ω, ((Real.sin (θ * S ω) * f ω : ℝ) : ℂ) * Complex.I ∂P
        = (∫ ω, ((Real.sin (θ * S ω) * f ω : ℝ) : ℂ) ∂P) * Complex.I :=
      integral_mul_const Complex.I _
    have h2 : ∫ ω, ((Real.sin (θ * S ω) * f ω : ℝ) : ℂ) ∂P = 0 := by
      rw [integral_complex_ofReal, hsin0, Complex.ofReal_zero]
    rw [h1, h2, zero_mul]
  calc ∫ ω, Complex.exp (((θ * S ω : ℝ) : ℂ) * Complex.I) * ((f ω : ℝ) : ℂ) ∂P
      = ∫ ω, (((Real.cos (θ * S ω) * f ω : ℝ) : ℂ)
          + ((Real.sin (θ * S ω) * f ω : ℝ) : ℂ) * Complex.I) ∂P :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = (∫ ω, ((Real.cos (θ * S ω) * f ω : ℝ) : ℂ) ∂P)
          + ∫ ω, ((Real.sin (θ * S ω) * f ω : ℝ) : ℂ) * Complex.I ∂P :=
        integral_add hcos_int.ofReal (hsin_int.ofReal.mul_const Complex.I)
    _ = 0 := by rw [hIcos, hIsin, add_zero]

/-- Integrability of `ω ↦ exp(iθ R ω)` for real a.e.-measurable `R`: the integrand has modulus
`1` everywhere, so on a probability measure it is integrable. -/
private theorem integrable_cexp_ofReal {R : Ω → ℝ} (hR : AEStronglyMeasurable R P) (θ : ℝ) :
    Integrable (fun ω => Complex.exp (((θ * R ω : ℝ) : ℂ) * Complex.I)) P := by
  refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun ω => ?_)
  · exact Complex.continuous_exp.comp_aestronglyMeasurable
      (((Complex.continuous_ofReal.comp_aestronglyMeasurable (hR.const_mul θ))).mul_const _)
  · rw [Complex.norm_exp_ofReal_mul_I]

/-- **The one-step defect bound (Billingsley telescoping, constant-variance case).** With
`θ` fixed, `a = 1 − vθ²/2`, and partial sums `Sₖ`, the characteristic-function increment
`E[exp(iθ Sₖ₊₁)] − a·E[exp(iθ Sₖ)]` has modulus at most `|θ|³C³/6`. Successive conditioning
factors the increment as `∫ exp(iθ Sₖ)·(exp(iθ uₖ₊₁) − a)`; the bracket splits into a pointwise
Taylor remainder (bounded by `|θ uₖ₊₁|³/6 ≤ |θ|³C³/6`) plus a linear term `iθ uₖ₊₁` and a
quadratic term `−(θ²/2)(uₖ₊₁² − v)` whose integrals against `exp(iθ Sₖ)` vanish by the MDS
mean-zero and constant-conditional-variance hypotheses (`integral_cexp_mul_ofReal_eq_zero`). -/
private theorem norm_charFun_step_le (h : IsMDS ℱ u P) {C v θ : ℝ} (k : ℕ)
    (hbdd_k : ∀ᵐ ω ∂P, |u ((k : ℤ) + 1) ω| ≤ C)
    (hsq_int : Integrable (fun ω => (u ((k : ℤ) + 1) ω) ^ 2) P)
    (hcv_k : P[fun ω => (u ((k : ℤ) + 1) ω) ^ 2 | ℱ (k : ℤ)] =ᵐ[P] fun _ => v) :
    ‖(∫ ω, Complex.exp (((θ * ∑ t ∈ Finset.range (k + 1), u ((t : ℤ) + 1) ω : ℝ) : ℂ)
            * Complex.I) ∂P)
        - ((1 - v * θ ^ 2 / 2 : ℝ) : ℂ)
          * ∫ ω, Complex.exp (((θ * ∑ t ∈ Finset.range k, u ((t : ℤ) + 1) ω : ℝ) : ℂ)
              * Complex.I) ∂P‖
      ≤ |θ| ^ 3 * C ^ 3 / 6 := by
  -- Notation: `g ω = exp(iθ Sₖ ω)`, `w ω = uₖ₊₁ ω`, `rem ω = Taylor remainder at θ·w ω`.
  set S : Ω → ℝ := fun ω => ∑ t ∈ Finset.range k, u ((t : ℤ) + 1) ω with hSdef
  set w : Ω → ℝ := u ((k : ℤ) + 1) with hwdef
  have hSsm : StronglyMeasurable[ℱ (k : ℤ)] S := stronglyMeasurable_partialSum h k
  have hS_aesm : AEStronglyMeasurable S P := (hSsm.mono (ℱ.le _)).aestronglyMeasurable
  have hw_int : Integrable w P := h.integrable _
  have hw_aesm : AEStronglyMeasurable w P := hw_int.aestronglyMeasurable
  set g : Ω → ℂ := fun ω => Complex.exp (((θ * S ω : ℝ) : ℂ) * Complex.I) with hgdef
  set rem : Ω → ℂ := fun ω => Complex.exp (((θ * w ω : ℝ) : ℂ) * Complex.I)
    - (1 + ((θ * w ω : ℝ) : ℂ) * Complex.I - ((θ * w ω : ℝ) : ℂ) ^ 2 / 2) with hremdef
  have hg_int : Integrable g P := integrable_cexp_ofReal hS_aesm θ
  have hg_norm : ∀ ω, ‖g ω‖ = 1 := fun ω => Complex.norm_exp_ofReal_mul_I _
  have hg_aesm : AEStronglyMeasurable g P := hg_int.aestronglyMeasurable
  have hg_bnd : ∀ᵐ ω ∂P, ‖g ω‖ ≤ 1 := Eventually.of_forall fun ω => (hg_norm ω).le
  -- Conditioning hypotheses at time `k + 1`.
  have hcond_w : P[w | ℱ (k : ℤ)] =ᵐ[P] 0 := by
    have hz := h.condExp_eq_zero ((k : ℤ) + 1)
    simpa only [add_sub_cancel_right] using hz
  have hcond_sq : P[(fun ω => (w ω) ^ 2) - (fun _ => v) | ℱ (k : ℤ)] =ᵐ[P] 0 := by
    have hsub := condExp_sub hsq_int (integrable_const v) (ℱ (k : ℤ))
    have hconst : P[fun _ : Ω => v | ℱ (k : ℤ)] = fun _ => v := condExp_const (ℱ.le _) v
    filter_upwards [hsub, hcv_k] with ω h1 h2
    rw [h1]
    simp only [Pi.sub_apply, Pi.zero_apply, hconst, h2, sub_self]
  -- The two conditioned mixed moments vanish.
  have hgw0 : ∫ ω, g ω * ((w ω : ℝ) : ℂ) ∂P = 0 :=
    integral_cexp_mul_ofReal_eq_zero θ hSsm hw_int hcond_w
  have hgwsq0 : ∫ ω, g ω * (((w ω) ^ 2 - v : ℝ) : ℂ) ∂P = 0 :=
    integral_cexp_mul_ofReal_eq_zero θ hSsm (hsq_int.sub (integrable_const v)) hcond_sq
  -- Integrability bookkeeping (every factor is `g` times an a.e.-bounded or integrable function).
  have hgw_int : Integrable (fun ω => g ω * ((w ω : ℝ) : ℂ)) P :=
    (hw_int.ofReal).bdd_mul hg_aesm hg_bnd
  have hgwsq_int : Integrable (fun ω => g ω * (((w ω) ^ 2 - v : ℝ) : ℂ)) P :=
    ((hsq_int.sub (integrable_const v)).ofReal).bdd_mul hg_aesm hg_bnd
  have hc1_int : Integrable (fun ω => ((θ : ℂ) * Complex.I) * (g ω * ((w ω : ℝ) : ℂ))) P :=
    hgw_int.const_mul _
  have hc2_int : Integrable
      (fun ω => (-(((θ ^ 2 / 2 : ℝ)) : ℂ)) * (g ω * (((w ω) ^ 2 - v : ℝ) : ℂ))) P :=
    hgwsq_int.const_mul _
  have hrem_aesm : AEStronglyMeasurable rem P := by
    have hθw : AEStronglyMeasurable (fun ω => ((θ * w ω : ℝ) : ℂ)) P :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable (hw_aesm.const_mul θ)
    rw [hremdef]
    fun_prop
  have hrem_c_bound : ∀ᵐ ω ∂P, ‖rem ω‖ ≤ |θ| ^ 3 * C ^ 3 / 6 := by
    filter_upwards [hbdd_k] with ω hω
    have hb : ‖rem ω‖ ≤ |θ * w ω| ^ 3 / 6 := by
      simp only [hremdef]
      exact (norm_cexp_sub_taylor_three (θ * w ω)).trans (min_le_left _ _)
    refine hb.trans ?_
    rw [abs_mul, mul_pow]
    exact (div_le_div_iff_of_pos_right (by norm_num)).mpr
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hω 3)
        (pow_nonneg (abs_nonneg θ) 3))
  have hrem_int : Integrable (fun ω => g ω * rem ω) P := hg_int.mul_bdd hrem_aesm hrem_c_bound
  -- Step 1: rewrite the successor partial sum and factor the exponential.
  have hbig : (fun ω => Complex.exp (((θ * ∑ t ∈ Finset.range (k + 1),
        u ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I))
      = fun ω => g ω * Complex.exp (((θ * w ω : ℝ) : ℂ) * Complex.I) := by
    funext ω
    rw [Finset.sum_range_succ]
    change Complex.exp (((θ * (S ω + w ω) : ℝ) : ℂ) * Complex.I) = _
    rw [hgdef, ← Complex.exp_add]
    push_cast; ring_nf
  -- Step 2: the increment is `∫ g·(exp(iθw) − a)`.
  have hincr : (∫ ω, Complex.exp (((θ * ∑ t ∈ Finset.range (k + 1),
          u ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂P)
        - ((1 - v * θ ^ 2 / 2 : ℝ) : ℂ) * ∫ ω, g ω ∂P
      = ∫ ω, g ω * (Complex.exp (((θ * w ω : ℝ) : ℂ) * Complex.I)
          - ((1 - v * θ ^ 2 / 2 : ℝ) : ℂ)) ∂P := by
    have hgcexp_int : Integrable
        (fun ω => g ω * Complex.exp (((θ * w ω : ℝ) : ℂ) * Complex.I)) P :=
      hg_int.mul_bdd
        (Complex.continuous_exp.comp_aestronglyMeasurable
          ((Complex.continuous_ofReal.comp_aestronglyMeasurable (hw_aesm.const_mul θ)).mul_const _))
        (Eventually.of_forall fun ω => by rw [Complex.norm_exp_ofReal_mul_I])
    have hga_int : Integrable (fun ω => ((1 - v * θ ^ 2 / 2 : ℝ) : ℂ) * g ω) P := hg_int.const_mul _
    have hc : ((1 - v * θ ^ 2 / 2 : ℝ) : ℂ) * ∫ ω, g ω ∂P
        = ∫ ω, ((1 - v * θ ^ 2 / 2 : ℝ) : ℂ) * g ω ∂P := (integral_const_mul _ _).symm
    rw [hbig, hc, ← integral_sub hgcexp_int hga_int]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    ring
  rw [hincr]
  -- Step 3: the increment equals `∫ g·rem` (linear/quadratic parts vanish by conditioning).
  have hApt : ∀ ω, g ω * (Complex.exp (((θ * w ω : ℝ) : ℂ) * Complex.I)
        - ((1 - v * θ ^ 2 / 2 : ℝ) : ℂ))
      = g ω * rem ω + ((θ : ℂ) * Complex.I) * (g ω * ((w ω : ℝ) : ℂ))
        + (-(((θ ^ 2 / 2 : ℝ)) : ℂ)) * (g ω * (((w ω) ^ 2 - v : ℝ) : ℂ)) := by
    intro ω; simp only [hremdef]; push_cast; ring
  have hrem_eq : ∫ ω, g ω * (Complex.exp (((θ * w ω : ℝ) : ℂ) * Complex.I)
        - ((1 - v * θ ^ 2 / 2 : ℝ) : ℂ)) ∂P = ∫ ω, g ω * rem ω ∂P := by
    have e1 : ∫ ω, ((θ : ℂ) * Complex.I) * (g ω * ((w ω : ℝ) : ℂ)) ∂P
        = ((θ : ℂ) * Complex.I) * ∫ ω, g ω * ((w ω : ℝ) : ℂ) ∂P := integral_const_mul _ _
    have e2 : ∫ ω, (-(((θ ^ 2 / 2 : ℝ)) : ℂ)) * (g ω * (((w ω) ^ 2 - v : ℝ) : ℂ)) ∂P
        = (-(((θ ^ 2 / 2 : ℝ)) : ℂ)) * ∫ ω, g ω * (((w ω) ^ 2 - v : ℝ) : ℂ) ∂P :=
      integral_const_mul _ _
    calc ∫ ω, g ω * (Complex.exp (((θ * w ω : ℝ) : ℂ) * Complex.I)
            - ((1 - v * θ ^ 2 / 2 : ℝ) : ℂ)) ∂P
        = ∫ ω, (g ω * rem ω + ((θ : ℂ) * Complex.I) * (g ω * ((w ω : ℝ) : ℂ))
            + (-(((θ ^ 2 / 2 : ℝ)) : ℂ)) * (g ω * (((w ω) ^ 2 - v : ℝ) : ℂ))) ∂P :=
          integral_congr_ae (Eventually.of_forall hApt)
      _ = (∫ ω, g ω * rem ω + ((θ : ℂ) * Complex.I) * (g ω * ((w ω : ℝ) : ℂ)) ∂P)
            + ∫ ω, (-(((θ ^ 2 / 2 : ℝ)) : ℂ)) * (g ω * (((w ω) ^ 2 - v : ℝ) : ℂ)) ∂P :=
          integral_add (hrem_int.add hc1_int) hc2_int
      _ = ((∫ ω, g ω * rem ω ∂P) + ∫ ω, ((θ : ℂ) * Complex.I) * (g ω * ((w ω : ℝ) : ℂ)) ∂P)
            + ∫ ω, (-(((θ ^ 2 / 2 : ℝ)) : ℂ)) * (g ω * (((w ω) ^ 2 - v : ℝ) : ℂ)) ∂P := by
          congr 1
          exact integral_add hrem_int hc1_int
      _ = ∫ ω, g ω * rem ω ∂P := by rw [e1, e2, hgw0, hgwsq0]; ring
  rw [hrem_eq]
  -- Step 4: `‖∫ g·rem‖ ≤ ∫ ‖rem‖ ≤ |θ|³C³/6`.
  have hrem_bound : (fun ω => ‖g ω * rem ω‖) ≤ᵐ[P] fun _ => |θ| ^ 3 * C ^ 3 / 6 := by
    filter_upwards [hrem_c_bound] with ω hω
    rw [norm_mul, hg_norm, one_mul]; exact hω
  calc ‖∫ ω, g ω * rem ω ∂P‖
      ≤ ∫ ω, ‖g ω * rem ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ _ω : Ω, |θ| ^ 3 * C ^ 3 / 6 ∂P :=
        integral_mono_ae hrem_int.norm (integrable_const _) hrem_bound
    _ = |θ| ^ 3 * C ^ 3 / 6 := by simp

/-- **Discharge of the analytic core (Hansen Theorem 14.11), bounded constant-conditional-variance
case.** For a martingale difference sequence `u` that is uniformly bounded (`|uₜ| ≤ C` a.s.) with
constant conditional variance (`E[uₜ² | ℱₜ₋₁] = v` a.s.), the characteristic function of the
normalized partial sums converges to the Gaussian target `exp(-v s²/2)` — i.e. the field
`charFun_tendsto` of `MDSCLTConditions` is a theorem, not a hypothesis, in this case.

The telescoping `‖ψₙ − aⁿ‖ ≤ n·|θ|³C³/6` (`norm_sub_pow_le_of_recursion` fed by
`norm_charFun_step_le`) is squeezed against `n·|θ|³C³/6 = |s|³C³/(6√n) → 0`, while
`aⁿ = (1 − v s²/2n)ⁿ → exp(-v s²/2)` (`tendsto_one_sub_pow_exp`). -/
theorem charFun_tendsto_of_bounded_constCondVar (h : IsMDS ℱ u P)
    {C v : ℝ} (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C)
    (hcondvar : ∀ t, P[fun ω => (u t ω) ^ 2 | ℱ (t - 1)] =ᵐ[P] fun _ => v) (s : ℝ) :
    Filter.Tendsto (fun n : ℕ => charFun
      (P.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω)) s)
      Filter.atTop (nhds (Complex.exp (-(v : ℂ) * (s : ℂ) ^ 2 / 2))) := by
  -- Squares are integrable (uniform bound), and `v ≥ 0` (conditional variance of `u₁²`).
  have hsq_int : ∀ t, Integrable (fun ω => (u t ω) ^ 2) P := fun t => by
    refine Integrable.of_bound (((h.integrable t).aestronglyMeasurable).pow 2) (C ^ 2) ?_
    filter_upwards [hbdd t] with ω hω
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  have hv0 : 0 ≤ v := by
    have hsqint_v : ∫ ω, (u 1 ω) ^ 2 ∂P = v :=
      calc ∫ ω, (u 1 ω) ^ 2 ∂P
          = ∫ ω, (P[fun ω => (u 1 ω) ^ 2 | ℱ ((1 : ℤ) - 1)]) ω ∂P :=
            (integral_condExp (ℱ.le _)).symm
        _ = ∫ ω, (fun _ => v) ω ∂P := integral_congr_ae (hcondvar 1)
        _ = v := by simp
    rw [← hsqint_v]; exact integral_nonneg fun ω => sq_nonneg _
  -- Reduce the Gaussian target to a real exponential.
  rw [show (-(v : ℂ) * (s : ℂ) ^ 2 / 2) = (((-(v * s ^ 2) / 2 : ℝ)) : ℂ) from by push_cast; ring,
    ← Complex.ofReal_exp]
  -- `charFun` of the pushforward is `E[exp(iθ Sₙ)]`.
  have hcharFun : ∀ n : ℕ, charFun (P.map (fun ω => (Real.sqrt (n : ℝ))⁻¹
        * ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω)) s
      = ∫ ω, Complex.exp (((s * (Real.sqrt (n : ℝ))⁻¹
          * ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂P := by
    intro n
    have hφ : AEMeasurable (fun ω => (Real.sqrt (n : ℝ))⁻¹
        * ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω) P :=
      (Finset.aemeasurable_fun_sum (Finset.range n)
        fun i _ => (h.integrable ((i : ℤ) + 1)).aemeasurable).const_mul ((Real.sqrt (n : ℝ))⁻¹)
    have haesm : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I))
        (P.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω)) :=
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    rw [charFun_apply_real, integral_map hφ haesm]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    push_cast; ring_nf
  -- Ingredients of the squeeze.
  have hsqrtinv : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hbase : ∀ n : ℕ, 1 - v * s ^ 2 / (2 * (n : ℝ)) = 1 - v * (s * (Real.sqrt n)⁻¹) ^ 2 / 2 := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have h3 : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt n.cast_nonneg
      rw [mul_pow, inv_pow, h3]
      field_simp
  have hAexp : Tendsto (fun n : ℕ => (1 - v * (s * (Real.sqrt n)⁻¹) ^ 2 / 2) ^ n) atTop
      (𝓝 (Real.exp (-(v * s ^ 2) / 2))) :=
    (tendsto_one_sub_pow_exp v s).congr fun n => by rw [hbase n]
  have hkey_all : ∀ n : ℕ, (n : ℝ) * ((Real.sqrt n)⁻¹) ^ 3 = (Real.sqrt n)⁻¹ := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have h3 : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt n.cast_nonneg
      rw [inv_pow, show (Real.sqrt n) ^ 3 = (n : ℝ) * Real.sqrt n from by rw [pow_succ, h3],
        mul_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  have hB : Tendsto (fun n : ℕ => (n : ℝ) * (|s * (Real.sqrt n)⁻¹| ^ 3 * C ^ 3 / 6))
      atTop (𝓝 0) := by
    have heq : ∀ n : ℕ, (n : ℝ) * (|s * (Real.sqrt n)⁻¹| ^ 3 * C ^ 3 / 6)
        = |s| ^ 3 * C ^ 3 / 6 * (Real.sqrt n)⁻¹ := by
      intro n
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), mul_pow,
        show (n : ℝ) * (|s| ^ 3 * ((Real.sqrt n)⁻¹) ^ 3 * C ^ 3 / 6)
          = |s| ^ 3 * C ^ 3 / 6 * ((n : ℝ) * ((Real.sqrt n)⁻¹) ^ 3) from by ring, hkey_all n]
    simp only [heq]
    simpa using hsqrtinv.const_mul (|s| ^ 3 * C ^ 3 / 6)
  have hxlim : Tendsto (fun n : ℕ => v * (s * (Real.sqrt n)⁻¹) ^ 2 / 2) atTop (𝓝 0) := by
    have hg : Continuous (fun t : ℝ => v * (s * t) ^ 2 / 2) := by fun_prop
    simpa using (hg.tendsto 0).comp hsqrtinv
  have ha_ev : ∀ᶠ n : ℕ in atTop, |1 - v * (s * (Real.sqrt n)⁻¹) ^ 2 / 2| ≤ 1 := by
    filter_upwards [hxlim.eventually_le_const (show (0 : ℝ) < 2 by norm_num)] with n hn
    set X : ℝ := v * (s * (Real.sqrt n)⁻¹) ^ 2 / 2 with hX
    have hxnn : 0 ≤ X := div_nonneg (mul_nonneg hv0 (sq_nonneg _)) (by norm_num)
    rw [abs_le]
    constructor <;> linarith
  -- The eventual telescoping bound.
  have hbound_ev : ∀ᶠ n : ℕ in atTop,
      ‖(∫ ω, Complex.exp (((s * (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n,
              u ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂P)
          - (((1 - v * (s * (Real.sqrt n)⁻¹) ^ 2 / 2) ^ n : ℝ) : ℂ)‖
        ≤ (n : ℝ) * (|s * (Real.sqrt n)⁻¹| ^ 3 * C ^ 3 / 6) := by
    filter_upwards [ha_ev] with n hn
    set θ := s * (Real.sqrt (n : ℝ))⁻¹ with hθ
    have ha : ‖(((1 - v * θ ^ 2 / 2 : ℝ)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hn
    have h0 : (fun kk => ∫ ω, Complex.exp (((θ * ∑ t ∈ Finset.range kk,
          u ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂P) 0 = 1 := by simp
    have hrec : ∀ kk, ‖(fun kk => ∫ ω, Complex.exp (((θ * ∑ t ∈ Finset.range kk,
            u ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂P) (kk + 1)
          - (((1 - v * θ ^ 2 / 2 : ℝ)) : ℂ) * (fun kk => ∫ ω, Complex.exp (((θ
              * ∑ t ∈ Finset.range kk, u ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂P) kk‖
        ≤ |θ| ^ 3 * C ^ 3 / 6 := by
      intro kk
      refine norm_charFun_step_le h kk (hbdd _) (hsq_int _) ?_
      have hcv := hcondvar ((kk : ℤ) + 1)
      simpa only [add_sub_cancel_right] using hcv
    have key := norm_sub_pow_le_of_recursion
      (ψ := fun kk => ∫ ω, Complex.exp (((θ * ∑ t ∈ Finset.range kk,
        u ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂P) ha h0 hrec n
    rw [← Complex.ofReal_pow] at key
    exact key
  -- Squeeze `charFun` to the Gaussian limit.
  have hdiff : Tendsto (fun n : ℕ => (∫ ω, Complex.exp (((s * (Real.sqrt n)⁻¹
          * ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂P)
        - (((1 - v * (s * (Real.sqrt n)⁻¹) ^ 2 / 2) ^ n : ℝ) : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hB
      (Eventually.of_forall fun n => norm_nonneg _) hbound_ev
  have hΨ := hdiff.add hAexp.ofReal
  simp only [sub_add_cancel, zero_add] at hΨ
  exact hΨ.congr fun n => (hcharFun n).symm

/-- Under the constant-conditional-variance hypothesis, the normalizing variance `Var[u₁]` equals
the constant `v`. Taking expectations of `E[u₁² | ℱ₀] = v` gives `E[u₁²] = v`, and `E[u₁] = 0`
(the MDS mean-zero property) gives `Var[u₁] = E[u₁²] = v`. This is what ties
`charFun_tendsto_of_bounded_constCondVar` (whose target is `exp(-v s²/2)`) to the bundle field
`MDSCLTConditions.charFun_tendsto` (whose target is `exp(-Var[u₁] s²/2)`). -/
private theorem variance_eq_of_constCondVar (h : IsMDS ℱ u P) {v : ℝ}
    (hcondvar : ∀ t, P[fun ω => (u t ω) ^ 2 | ℱ (t - 1)] =ᵐ[P] fun _ => v) :
    variance (u 1) P = v := by
  have hsqint_v : ∫ ω, (u 1 ω) ^ 2 ∂P = v :=
    calc ∫ ω, (u 1 ω) ^ 2 ∂P
        = ∫ ω, (P[fun ω => (u 1 ω) ^ 2 | ℱ ((1 : ℤ) - 1)]) ω ∂P := (integral_condExp (ℱ.le _)).symm
      _ = ∫ ω, (fun _ => v) ω ∂P := integral_congr_ae (hcondvar 1)
      _ = v := by simp
  rw [variance_of_integral_eq_zero (h.integrable 1).aemeasurable (h.integral_eq_zero 1)]
  exact hsqint_v

/-- **Hansen Theorem 14.11, conditionally discharged (bounded constant-conditional-variance
case).** From the honest hypotheses — a strictly stationary, ergodic martingale difference
sequence that is uniformly bounded (`|uₜ| ≤ C` a.s.) with constant conditional variance
(`E[uₜ² | ℱₜ₋₁] = v` a.s.) — the full `MDSCLTConditions` bundle is *constructed* rather than
assumed: its analytic field `charFun_tendsto` is discharged by
`charFun_tendsto_of_bounded_constCondVar`, with `variance_eq_of_constCondVar` matching the
Gaussian limit. Consequently `MDSCLTConditions.central_limit` applies to deliver the
convergence-in-distribution conclusion without a bundle-level assumption. The uniform bound
supplies square-integrability (`MemLp _ 2`) automatically on the probability space. -/
def MDSCLTConditions.of_bounded_constCondVar (h : IsMDS ℱ u P)
    (hstat : IsStrictlyStationary u P) (herg : IsErgodicProcess u P)
    {C v : ℝ} (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C)
    (hcondvar : ∀ t, P[fun ω => (u t ω) ^ 2 | ℱ (t - 1)] =ᵐ[P] fun _ => v) :
    MDSCLTConditions ℱ u P where
  toIsMDS := h
  stationary := hstat
  ergodic := herg
  memLp_two t := (memLp_top_of_bound (h.integrable t).aestronglyMeasurable C
    ((hbdd t).mono fun ω hω => by rwa [Real.norm_eq_abs])).mono_exponent le_top
  charFun_tendsto s := by
    rw [variance_eq_of_constCondVar h hcondvar]
    exact charFun_tendsto_of_bounded_constCondVar h hbdd hcondvar s

/-! ### The bounded-ergodic McLeish martingale: definitions and the exact mean identity -/

/-- `mcExpu u θ k = exp(iθ u_{k+1})`, the per-step complex increment. -/
private noncomputable def mcExpu (u : ℤ → Ω → ℝ) (θ : ℝ) (k : ℕ) : Ω → ℂ :=
  fun ω => Complex.exp (((θ * u ((k : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)

/-- `mcPhi θ k = E[exp(iθ u_{k+1}) | ℱ k]`, the McLeish per-step conditional factor. -/
private noncomputable def mcPhi (P : Measure Ω) (ℱ : Filtration ℤ m) (u : ℤ → Ω → ℝ) (θ : ℝ)
    (k : ℕ) : Ω → ℂ := P[mcExpu u θ k | ℱ k]

/-- `mcExpS u θ k = exp(iθ Sₖ)` with `Sₖ = ∑_{t<k} u_{t+1}`. -/
private noncomputable def mcExpS (u : ℤ → Ω → ℝ) (θ : ℝ) (k : ℕ) : Ω → ℂ :=
  fun ω => Complex.exp (((θ * ∑ t ∈ Finset.range k, u ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)

/-- `mcProd θ n = ∏_{k<n} φ k`, the McLeish normalizing product. -/
private noncomputable def mcProd (P : Measure Ω) (ℱ : Filtration ℤ m) (u : ℤ → Ω → ℝ) (θ : ℝ)
    (n : ℕ) : Ω → ℂ := fun ω => ∏ k ∈ Finset.range n, mcPhi P ℱ u θ k ω

/-- `mcM θ n = exp(iθSₙ) / Pₙ`, the exact McLeish martingale. -/
private noncomputable def mcM (P : Measure Ω) (ℱ : Filtration ℤ m) (u : ℤ → Ω → ℝ) (θ : ℝ) (n : ℕ) :
    Ω → ℂ := fun ω => mcExpS u θ n ω * (mcProd P ℱ u θ n ω)⁻¹

omit [IsProbabilityMeasure P] in
private theorem mcExpu_norm (θ : ℝ) (k : ℕ) (ω : Ω) : ‖mcExpu u θ k ω‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

omit [IsProbabilityMeasure P] in
private theorem mcExpS_norm (θ : ℝ) (k : ℕ) (ω : Ω) : ‖mcExpS u θ k ω‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

omit [IsProbabilityMeasure P] in
private theorem mcExpu_aesm (h : IsMDS ℱ u P) (θ : ℝ) (k : ℕ) :
    AEStronglyMeasurable (mcExpu u θ k) P :=
  Complex.continuous_exp.comp_aestronglyMeasurable
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((h.integrable _).aestronglyMeasurable.const_mul θ)).mul_const _)

private theorem mcExpu_int (h : IsMDS ℱ u P) (θ : ℝ) (k : ℕ) : Integrable (mcExpu u θ k) P :=
  Integrable.of_bound (mcExpu_aesm h θ k) 1 (Eventually.of_forall fun ω => (mcExpu_norm θ k ω).le)

omit [IsProbabilityMeasure P] in
private theorem mcExpS_sm (h : IsMDS ℱ u P) (θ : ℝ) (k : ℕ) :
    StronglyMeasurable[ℱ (k : ℤ)] (mcExpS u θ k) := by
  have hS : StronglyMeasurable[ℱ (k : ℤ)] (fun ω => ∑ t ∈ Finset.range k, u ((t : ℤ) + 1) ω) := by
    refine Finset.stronglyMeasurable_fun_sum _ (fun t ht => ?_)
    simp only [Finset.mem_range] at ht
    exact ((h.adapted ((t : ℤ) + 1)).stronglyMeasurable).mono (ℱ.mono (by omega))
  exact Complex.continuous_exp.comp_stronglyMeasurable
    ((Complex.continuous_ofReal.comp_stronglyMeasurable (hS.const_mul θ)).mul_const _)

omit [IsProbabilityMeasure P] in
private theorem mcPhi_sm (θ : ℝ) (k : ℕ) : StronglyMeasurable[ℱ (k : ℤ)] (mcPhi P ℱ u θ k) :=
  stronglyMeasurable_condExp

omit [IsProbabilityMeasure P] in
private theorem mcPhi_inv_sm (θ : ℝ) (k : ℕ) :
    StronglyMeasurable[ℱ (k : ℤ)] (fun ω => (mcPhi P ℱ u θ k ω)⁻¹) := by
  have hh := mcPhi_sm (P := P) (ℱ := ℱ) (u := u) θ k
  rw [stronglyMeasurable_iff_measurable] at hh ⊢
  exact hh.inv

omit [IsProbabilityMeasure P] in
private theorem mcProd_sm_le (θ : ℝ) (k : ℕ) : StronglyMeasurable[ℱ (k : ℤ)] (mcProd P ℱ u θ k) :=
  Finset.stronglyMeasurable_fun_prod _ (fun j hj => by
    simp only [Finset.mem_range] at hj
    exact (mcPhi_sm θ j).mono (ℱ.mono (by exact_mod_cast hj.le)))

omit [IsProbabilityMeasure P] in
private theorem mcProd_inv_sm_le (θ : ℝ) (k : ℕ) :
    StronglyMeasurable[ℱ (k : ℤ)] (fun ω => (mcProd P ℱ u θ k ω)⁻¹) := by
  have hh := mcProd_sm_le (P := P) (ℱ := ℱ) (u := u) θ k
  rw [stronglyMeasurable_iff_measurable] at hh ⊢
  exact hh.inv

omit [IsProbabilityMeasure P] in
private theorem mcM_sm_le (h : IsMDS ℱ u P) (θ : ℝ) (k : ℕ) :
    StronglyMeasurable[ℱ (k : ℤ)] (mcM P ℱ u θ k) :=
  (mcExpS_sm h θ k).mul (mcProd_inv_sm_le θ k)

omit [IsProbabilityMeasure P] in
private theorem mcProd_inv_aesm (θ : ℝ) (n : ℕ) :
    AEStronglyMeasurable (fun ω => (mcProd P ℱ u θ n ω)⁻¹) P := by
  have hh : StronglyMeasurable[m] (mcProd P ℱ u θ n) :=
    Finset.stronglyMeasurable_fun_prod _ (fun j _ => (mcPhi_sm θ j).mono (ℱ.le _))
  have hh2 : StronglyMeasurable[m] (fun ω => (mcProd P ℱ u θ n ω)⁻¹) := by
    rw [stronglyMeasurable_iff_measurable] at hh ⊢; exact hh.inv
  exact hh2.aestronglyMeasurable

omit [IsProbabilityMeasure P] in
private theorem mcM_aesm (h : IsMDS ℱ u P) (θ : ℝ) (n : ℕ) :
    AEStronglyMeasurable (mcM P ℱ u θ n) P :=
  (((mcExpS_sm h θ n).mono (ℱ.le _)).aestronglyMeasurable).mul (mcProd_inv_aesm θ n)

/-- Per-factor a.e. lower bound `1 − θ²C²/2 ≤ ‖φ k‖`, from `norm_condExp_cexp_bounds`. -/
private theorem mcPhi_norm_lb (h : IsMDS ℱ u P) {C θ : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C) (k : ℕ) :
    ∀ᵐ ω ∂P, 1 - θ ^ 2 * C ^ 2 / 2 ≤ ‖mcPhi P ℱ u θ k ω‖ :=
  (norm_condExp_cexp_bounds (h.integrable ((k : ℤ) + 1)) (hbdd ((k : ℤ) + 1))).1

private theorem mcPhi_norm_le_one (h : IsMDS ℱ u P) {C θ : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C) (k : ℕ) :
    ∀ᵐ ω ∂P, ‖mcPhi P ℱ u θ k ω‖ ≤ 1 :=
  (norm_condExp_cexp_bounds (h.integrable ((k : ℤ) + 1)) (hbdd ((k : ℤ) + 1))).2

private theorem mcPhi_ne_zero (h : IsMDS ℱ u P) {C θ : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C) (hpos : 0 < 1 - θ ^ 2 * C ^ 2 / 2) (k : ℕ) :
    ∀ᵐ ω ∂P, mcPhi P ℱ u θ k ω ≠ 0 := by
  filter_upwards [mcPhi_norm_lb h hbdd k] with ω hω
  have hpp : (0 : ℝ) < ‖mcPhi P ℱ u θ k ω‖ := lt_of_lt_of_le hpos hω
  simpa using (norm_pos_iff.mp hpp)

private theorem mcProd_norm_lb (h : IsMDS ℱ u P) {C θ : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C) (hpos : 0 < 1 - θ ^ 2 * C ^ 2 / 2) (n : ℕ) :
    ∀ᵐ ω ∂P, (1 - θ ^ 2 * C ^ 2 / 2) ^ n ≤ ‖mcProd P ℱ u θ n ω‖ := by
  filter_upwards [ae_all_iff.mpr (fun k => mcPhi_norm_lb h hbdd k)] with ω hω
  simp only [mcProd, norm_prod]
  calc (1 - θ ^ 2 * C ^ 2 / 2) ^ n
      = ∏ _k ∈ Finset.range n, (1 - θ ^ 2 * C ^ 2 / 2) := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ k ∈ Finset.range n, ‖mcPhi P ℱ u θ k ω‖ :=
        Finset.prod_le_prod (fun k _ => hpos.le) (fun k _ => hω k)

private theorem mcProd_ne_zero (h : IsMDS ℱ u P) {C θ : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C) (hpos : 0 < 1 - θ ^ 2 * C ^ 2 / 2) (n : ℕ) :
    ∀ᵐ ω ∂P, mcProd P ℱ u θ n ω ≠ 0 := by
  filter_upwards [mcProd_norm_lb h hbdd hpos n] with ω hω
  have hpow : (0 : ℝ) < (1 - θ ^ 2 * C ^ 2 / 2) ^ n := pow_pos hpos n
  have hpp : (0 : ℝ) < ‖mcProd P ℱ u θ n ω‖ := lt_of_lt_of_le hpow hω
  simpa using (norm_pos_iff.mp hpp)

/-- Uniform a.e. upper bound `‖Mₙ‖ ≤ (1 − θ²C²/2)^{−n}` (the decorrelation `K` in the tail regime).
-/
private theorem mcM_norm_le (h : IsMDS ℱ u P) {C θ : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C) (hpos : 0 < 1 - θ ^ 2 * C ^ 2 / 2) (n : ℕ) :
    ∀ᵐ ω ∂P, ‖mcM P ℱ u θ n ω‖ ≤ ((1 - θ ^ 2 * C ^ 2 / 2) ^ n)⁻¹ := by
  filter_upwards [mcProd_norm_lb h hbdd hpos n] with ω hω
  have hpow : (0 : ℝ) < (1 - θ ^ 2 * C ^ 2 / 2) ^ n := pow_pos hpos n
  simp only [mcM, norm_mul, mcExpS_norm, one_mul, norm_inv]
  rw [inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le hpow hω

private theorem mcM_int (h : IsMDS ℱ u P) {C θ : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C) (hpos : 0 < 1 - θ ^ 2 * C ^ 2 / 2) (n : ℕ) :
    Integrable (mcM P ℱ u θ n) P :=
  Integrable.of_bound (mcM_aesm h θ n) _ (mcM_norm_le h hbdd hpos n)

omit [IsProbabilityMeasure P] in
/-- `exp(iθ S_{k+1}) = exp(iθ Sₖ)·exp(iθ u_{k+1})`. -/
private theorem mcExpS_succ (θ : ℝ) (k : ℕ) (ω : Ω) :
    mcExpS u θ (k + 1) ω = mcExpS u θ k ω * mcExpu u θ k ω := by
  simp only [mcExpS, mcExpu]
  rw [Finset.sum_range_succ, ← Complex.exp_add]
  congr 1
  push_cast; ring

omit [IsProbabilityMeasure P] in
/-- `M_{k+1} = M_k·(φ k)⁻¹·exp(iθ u_{k+1})` (pure field algebra on the product structure). -/
private theorem mcM_succ_eq (θ : ℝ) (k : ℕ) (ω : Ω) :
    mcM P ℱ u θ (k + 1) ω
      = mcM P ℱ u θ k ω * (mcPhi P ℱ u θ k ω)⁻¹ * mcExpu u θ k ω := by
  simp only [mcM, mcProd]
  rw [Finset.prod_range_succ, mcExpS_succ, mul_inv]
  ring

/-- **Piece E — the exact martingale step.** `E[M_{k+1} | ℱ k] = M_k` a.e. The ℱ k-measurable
factor `M_k·(φ k)⁻¹` pulls out of `E[exp(iθ u_{k+1}) | ℱ k] = φ k`, and `(φ k)⁻¹·φ k = 1` a.e. -/
private theorem mcM_condExp_step (h : IsMDS ℱ u P) {C θ : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C) (hpos : 0 < 1 - θ ^ 2 * C ^ 2 / 2) (k : ℕ) :
    P[mcM P ℱ u θ (k + 1) | ℱ (k : ℤ)] =ᵐ[P] mcM P ℱ u θ k := by
  have hf_sm : StronglyMeasurable[ℱ (k : ℤ)]
      (fun ω => mcM P ℱ u θ k ω * (mcPhi P ℱ u θ k ω)⁻¹) :=
    (mcM_sm_le h θ k).mul (mcPhi_inv_sm θ k)
  have hfg_eq : (fun ω => (mcM P ℱ u θ k ω * (mcPhi P ℱ u θ k ω)⁻¹) * mcExpu u θ k ω)
      = mcM P ℱ u θ (k + 1) := by
    funext ω; exact (mcM_succ_eq θ k ω).symm
  have hg_int : Integrable (mcExpu u θ k) P := mcExpu_int h θ k
  have hfg_int : Integrable
      (fun ω => (mcM P ℱ u θ k ω * (mcPhi P ℱ u θ k ω)⁻¹) * mcExpu u θ k ω) P := by
    rw [hfg_eq]; exact mcM_int h hbdd hpos (k + 1)
  have hpull := condExp_cmul_of_stronglyMeasurable_left (P := P) (j := (k : ℤ))
    (f := fun ω => mcM P ℱ u θ k ω * (mcPhi P ℱ u θ k ω)⁻¹) (g := mcExpu u θ k)
    hf_sm hfg_int hg_int
  have hne := mcPhi_ne_zero h hbdd hpos k
  have hstep1 : P[mcM P ℱ u θ (k + 1) | ℱ (k : ℤ)]
      = P[fun ω => (mcM P ℱ u θ k ω * (mcPhi P ℱ u θ k ω)⁻¹) * mcExpu u θ k ω | ℱ (k : ℤ)] := by
    rw [hfg_eq]
  rw [hstep1]
  refine hpull.trans ?_
  filter_upwards [hne] with ω hω
  change (mcM P ℱ u θ k ω * (mcPhi P ℱ u θ k ω)⁻¹) * mcPhi P ℱ u θ k ω = mcM P ℱ u θ k ω
  rw [mul_assoc, inv_mul_cancel₀ hω, mul_one]

/-- **`E[Mₙ] = 1` exactly** (forward induction peeling `E[· | ℱ k]`), the McLeish martingale mean
identity that the decorrelation lemma consumes. -/
private theorem mcM_integral_eq_one (h : IsMDS ℱ u P) {C θ : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C) (hpos : 0 < 1 - θ ^ 2 * C ^ 2 / 2) (n : ℕ) :
    ∫ ω, mcM P ℱ u θ n ω ∂P = 1 := by
  induction n with
  | zero =>
    have h0 : (fun ω => mcM P ℱ u θ 0 ω) = fun _ => (1 : ℂ) := by
      funext ω; simp [mcM, mcExpS, mcProd]
    rw [h0]; simp
  | succ k ih =>
    calc ∫ ω, mcM P ℱ u θ (k + 1) ω ∂P
        = ∫ ω, (P[mcM P ℱ u θ (k + 1) | ℱ (k : ℤ)]) ω ∂P :=
          (integral_condExp (ℱ.le (k : ℤ))).symm
      _ = ∫ ω, mcM P ℱ u θ k ω ∂P := integral_congr_ae (mcM_condExp_step h hbdd hpos k)
      _ = 1 := ih

/-- **Uniform bound `‖Mₙ‖ ≤ exp(−2nx)⁻¹`** (Piece E). With `x = θ²C²/2` and `θ = s/√n`, the
exponent `2nx = s²C²` is `n`-independent, giving `‖Mₙ‖ ≤ exp(s²C²)` — the decorrelation `K`. -/
private theorem mcM_norm_le_of_regime (h : IsMDS ℱ u P) {C θ x : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C) (hxeq : x = θ ^ 2 * C ^ 2 / 2) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1 / 2) (n : ℕ) :
    ∀ᵐ ω ∂P, ‖mcM P ℱ u θ n ω‖ ≤ (Real.exp (-(2 * ((n : ℝ) * x))))⁻¹ := by
  have hlb : ∀ k, ∀ᵐ ω ∂P, 1 - x ≤ ‖mcPhi P ℱ u θ k ω‖ := by
    intro k; rw [hxeq]; exact mcPhi_norm_lb h hbdd k
  have hprod := norm_prod_ge_of_ae_norm_ge (P := P) (φ := fun k => mcPhi P ℱ u θ k) hx0 hx1 hlb n
  filter_upwards [hprod] with ω hω
  have hpos : (0 : ℝ) < Real.exp (-(2 * ((n : ℝ) * x))) := Real.exp_pos _
  simp only [mcM, norm_mul, mcExpS_norm, one_mul, norm_inv]
  rw [inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos hω

/-- **`∫ v₀ = Var[u₁]`** (mirror of `variance_eq_of_constCondVar`). Since `v₀ = E[u₁² | ℱ₀]` a.e.,
`∫ v₀ = ∫ u₁²` by the tower law, and `E[u₁] = 0` gives `Var[u₁] = ∫ u₁²`. -/
private theorem integral_condVar_eq_variance (h : IsMDS ℱ u P) {v : ℤ → Ω → ℝ}
    (hv_link : ∀ t, v t =ᵐ[P] P[fun ω => (u (t + 1) ω) ^ 2 | ℱ t]) :
    ∫ ω, v 0 ω ∂P = variance (u 1) P := by
  have hsqint : ∫ ω, v 0 ω ∂P = ∫ ω, (u 1 ω) ^ 2 ∂P := by
    calc ∫ ω, v 0 ω ∂P
        = ∫ ω, (P[fun ω => (u ((0 : ℤ) + 1) ω) ^ 2 | ℱ (0 : ℤ)]) ω ∂P :=
          integral_congr_ae (hv_link 0)
      _ = ∫ ω, (u ((0 : ℤ) + 1) ω) ^ 2 ∂P := integral_condExp (ℱ.le (0 : ℤ))
      _ = ∫ ω, (u 1 ω) ^ 2 ∂P := by norm_num
  rw [variance_of_integral_eq_zero (h.integrable 1).aemeasurable (h.integral_eq_zero 1), hsqint]

/-- **Piece C per-factor bound.** `‖φ k − exp(−(θ²/2)·v k)‖ ≤ |θ|³C³/6 + (θ²C²/2)²` a.e.: the
conditional Taylor bound (`norm_condExp_cexp_sub_taylor_le`, with `v k =ᵐ E[u_{k+1}²|ℱ k]`) plus the
second-order exponential remainder `‖1 + z − exp z‖ ≤ ‖z‖²` (`Complex.norm_exp_sub_one_sub_id_le`).
-/
private theorem mcPhi_sub_gexp_bound (h : IsMDS ℱ u P) {C θ : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C) (hθ : θ ^ 2 * C ^ 2 ≤ 2)
    {v : ℤ → Ω → ℝ} (hv_nonneg : ∀ t, 0 ≤ᵐ[P] v t)
    (hv_link : ∀ t, v t =ᵐ[P] P[fun ω => (u (t + 1) ω) ^ 2 | ℱ t]) (k : ℕ) :
    ∀ᵐ ω ∂P, ‖mcPhi P ℱ u θ k ω - (Real.exp (-(θ ^ 2 / 2 * v (k : ℤ) ω)) : ℂ)‖
      ≤ |θ| ^ 3 * C ^ 3 / 6 + (θ ^ 2 * C ^ 2 / 2) ^ 2 := by
  have hsq_int : Integrable (fun ω => (u ((k : ℤ) + 1) ω) ^ 2) P := by
    refine Integrable.of_bound (((h.integrable ((k : ℤ) + 1)).aestronglyMeasurable).pow 2)
      (C ^ 2) ?_
    filter_upwards [hbdd ((k : ℤ) + 1)] with ω hω
    rw [norm_pow, Real.norm_eq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  have hmean : P[u ((k : ℤ) + 1) | ℱ (k : ℤ)] =ᵐ[P] 0 := by
    have hz := h.condExp_eq_zero ((k : ℤ) + 1)
    simpa only [add_sub_cancel_right] using hz
  have htaylor := norm_condExp_cexp_sub_taylor_le (P := P) (ℱ := ℱ) (θ := θ) (C := C) (j := (k : ℤ))
    (h.integrable ((k : ℤ) + 1)) hsq_int (hbdd ((k : ℤ) + 1)) hmean
  -- v k ≤ C² a.e.
  have hvle : v (k : ℤ) ≤ᵐ[P] fun _ => C ^ 2 := by
    have hb2 : (fun ω => (u ((k : ℤ) + 1) ω) ^ 2) ≤ᵐ[P] fun _ => C ^ 2 := by
      filter_upwards [hbdd ((k : ℤ) + 1)] with ω hω
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hω 2
    have hmono := condExp_mono (m := ℱ (k : ℤ)) hsq_int (integrable_const (C ^ 2)) hb2
    have hc : P[fun _ : Ω => C ^ 2 | ℱ (k : ℤ)] = fun _ => C ^ 2 := condExp_const (ℱ.le _) _
    filter_upwards [hv_link (k : ℤ), hmono] with ω h1 h2
    rw [h1]; rw [hc] at h2; exact h2
  filter_upwards [htaylor, hvle, hv_nonneg (k : ℤ), hv_link (k : ℤ)] with ω ht hle hnn hlink
  -- rewrite the Taylor centre in terms of v k
  set y : ℝ := θ ^ 2 / 2 * v (k : ℤ) ω with hy
  have hy0 : (0 : ℝ) ≤ y := by rw [hy]; exact mul_nonneg (by positivity) hnn
  have hyb : y ≤ θ ^ 2 * C ^ 2 / 2 := by
    rw [hy]
    calc θ ^ 2 / 2 * v (k : ℤ) ω ≤ θ ^ 2 / 2 * C ^ 2 :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = θ ^ 2 * C ^ 2 / 2 := by ring
  have hcond_eq : P[fun ω => (u ((k : ℤ) + 1) ω) ^ 2 | ℱ (k : ℤ)] ω = v (k : ℤ) ω := hlink.symm
  have ht' : ‖mcPhi P ℱ u θ k ω - ((1 - y : ℝ) : ℂ)‖ ≤ |θ| ^ 3 * C ^ 3 / 6 := by
    rw [hy]; rw [hcond_eq] at ht; exact ht
  -- exponential remainder
  set z : ℂ := ((-y : ℝ) : ℂ) with hz
  have hznorm : ‖z‖ = y := by
    rw [hz, show ((-y : ℝ) : ℂ) = -((y : ℝ) : ℂ) by push_cast; ring, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0]
  have hyle1 : y ≤ 1 := by nlinarith [hθ, hyb]
  have hexp : ‖((1 - y : ℝ) : ℂ) - (Real.exp (-y) : ℂ)‖ ≤ y ^ 2 := by
    have hcast : (Real.exp (-y) : ℂ) = Complex.exp z := by rw [hz, ← Complex.ofReal_exp]
    have hbnd := Complex.norm_exp_sub_one_sub_id_le (x := z) (by rw [hznorm]; exact hyle1)
    have heq : ((1 - y : ℝ) : ℂ) - (Real.exp (-y) : ℂ) = -(Complex.exp z - 1 - z) := by
      rw [hcast, hz]; push_cast; ring
    rw [heq, norm_neg]
    calc ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 := hbnd
      _ = y ^ 2 := by rw [hznorm]
  calc ‖mcPhi P ℱ u θ k ω - (Real.exp (-(θ ^ 2 / 2 * v (k : ℤ) ω)) : ℂ)‖
      = ‖mcPhi P ℱ u θ k ω - (Real.exp (-y) : ℂ)‖ := by rw [hy]
    _ ≤ ‖mcPhi P ℱ u θ k ω - ((1 - y : ℝ) : ℂ)‖ + ‖((1 - y : ℝ) : ℂ) - (Real.exp (-y) : ℂ)‖ := by
        have := norm_add_le (mcPhi P ℱ u θ k ω - ((1 - y : ℝ) : ℂ))
          (((1 - y : ℝ) : ℂ) - (Real.exp (-y) : ℂ))
        simpa using this
    _ ≤ |θ| ^ 3 * C ^ 3 / 6 + y ^ 2 := add_le_add ht' hexp
    _ ≤ |θ| ^ 3 * C ^ 3 / 6 + (θ ^ 2 * C ^ 2 / 2) ^ 2 := by
        have hysq : y ^ 2 ≤ (θ ^ 2 * C ^ 2 / 2) ^ 2 := by nlinarith [hy0, hyb]
        linarith

/-- **Piece C product bound.** `‖Pₙ − ∏ exp(−(θ²/2)vₖ)‖ ≤ n·(|θ|³C³/6 + (θ²C²/2)²)` a.e.:
`norm_prod_sub_prod_le_of_norm_le_one` (both factor families have modulus `≤ 1`) summed against the
per-factor bound `mcPhi_sub_gexp_bound`. -/
private theorem mcProd_sub_prod_gexp_bound (h : IsMDS ℱ u P) {C θ : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C) (hθ : θ ^ 2 * C ^ 2 ≤ 2)
    {v : ℤ → Ω → ℝ} (hv_nonneg : ∀ t, 0 ≤ᵐ[P] v t)
    (hv_link : ∀ t, v t =ᵐ[P] P[fun ω => (u (t + 1) ω) ^ 2 | ℱ t]) (n : ℕ) :
    ∀ᵐ ω ∂P, ‖mcProd P ℱ u θ n ω
        - ∏ k ∈ Finset.range n, (Real.exp (-(θ ^ 2 / 2 * v (k : ℤ) ω)) : ℂ)‖
      ≤ (n : ℝ) * (|θ| ^ 3 * C ^ 3 / 6 + (θ ^ 2 * C ^ 2 / 2) ^ 2) := by
  filter_upwards [ae_all_iff.mpr (fun k => mcPhi_sub_gexp_bound h hbdd hθ hv_nonneg hv_link k),
    ae_all_iff.mpr (fun k => mcPhi_norm_le_one (θ := θ) h hbdd k),
    ae_all_iff.mpr hv_nonneg] with ω hdiff hub' hnn
  have hgle : ∀ k : ℕ, ‖(Real.exp (-(θ ^ 2 / 2 * v (k : ℤ) ω)) : ℂ)‖ ≤ 1 := by
    intro k
    have hv0 : 0 ≤ v (k : ℤ) ω := hnn (k : ℤ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by nlinarith [hv0, sq_nonneg θ])
  simp only [mcProd]
  calc ‖(∏ k ∈ Finset.range n, mcPhi P ℱ u θ k ω)
        - ∏ k ∈ Finset.range n, (Real.exp (-(θ ^ 2 / 2 * v (k : ℤ) ω)) : ℂ)‖
      ≤ ∑ k ∈ Finset.range n,
          ‖mcPhi P ℱ u θ k ω - (Real.exp (-(θ ^ 2 / 2 * v (k : ℤ) ω)) : ℂ)‖ :=
        norm_prod_sub_prod_le_of_norm_le_one hub' hgle n
    _ ≤ ∑ k ∈ Finset.range n, (|θ| ^ 3 * C ^ 3 / 6 + (θ ^ 2 * C ^ 2 / 2) ^ 2) :=
        Finset.sum_le_sum (fun k _ => hdiff k)
    _ = (n : ℝ) * (|θ| ^ 3 * C ^ 3 / 6 + (θ ^ 2 * C ^ 2 / 2) ^ 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

omit [IsProbabilityMeasure P] in
private theorem mcProd_aesm (θ : ℝ) (n : ℕ) : AEStronglyMeasurable (mcProd P ℱ u θ n) P :=
  ((mcProd_sm_le θ n).mono (ℱ.le _)).aestronglyMeasurable

private theorem mcProd_le_one (h : IsMDS ℱ u P) {C θ : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C) (n : ℕ) :
    ∀ᵐ ω ∂P, ‖mcProd P ℱ u θ n ω‖ ≤ 1 := by
  filter_upwards [ae_all_iff.mpr (fun k => mcPhi_norm_le_one (θ := θ) h hbdd k)] with ω hub
  simp only [mcProd, norm_prod]
  calc ∏ k ∈ Finset.range n, ‖mcPhi P ℱ u θ k ω‖
      ≤ ∏ _k ∈ Finset.range n, (1 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun k _ => hub k)
    _ = 1 := by simp

/-- **Piece C — `Pₙ → exp(−Var·s²/2)` in `L¹`.** `∫‖Pₙ − exp(−(s²/2)∫v₀)‖ → 0`: split through the
Gaussian factor `Gₙ = exp(−(θ²/2)∑vₖ)`; `‖Pₙ − Gₙ‖ ≤ n·(|θ|³C³/6+(θ²C²/2)²) → 0` (Piece C product
bound, eventual regime) and `‖Gₙ − exp(−(s²/2)∫v₀)‖ → 0` in `L¹` by the ergodic normalization. -/
private theorem mcProd_tendsto_integral_norm_sub (h : IsMDS ℱ u P) {C : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C)
    {v : ℤ → Ω → ℝ} (hv_erg : IsErgodicProcess v P) (hv_meas : ∀ t, AEMeasurable (v t) P)
    (hv_int : Integrable (v 0) P) (hv_nonneg : ∀ t, 0 ≤ᵐ[P] v t)
    (hv_link : ∀ t, v t =ᵐ[P] P[fun ω => (u (t + 1) ω) ^ 2 | ℱ t]) (s : ℝ) :
    Tendsto (fun n : ℕ => ∫ ω, ‖mcProd P ℱ u (s / Real.sqrt n) n ω
        - (Real.exp (-(s ^ 2 / 2 * ∫ ω, v 0 ω ∂P)) : ℂ)‖ ∂P) atTop (𝓝 0) := by
  set A : ℝ := ∫ ω, v 0 ω ∂P with hA
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg_of_ae (hv_nonneg 0)
  -- limits of the normalizers
  have hsqrtinv : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hninv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  -- measurability / boundedness / integrability of the two families
  have hsum_aem : ∀ n : ℕ, AEMeasurable (fun ω => ∑ t ∈ Finset.range n, v (t : ℤ) ω) P :=
    fun n => Finset.aemeasurable_fun_sum _ (fun t _ => hv_meas _)
  have hGc_aesm : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω => (Real.exp
        (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)) P :=
    fun n => Complex.continuous_ofReal.comp_aestronglyMeasurable
      (Real.continuous_exp.measurable.comp_aemeasurable
        ((((hsum_aem n).const_mul _).const_mul _).neg)).aestronglyMeasurable
  have hGc_le1 : ∀ n : ℕ, ∀ᵐ ω ∂P,
      ‖(Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)‖ ≤ 1 := by
    intro n
    filter_upwards [ae_all_iff.mpr hv_nonneg] with ω hnn
    have havg0 : 0 ≤ (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun t _ => hnn (t : ℤ))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by nlinarith [havg0, sq_nonneg s])
  have hc_le1 : ‖(Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by nlinarith [hA0, sq_nonneg s])
  have hProd_int : ∀ n : ℕ, Integrable (mcProd P ℱ u (s / Real.sqrt n) n) P :=
    fun n => Integrable.of_bound (mcProd_aesm _ n) 1 (mcProd_le_one h hbdd n)
  have hGc_int : ∀ n : ℕ, Integrable
      (fun ω => (Real.exp
        (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)) P :=
    fun n => Integrable.of_bound (hGc_aesm n) 1 (hGc_le1 n)
  have hc_int : Integrable (fun _ : Ω => (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)) P := integrable_const _
  -- Term 2: the ergodic factor converges in L¹.
  have hMET := tendsto_eLpNorm_exp_neg_average_sub hv_erg hv_meas hv_int hv_nonneg
    (lam := s ^ 2 / 2) (by positivity)
  have hT2 : Tendsto (fun n : ℕ => ∫ ω,
      ‖(Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)
        - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖ ∂P) atTop (𝓝 0) := by
    have hbridge : ∀ n : ℕ, (∫ ω,
        ‖(Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)
          - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖ ∂P)
        = (eLpNorm (fun ω =>
            Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω)))
            - Real.exp (-(s ^ 2 / 2 * A))) 1 P).toReal := by
      intro n
      have hpt : ∀ ω,
          ‖(Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)
            - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖
          = ‖Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω)))
            - Real.exp (-(s ^ 2 / 2 * A))‖ := by
        intro ω
        rw [← Complex.ofReal_sub, Complex.norm_real]
      have haesm : AEStronglyMeasurable
          (fun ω => Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω)))
            - Real.exp (-(s ^ 2 / 2 * A))) P :=
        (Real.continuous_exp.measurable.comp_aemeasurable
          ((((hsum_aem n).const_mul _).const_mul _).neg)).aestronglyMeasurable.sub
          aestronglyMeasurable_const
      rw [integral_congr_ae (Eventually.of_forall hpt),
        integral_norm_eq_lintegral_enorm haesm, eLpNorm_one_eq_lintegral_enorm]
    have hconv : Tendsto (fun n : ℕ => (eLpNorm (fun ω =>
        Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω)))
          - Real.exp (-(s ^ 2 / 2 * A))) 1 P).toReal) atTop (𝓝 0) := by
      have hcomp := (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hMET
      rw [← hA] at hcomp
      simpa using hcomp
    exact (Tendsto.congr (fun n => (hbridge n).symm) hconv)
  -- Bₙ → 0.
  set Bn : ℕ → ℝ := fun n => (n : ℝ) *
    (|s / Real.sqrt n| ^ 3 * C ^ 3 / 6 + ((s / Real.sqrt n) ^ 2 * C ^ 2 / 2) ^ 2) with hBndef
  have hBn : Tendsto Bn atTop (𝓝 0) := by
    have hEq : ∀ n : ℕ,
        Bn n = |s| ^ 3 * C ^ 3 / 6 * (Real.sqrt n)⁻¹ + s ^ 4 * C ^ 4 / 4 * ((n : ℝ)⁻¹) := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hBndef]
      · have hrpos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
        have hrn : (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt (by positivity)).symm
        simp only [hBndef]
        rw [abs_div, abs_of_pos hrpos]
        set r := Real.sqrt n with hrdef
        rw [hrn]
        have hr0 : r ≠ 0 := hrpos.ne'
        field_simp
        ring
    have hrhs : Tendsto (fun n : ℕ =>
        |s| ^ 3 * C ^ 3 / 6 * (Real.sqrt n)⁻¹ + s ^ 4 * C ^ 4 / 4 * ((n : ℝ)⁻¹)) atTop (𝓝 0) := by
      simpa using
        (hsqrtinv.const_mul (|s| ^ 3 * C ^ 3 / 6)).add (hninv.const_mul (s ^ 4 * C ^ 4 / 4))
    exact hrhs.congr fun n => (hEq n).symm
  -- eventual regime for the product bound.
  have hlim : Tendsto (fun n : ℕ => (s / Real.sqrt n) ^ 2 * C ^ 2) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => s ^ 2 * C ^ 2 * ((Real.sqrt n)⁻¹) ^ 2) atTop (𝓝 0) := by
      simpa using ((hsqrtinv.pow 2).const_mul (s ^ 2 * C ^ 2))
    refine h0.congr (fun n => ?_)
    rw [div_pow, inv_pow]; ring
  have hregime : ∀ᶠ n : ℕ in atTop, (s / Real.sqrt n) ^ 2 * C ^ 2 ≤ 2 :=
    hlim.eventually_le_const (show (0 : ℝ) < 2 by norm_num)
  -- eventual upper bound A_target ≤ Bₙ + T2ₙ.
  have hUp : ∀ᶠ n : ℕ in atTop,
      (∫ ω, ‖mcProd P ℱ u (s / Real.sqrt n) n ω - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖ ∂P)
      ≤ Bn n + ∫ ω,
        ‖(Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)
          - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖ ∂P := by
    filter_upwards [hregime] with n hθ
    -- Gₙ = ∏ exp(−(θ²/2)vₖ).
    have hGprod : ∀ ω, (∏ k ∈ Finset.range n,
          (Real.exp (-((s / Real.sqrt n) ^ 2 / 2 * v (k : ℤ) ω)) : ℂ))
        = (Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ) := by
      intro ω
      rw [← Complex.ofReal_prod]
      congr 1
      rw [← Real.exp_sum]
      congr 1
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
        have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        have hc12 : (s / Real.sqrt n) ^ 2 / 2 = s ^ 2 / 2 * (n : ℝ)⁻¹ := by
          rw [div_pow, hsq]; field_simp
        calc ∑ k ∈ Finset.range n, -((s / Real.sqrt n) ^ 2 / 2 * v (k : ℤ) ω)
            = ∑ k ∈ Finset.range n, -(s ^ 2 / 2 * (n : ℝ)⁻¹ * v (k : ℤ) ω) := by
              simp_rw [hc12]
          _ = -(s ^ 2 / 2 * (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, v (k : ℤ) ω) := by
              rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
          _ = -(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω)) := by ring
    -- pointwise triangle bound.
    have hae : ∀ᵐ ω ∂P,
        ‖mcProd P ℱ u (s / Real.sqrt n) n ω - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖
        ≤ Bn n + ‖(Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)
            - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖ := by
      filter_upwards [mcProd_sub_prod_gexp_bound h hbdd hθ hv_nonneg hv_link n] with ω hpc
      rw [hGprod ω] at hpc
      calc ‖mcProd P ℱ u (s / Real.sqrt n) n ω - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖
          ≤ ‖mcProd P ℱ u (s / Real.sqrt n) n ω
              - (Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)‖
            + ‖(Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)
              - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖ := by
            rw [show mcProd P ℱ u (s / Real.sqrt n) n ω - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)
                = (mcProd P ℱ u (s / Real.sqrt n) n ω
                    - (Real.exp
                        (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ))
                  + ((Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)
                    - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)) from by ring]
            exact norm_add_le _ _
        _ ≤ Bn n + ‖(Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)
              - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖ := by
            have hpc' : ‖mcProd P ℱ u (s / Real.sqrt n) n ω
                - (Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)‖
                ≤ Bn n := hpc
            linarith [hpc']
    calc (∫ ω, ‖mcProd P ℱ u (s / Real.sqrt n) n ω - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖ ∂P)
        ≤ ∫ ω, (Bn n
            + ‖(Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)
              - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖) ∂P := by
          refine integral_mono_ae ((hProd_int n).sub hc_int).norm ?_ hae
          exact (integrable_const _).add ((hGc_int n).sub hc_int).norm
      _ = Bn n + ∫ ω,
            ‖(Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)
              - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖ ∂P := by
          have h1 : (∫ ω, (Bn n
              + ‖(Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)
                - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖) ∂P)
              = (∫ _ω : Ω, Bn n ∂P) + ∫ ω,
                ‖(Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)
                  - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖ ∂P :=
            integral_add (integrable_const (Bn n)) ((hGc_int n).sub hc_int).norm
          rw [h1]; simp
  -- squeeze.
  have hUpper : Tendsto (fun n : ℕ => Bn n + ∫ ω,
      ‖(Real.exp (-(s ^ 2 / 2 * ((n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, v (t : ℤ) ω))) : ℂ)
        - (Real.exp (-(s ^ 2 / 2 * A)) : ℂ)‖ ∂P) atTop (𝓝 0) := by
    simpa using hBn.add hT2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
    (Eventually.of_forall fun n => integral_nonneg fun ω => norm_nonneg _) hUp

/-! ### The glue: the McLeish decorrelation to `charFun_tendsto`, and the bundle -/

private theorem mcExpS_int (h : IsMDS ℱ u P) (θ : ℝ) (n : ℕ) : Integrable (mcExpS u θ n) P :=
  Integrable.of_bound ((mcExpS_sm h θ n).mono (ℱ.le _)).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => (mcExpS_norm θ n ω).le)

/-- `Mₙ·Pₙ = exp(iθSₙ)` a.e. (where `Pₙ ≠ 0`), so `∫ Mₙ Pₙ = ∫ exp(iθSₙ)`. -/
private theorem mcM_mul_mcProd (h : IsMDS ℱ u P) {C θ : ℝ} (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C)
    (hpos : 0 < 1 - θ ^ 2 * C ^ 2 / 2) (n : ℕ) :
    (fun ω => mcM P ℱ u θ n ω * mcProd P ℱ u θ n ω) =ᵐ[P] mcExpS u θ n := by
  filter_upwards [mcProd_ne_zero h hbdd hpos n] with ω hne
  simp only [mcM]
  rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]

/-- Regime arithmetic: `θ²C²/2 ≤ 1/2` when `s²C² ≤ n` (with `θ = s/√n`). -/
private theorem mc_x_le_half {s C : ℝ} {n : ℕ} (hn : s ^ 2 * C ^ 2 ≤ (n : ℝ)) (hnpos : 0 < n) :
    (s / Real.sqrt n) ^ 2 * C ^ 2 / 2 ≤ 1 / 2 := by
  have hnpos' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hθsq : (s / Real.sqrt n) ^ 2 = s ^ 2 / (n : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
  rw [hθsq, show s ^ 2 / (n : ℝ) * C ^ 2 / 2 = s ^ 2 * C ^ 2 / (2 * (n : ℝ)) from by
    field_simp, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (n : ℝ))]
  nlinarith [hn]

/-- **Uniform bound `‖Mₙ‖ ≤ exp(s²C²)`** for `s²C² ≤ n` (the decorrelation `K`, `n`-independent). -/
private theorem mcM_norm_le_exp (h : IsMDS ℱ u P) {C : ℝ} (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C)
    {s : ℝ} {n : ℕ} (hn : s ^ 2 * C ^ 2 ≤ (n : ℝ)) (hnpos : 0 < n) :
    ∀ᵐ ω ∂P, ‖mcM P ℱ u (s / Real.sqrt n) n ω‖ ≤ Real.exp (s ^ 2 * C ^ 2) := by
  have hnpos' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hθsq : (s / Real.sqrt n) ^ 2 = s ^ 2 / (n : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
  have hx0 : (0 : ℝ) ≤ (s / Real.sqrt n) ^ 2 * C ^ 2 / 2 := by positivity
  have hbound := mcM_norm_le_of_regime h hbdd rfl hx0 (mc_x_le_half hn hnpos) n
  have hnx : (2 : ℝ) * ((n : ℝ) * ((s / Real.sqrt n) ^ 2 * C ^ 2 / 2)) = s ^ 2 * C ^ 2 := by
    rw [hθsq]; field_simp
  filter_upwards [hbound] with ω hω
  rwa [hnx, Real.exp_neg, inv_inv] at hω

/-- **Hansen 14.11 analytic core, discharged for bounded stationary–ergodic MDS (Hall–Heyde variance
hypotheses).** `charFun` of the normalized partial sums converges to `exp(−Var[u₁]·s²/2)`. The
McLeish martingale `Mₙ = exp(iθSₙ)/Pₙ` with `∫Mₙ = 1` and `‖Mₙ‖ ≤ exp(s²C²)` (uniform), together
with `Pₙ → exp(−Var·s²/2)` in `L¹`, feeds the decorrelation lemma; the small-`n` regime failure is
sidestepped by reindexing by `N ≥ s²C²`. -/
theorem charFun_tendsto_of_bounded_ergodic (h : IsMDS ℱ u P) {C : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C)
    {v : ℤ → Ω → ℝ} (hv_erg : IsErgodicProcess v P) (hv_meas : ∀ t, AEMeasurable (v t) P)
    (hv_int : Integrable (v 0) P) (hv_nonneg : ∀ t, 0 ≤ᵐ[P] v t)
    (hv_link : ∀ t, v t =ᵐ[P] P[fun ω => (u (t + 1) ω) ^ 2 | ℱ t]) (s : ℝ) :
    Filter.Tendsto (fun n : ℕ => charFun
      (P.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω)) s)
      Filter.atTop (nhds (Complex.exp (-(variance (u 1) P : ℂ) * (s : ℂ) ^ 2 / 2))) := by
  -- `charFun` of the pushforward is `∫ exp(iθSₙ) = ∫ mcExpS`.
  have hcharFun : ∀ n : ℕ, charFun (P.map (fun ω => (Real.sqrt (n : ℝ))⁻¹
        * ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω)) s
      = ∫ ω, mcExpS u (s / Real.sqrt n) n ω ∂P := by
    intro n
    have hφ : AEMeasurable (fun ω => (Real.sqrt (n : ℝ))⁻¹
        * ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω) P :=
      (Finset.aemeasurable_fun_sum (Finset.range n)
        fun i _ => (h.integrable ((i : ℤ) + 1)).aemeasurable).const_mul ((Real.sqrt (n : ℝ))⁻¹)
    have haesm : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((s : ℂ) * (x : ℂ) * Complex.I))
        (P.map (fun ω => (Real.sqrt (n : ℝ))⁻¹ * ∑ t ∈ Finset.range n, u ((t : ℤ) + 1) ω)) :=
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    rw [charFun_apply_real, integral_map hφ haesm]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [mcExpS]
    push_cast; ring_nf
  -- reindex offset `N ≥ s²C²`.
  set N : ℕ := Nat.ceil (s ^ 2 * C ^ 2) + 1 with hNdef
  have hN1 : 1 ≤ N := Nat.le_add_left 1 _
  have hn_shift : ∀ k : ℕ, s ^ 2 * C ^ 2 ≤ ((k + N : ℕ) : ℝ) := by
    intro k
    have hle : s ^ 2 * C ^ 2 ≤ (Nat.ceil (s ^ 2 * C ^ 2) : ℝ) := Nat.le_ceil _
    have : ((k + N : ℕ) : ℝ) = (k : ℝ) + ((Nat.ceil (s ^ 2 * C ^ 2) : ℝ) + 1) := by
      rw [hNdef]; push_cast; ring
    rw [this]; have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    linarith
  have hnpos_shift : ∀ k : ℕ, 0 < k + N := fun k => by omega
  have hpos_shift : ∀ k : ℕ, 0 < 1 - (s / Real.sqrt ((k + N : ℕ) : ℝ)) ^ 2 * C ^ 2 / 2 :=
    fun k => by linarith [mc_x_le_half (hn_shift k) (hnpos_shift k)]
  -- the target constant = Piece C constant.
  have hc_eq : (Real.exp (-(s ^ 2 / 2 * ∫ ω, v 0 ω ∂P)) : ℂ)
      = Complex.exp (-(variance (u 1) P : ℂ) * (s : ℂ) ^ 2 / 2) := by
    rw [integral_condVar_eq_variance h hv_link, Complex.ofReal_exp]
    congr 1; push_cast; ring
  -- decorrelation on the shifted sequences.
  have hdecorr := tendsto_integral_mul_of_tendsto_integral_norm_sub
    (M := fun k => mcM P ℱ u (s / Real.sqrt ((k + N : ℕ) : ℝ)) (k + N))
    (Q := fun k => mcProd P ℱ u (s / Real.sqrt ((k + N : ℕ) : ℝ)) (k + N))
    (c := (Real.exp (-(s ^ 2 / 2 * ∫ ω, v 0 ω ∂P)) : ℂ)) (K := Real.exp (s ^ 2 * C ^ 2))
    (fun k => mcM_int h hbdd (hpos_shift k) (k + N))
    (fun k => Integrable.of_bound (mcProd_aesm _ (k + N)) 1 (mcProd_le_one h hbdd (k + N)))
    (fun k => (mcExpS_int h _ (k + N)).congr (mcM_mul_mcProd h hbdd (hpos_shift k) (k + N)).symm)
    (fun k => mcM_integral_eq_one h hbdd (hpos_shift k) (k + N))
    (fun k => mcM_norm_le_exp h hbdd (hn_shift k) (hnpos_shift k))
    ((mcProd_tendsto_integral_norm_sub h hbdd hv_erg hv_meas hv_int hv_nonneg hv_link s).comp
      (tendsto_add_atTop_nat N))
  -- rewrite `∫ Mₖ Pₖ = charFun` and reindex back.
  have hshift : Tendsto (fun k : ℕ => charFun (P.map (fun ω => (Real.sqrt ((k + N : ℕ) : ℝ))⁻¹
        * ∑ t ∈ Finset.range (k + N), u ((t : ℤ) + 1) ω)) s) atTop
      (𝓝 (Real.exp (-(s ^ 2 / 2 * ∫ ω, v 0 ω ∂P)) : ℂ)) := by
    refine hdecorr.congr (fun k => ?_)
    rw [integral_congr_ae (mcM_mul_mcProd h hbdd (hpos_shift k) (k + N)), ← hcharFun (k + N)]
  rw [← hc_eq]
  exact (tendsto_add_atTop_iff_nat N).mp hshift

/-- **Hansen Theorem 14.11, discharged for bounded stationary–ergodic MDS (Hall–Heyde variance
hypotheses).** From the honest hypotheses — a strictly stationary, ergodic, uniformly bounded MDS
with a stationary–ergodic, integrable, nonnegative conditional-variance process
`vₜ = E[u_{t+1}²|ℱₜ]` — the full `MDSCLTConditions` bundle is *constructed*: its analytic field is
discharged by `charFun_tendsto_of_bounded_ergodic`. The remaining delta to Hansen's literal
statement is unboundedness (a truncation layer, future work). -/
def MDSCLTConditions.of_bounded_ergodic (h : IsMDS ℱ u P)
    (hstat : IsStrictlyStationary u P) (herg : IsErgodicProcess u P)
    {C : ℝ} (hbdd : ∀ t, ∀ᵐ ω ∂P, |u t ω| ≤ C)
    {v : ℤ → Ω → ℝ} (hv_erg : IsErgodicProcess v P) (hv_meas : ∀ t, AEMeasurable (v t) P)
    (hv_int : Integrable (v 0) P) (hv_nonneg : ∀ t, 0 ≤ᵐ[P] v t)
    (hv_link : ∀ t, v t =ᵐ[P] P[fun ω => (u (t + 1) ω) ^ 2 | ℱ t]) :
    MDSCLTConditions ℱ u P where
  toIsMDS := h
  stationary := hstat
  ergodic := herg
  memLp_two t := (memLp_top_of_bound (h.integrable t).aestronglyMeasurable C
    ((hbdd t).mono fun ω hω => by rwa [Real.norm_eq_abs])).mono_exponent le_top
  charFun_tendsto s :=
    charFun_tendsto_of_bounded_ergodic h hbdd hv_erg hv_meas hv_int hv_nonneg hv_link s

end Probabilistic

/-!
## Status — bounded-ergodic McLeish route discharged; remaining delta = unboundedness

Hansen Theorem 14.11 is now **discharged for a bounded stationary–ergodic MDS** under the Hall–Heyde
conditional-variance hypotheses (`charFun_tendsto_of_bounded_ergodic`,
`MDSCLTConditions.of_bounded_ergodic`), zero sorries and kernel-clean. The full McLeish assembly is
in place, dependency-ordered:

1. **Definitions.** `mcExpu`, `mcPhi θ k = E[exp(iθ u_{k+1}) | ℱ k]`, `mcExpS θ k = exp(iθ Sₖ)`,
   `mcProd θ n = ∏_{k<n} φ k`, `mcM θ n = exp(iθSₙ)·(Pₙ)⁻¹` (division is `⁻¹` in the field `ℂ`, so
   the null set `Pₙ = 0` is harmless). A/e nonvanishing `Pₙ ≠ 0` is `mcProd_ne_zero`.

2. **Piece E — `E[Mₙ] = 1`** (`mcM_integral_eq_one`, forward induction peeling `E[·|ℱ k]`). One
   correction to the earlier design note: `φ k⁻¹` is `StronglyMeasurable[ℱ k]` but **not** by a free
   `StronglyMeasurable.inv` — `ℂ` has no `ContinuousInv` (inv is discontinuous at `0`). The valid
   route is `stronglyMeasurable_iff_measurable` ▸ `Measurable.inv` (via `MeasurableInv₀`), packaged
   as `mcPhi_inv_sm`. With that, the plain `condExp_cmul_of_stronglyMeasurable_left` pulls the
   `ℱ k`-measurable factor `Mₖ·φ k⁻¹` out of `E[exp(iθu_{k+1})|ℱ k] = φ k` (`mcM_condExp_step`).

3. **Piece C — `Pₙ → exp(−s²·Var[u₁]/2)` in `L¹`** (`mcProd_tendsto_integral_norm_sub`). Compare
   `Pₙ` to the real Gaussian factor `Gₙ = ∏ₖ exp(−(θ²/2)vₖ)`:
   `‖Pₙ − Gₙ‖ ≤ n·(|θ|³C³/6 + (θ²C²/2)²) → 0` a.e. (`mcProd_sub_prod_gexp_bound`, from the
   conditional Taylor bound `norm_condExp_cexp_sub_taylor_le` plus
   `Complex.norm_exp_sub_one_sub_id_le`), then `‖Gₙ − exp(−s²Var/2)‖ → 0` in `L¹` by the ergodic
   normalization `tendsto_eLpNorm_exp_neg_average_sub` and the eLpNorm↔Bochner bridge.

4. **Gluing** (`charFun_tendsto_of_bounded_ergodic`). `∫ exp(iθSₙ) = ∫ Mₙ·Pₙ` (`mcM_mul_mcProd`) →
   `exp(−Var·s²/2)` via `tendsto_integral_mul_of_tendsto_integral_norm_sub`, with `‖Mₙ‖ ≤ exp(s²C²)`
   uniform (`mcM_norm_le_exp`) and `∫ v₀ = Var[u₁]` (`integral_condVar_eq_variance`). The small-`n`
   regime failure (`θ²C² ≥ 2`, where `Mₙ` degenerates) is sidestepped by reindexing by `N ≥ s²C²`
   (`Tendsto` is tail-insensitive) — see the shift in the glue.

**Remaining delta to Hansen's literal statement: unboundedness.** The uniform bound `|uₜ| ≤ C` is
used throughout (nonvanishing of `φ`, the `|θ|³C³` Taylor remainder, the uniform `K`). Extending to
a general square-integrable stationary–ergodic MDS requires a truncation layer
`uₜ = uₜ·1{|uₜ|≤Cₘ} + …` with `Cₘ → ∞`, a Slutsky/tightness argument controlling the truncation
error — a separate wave.
-/

end ProbabilityTheory
